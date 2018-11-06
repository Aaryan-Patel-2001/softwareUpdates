Require Import POCS.

Require Import Examples.Logging.Impl.
Require Import Helpers.Array.

Require Import Spec.HoareTactics.

Record LogicalState :=
  { ls_disk : disk;
    ls_log : list (addr * block);
  }.

Inductive DiskDecode (d: disk) (ls: LogicalState) : Prop :=
| disk_decode
    (Hsize: 2 + LOG_LENGTH + diskSize ls.(ls_disk) = diskSize d)
    (Hdisk: forall i, i <= diskSize ls.(ls_disk) -> diskGet ls.(ls_disk) i = diskGet d (i + 258)).

Inductive LogDecode (d: disk) (ls: LogicalState) : Prop :=
| log_decode bhdr bdesc hdr desc 
    (Hbhdr: diskGet d O = Some bhdr)
    (Hbdesc: diskGet d 1 = Some bdesc)
    (Hhdr_dec : LogHdr_fmt.(decode) bhdr = hdr)
    (Hdesc_dec : Descriptor_fmt.(decode) bdesc = desc)
    (Hlog_length: length ls.(ls_log) <= LOG_LENGTH)
    (Hlog: forall i, i < hdr.(log_length) ->
                     exists a b,
                       sel ls.(ls_log) i = (a, b) /\
                       sel desc.(addresses) i = a /\
                       diskGet d (2 + i) = Some b):
    LogDecode d ls.

Definition disk_invariant (d: disk) :=
  diskSize d >= 2 + LOG_LENGTH.

Record PhysicalState :=
  { p_hdr: LogHdr;
    p_desc: Descriptor;
    p_log_values: list block;
    p_data_region: disk; }.

Definition PhyDecode (d: disk) : option PhysicalState :=
  match diskGet d 0, diskGet d 1 with
  | Some bhdr, Some bdesc =>
    Some {| p_hdr := LogHdr_fmt.(decode) bhdr;
            p_desc := Descriptor_fmt.(decode) bdesc;
            p_log_values := diskSubslice d 2 (LOG_LENGTH);
            p_data_region := diskSubslice d (2+LOG_LENGTH) (diskSize d - (2 + LOG_LENGTH)); |}
  | _, _ => None
  end.

Theorem PhyDecode_invariant : forall d,
    disk_invariant d ->
    exists ps, PhyDecode d = Some ps /\
          (exists b, diskGet d 0 = Some b /\
                LogHdr_fmt.(decode) b = ps.(p_hdr)) /\
          (exists b, diskGet d 1 = Some b /\
                Descriptor_fmt.(decode) b = ps.(p_desc)) /\
          length ps.(p_log_values) = LOG_LENGTH /\
          2 + LOG_LENGTH + diskSize ps.(p_data_region) = diskSize d.
Proof.
  unfold disk_invariant; intros.
  unfold PhyDecode.
  edestruct (@disk_inbounds_exists 0 d); try omega.
  edestruct (@disk_inbounds_exists 1 d); try omega.
  repeat simpl_match.
  descend; (intuition idtac);
    cbn [p_hdr p_desc p_log_values p_data_region].
  - descend; intuition eauto.
  - descend; intuition eauto.
  - simpl; autorewrite with disk_size; auto.
  - autorewrite with disk_size.
    omega.
Qed.

Inductive CommitStatus d b : Prop :=
| commit_status bhdr 
    (Hbhdr: diskGet d O = Some bhdr)
    (Hstatus : (LogHdr_fmt.(decode) bhdr).(committed) = b):
    CommitStatus d b.

Fixpoint logical_log_apply (l: list (addr * block)) (d: disk)  : disk :=
  match l with
  | nil => d
  | (a, b) :: l' => logical_log_apply l' (diskUpd d (2+LOG_LENGTH+a) b)
  end.

Definition ls_snoc ls a v : LogicalState :=
  {| ls_disk := ls_disk ls;
     ls_log := ls_log ls ++ ((a, v) :: nil) |}.

Definition ls_clear ls : LogicalState :=
  {| ls_disk := ls_disk ls;
     ls_log := nil |}.

Definition log_write_cspec ls (a: addr) (v: block) : Specification TxnD.WriteStatus unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' status =>
                match status with
                | TxnD.WriteErr => state' = state
                | TxnD.WriteOK =>
                  LogDecode state' (ls_snoc ls a v)
                  /\ DiskDecode state' (ls_snoc ls a v)
                  /\ CommitStatus state' false
                end;
      alternate := fun state' _ => DiskDecode state' ls /\ CommitStatus state' false
    |}.
                  
Definition log_size_cspec ls : Specification nat unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' sz => state = state' /\ sz = diskSize ls.(ls_disk);
      alternate := fun state' _ => state = state'
    |}.
    
Definition log_read_cspec ls (a: addr) : Specification block unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' v => state = state' /\
                              match diskGet ls.(ls_disk) a with
                              | Some v' => v = v'
                              | None => True
                              end;
      alternate := fun state' _ => state = state'
    |}.

Definition log_recover_spec ls : Specification block unit D.State :=
  fun state =>
    {|
      pre := LogDecode state ls /\ DiskDecode state ls /\ CommitStatus state false;
      post := fun state' v => LogDecode state' (ls_clear ls) /\
                       DiskDecode state' (ls_clear ls) /\
                       CommitStatus state' false;
      alternate := fun state' _ => state = state'
    |}.

Ltac simplify :=
  repeat match goal with
         | _ => progress propositional
         end.

Ltac finish :=
  repeat match goal with
         | _ => auto
         | _ => congruence
         end.

(* specs for one-disk primitives (restatement of semantics as specs) *)
Ltac prim :=
  eapply proc_cspec_impl; [ unfold spec_impl | eapply op_spec_sound ];
    simpl;
    propositional;
    (intuition auto);
    propositional.

Theorem read_ok a :
  proc_cspec D.ODLayer
             (read a)
             (fun state =>
                {| pre := True;
                   post state' r :=
                     diskGet state a ?|= eq r /\
                     state' = state;
                   alternate state' _ :=
                     state' = state; |}).
Proof.
  unfold read.
  prim;
    repeat match goal with
           | [ H: D.op_step _ _ _ _ |- _ ] => invert H; clear H
           end;
    propositional;
    auto.
  destruct (diskGet s' a); simpl; eauto.
Qed.

Theorem write_ok a v :
  proc_cspec D.ODLayer
             (write a v)
             (fun state =>
                {| pre := True;
                   post state' r :=
                     r = tt /\
                     state' = diskUpd state a v;
                   alternate state' _ :=
                     state' = state \/
                     state' = diskUpd state a v; |}).
Proof.
  unfold write.
  prim;
    repeat match goal with
           | [ H: D.op_step _ _ _ _ |- _ ] => invert H; clear H
           end;
    propositional;
    auto.
Qed.

Theorem size_ok :
  proc_cspec D.ODLayer
             (size)
             (fun state =>
                {| pre := True;
                   post state' r :=
                     r = diskSize state /\
                     state' = state;
                   alternate state' _ :=
                     state' = state; |}).
Proof.
  unfold size.
  prim;
    repeat match goal with
           | [ H: D.op_step _ _ _ _ |- _ ] => invert H; clear H
           end;
    propositional;
    auto.
Qed.

Hint Resolve read_ok write_ok size_ok.

Ltac step :=
  unshelve step_proc; simplify; finish.

Opaque diskGet.

Theorem gethdr ps :
  proc_cspec D.ODLayer
             gethdr
             (fun state =>
                {| pre := disk_invariant state /\
                          PhyDecode state = Some ps;
                   post state' r :=
                     r = ps.(p_hdr) /\
                     state' = state;
                   alternate state' _ :=
                     state' = state; |}).
Proof.
  unfold gethdr.
  step.
  step.
  eapply PhyDecode_invariant in H; propositional; eauto.
  replace (diskGet state 0) in *; simpl in *; propositional; eauto.
  congruence.
Qed.

Theorem writedesc ps desc :
  proc_cspec D.ODLayer
             (writedesc desc)
             (fun state =>
                {| pre := disk_invariant state /\
                          PhyDecode state = Some ps;
                   post state' r :=
                     disk_invariant state' /\
                     exists ps', PhyDecode state' = Some ps' /\
                            ps' = {| p_hdr := ps.(p_hdr);
                                     p_desc := desc;
                                     p_log_values := ps.(p_log_values);
                                     p_data_region := ps.(p_data_region); |};
                   alternate state' _ :=
                     disk_invariant state' /\
                     exists ps', PhyDecode state' = Some ps' /\
                            ps' = ps \/
                            ps' = {| p_hdr := ps.(p_hdr);
                                     p_desc := desc;
                                     p_log_values := ps.(p_log_values);
                                     p_data_region := ps.(p_data_region); |};
                   |}).
Proof.
  unfold writedesc.
  eapply proc_cspec_impl; [ unfold spec_impl | solve [eauto] ];
    simpl;
    propositional;
    (intuition auto);
    propositional.
  - unfold disk_invariant in *.
    autorewrite with upd; auto.
  - eexists; intuition eauto.
Abort.