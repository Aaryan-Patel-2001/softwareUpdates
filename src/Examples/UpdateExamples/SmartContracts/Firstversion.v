From RecoveryRefinement Require Import Lib.
Require Import Helpers.RelationRewriting.
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.

Module abs. 

  Definition State := nat%type.

  Inductive Message : Type :=
  | Incr (i : nat).

  Inductive Op : Type -> Type :=
  | op_receive (Msg : option Message) : Op unit
  | op_observe : Op nat. 

  Print Dynamics. (** (op: Type -> Type)  (State: Type) : Type *)

  Definition IncrCounter (i : nat) : State -> State :=
    fun 'x => x + i.

  Definition NoOp : State -> State :=
    fun 'x => x.

  Definition read : State -> nat :=
    fun 'x => x.

  Inductive op1_step : OpSemantics Op State :=
  | step_receive : forall Msg: option Message, forall state state',
    match Msg with
    | Some (Incr i) => state' = ((IncrCounter i) state)
    | None => state' = state
    end ->
    op1_step (op_receive Msg) state state' tt
  | step_observe : forall state,
    op1_step (op_observe) state state (read state). 

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T):=
        match op with
        | op_receive Msg => (match Msg with
                             | Some (Incr i) =>  puts (IncrCounter i)
                             | None => puts (NoOp)
                              end)
        | op_observe  => reads (read)
        end;
      crash_step :=
        puts (fun 'x => 0); 
    |}.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       initP := fun s => s = 0|}.
End abs.

Module con.

  (** State is a global variable   *)
  Definition State := nat%type.

  (** Methods for accessing and setting those variables    *)
  Inductive Op : Type -> Type :=
  | op_get  : Op nat
  | op_set (i : nat) : Op unit
  | noop : Op unit. 

  Definition get : State -> nat :=
    fun 'x => x.

  Definition set (i : nat) : State -> State :=
    fun 'x => i.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T):=
        match op with
        | op_get  => reads (get)
        | op_set i => puts (set i)
        | noop => puts (fun 'x => x)
        end;
      crash_step :=
        puts (fun 'x => 0);
    |}.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
      initP := fun s => s = 0|}.

End con.


Definition read: proc _ nat := Call (con.op_get).
Print read. 
Definition write i : proc _ unit := Call (con.op_set i).
Definition noop: proc _ unit := Call (con.noop).
Definition update i: proc _ unit := (currentVal <- Call (con.op_get); 
  _ <- Call (con.op_set (currentVal + i)%nat); Ret tt )%proc.  


Definition impl : LayerImpl con.Op  abs.Op :=
  {| compile_op T (op: abs.Op T) :=
      match op with
      | abs.op_receive Msg => match Msg with
                             | Some (abs.Incr i) => update i
                               | None => noop
                               end
      | abs.op_observe => (val <- read; Ret (val)%nat)%proc
       end;
     recover := Ret tt;
    init := Ret Initialized; |}.

Definition absr : relation abs.l.(State) con.l.(State) unit :=
  fun l s _ => l = s.

(** --------------------- TACTICS  ------------------------------------------*)

Ltac simplify :=
  repeat match goal with
         | |- forall _, _ => intros
         | _ => deex
         | _ => destruct_tuple
         | _ => destruct_tuple
         | [ H: reads _ _ _ _ |- _] => unfold reads in H
         | [ H: puts _ _ _ _ |- _] => unfold puts in H
         | [ u: unit |- _ ] => destruct u
         | |- _ /\ _ => split; [ solve [auto] | ]
         | |- _ /\ _ => split; [ | solve [auto] ]
         | _ => progress simpl in *
         | _ => progress safe_intuition
         | _ => progress subst
         | _ => progress autorewrite with array in *
end.

Ltac extract_post :=
  lazymatch goal with
  | |- pre _ => simpl
  | |- alternate _ _ _ => simpl
  | |- post _ _ _ => simpl
  | _ => idtac
  end.

Lemma op_step_crash T (op: con.Op T) u s' r :
  (op_spec con.dynamics op u).(alternate) s' r ->
  s' = 0.
Proof.
  intros.
  hnf in H; propositional.
  destruct H0; propositional.
Qed.

Lemma crash_step_simp s s' r :
  con.dynamics.(crash_step) s s' r ->
  s' = 0.
Proof.
  compute; auto.
Qed.

Ltac extract_crash H :=
  lazymatch type of H with
  | con.dynamics.(crash_step) _ _ _ =>
    apply crash_step_simp in H; subst
  | (op_spec con.dynamics _ _).(alternate) _ _ =>
    apply op_step_crash in H; subst
  | _ => idtac
  end.

Ltac extract_pre H :=
  let P := type of H in
  match eval hnf in P with
  | True => clear H
  | ?v = _ =>
    is_var v;
    hnf in H; subst
  | (?v = _) /\ _ =>
    is_var v;
    hnf in H;
    let Heq := fresh "Heq" in
    destruct H as (Heq&H); subst
  | _ => idtac
  end.

Ltac step_ret :=
  apply ret_hspec; cbn [pre post alternate];
  (let H := fresh "Hpre" in
   intros * H; extract_pre H);
  apply conj;
  [ extract_post
  | let H := fresh "Hcrash" in
    intros * H; extract_crash H; extract_post ].

Lemma util_and3 (P Q R:Prop) :
  P -> Q -> R -> P /\ Q /\ R.
Proof. firstorder. Qed.

Ltac step_bind :=
  eapply proc_hspec_rx; [ solve [ eauto ] | cbn [pre post alternate] .. ];
  (let H := fresh "Hpre" in
   intros * H; extract_pre H);
  apply util_and3;
  swap 1 2;
  [ intros
  | extract_post
  | let H := fresh "Hcrash" in
    intros * H; extract_crash H;
    extract_post ].

Ltac newstep :=
  monad_simpl;
  lazymatch goal with
  | |- proc_hspec _ (compile_op _ _) _ => simpl
  | |- proc_hspec _ (Ret _) _ => step_ret
  | |- proc_hspec _ (Bind _ _) _ => step_bind
  end.

(** --------------------- SPECS ------------------------------------------*)

Definition init_hspec : Specification InitStatus unit con.State :=
  fun state =>
    {|
      pre := state = 0;
      post := fun state' _ => state' = 0; 
      alternate := fun state' (_:unit) => True;
    |}.                            

Definition receive_hspec (msg: option abs.Message) : Specification unit unit con.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' (_:unit) => match msg with
                              | Some (abs.Incr i) => state' = state + i
                              | None => state' = state
                              end;
      alternate := fun state' (_:unit) => state' = 0;
    |}.

Definition receive_rspec (msg: option abs.Message) : Specification unit unit con.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' (_:unit) => match msg with
                              | Some (abs.Incr i) => state' = state + i
                              | None => state' = state
                              end;
      alternate := fun state' (_:unit) => state' = 0;
    |}.

Definition observe_hspec : Specification nat unit con.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' v => state' = state /\ v = state;
      alternate := fun state' v => state' = 0;
    |}.

Definition observe_rspec : Specification nat unit con.State :=
  fun state =>
    {|
      pre := True;
      post := fun state' v => state' = state /\ v = state;
      alternate := fun state' v => state' = 0;
    |}.

Definition recover_spec : Specification unit unit con.State :=
  fun state =>
    {|
      pre := state = 0;
      post := fun state' (_:unit) => state' = 0;
      alternate := fun state' (_:unit) => state' = 0;
    |}.

(** --------------------- PROOFS ------------------------------------------*)

Lemma recover_cok : proc_hspec con.dynamics (impl.(recover)) recover_spec.
Proof. simpl. eapply ret_hspec; firstorder. Qed.

Lemma recover_idempotent :
  idempotent (fun (t: unit) => recover_spec).
Proof.
  unfold idempotent; intuition; exists tt; simpl in *.
  unfold puts in *; firstorder; congruence.
Qed.

Global Hint Resolve recover_cok recover_idempotent : core.

Lemma recover_rok : proc_rspec con.dynamics (impl.(recover)) (impl.(recover)) recover_spec.
Proof. eapply proc_hspec_to_rspec; eauto. intros []; eauto. Qed.

Definition receive_cok (msg: option abs.Message):
  proc_hspec con.dynamics (impl.(compile_op) (abs.op_receive msg)) (receive_hspec msg).
Proof.
  unfold proc_hspec. simpl. split.
  - unfold rimpl. intros. unfold spec_exec. unfold receive_hspec. simpl. intros. destruct msg.
    + destruct m.  unfold update in H. unfold exec in H. unfold and_then in H. destruct H as [o1 H]. destruct H as [y0 H]. destruct H as [H H1].
      unfold con.dynamics in H. simpl in H. unfold reads in H. unfold con.get in H. destruct H as [H H2].
      destruct H1 as [o2 H1]. destruct H1 as [y1 H1]. unfold con.dynamics in H1. simpl in H1. unfold puts in H1. unfold con.set in H1. unfold pure in H1. destruct H1 as [H1 [H3 H4]]. rewrite -> H3 in H1. rewrite -> H in H1. auto.
    + unfold noop in H. unfold exec in H. unfold con.dynamics in H. simpl in H. unfold puts in H. auto.
  - unfold rimpl. intros. unfold spec_aexec. unfold receive_hspec. simpl. intros.
    destruct msg in H.
    + destruct m in H. unfold update in H. unfold exec_crash in H. simpl in H. unfold rel_or in H. unfold puts in H. destruct H as [H1 | H2].
      { destruct H1 as [H1 | H2].
        { auto. }
        { unfold and_then in H2. destruct H2 as [o1 H2]. destruct H2 as [y0 H2]. destruct H2 as [H3 H2]. auto. }}
      { unfold and_then in H2. destruct  H2 as [o1 H2]. destruct H2 as [y0 H2].  destruct H2 as [H3 H2]. destruct H2 as [H1 | H2].
        { destruct H1 as [H1 | H2]. { auto. } {destruct H2 as [_ H2]. destruct H2 as [y1 H2]. destruct H2 as [H1 H2]. auto. }}
        { destruct H2 as [_ H2]. destruct H2 as [y1 H2]. destruct H2 as [H1 H2]. auto. }}
    + unfold noop in H. unfold exec_crash in H. unfold rel_or in H. destruct H as [H | H1].
      { unfold con.dynamics in H.  simpl in H. unfold puts in H. auto. }
      { unfold and_then in H1. destruct H1 as [o1 H1]. destruct H1 as [y0 H1]. unfold con.dynamics in H1.  simpl in H1. unfold puts in H1. destruct H1 as [H1 H]. auto. }
Qed. 

Print tt.

Print idempotent.

Print proc_hspec_to_rspec. 

Definition receive_ok (msg: option abs.Message):
  proc_rspec con.dynamics (impl.(compile_op) (abs.op_receive msg)) impl.(recover) (receive_rspec msg).
Proof.
 Print proc_hspec_to_rspec. Print SpecProps. Print Specification. Print recover_spec.  eapply proc_hspec_to_rspec with (p_hspec := receive_hspec msg) (rec_hspec := fun _ => recover_spec). 
  - eapply receive_cok. 
  - intros.  unfold proc_hspec. unfold rimpl. split.
    + intros. unfold spec_exec. unfold recover_spec.  simpl. intros.
      unfold impl in H. simpl in H. unfold pure in H. destruct H as [H H1].
      rewrite -> H0 in H. auto.
    + intros. unfold spec_aexec. unfold recover_spec. simpl. intros.
      unfold impl in H. simpl in H. unfold puts in H. auto.
  - unfold idempotent. intros. exists a. unfold recover_spec. simpl.
    unfold recover_spec in H. simpl in H. unfold recover_spec in H0. simpl in H0. 
    split.
    + auto.
    + intros. auto.
  - intros. unfold receive_hspec. unfold receive_rspec. simpl. split.
    + auto.
    + intros. destruct msg.
      { destruct m. auto. }
      { auto. }
  - intros. unfold receive_hspec in H. simpl in H. unfold receive_hspec in H0. simpl in H0. exists v. unfold recover_spec. simpl. auto.
  - intros. unfold receive_rspec. simpl.
    unfold receive_rspec in H. simpl in H. unfold recover_spec in H0. simpl in H0. auto. 
Qed. 

Print step_bind.
Print proc_hspec. 
Print proc_hspec_rx.
About solve. 

Definition observe_cok:
  proc_hspec con.dynamics (impl.(compile_op) (abs.op_observe)) (observe_hspec).
Proof. 
  simpl. unfold proc_hspec. split.
  + simpl. unfold rimpl. intros. unfold spec_exec. intros. unfold observe_hspec. simpl.
    unfold observe_hspec in H0. simpl in H0.
    unfold and_then in H. destruct H as [o' H2]. destruct H2 as [y0 H3]. destruct H3 as [H3 H4].
    unfold reads in H3. unfold con.get in H3.
    unfold pure in H4. destruct H4 as [H4 H5]. destruct H3 as [H2 H3]. rewrite <- H5 in H2. rewrite -> H4 in H3. split.
    - inversion H3. reflexivity.
    - inversion H2. reflexivity.
      + simpl. unfold rimpl. intros.
        unfold spec_aexec. intros. unfold observe_hspec. simpl.
        unfold observe_hspec in H0. simpl in H0.
        unfold rel_or in H. unfold puts in H. unfold and_then in H. destruct H as [H1 | H2].
        { destruct H1 as [ H2 | H3]. { assumption. } { destruct H3 as [o' H3]. destruct H3 as [y0 H3]. destruct H3 as [H3 H4]. assumption. }}
        { destruct H2 as [o' H2]. destruct H2 as [y0 H2]. destruct H2 as [H2 H3]. assumption. }
Qed. 


Definition observe_ok:
  proc_rspec con.dynamics (impl.(compile_op) (abs.op_observe)) impl.(recover) (observe_rspec).
Proof.
  unfold proc_rspec. simpl. unfold rimpl. split.
  - intros. unfold spec_exec. unfold observe_rspec. simpl. intros.
    unfold and_then in H. destruct H as [o1 H]. destruct H as [y0 H]. destruct H as [H1 H2]. unfold reads in H1. unfold con.get in H1. unfold pure in H2. destruct H2 as [H2 H3]. rewrite -> H2 in H1. rewrite <- H3 in H1. destruct H1 as [H1 H]. split.
    + inversion H. reflexivity.
    + inversion H1. reflexivity. 
  - intros. unfold spec_aexec. unfold observe_rspec. simpl. intros.
    unfold rexec in H. unfold and_then in H. destruct H as [o1 H]. destruct H as [y0 H]. unfold exec_crash in H. unfold rel_or in H. simpl in H. destruct H as [H1 H2]. destruct H1 as [H3 | H4].
    + destruct H3 as [H1 | H3].
      { unfold puts in H1. unfold exec_recover in H2. unfold and_then in H2. destruct H2 as [o' H2]. destruct H2 as [y1 H2]. unfold exec in H2. unfold pure in H2. destruct H2 as [H3 [H4 H5]]. Print seq_star. induction H3.
        { rewrite -> H4 in H1. auto. }
        { unfold exec_crash in H. unfold con.dynamics in H. simpl in H. unfold puts in H. apply IHseq_star in H. { auto. }{ auto. }}}
      { unfold and_then in H3. destruct H3 as [o2 H3]. destruct H3 as [y' H3]. unfold exec_recover in H2. unfold and_then in H2. destruct H2 as [o1' H2]. destruct H2 as [y1' H2]. destruct H3 as [H H1]. unfold puts in H1. unfold reads in H. unfold con.get in H. destruct H as [H3 H4]. destruct H2 as [H2 H5]. unfold exec in H5. unfold pure in H5. destruct H5 as [H5 H6]. induction H2.
        { rewrite -> H5 in H1. auto. }
        { unfold exec_crash in H. unfold con.dynamics in H. simpl in H. unfold puts in H. apply IHseq_star in H. { auto. }{ auto. }}}
    + unfold and_then in H4. destruct H4 as [o2 H4]. destruct H4 as [y' H4]. unfold reads in H4. unfold con.get in H4. unfold puts in H4. destruct H4 as [[H H1] H3]. unfold exec_recover in H2. unfold and_then in H2. destruct H2 as [o1' H2]. destruct H2 as [y1' H2]. destruct H2 as [H2 H4]. unfold exec in H4. unfold pure in H4. destruct H4 as [H4 H5]. induction H2.
      { rewrite -> H4 in H3. auto. }
      { unfold exec_crash in H2. unfold con.dynamics in H2. simpl in H2. unfold puts in H2. apply IHseq_star in H2. { auto. }{ auto. }}
Qed. 

Lemma init_cok:
  proc_hspec con.dynamics (impl.(init)) (init_hspec).
Proof.
  eapply ret_hspec; firstorder. Qed.

Global Hint Resolve init_cok receive_ok observe_ok : core. 
 

Definition rf : LayerRefinement con.l abs.l.
Proof.
  refine {| Layer.impl := impl;
           Layer.absr := absr; |}.
  - (** compile op refines step *)
    red; intros. destruct op.
    + (** op = receive *)
      eapply proc_rspec_crash_refines_op  with (spec := receive_rspec Msg); eauto; unfold spec_impl, absr in *; simplify.
      * eapply proc_rspec_impl with (spec1 := receive_rspec Msg).
        ** unfold spec_impl. simplify. split.
           *** intros. exists s'. split.
               { auto. }
               { destruct Msg. {destruct m. auto. } { auto. }}
           *** intros. exists s'. split. { auto. }  { auto. }
        ** eapply receive_ok. 
      * destruct Msg.
        ** destruct m. unfold puts. unfold abs.IncrCounter. auto. 
        ** unfold abs.NoOp. unfold puts. auto. 
    + (** op = observe *)
      eapply proc_rspec_crash_refines_op  with (spec := observe_rspec); eauto; unfold spec_impl, absr in *; simplify.
      * eapply proc_rspec_impl with (spec1 :=  observe_rspec).
        ** unfold spec_impl. simplify. split.
           *** intros. exists s'. destruct H as [H H']. split.
               **** auto. 
               **** split. { auto. } { auto. } 
           *** intros. exists s'. split.
               **** auto.
               **** auto. 
        ** eapply observe_ok.  
      * unfold reads.  unfold abs.read. split.  { auto. } { auto. } 
  - (** recovery refines crash step *)
    eapply proc_rspec_recovery_refines_crash_step; [ intros; eapply recover_rok |..]; simplify. Print tt. 
    intuition; exists 0; unfold absr in *; simplify; intuition; subst; simplify; try congruence. 
  - (** init step *)
    eapply proc_hspec_init_ok with (spec := init_hspec).
    * unfold impl. simpl. eapply init_cok. 
    * intros. unfold init_hspec. simpl. unfold con.l in H. simpl in H. auto. 
    * intros. exists 0. unfold absr. unfold abs.l. simpl.
      unfold init_hspec in H.  simpl in H. split.
      ** auto.
      ** auto. 
Qed.  
