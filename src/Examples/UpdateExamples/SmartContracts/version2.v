From RecoveryRefinement Require Import Lib.
Require Import Helpers.RelationRewriting.
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Require Import Coq.Arith.Arith.
Require Import Examples.UpdateExamples.SmartContracts.Firstversion. 
Require Import Spec.update. 

Module abs2. 

  Definition State := nat%type.

  Inductive O' : Type -> Type :=
  | op_decrease (i : option nat) : O' unit.

  About update.Op2. 

  Definition Op2 := update.COP Firstversion.abs.Op O'.

  Print Dynamics. (** (op: Type -> Type)  (State: Type) : Type *)

  Definition DecCounter (i: nat) : State -> State :=
    fun 'x => if  x-i <=? 0  then  0  else x-i.   
 

  Definition test (T: Type) (op: Op2 T) :=
    match op with
    | O'case _ _ T o' =>  match o' with
                      | op_decrease i => (match i with
                             | Some i0 => True
                             | None => True
                                         end)
                      end
    | Op1case _  _ T op1   => match op1 with
                             | abs.op_receive Msg => True
                             | abs.op_observe => True
                            end
                                 
    end. 
  
  Definition dynamics : Dynamics Op2 State :=
    {| step T (op: Op2 T):=
        match op with
        | Op1case _ _ T op1 => match op1 with
                        | abs.op_receive Msg => (match Msg with
                             | Some (abs.Incr i) =>  puts (abs.IncrCounter i)
                             | None => puts (abs.NoOp)
                              end)
                        | abs.op_observe  => reads (abs.read)
                        end
        | O'case _ _ T o' => match o' with
                      | op_decrease i => (match i with
                             | Some i0 => puts (DecCounter i0)
                             | None => puts (abs.NoOp)
                                         end)
                      end
       end;
      crash_step := puts (fun 'x => 0); 
    |}.

  Definition l : Layer Op2 :=
    {| Layer.State := State;
       sem := dynamics;
       initP := fun s => s = 0|}.
End abs2. 

(** OLD IMPL

Definition impl : LayerImpl Firstversion.con.Op  abs.Op :=
  {| compile_op T (op: abs.Op T) :=
      match op with
      | abs.op_receive Msg => match Msg with
                             | Some (abs.Incr i) => update i
                             | Some (abs.Decr i) =>
                                 (currentVal <- read; 
                                 _ <- (if currentVal - i <? 0 then noop
                                 else write (currentVal - i)); Ret tt)%proc
                               | None => noop
                               end
      | abs.op_observe => (val <- read; Ret (val)%nat)%proc
       end;
     recover := Ret tt;
    init := Ret Initialized; |}.

*)


Definition impl : LayerImpl Firstversion.con.Op  abs2.Op2 :=
  {| compile_op T (op: abs2.Op2 T) :=
      match op with
      | Op1case _ _ T op1 => Firstversion.impl.(compile_op) op1 
      | O'case _ _ T o'  => match o' with
                             | abs2.op_decrease i => (match i with
                             | Some i0 => (currentVal <- read; 
                                 _ <- (if currentVal - i0 <? 0 then noop
                                 else write (currentVal - i0)); Ret tt)%proc
                             | None => noop
                                                end)
                           end
       end;
     recover := Ret tt;
    init := Ret Initialized; |}.

Definition absr : relation abs2.l.(State) con.l.(State) unit :=
  fun l s _ => l = s.


(** --------------------- SPECS  ------------------------------------------*)

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

Definition decrease_rspec (i: option nat) :  Specification unit unit con.State :=
  fun state =>
    {|
      pre := True;
      post :=  fun state' (_:unit) => match i with
                               | Some i0 => (state - i0 < 0 -> state' = state) /\ (state - i0 >= 0 -> state' = state - i0)
                               | None => state' = state
                               end;
      alternate :=fun state' (_:unit) => state' = 0;
      |}. 

Definition decrease_hspec (i: option nat) :  Specification unit unit con.State :=
  fun state =>
    {|
      pre := True;
      post :=  fun state' (_:unit) => match i with
                               | Some i0 => (state - i0 < 0 -> state' = state) /\ (state - i0 >= 0 -> state' = state - i0)
                               | None => state' = state
                               end;
      alternate :=fun state' (_:unit) => state' = 0;
      |}.


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

Lemma init_cok:
  proc_hspec con.dynamics (impl.(init)) (init_hspec).
Proof.
  eapply ret_hspec; firstorder. Qed.


(**Lemma decrease_cok : proc_hspec con.dynamics (impl.(compile_op) (abs2.Op2 (abs2.op_decrease) )) (decrease_hspec).
Proof.
Admitted.

Lemma decrease_ok : proc_rspec con.dynamics (impl.(compile_op) (abs2.op_decrease)) impl.(recover) (decrease_rspec).
Proof.
Admitted. *)

Lemma decrease1_ok : forall (n:nat) (sC: con.State),   proc_rspec con.dynamics
    (currentVal <- read; _ <- write (currentVal - n); Ret tt)%proc 
    (Ret tt) (decrease_rspec (Some n)).
Proof.
  intros. unfold proc_rspec. unfold rimpl. simpl. split.
  * intros. unfold spec_exec. unfold decrease_rspec. simpl. intros.
    unfold and_then in H. destruct H as [o1 H]. destruct H as [y0 H]. destruct H as [H1 H2]. destruct H2 as [o2 H2]. destruct H2 as [y1 H2]. unfold reads in H1. unfold con.get in H1. destruct H1 as [H1 H3].
    unfold puts in H2. unfold con.set in H2. unfold pure in H2. destruct H2 as [H2 H4]. destruct H4 as [H4 H5].  split.
    ** intros. rewrite -> H1 in H2. admit. 
    ** intros.  rewrite -> H1 in H2. rewrite -> H4 in H2. auto. 
  * intros. unfold spec_aexec. unfold decrease_rspec. simpl. intros. unfold rexec in H. unfold and_then in H. destruct H as [o1 [y0 H]]. induction H. unfold exec_recover in H1. unfold and_then in H1. destruct H1 as [o1' [y1' [H1 H3]]].  unfold exec in H3. unfold pure in H3. induction H1.
    ** unfold exec_crash in H. unfold rel_or in H. simpl in H. unfold puts in H. unfold and_then in H. destruct H.
       *** destruct H.
           **** destruct H3 as [H3 H4]. rewrite -> H in H3. inversion H3. reflexivity.
          **** destruct H as [o2 [y1 H]]. unfold reads in H. destruct H as [H1 H]. destruct H3 as [H3 H4]. rewrite -> H in H3. inversion H3. reflexivity.
       *** destruct H as [o2 [y1 H]]. unfold reads in H. unfold con.get in H. destruct H as [H6 H]. destruct H.
           **** destruct H. {destruct H3 as [H3 H4]. rewrite -> H in H3. inversion H3. reflexivity.} {destruct H. destruct H. destruct H as [H5 H]. destruct H3 as [H3 H4]. rewrite -> H in H3. inversion H3. reflexivity.}
           ****  destruct H. destruct H. destruct H as [H5 H]. destruct H3 as [H3 H4]. rewrite -> H in H3. inversion H3. reflexivity.
   ** 
Admitted.

Lemma decrease2_ok : forall sC: con.State, proc_rspec con.dynamics noop (Ret tt) (decrease_rspec None).
Proof.
Admitted.


Global Hint Resolve init_cok receive_ok observe_ok : core. 
 

Definition rf : LayerRefinement con.l abs2.l.
Proof.
  refine {| Layer.impl := impl;
           Layer.absr := absr; |}.
  - (** compile op refines step *)
    red; intros. destruct op.
    +  destruct o.
      ++ (** op = receive *)
      eapply proc_rspec_crash_refines_op  with (spec := receive_rspec Msg); eauto; unfold spec_impl, absr in *; simplify.
      * eapply proc_rspec_impl with (spec1 := receive_rspec Msg).
        ** unfold spec_impl. simplify. split.
           *** intros. exists s'. split.
               { auto. }
               { destruct Msg.
                 {destruct m.
                  **** auto.}
                 { auto. }}
           *** intros. exists s'. split. { auto. }  { auto. }
        ** eapply receive_ok. 
      * destruct Msg.
        ** destruct m.
           *** unfold puts. unfold abs.IncrCounter. auto.
        ** unfold abs.NoOp. unfold puts. auto. 
    ++ (** op = observe *)
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
    + destruct o. eapply proc_rspec_crash_refines_op  with (spec := decrease_rspec i); eauto; unfold spec_impl, absr in *; simplify.
      * eapply proc_rspec_impl with (spec1 := decrease_rspec i).
        ** unfold spec_impl. simplify. split.
           *** intros. exists s'. split.
               { auto. }
               { destruct i.  { apply H. } {auto. }
                 }
           *** intros.  exists s'. split. { auto. }  { auto. }
        ** destruct i.
           *** apply decrease1_ok. auto. 
           *** apply decrease2_ok.  auto.  
      * destruct i.
        ** unfold puts. unfold abs2.DecCounter. destruct (sA - n).
           *** simpl. destruct H0 as [H0 H1]. assert (0 >= 0) as H2.
               { auto.} { specialize (H1 H2). auto. }
           *** simpl. destruct H0 as [H0 H1]. assert (S n0 >= 0) as H.
               { auto. apply le_0_n. } { specialize (H1 H). auto. } 
        ** unfold puts. unfold abs.NoOp. auto.  
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




(**
 Inductive Op : Type -> Type :=
  | op1case (T:Type) : Op1 T -> Op T
  | o'case  (T:Type) : O' T -> Op T.

 Inductive  Op2: Type -> Type :=
  | Op1case(T:Type) : Op1 T -> Op2 T
  | O'case(T:Type) : O' T -> Op2 T.

  Inductive Op1 : Type -> Type :=
  | op_receive (Msg : option Message) : Op1 unit
  | op_observe : Op1 nat. 

Inductive  Op2: Type -> Type :=
| Op1case(T:Type) : Op1 T -> Op2 T
| O'case(T:Type) : O' T -> Op2 T.

  Inductive OpTest : Type -> Type :=
  | op1case2 (T : Type) (op : Op1 T) : OpTest T
  | o'case2 (T : Type) (op : O' T) : OpTest T.

  Definition  opTest_step (T:Type) (op: OpTest T) : OpSemantics OpTest State :=
    match op with
    | op1case2 op1 => (match op1 with
        | op_receive Msg => (match Msg with
                             | Some (Incr i) =>  puts (IncrCounter i)
                             | None => puts (NoOp)
                              end)
        | op_observe  => reads (read)
                      end)
    | o'case2 o' => (match o' with
        | op_decrease i => (match i with
                       | Some i0 => puts (DecCounter i0)
                       | None => NoOp
                           end)
                    end)
    end.

   *)

  (** Inductive o'_step : OpSemantics O' State :=
  | step_decrease : forall i: option nat, forall state state',
    match i with
    | Some i0 => state' = ((DecCounter i0) state)
    | None => state' = state
    end ->
    o'_step (op_decrease i) state state' tt. *)

  (** ATTEMPT 1 : DIDN'T WORK 

 Definition relinkO'{T:Type} (o' : O' T) : Op T :=
    match o' with
    | op_decrease i => (match i with
                       | Some i0 => puts (DecCounter i0)
                       | None => NoOp
                       end)
    end. 

  Definition relinkOp1{T:Type} (op1: Firstversion.abs.Op T) : Op T :=
    match op1 with
    | op_receive Msg => (match Msg with
                             | Some (Incr i) =>  puts (IncrCounter i)
                             | None => puts (NoOp)
                              end)
    | op_observe  => reads (read)
    end.

 *)
(**  Inductive op_step : OpSemantics Op State :=
 | step_op1 :forall (T:Type) (op: Op1 T) (state state' : State) (res: T),
    Firstversion.abs.op1_step op state state' res ->
    op_step (op1case op) state state' res
  | step_o' :  forall (T: Type) (op: O' T) (state state': State) (res: T),
      o'_step op state state' res ->
      op_step (o'case op) state state' res. *)
