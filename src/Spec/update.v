Require Import Spec.Layer.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Import  RelationNotations.

Section Updates.

Variable Op: Type -> Type. 
          
Notation a_proc := (proc Op).

Variable  Op1: Type -> Type.

Variable  O': Type -> Type.

Inductive  COP: Type -> Type :=
| Op1case(T:Type) : Op1 T -> COP T
| O'case(T:Type) : O' T -> COP T. 

Variable  Lc : Layer Op.

Variable LA1: Layer Op1.

Variable LA2: Layer COP.

Print relation. 

Variable shutdown: relation Lc.(State) Lc.(State) unit. 

Print proc. 

Fixpoint  relinkingFunction {T: Type} (p: proc Op1 T) : proc COP T :=
  match p with
  | Call o => Call (Op1case o)
  | Ret v => Ret v
  | Bind e f => Bind (relinkingFunction e) (fun x => relinkingFunction(f x))
  end. 

Print LayerImpl.

Search "compile".

About compile.

Definition compatibleUpdate  (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit) :=
  forall (T:Type) (p: proc Op1 T), forall (s1 s2 c1: Lc.(State)) (state : LA1.(State)) (r:T),
  ((exec Lc.(sem) (compile M2 p)) (s1) (s2) (r) /\ R2 (state) (s1) (tt)  /\ R1 (state) (c1) (tt) ) ->
  exists (state' : LA1.(State)) (c2: Lc.(State)), (exec Lc.(sem) (compile M1 p)) (c1) (c2) (r) /\ (exec LA1.(sem) p ) (state) (state') (r) /\ R2 (state') (s2) (tt) /\ R1 (state') (c2) (tt). 

Theorem updateOP : forall (T:Type) (op: Op1 T) (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit) (s1 s2 c1: Lc.(State)) (state : LA1.(State)) (r:T),
  exec Lc (compile M2 (Call op)) s1 s2 r /\ R2 state s1 tt /\ R1 state c1 tt ->
  exists (state' : LA1.(State)) (c2 : Lc.(State)),
    exec Lc (compile M1 (Call op)) c1 c2 r /\
    exec LA1 (Call op) state state' r /\ R2 state' s2 tt /\ R1 state' c2 tt.
Proof.
  Admitted. 

Theorem compatibleUpdateInductive: forall (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit), compatibleUpdate M1 M2 R1 R2.
Proof.
  intros. unfold compatibleUpdate. induction p.
  - apply updateOP. 
  - intros. destruct H as [H1 [H2 H3]]. simpl in H1. unfold pure in H1. destruct H1 as [H0 H1].
    exists state. exists c1. split.
    + simpl. unfold pure. auto. 
    + split.
      ++ simpl. unfold pure. auto. 
      ++ split.
         +++ rewrite -> H0 in H2.  assumption.
         +++ assumption. 
  - intros. destruct H0 as [H1 [H2 H3]].  simpl in H1. unfold and_then in H1.
    destruct H1 as [o1 H1]. destruct H1 as [y [H1 H4]]. specialize IHp with s1 y c1 state o1.
  assert (exec Lc (compile M2 p) s1 y o1 /\ R2 state s1 tt /\ R1 state c1 tt) as IH by (repeat (split; try assumption)). 
    (* remember (IHp (conj (H1) (conj H2 H3))) as XXX . *)
    apply IHp in IH. destruct IH as [state' IH]. destruct IH as [c2 IH].
    specialize H with o1 y s2 c2 state' r. destruct IH as [IH [H5 H6]].
    assert ( exec Lc (compile M2 (p2 o1)) y s2 r /\ R2 state' y tt /\ R1 state' c2 tt) as IH' by (repeat (split; try assumption)). apply H in IH'. destruct IH' as [state'' IH']. destruct IH' as [c3 IH'].

    exists state''. exists c3. destruct IH' as [IH' [H7 H8]].  split.
    + simpl. unfold and_then. exists o1.  exists c2. split.
      ++ assumption. 
      ++ assumption. 
    + split.
      ++ simpl. unfold and_then. exists o1. exists state'. auto.  
      ++ auto.
Qed. 

Print Layer.

Definition CompatibleUpdateWithoutAbsr  (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) :=
  forall (T:Type) (p1 p2: proc Op1 T), forall (s s' c'': Lc.(State)) (r r1: T),
  Lc.(initP) (s) /\ (exec Lc.(sem) (compile M1 p1)) (s) (s') (r) /\
  shutdown (s') (s') (tt)  /\
  (exec Lc.(sem) (compile M2 p2)) (s') (c'') (r1) ->
  exists (s'':Lc.(State)) (r2: T),  (exec Lc.(sem) (compile M1 p2)) (s') (s'') (r2) /\ 
  r1 = r2 . 

Theorem CUAbsrImpliesWithoutAbsr : forall (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit), compatibleUpdate M1 M2 R1 R2 -> CompatibleUpdateWithoutAbsr M1 M2.
Proof.
  intros.
  Admitted. 

Theorem CompatibleUpdateWithoutAbsrInductive : forall (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1),
  CompatibleUpdateWithoutAbsr M1 M2.
Proof.
  intros. unfold CompatibleUpdateWithoutAbsr. intros. induction p2.
  - admit.
  - admit.
  - 
  Admitted. 
  

Definition HoareTriple {T: Type} (P Q: Lc.(State) ->  Prop) (M1 : LayerImpl Op Op1) (z: proc Op1 T) :=
  forall (s s': Lc.(State)) (r: T), P (s) /\ (exec Lc.(sem) (compile M1 z)) (s) (s') (r) -> Q (s').

Definition HoareTripleP {T: Type} (P Q: LA1.(State) ->  Prop) (z: proc Op1 T) :=
  forall (s s': LA1.(State)) (r: T), P (s) /\ (exec LA1.(sem) z) (s) (s') (r) -> Q (s').

Print LayerRefinement. 

Theorem proofPreservation: forall (T:Type) (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit) (P Q: Lc.(State) ->  Prop)  (P' Q': LA1.(State) ->  Prop) (z: proc Op1 T),
  HoareTriple P Q M1 z /\ compatibleUpdate M1 M2 R1 R2 -> HoareTriple P Q M2 z.
Proof.
  intros. destruct H as [H1 H2 ]. unfold HoareTriple. intros. 
  unfold HoareTriple in H1. specialize H1 with s s' r.
  unfold compatibleUpdate in H2.
  Admitted. 


(** ------------------------------------ OLD----------------------------------------- *)

Definition compatibleUpdate1  (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit) :=
  forall (T:Type) (p: proc Op1 T) (s1 s2: Lc.(State)) (state : LA1.(State)) (r:T),  exists (c1 c2: Lc.(State)),
  ((exec Lc.(sem) (compile M2 p)) (s1) (s2) (r) /\ R2 (state) (s1) (tt) ->  (exec Lc.(sem) (compile M1 p)) (c1) (c2) (r) /\ R1 (state) (c1) (tt) ) ->
  exists state':LA1.(State), (exec LA1.(sem) p ) (state) (state') (r) /\ R2 (state') (s2) (tt) /\ R1 (state') (c2) (tt).

Lemma updateOP1: forall (T:Type) (op: Op1 T) (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit) (s1 s2: Lc.(State)) (state : LA1.(State)) (r:T),
  exists (c1 c2: Lc.(State)), (exec Lc (M2.(compile_op) op) s1 s2 r /\ R2 state s1 tt ->
     exec Lc (M1.(compile_op) op) c1 c2 r /\ R1 state c1 tt) ->
    exists state' : LA1.(State),
      LA1.(step) op state state' r /\ R2 state' s2 tt /\ R1 state' c2 tt.
Proof.
  Admitted.

Theorem compatibleUpdateProof1: forall (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit), compatibleUpdate1 M1 M2 R1 R2.
Proof.
  intros. unfold compatibleUpdate1. induction p as [ | | ]. 
  - admit. 
  - admit. (**simpl. unfold pure. exists s1.  exists s2. intros. exists state. assert ( (s1 = s2 /\ r = v) /\ R2 state s1 tt) as HP.
    + admit.
    + specialize (H HP).
      destruct H as [H H']. destruct H as [H H''].
      destruct HP as [HP HPP]. destruct HP as [HP HP'].
      split.
      * split.
        ** auto.
        ** apply H''. 
      * split.
        ** rewrite <- H. apply HPP. 
        ** rewrite <- H. apply H'. *)
  -  intros. exists s1. exists s2. 
    admit.
  Admitted.  

Definition refinementUpdate (M1 : LayerImpl Op Op1) (M2 : LayerImpl Op Op1) (R1: relation LA1.(State) Lc.(State) unit) (R2: relation LA1.(State) Lc.(State) unit) :=
  forall (T:Type) (p: proc Op1 T),
  forall (c1 c2: Lc.(State)) (state : LA1.(State)) (r:T),
  (exec Lc.(sem) (compile M1 p)) (c1) (c2) (r)  /\ R1 (state) (c1) (tt) -> exists (s1 s2 : Lc.(State)), exec Lc.(sem)  (compile M2 p) (s1) (s2) (r) /\ R2(state) (s1) (tt).  
  

Definition softwareUpdate(M1: LayerImpl Op  Op1) (M2: LayerImpl Op  COP):=
   forall (T: Type) (p1 p2 : proc Op1 T),
  exec Lc.(sem)  M1.(init) ;; exec Lc.(sem) (compile M1 p1) ;; shutdown ;;
  exec Lc.(sem)  (compile M2 (relinkingFunction p2))
            --->
   exec Lc.(sem) M1.(init) ;; exec Lc.(sem) (compile M1 p1) ;; shutdown ;;
  exec Lc.(sem) (compile M1 p2).

Definition restrictiveSoftwareUpdate(M1: LayerImpl Op  Op1) (M2: LayerImpl Op  Op1):=
   forall (T: Type) (p1 p2 : proc Op1 T),
  exec Lc.(sem)  M1.(init) ;; exec Lc.(sem) (compile M1 p1) ;; shutdown ;;
  exec Lc.(sem)  (compile M2 p2)
            --->
   exec Lc.(sem) M1.(init) ;; exec Lc.(sem) (compile M1 p1) ;; shutdown ;;
  exec Lc.(sem) (compile M1 p2).

(** This will help us prove two base cases *)
Theorem  CompileImpl : forall  (M1 : LayerImpl Op  Op1) (M2 : LayerImpl Op COP)
  (T: Type) (p: proc Op1 T),
  exec Lc.(sem) (compile M2 (relinkingFunction p))
            --->
            exec Lc.(sem) (compile M1 p).
Proof.
  Admitted.
 

Theorem RSUProof :forall M1 M2: LayerImpl Op  Op1, restrictiveSoftwareUpdate M1 M2.
Proof.
  intros M1 M2. unfold restrictiveSoftwareUpdate. intros T p1 p2.
  Admitted.   
  
  
End Updates. 

