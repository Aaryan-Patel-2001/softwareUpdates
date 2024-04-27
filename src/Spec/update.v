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

Inductive  Op2: Type -> Type :=
| Op1case(T:Type) : Op1 T -> Op2 T
| O'case(T:Type) : O' T -> Op2 T. 

Variable  Lc : Layer Op.

Variable LA1: Layer Op1.

Variable LA2: Layer Op2.

Print relation. 

Variable shutdown: relation Lc.(State) Lc.(State) unit. 

Print proc. 

Fixpoint  relinkingFunction {T: Type} (p: proc Op1 T) : proc Op2 T :=
  match p with
  | Call o => Call (Op1case o)
  | Ret v => Ret v
  | Bind e f => Bind (relinkingFunction e) (fun x => relinkingFunction(f x))
  end. 

Print LayerImpl.

Search "compile".

About compile.

About exec. 

Definition softwareUpdate(M1: LayerImpl Op  Op1) (M2: LayerImpl Op  Op2):=
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



End Updates. 

