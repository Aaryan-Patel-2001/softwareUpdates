Require Import Spec.Layer.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.

Section Updates.

Variable Op: Type -> Type. 
          
Notation a_proc := (proc Op).

Variable  Op1: Type -> Type.

Variable  O': Type -> Type.

(**Variable shutdown**)

Inductive  Op2: Type -> Type :=
| Op1case(T:Type) : Op1 T -> Op2 T
| O'case(T:Type) : O' T -> Op2 T. 

Variable  Lc : Layer Op.

Variable LA1: Layer Op1.

Variable LA2: Layer Op2. 

Print proc. 

Fixpoint  relinkingFunciton {T: Type} (p: proc Op1 T) : proc Op2 T :=
  match p with
  | Call o => Call (Op1case o)
  | Ret v => Ret v
  | Bind e f => Bind (relinkingFunciton e) (fun x => relinkingFunciton(f x))
  end. 

Print LayerImpl.

Search "compile".

About compile. 

Definition softwareUpdate (M1: LayerImpl Lc Op1) (M2: LayerImpl Lc Op2) :=
 M1.(init) ;; compile M1 p ;;


End Updates. 

