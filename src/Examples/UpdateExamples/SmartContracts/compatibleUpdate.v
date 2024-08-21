Require Import Spec.update.
Require Import Examples.UpdateExamples.SmartContracts.Firstversion.
Require Import Examples.UpdateExamples.SmartContracts.version2.
Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Import  RelationNotations.


About softwareUpdate.

(**
Record LayerImpl (C_Op Op0 : Type -> Type) : Type := Build_LayerImpl
  { compile_op : forall T : Type, Op0 T -> proc C_Op T;
    recover : proc C_Op unit;
    init : proc C_Op InitStatus }.

Arguments LayerImpl (C_Op Op)%function_scope
Arguments Build_LayerImpl [C_Op]%function_scope (Op compile_op)%function_scope
  recover init



Print Firstversion.impl.

Definition reldef: relation Firstversion.con.l.(Layer.State) Firstversion.con.l.(Layer.State) unit.
Proof.
  Admitted. 

Lemma compatilbeSoftwareUpdate :
  softwareUpdate (Firstversion.con.l) (reldef)  (Firstversion.impl) (version2.impl).
Proof.                                                                                           Admitted. 

 *)
