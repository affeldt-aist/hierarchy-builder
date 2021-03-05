From HB Require Import structures.

HB.mixin Record has_assoc T (F : T -> T -> T) := {
  assoc : forall x y z : T , F x (F y z) = F (F x y) z;
}.
HB.structure Definition Magma T := { F of has_assoc T F }.

HB.mixin Record has_neutral T (F : T -> T -> T) := {
  id : T;
  idl : forall x : T , F id x = x;
  idr : forall x : T , F x id = x;
}.
HB.structure Definition Monoid T := { F of Magma T F & has_neutral T F }.

About id.

Require Import Arith ssreflect.

HB.instance Definition _ := has_assoc.Build nat plus plus_assoc.

Lemma plus_O_r x : x + 0 = x. Proof. by rewrite -plus_n_O. Qed.
HB.instance Definition _ := has_neutral.Build nat plus 0 plus_O_n plus_O_r.

Check Monoid.of plus.

Lemma test x : x + 0 = x.
Proof. by rewrite idr. Qed.

HB.factory Record MOT T (F : T -> T -> T) := {
  assoc : forall x y z : T , F x (F y z) = F (F x y) z;
  id : T;
  idl : forall x : T , F id x = x;
  commid : forall x : T , F x id = F id x;
}.

HB.builders Context T F of MOT T F.

HB.instance Definition _ := has_assoc.Build T F assoc.

Lemma myidr x : F x id = x.
Proof. by rewrite commid idl. Qed.

HB.instance Definition _ := has_neutral.Build T F id idl myidr.

HB.end.

#[verbose]
HB.instance Definition _ :=
  MOT.Build nat mult Nat.mul_assoc 1 Nat.mul_1_l (fun x => Nat.mul_comm x 1).

Check Monoid.of mult.

