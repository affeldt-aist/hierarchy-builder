From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

(**************************************************************************)
(* Stage 2: AddComoid -> AddAG -> Ring                                  *)
(**************************************************************************)

HB.mixin Record hasA T := { a : T }.
HB.structure Definition A := {T of hasA T}.

HB.mixin Record hasB T of A T := { b : T }.
HB.structure Definition B := {T of A T & hasB T}.

HB.mixin Record hasC T of B T := { c : T }.
HB.structure Definition C := {T of B T & hasC T}.

HB.mixin Record hasD T of C T := { d : T }.
HB.structure Definition D := {T of C T & hasD T}.

HB.instance Definition prodA (A A' : A.type) :=
  hasA.Build (A * A')%type (a, a).

HB.instance Definition prodB (B B' : B.type) :=
  hasB.Build (B * B')%type (b, b).

HB.instance Definition prodC (C C' : C.type) :=
  hasC.Build (C * C')%type (c, c).

HB.instance Definition prodD (D D' : D.type) :=
  hasD.Build (D * D')%type (d, d).

Set Printing Coercions.
Print prod_prod_canonical_D.