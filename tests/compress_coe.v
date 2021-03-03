From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

(**************************************************************************)
(* Stage 2: AddComoid -> AddAG -> Ring                                  *)
(**************************************************************************)

HB.mixin Record hasA T := { a : T }.
HB.structure Definition A := {T of hasA T}.

HB.mixin Record hasB (p : unit) T of A T := { b : T }.
HB.structure Definition B p := {T of A T & hasB p T}.

HB.mixin Record hasC (p q : unit) T of B p T := { c : T }.
HB.structure Definition C p q := {T of B p T & hasC p q T}.

HB.mixin Record hasD T of C tt tt T := { d : T }.
HB.structure Definition D := {T of C tt tt T & hasD T}.

HB.instance Definition prodA (A A' : A.type) :=
  hasA.Build (A * A')%type (a, a).

HB.instance Definition prodB p (B B' : B.type p) :=
  hasB.Build p (B * B')%type (b, b).

  HB.instance Definition prodC p q (C C' : C.type p q) :=
  hasC.Build p q (C * C')%type (c, c).

HB.instance Definition prodD (D D' : D.type) :=
  hasD.Build (D * D')%type (d, d).

Set Printing Coercions.
Print prod_prod_canonical_D.