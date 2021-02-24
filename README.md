[![Actions Status](https://github.com/math-comp/hierarchy-builder/workflows/CI/badge.svg)](https://github.com/math-comp/hierarchy-builder/actions)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://coq.zulipchat.com/#narrow/stream/237868-Hierarchy-Buidlder)

# Hierarchy Builder

High level commands to declare and evolve a hierarchy based on packed classes.

[Presented at FSCD2020, talk available on youtube.](https://www.youtube.com/watch?v=F6iRaTlQrlo)

## Example

```coq
From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

HB.mixin Record AddComoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.
HB.structure Definition AddComoid := { A of AddComoid_of_Type A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.
```

This is all we need to do in order to declare the `AddComoid` structure
and write statements in its signature.

We proceed by declaring how to obtain an Abelian group out of the
additive, commutative, monoid.

```coq
HB.mixin Record AbelianGrp_of_AddComoid A of AddComoid A := {
  opp : A -> A;
  addNr : forall x, opp x + x = 0;
}.
HB.structure Definition AbelianGrp := { A of AbelianGrp_of_AddComoid A & }.

Notation "- x" := (opp x).
```

Abelian groups feature the operations and properties given by the
`AbelianGrp_of_AddComoid` mixin (and its dependency `AddComoid`).

```coq
Lemma example (G : AbelianGrp.type) (x : G) : x + (- x) = - 0.
Proof. by rewrite addrC addNr -[LHS](addNr zero) addrC add0r. Qed.
```

We proceed by showing that `Z` is an example of both structures, and use
the lemma just proved on a statement about `Z`.

```coq
HB.instance Definition Z_CoMoid := AddComoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Definition Z_AbGrp := AbelianGrp_of_AddComoid.Build Z Z.opp Z.add_opp_diag_l.

Lemma example2 (x : Z) : x + (- x) = - 0.
Proof. by rewrite example. Qed.
```

## Documentation

#### Status

The software is beta-quality, it works but error messages should be improved.

The current version forces the carrier to be a type, ruling hierarchies of morphisms out.

This [draft paper](https://hal.inria.fr/hal-02478907) describes the language
in full detail.

#### Installation & availability

<details><summary>(click to expand)</summary><p>

HB works on Coq 8.11, 8.12 and 8.13

- You can install it via OPAM

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hierarchy-builder
```

- You can use it in nix with the attribute `coqPackages_8_11.hierarchy-builder` e.g. via `nix-shell -p coq_8_11 -p coqPackages_8_11.hierarchy-builder`
 
</p></details>

#### Key concepts

<details><summary>(click to expand)</summary><p>

- a *mixin* is a bare bone building block of the hierarchy, it packs operations
  and axioms.

- a *factory* is a package of operations and properties that is elaborated by
  HB to one or more mixin. A mixin is hence a trivial factory.

- a *structure* is declared by attaching zero or more factories to a type.

- a *builder* is a user provided piece of code capable of
  building one or more mixins from a factory.

- an *instance* is an example of a structure: it provides all operation and
  fulfills all axioms.

</p></details>

#### The commands of HB

<details><summary>(click to expand)</summary><p>

- `HB.mixin` declares a mixin
- `HB.structure` declares a structure
- `HB.factory` declares a factory
- `HB.builders` and `HB.end` declare a set of builders
- `HB.instance` declares a structure instance
- `HB.export` exports a module and schedules it for re-export
- `HB.reexport` exports all modules scheduled for re-export
- `HB.status` dumps the contents of the hierarchy (debug purposes)

Their documentation can be found in the comments of [structures.v](structures.v),
search for `Elpi Command` and you will find them. All commands can be
prefixed with the attribute `#[verbose]` to get an idea of what they are doing.

</p></details>

#### Demos

<details><summary>(click to expand)</summary><p>

- [demo1](demo1/) and [demo3](demo3/) declare and evolve a hierarchy up to
  rings with various clients that are tested not to break when the hierarchy
  evolves
- [demo2](demo2/) describes the subtle triangular interaction between groups,
  topological space and uniform spaces. Indeed, 1. all uniform spaces induce a
  topology, which makes them topological spaces, but 2. all topological groups
  (groups that are topological spaces such that the addition and opposite are
  continuous) induce a uniformity, which makes them uniform spaces. We solve
  this seamingly mutual dependency using HB.

</p></details>

#### Plan B

Scared of making your project depend on HB? This section is for you.

HB is based on a thick layer of software which we plan to maintain, but we
also understand it can look scary. Hence this insurance plan. By passing
the attribute `#[log]` each command prints Coq commands which are equivalent to
its effect. By replacing each HB command by its equivalent Coq commands, you
can eliminate the dependency on HB from your project.

This is a "plan B", by looking at the output of`#[log]` you will realize that
HB commands are much nicer (and shorter) than the equivalent Coq code. The
point of a "plan B" is to avoid nightmares, not to be nicer than plan A ;-)

How can you be ensure plan B works? We provide tools to check that, see
the details below.

<details><summary>(click to expand)</summary><p>


Hierarchy Builder commands can log their equivalent vernacular commands
to "patch" file (extension `.hb`). In order to do so, one has to
compile the project with the `COQ_ELPI_ATTRIBUTES=log_hb` variable set. Eg

```shell
COQ_ELPI_ATTRIBUTES=log_hb make
```

The `hb` command line utility, provided by the `coq-hierarchy-builder` package,
is able to apply the generated patches: it comments out HB commands and
inserts their equivalent Coq commands.

```shell
hb apply file1.v file2.v ...
```

The converse operation can be performed using the following command:

```shell
hb reset file1.v file2.v ...
```

We recommend to setup a CI job testing plan B. If you are using
`docker-coq-action` the following snippet is a good start:

```yaml
  hb-plan-B:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2
    - uses: coq-community/docker-coq-action@v1
      with:
        opam_file: './your-project.opam'        # depends on coq-hierarchy-builder
        script: |
          COQ_ELPI_ATTRIBUTES=log_hb make -j2
          hb patch `find . -name \*.v`
          rm -rf `coqc -where`/user-constribs/HB
          make -j2
          hb reset `find . -name \*.v`
          git diff --exit-code
```

</p></details>
