(*
Copyright 2010 IMDEA Software Institute
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*)

(******************************************************************************)
(* This file is Prelude -- often used notation definitions and lemmas that    *)
(* are not included in the other libraries.                                   *)
(******************************************************************************)

From HB Require Import structures.
From Coq Require Import ssreflect ssrfun Eqdep. 
From mathcomp Require Import ssrbool ssrnat seq eqtype choice.
From mathcomp Require Import  fintype finfun tuple perm fingroup.
From pcm Require Import options axioms.

(***********)
(* Prelude *)
(***********)

(* often used notation definitions and lemmas that are *)
(* not included in the other libraries *)

(* export inj_pair without exporting the whole Eqdep library *)
Definition inj_pair2 := @inj_pair2.
Arguments inj_pair2 {U P p x y}.

(* Because of a bug in inversion and injection tactics *)
(* we occasionally have to destruct pair by hand, else we *)
(* lose the second equation. *)
Lemma inj_pair A B (a1 a2 : A) (b1 b2 : B) :
         (a1, b1) = (a2, b2) -> 
         (a1 = a2) * (b1 = b2).
Proof. by case. Qed.

Arguments inj_pair {A B a1 a2 b1 b2}.

(* eta laws for pairs and units *)
Notation prod_eta := surjective_pairing.

(* eta law often used with injection *)
Lemma prod_inj A B (x y : A * B) : 
        x = y <-> 
        (x.1, x.2) = (y.1, y.2).
Proof. by case: x y=>x1 x2 []. Qed.

Lemma idfunE (U : Type) (x : U) : idfun x = x.
Proof. by []. Qed.

(* idfun is a left and right unit for composition *)
Lemma idfun0E (U V : Type) (f : U -> V):
        (idfun \o f = f) * (f \o idfun = f).
Proof. by []. Qed.

Lemma trans_eq A (x y z : A) : 
        x = y -> 
        x = z -> 
        y = z.
Proof. by move/esym; apply: eq_trans. Qed.

(* Triples *)
Section TripleLemmas.
Variables (A B C : Type).
Implicit Types (a : A) (b : B) (c : C).

Lemma t1P a1 a2 b1 b2 c1 c2 : 
        (a1, b1, c1) = (a2, b2, c2) -> 
        a1 = a2.
Proof. by case. Qed.

Lemma t2P a1 a2 b1 b2 c1 c2 : 
        (a1, b1, c1) = (a2, b2, c2) -> 
        b1 = b2.
Proof. by case. Qed.

Lemma t3P a1 a2 b1 b2 c1 c2 : 
        (a1, b1, c1) = (a2, b2, c2) -> 
        c1 = c2.
Proof. by case. Qed.

Lemma t12P a1 a2 b1 b2 c1 c2 : 
        (a1, b1, c1) = (a2, b2, c2) -> 
        (a1 = a2) * (b1 = b2).
Proof. by case. Qed.

Lemma t13P a1 a2 b1 b2 c1 c2 : 
        (a1, b1, c1) = (a2, b2, c2) -> 
        (a1 = a2) * (c1 = c2).
Proof. by case. Qed.

Lemma t23P a1 a2 b1 b2 c1 c2 : 
        (a1, b1, c1) = (a2, b2, c2) -> 
        (b1 = b2) * (c1 = c2).
Proof. by case. Qed.

End TripleLemmas.

Prenex Implicits t1P t2P t3P t12P t13P t23P.

(************)
(* Products *)
(************)

Inductive Prod3 U1 U2 U3 := 
  mk3 {proj31 : U1; proj32 : U2; proj33 : U3}.
Inductive Prod4 U1 U2 U3 U4 := 
  mk4 {proj41 : U1; proj42 : U2; proj43 : U3; proj44 : U4}.
Inductive Prod5 U1 U2 U3 U4 U5 := 
  mk5 {proj51 : U1; proj52 : U2; proj53 : U3; proj54 : U4; proj55 : U5}.
Inductive Prod6 U1 U2 U3 U4 U5 U6 := 
  mk6 {proj61 : U1; proj62 : U2; proj63 : U3; 
       proj64 : U4; proj65 : U5; proj66 : U6}.
Inductive Prod7 U1 U2 U3 U4 U5 U6 U7 := 
  mk7 {proj71 : U1; proj72 : U2; proj73 : U3; 
       proj74 : U4; proj75 : U5; proj76 : U6; proj77 : U7}.
Prenex Implicits proj31 proj32 proj33.
Prenex Implicits proj41 proj42 proj43 proj44.
Prenex Implicits proj51 proj52 proj53 proj54 proj55.
Prenex Implicits proj61 proj62 proj63 proj64 proj65 proj66.
Prenex Implicits proj71 proj72 proj73 proj74 proj75 proj76 proj77.

Definition eq3 (U1 U2 U3 : eqType) (x y : Prod3 U1 U2 U3) := 
 [&& proj31 x == proj31 y, proj32 x == proj32 y & proj33 x == proj33 y].
Definition eq4 (U1 U2 U3 U4 : eqType) (x y : Prod4 U1 U2 U3 U4) := 
 [&& proj41 x == proj41 y, proj42 x == proj42 y, proj43 x == proj43 y & 
     proj44 x == proj44 y].
Definition eq5 (U1 U2 U3 U4 U5 : eqType) (x y : Prod5 U1 U2 U3 U4 U5) := 
 [&& proj51 x == proj51 y, proj52 x == proj52 y, proj53 x == proj53 y,
     proj54 x == proj54 y & proj55 x == proj55 y].
Definition eq6 (U1 U2 U3 U4 U5 U6 : eqType) (x y : Prod6 U1 U2 U3 U4 U5 U6) := 
 [&& proj61 x == proj61 y, proj62 x == proj62 y, proj63 x == proj63 y,
     proj64 x == proj64 y, proj65 x == proj65 y & proj66 x == proj66 y].
Definition eq7 (U1 U2 U3 U4 U5 U6 U7 : eqType) (x y : Prod7 U1 U2 U3 U4 U5 U6 U7) := 
 [&& proj71 x == proj71 y, proj72 x == proj72 y, proj73 x == proj73 y,
     proj74 x == proj74 y, proj75 x == proj75 y, proj76 x == proj76 y & 
     proj77 x == proj77 y].

Lemma eq3P U1 U2 U3 : 
        Equality.axiom (@eq3 U1 U2 U3).
Proof.
rewrite /eq3; case=>x1 x2 x3 [y1 y2 y3] /=. 
by do ![case: eqP=>[->|]]; constructor=>//; case.
Qed.

Lemma eq4P U1 U2 U3 U4 : 
        Equality.axiom (@eq4 U1 U2 U3 U4).
Proof.
rewrite /eq4; case=>x1 x2 x3 x4 [y1 y2 y3 y4] /=. 
by do ![case: eqP=>[->|]]; constructor=>//; case.
Qed.

Lemma eq5P U1 U2 U3 U4 U5 : 
        Equality.axiom (@eq5 U1 U2 U3 U4 U5).
Proof.
rewrite /eq5; case=>x1 x2 x3 x4 x5 [y1 y2 y3 y4 y5] /=. 
by do ![case: eqP=>[->|]]; constructor=>//; case.
Qed.

Lemma eq6P U1 U2 U3 U4 U5 U6 : 
        Equality.axiom (@eq6 U1 U2 U3 U4 U5 U6).
Proof.
rewrite /eq6; case=>x1 x2 x3 x4 x5 x6 [y1 y2 y3 y4 y5 y6] /=. 
by do ![case: eqP=>[->|]]; constructor=>//; case.
Qed.

Lemma eq7P U1 U2 U3 U4 U5 U6 U7 : 
        Equality.axiom (@eq7 U1 U2 U3 U4 U5 U6 U7).
Proof.
rewrite /eq7; case=>x1 x2 x3 x4 x5 x6 x7 [y1 y2 y3 y4 y5 y6 y7] /=. 
by do ![case: eqP=>[->|]]; constructor=>//; case.
Qed.

HB.instance Definition _ (U1 U2 U3 : eqType) := 
  hasDecEq.Build (Prod3 U1 U2 U3) (@eq3P U1 U2 U3).
HB.instance Definition _ (U1 U2 U3 U4 : eqType) := 
  hasDecEq.Build (Prod4 U1 U2 U3 U4) (@eq4P U1 U2 U3 U4).
HB.instance Definition _ (U1 U2 U3 U4 U5 : eqType) := 
  hasDecEq.Build (Prod5 U1 U2 U3 U4 U5) (@eq5P U1 U2 U3 U4 U5).
HB.instance Definition _ (U1 U2 U3 U4 U5 U6 : eqType) := 
  hasDecEq.Build (Prod6 U1 U2 U3 U4 U5 U6) (@eq6P U1 U2 U3 U4 U5 U6).
HB.instance Definition _ (U1 U2 U3 U4 U5 U6 U7 : eqType) := 
  hasDecEq.Build (Prod7 U1 U2 U3 U4 U5 U6 U7) (@eq7P U1 U2 U3 U4 U5 U6 U7).

(***************************)
(* operations on functions *)
(***************************)

Lemma eta A (B : A -> Type) (f : forall x, B x) : f = [eta f].
Proof. by []. Qed.

Lemma ext A (B : A -> Type) (f1 f2 : forall x, B x) :
        f1 = f2 -> forall x, f1 x = f2 x.
Proof. by move=>->. Qed.

Lemma compA A B C D (h : A -> B) (g : B -> C) (f : C -> D) :
        (f \o g) \o h = f \o (g \o h).
Proof. by []. Qed.

Lemma compE A B C (g : B -> C) (f : A -> B) x : 
        g (f x) = (g \o f) x.
Proof. by []. Qed.

Definition fprod A1 A2 B1 B2 (f1 : A1 -> B1) (f2 : A2 -> B2) :=
  fun (x : A1 * A2) => (f1 x.1, f2 x.2).

Notation "f1 \* f2" := (fprod f1 f2) 
  (at level 42, left associativity) : fun_scope.

(* product morphism, aka. fork/fanout/fsplice *)
Definition pmorphism A B1 B2 (f1 : A -> B1) (f2 : A -> B2) :=
  fun x : A => (f1 x, f2 x).
Arguments pmorphism {A B1 B2} f1 f2 x /.
Notation "f1 \** f2 " := (pmorphism f1 f2)
  (at level 50, left associativity, format "f1  \** '/ '  f2") : fun_scope.

(* product with functions *)
Lemma prod_feta (A B : Type) : @idfun (A * B) = fst \** snd.
Proof. by apply: fext=>x; rewrite /pmorphism -prod_eta. Qed.

Reserved Notation "[ ** f1 & f2 ]" (at level 0).
Reserved Notation "[ ** f1 , f2 & f3 ]" (at level 0, format
  "'[hv' [ ** '['  f1 , '/'  f2 ']' '/ '  &  f3 ] ']'").
Reserved Notation "[ ** f1 , f2 , f3 & f4 ]" (at level 0, format
  "'[hv' [ ** '['  f1 , '/'  f2 , '/'  f3 ']' '/ '  &  f4 ] ']'").
Reserved Notation "[ ** f1 , f2 , f3 , f4 & f5 ]"  (at level 0, format
  "'[hv' [ ** '['  f1 , '/'  f2 , '/'  f3 , '/'  f4 ']' '/ '  &  f5 ] ']'").

Notation "[ ** f1 & f2 ]" := (f1 \** f2) (only parsing) : fun_scope.
Notation "[ ** f1 , f2 & f3 ]" := ((f1 \** f2) \** f3) : fun_scope.
Notation "[ ** f1 , f2 , f3 & f4 ]" := (((f1 \** f2) \** f3) \** f4) : fun_scope.
Notation "[ ** f1 , f2 , f3 , f4 & f5 ]" := ((((f1 \** f2) \** f3) \** f4) \** f5) : fun_scope.

(************************)
(* extension to ssrbool *)
(************************)

Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  &  P6 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 ']' '/ '  &  P7 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 ']' '/ '  &  P7 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 ']' '/ '  &  P8 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 ']' '/ '  &  P9 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/' P9 ']' '/ '  &  P10 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/' P9 , '/' P10 ']' '/ '  &  P11 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 & P12 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 , '/'  P6 , '/'  P7 , '/'  P8 , '/' P9 , '/' P10 , '/' P11 ']' '/ '  &  P12 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  |  P5 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 , '/'  P5 ']' '/ '  |  P6 ] ']'").

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.
Inductive and7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Inductive and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Prop) : Prop :=
  And8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Inductive and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Inductive and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop) : Prop :=
  And10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.
Inductive and11 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 : Prop) : Prop :=
  And11 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11.
Inductive and12 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 : Prop) : Prop :=
  And12 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12.

Inductive or5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  Or51 of P1 | Or52 of P2 | Or53 of P3 | Or54 of P4 | Or55 of P5.
Inductive or6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  Or61 of P1 | Or62 of P2 | Or63 of P3 | Or64 of P4 | Or65 of P5 | Or66 of P6.
Inductive or7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  Or71 of P1 | Or72 of P2 | Or73 of P3 | Or74 of P4 | Or75 of P5 | Or76 of P6 | Or77 of P7.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" :=
  (and11 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 & P12 ]" :=
  (and12 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12) : type_scope.

Notation "[ \/ P1 , P2 , P3 , P4 | P5 ]" := (or5 P1 P2 P3 P4 P5) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 | P6 ]" := (or6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ \/ P1 , P2 , P3 , P4 , P5 , P6 | P7 ]" := (or7 P1 P2 P3 P4 P5 P6 P7) : type_scope.

(** Add the ability to rewrite with [<->] for the custom logical connectives *)

(* DEVCOMMENT *)
(* TODO: we should move some of the following to [ssrbool] in Coq *)
(* /DEVCOMMENT *)

From Coq Require Import Classes.Morphisms Program.Basics Program.Tactics.
From Coq Require Import Relations.

Local Obligation Tactic := try solve [simpl_relation | firstorder auto].

Definition iter_arrow_type (n : nat) (A : Type) := iter n (fun T => A -> T).

Fixpoint iter_respectful {S T} (A : relation S) (Z : relation T) (n : nat)
  : relation (iter_arrow_type n S T) :=
  if n is n'.+1 then respectful A (@iter_respectful _ _ A Z n')
  else Z.
Arguments iter_respectful {S T} A Z n.

(** Logical conjunction *)
#[export] Program Instance and3_impl_morphism : Proper (iter_respectful impl impl 3) and3 | 1.
#[export] Program Instance and3_iff_morphism : Proper (iter_respectful iff iff 3) and3 | 1.

#[export] Program Instance and4_impl_morphism : Proper (iter_respectful impl impl 4) and4 | 1.
#[export] Program Instance and4_iff_morphism : Proper (iter_respectful iff iff 4) and4 | 1.

#[export] Program Instance and5_impl_morphism : Proper (iter_respectful impl impl 5) and5 | 1.
#[export] Program Instance and5_iff_morphism : Proper (iter_respectful iff iff 5) and5 | 1.

#[export] Program Instance and6_impl_morphism : Proper (iter_respectful impl impl 6) and6 | 1.
#[export] Program Instance and6_iff_morphism : Proper (iter_respectful iff iff 6) and6 | 1.

#[export] Program Instance and7_impl_morphism : Proper (iter_respectful impl impl 7) and7 | 1.
#[export] Program Instance and7_iff_morphism : Proper (iter_respectful iff iff 7) and7 | 1.

#[export] Program Instance and8_impl_morphism : Proper (iter_respectful impl impl 8) and8 | 1.
#[export] Program Instance and8_iff_morphism : Proper (iter_respectful iff iff 8) and8 | 1.

#[export] Program Instance and9_impl_morphism : Proper (iter_respectful impl impl 9) and9 | 1.
#[export] Program Instance and9_iff_morphism : Proper (iter_respectful iff iff 9) and9 | 1.

#[export] Program Instance and10_impl_morphism : Proper (iter_respectful impl impl 10) and10 | 1.
#[export] Program Instance and10_iff_morphism : Proper (iter_respectful iff iff 10) and10 | 1.

#[export] Program Instance and11_impl_morphism : Proper (iter_respectful impl impl 11) and11 | 1.
#[export] Program Instance and11_iff_morphism : Proper (iter_respectful iff iff 11) and11 | 1.

#[export] Program Instance and12_impl_morphism : Proper (iter_respectful impl impl 12) and12 | 1.
#[export] Program Instance and12_iff_morphism : Proper (iter_respectful iff iff 12) and12 | 1.

(** Logical disjunction *)
#[export] Program Instance or3_impl_morphism : Proper (iter_respectful impl impl 3) or3 | 1.
#[export] Program Instance or3_iff_morphism : Proper (iter_respectful iff iff 3) or3 | 1.

#[export] Program Instance or4_impl_morphism : Proper (iter_respectful impl impl 4) or4 | 1.
#[export] Program Instance or4_iff_morphism : Proper (iter_respectful iff iff 4) or4 | 1.

#[export] Program Instance or5_impl_morphism : Proper (iter_respectful impl impl 5) or5 | 1.
#[export] Program Instance or5_iff_morphism : Proper (iter_respectful iff iff 5) or5 | 1.

#[export] Program Instance or6_impl_morphism : Proper (iter_respectful impl impl 6) or6 | 1.
#[export] Program Instance or6_iff_morphism : Proper (iter_respectful iff iff 6) or6 | 1.

#[export] Program Instance or7_impl_morphism : Proper (iter_respectful impl impl 7) or7 | 1.
#[export] Program Instance or7_iff_morphism : Proper (iter_respectful iff iff 7) or7 | 1.


Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and7P : reflect [/\ b1, b2, b3, b4, b5, b6 & b7] [&& b1, b2, b3, b4, b5, b6 & b7].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and8P : reflect [/\ b1, b2, b3, b4, b5, b6, b7 & b8] [&& b1, b2, b3, b4, b5, b6, b7 & b8].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and9P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8 & b9] [&& b1, b2, b3, b4, b5, b6, b7, b8 & b9].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and10P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10] [&& b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and11P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and12P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
by constructor.
Qed.

Lemma or5P : reflect [\/ b1, b2, b3, b4 | b5] [|| b1, b2, b3, b4 | b5].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
by constructor; case.
Qed.

Lemma or6P : reflect [\/ b1, b2, b3, b4, b5 | b6] [|| b1, b2, b3, b4, b5 | b6].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
by constructor; case.
Qed.

Lemma or7P : reflect [\/ b1, b2, b3, b4, b5, b6 | b7] [|| b1, b2, b3, b4, b5, b6 | b7].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
case b5; first by constructor; constructor 5.
case b6; first by constructor; constructor 6.
case b7; first by constructor; constructor 7.
by constructor; case.
Qed.

End ReflectConnectives.

Arguments and6P {b1 b2 b3 b4 b5 b6}.
Arguments and7P {b1 b2 b3 b4 b5 b6 b7}.
Arguments and8P {b1 b2 b3 b4 b5 b6 b7 b8}.
Arguments and9P {b1 b2 b3 b4 b5 b6 b7 b8 b9}.
Arguments and10P {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10}.
Arguments and11P {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11}.
Arguments and12P {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12}.

Arguments or5P {b1 b2 b3 b4 b5}.
Arguments or6P {b1 b2 b3 b4 b5 b6}.
Arguments or7P {b1 b2 b3 b4 b5 b6 b7}.
Prenex Implicits and6P and7P or5P or6P or7P.

Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof. by case: a; case: b; constructor=>//; case. Qed.

Arguments andX {a b}.

Lemma iffPb (b1 b2 : bool) : reflect (b1 <-> b2) (b1 == b2).
Proof.
case: eqP=>[->|N]; constructor=>//.
case: b1 b2 N; case=>//= _.
- by case=>/(_ erefl).
by case=>_ /(_ erefl).
Qed.

Lemma implyb_trans a b c : 
        a ==> b -> 
        b ==> c -> 
        a ==> c.
Proof. by case: a=>//=->. Qed.

Lemma iffE (b1 b2 : bool) : b1 = b2 <-> (b1 <-> b2).
Proof. by split=>[->|] //; move/iffPb/eqP. Qed.

(* subsets *)

Lemma subsetC T (p q : mem_pred T) :
        {subset p <= q} -> 
        {subset predC q <= predC p}.
Proof. by move=>H x; apply: contra (H x). Qed.

Lemma subsetR T (p q : mem_pred T) :
        {subset p <= predC q} -> 
        {subset q <= predC p}.
Proof. by move=>H x; apply: contraL (H x). Qed.

Lemma subsetL T (p q : mem_pred T) :
        {subset predC p <= q} -> 
        {subset predC q <= p}.
Proof. by move=>H x; apply: contraR (H x). Qed.

Lemma subsetLR T (p q : mem_pred T) :
        {subset predC p <= predC q} -> 
        {subset q <= p}.
Proof. by move=>H x; apply: contraLR (H x). Qed.

Lemma subset_disj T (p q r : mem_pred T) :
        {subset p <= q} -> 
        (forall x, x \in q -> x \in r -> false) ->
        (forall x, x \in p -> x \in r -> false).
Proof. by move=>H D x /H/D. Qed.

Lemma subset_disj2 T (p p1 q q1 : mem_pred T) :
        {subset p1 <= p} -> 
        {subset q1 <= q} -> 
        (forall x, x \in p -> x \in q -> false) ->
        (forall x, x \in p1 -> x \in q1 -> false).
Proof. 
move=>H1 H2 D1; apply: subset_disj H1 _ => x H /H2.
by apply: D1 H.
Qed.

(**************)
(* empty type *)
(**************)

Lemma False_eqP : Equality.axiom (fun _ _ : False => true).
Proof. by case. Qed.

HB.instance Definition _ := hasDecEq.Build False False_eqP. 

(*************)
(* sum types *)
(*************)

Section InvertingSumTags.
Variables A B : Type.

Definition lft : A + B -> option A :=
  fun x => if x is inl x' then Some x' else None.
Definition rgt : A + B -> option B :=
  fun x => if x is inr x' then Some x' else None.

Lemma lft_inl_ocanc : ocancel lft inl. Proof. by case. Qed.
Lemma rgt_inr_ocanc : ocancel rgt inr. Proof. by case. Qed.
Lemma inl_lft_pcanc : pcancel inl lft. Proof. by []. Qed.
Lemma inr_rgt_pcanc : pcancel inr rgt. Proof. by []. Qed.

End InvertingSumTags.

Prenex Implicits lft rgt.

#[export] Hint Extern 0 (ocancel _ _) =>
 (apply: lft_inl_ocanc || apply: rgt_inr_ocanc) : core.

(****************)
(* option types *)
(****************)

(* Alternative mechanism for manipulating *)
(* properties of the form isSome X. *)
(* To use a lemma of the form isSome X *)
(* one tyoically has to explicitly put the conclusion *)
(* of that lemma onto the context, and then case on X. *)
(* If such lemma is restated using is_some X *)
(* then it suffices to case on the lemma's name. *)
(* This saves typing X explicitly, which *)
(* may be significant if X is large. *)

Inductive is_some_spec A x : option A -> Prop := 
| is_some_case v of x = Some v : is_some_spec x (Some v).

Hint Resolve is_some_case : core.

Notation is_some x := (is_some_spec x x).

Lemma is_someP A (x : option A) : reflect (is_some x) (isSome x).
Proof. by case: x=>[a|]; constructor=>//; case. Qed.

(* some simplifications *)
Lemma oapp_some A (x : option A) : oapp [eta Some] None x = x.
Proof. by case: x. Qed.

Lemma obind_some A (x : option A) : obind [eta Some] x = x.
Proof. exact: oapp_some. Qed.

(********)
(* nats *)
(********)

Lemma gt0 m n : m < n -> 0 < n.
Proof. by case: n. Qed.

Lemma neq0 m n : m < n -> n != 0.
Proof. by move/gt0; rewrite lt0n. Qed.

Lemma neqSn n : n.+1 != n.
Proof. by elim: n. Qed.

Lemma neqnS n : n != n.+1.
Proof. by elim: n. Qed.

(**************************************)
(* Inhabited (non-empty) finite types *)
(**************************************)

Lemma inhabits (T : finType) (t : T) : 0 < #|T|.
Proof. by apply/card_gt0P; exists t. Qed.

Lemma inhabits_irr (T : finType) (t1 t2 : T) : 
        inhabits t1 = inhabits t2.
Proof. by apply: bool_irrelevance. Qed.

Definition inhabited_axiom (T : finType) := 0 < #|T|.

HB.mixin Record isInhabited T of Finite T := {
  card_inhab : inhabited_axiom T}.

#[short(type="ifinType")]
HB.structure Definition Inhabited := {T of isInhabited T & Finite T}.

Lemma inhabF (T : ifinType) : ~ (@predT T =1 xpred0).
Proof. by case/card_gt0P: (@card_inhab T)=>x _ /(_ x). Qed.

Definition inhab {T : ifinType} : T := 
  match pickP predT with 
  | Pick x _ => x
  | Nopick pf => False_rect T (inhabF pf)
  end.

HB.instance Definition _ := isInhabited.Build unit (inhabits tt).
HB.instance Definition _ := isInhabited.Build bool (inhabits false).
HB.instance Definition _ n := isInhabited.Build 'I_n.+1 (inhabits ord0).
HB.instance Definition _ (T : finType) := 
  isInhabited.Build (option T) (inhabits None).

(*************************************)
(* A copy of booleans with mnemonics *)
(* LL and RR for working with sides  *)
(*************************************)

Inductive Side := LL | RR.
Definition Side_eq x y :=
  match x, y with LL, LL => true | RR, RR => true | _, _ => false end.
Definition nat2Side x := if odd x then LL else RR.
Definition Side2nat x := if x is RR then 0 else 1.

Lemma ssrcanc : ssrfun.cancel Side2nat nat2Side. Proof. by case. Qed.
HB.instance Definition _ : isCountable Side := CanIsCountable ssrcanc.

Lemma Side_enumP : Finite.axiom [:: LL; RR]. Proof. by case. Qed.
HB.instance Definition _ : isFinite Side := isFinite.Build Side Side_enumP.
HB.instance Definition _ := isInhabited.Build Side (inhabits LL).

(*************)
(* Sequences *)
(*************)

(* folds *)
(* TODO upstream to mathcomp *)

Lemma map_foldr {T1 T2} (f : T1 -> T2) xs :
        map f xs = foldr (fun x ys => f x :: ys) [::] xs.
Proof. by []. Qed.

Lemma fusion_foldr {T R Q} (g : R -> Q) f0 f1 z0 z1 (xs : seq T) :
        (forall x y, g (f0 x y) = f1 x (g y)) -> 
        g z0 = z1 ->
        g (foldr f0 z0 xs) = foldr f1 z1 xs.
Proof. by move=>Hf Hz; elim: xs=>//= x xs <-. Qed.

Lemma fusion_foldl {T R Q} (g : R -> Q) f0 f1 z0 z1 (xs : seq T) :
        (forall x y, g (f0 x y) = f1 (g x) y) -> 
        g z0 = z1 ->
        g (foldl f0 z0 xs) = foldl f1 z1 xs.
Proof.
move=>Hf Hz; elim: xs z0 z1 Hz =>//= x xs IH z0 z1 Hz.
by apply: IH; rewrite Hf Hz.
Qed.

Lemma foldl_foldr {T R} (f : R -> T -> R) z xs :
        foldl f z xs = foldr (fun b g x => g (f x b)) id xs z.
Proof. by elim: xs z=>/=. Qed.

Lemma foldr_foldl {T R} (f : T -> R -> R) z xs :
        foldr f z xs = foldl (fun g b x => g (f b x)) id xs z.
Proof.
elim/last_ind: xs z=>//= xs x IH z.
by rewrite foldl_rcons -IH foldr_rcons.
Qed.

(* pmap *)
(* TODO upstream to mathcomp *)
Lemma pmap_pcomp {S T U} (f : T -> option U) (g : S -> option T) s : 
        pmap (pcomp f g) s = pmap f (pmap g s).
Proof. by elim: s=>//= x s ->; rewrite /pcomp; case: (g x). Qed.

(* sequence prefixes *)

(* Two helper concepts for searching in sequences:                       *)
(* - onth: like nth, but returns None when the element is not found      *)
(* - Prefix: a prefix relation on sequences, used for growing            *)
(*   interpretation contexts                                             *)

Fixpoint onth A (s : seq A) n : option A :=
  if s is x::sx then if n is nx.+1 then onth sx nx else Some x else None.

Definition Prefix A (s1 s2 : seq A) : Prop :=
  forall n x, onth s1 n = some x -> onth s2 n = some x.

(* Lemmas *)

Section SeqPrefix.
Variable A : Type.
Implicit Type s : seq A.

Variant onth_spec s n : bool -> Type :=
| onth_none   : onth s n = None   -> onth_spec s n false
| onth_some v : onth s n = Some v -> onth_spec s n true.

Lemma onth_sizeP s n : onth_spec s n (n < size s).
Proof.
elim: s n=>/= [|a s IH] n; first by rewrite ltn0; constructor.
case: n=>[|n] /=; first by apply: (@onth_some _ _ a).
rewrite ltnS; case: (IH n)=>[|v] H.
- by constructor.
by apply: (@onth_some _ _ v).
Qed.

Lemma size_onth s n : n < size s -> exists x, onth s n = Some x.
Proof.
by case: onth_sizeP=>// v H _; exists v.
Qed.

Lemma onth_size s n x : onth s n = Some x -> n < size s.
Proof.
by case: onth_sizeP=>//->.
Qed.

Lemma size_onthPn s n : reflect (onth s n = None) (size s <= n).
Proof.
by rewrite leqNgt; apply: (iffP idP); case: onth_sizeP=>//= v ->.
Qed.

Lemma onth_sizeN s : onth s (size s) = None.
Proof. by apply/size_onthPn. Qed.

Lemma nth_onth x0 n s : nth x0 s n = odflt x0 (onth s n).
Proof.
elim: s n=>/= [|a s IH] n /=; first by apply: nth_nil.
by case: n.
Qed.

Lemma onth_nth x0 n s : 
        n < size s -> 
        onth s n = Some (nth x0 s n).
Proof.
elim: s n=>//= a s IH n.
by rewrite ltnS; case: n.
Qed.

Lemma Prefix_refl s : Prefix s s.
Proof. by move=>n x <-. Qed.

Lemma Prefix_trans s2 s1 s3 : 
        Prefix s1 s2 -> Prefix s2 s3 -> Prefix s1 s3.
Proof. by move=>H1 H2 n x E; apply: H2; apply: H1. Qed.

Lemma Prefix_cons x s1 s2 : Prefix (x :: s1) (x :: s2) <-> Prefix s1 s2.
Proof. by split=>E n; [apply: (E n.+1) | case: n]. Qed.

Lemma Prefix_cons' x y s1 s2 :
        Prefix (x :: s1) (y :: s2) -> x = y /\ Prefix s1 s2.
Proof. by move=>H; case: (H 0 x (erefl _)) (H)=>-> /Prefix_cons. Qed.

Lemma Prefix_rcons x s : Prefix s (rcons s x).
Proof. by elim: s=>//= y ys IH; apply/Prefix_cons; apply: IH. Qed.

Lemma Prefix_cat s1 s2 : Prefix s1 (s1 ++ s2).
Proof.
elim: s2 s1=>[|x xs IH] s1; first by rewrite cats0.
rewrite -cat_rcons; apply: Prefix_trans (IH _).
by apply: Prefix_rcons.
Qed.

Lemma Prefix_size s1 s2 : Prefix s1 s2 -> size s1 <= size s2.
Proof.
elim: s1 s2=>[//|a s1 IH] [|b s2] H; first by move: (H 0 a (erefl _)).
by rewrite ltnS; apply: (IH _ (proj2 (Prefix_cons' H))).
Qed.

Lemma Prefix_onth s t x : 
        x < size s -> 
        Prefix s t -> onth s x = onth t x.
Proof.
elim:s t x =>[//|a s IH] [|b t] x H1 H2; first by move: (H2 0 a (erefl _)).
by case/Prefix_cons': H2=><- H2; case: x H1=>[|n] //= H1; apply: IH.
Qed.

Lemma PrefixE s1 s2 : Prefix s1 s2 <-> exists s3, s2 = s1 ++ s3.
Proof.
split; last by case=>s3 ->; apply: Prefix_cat.
elim: s1 s2=>[|x xs IH] s2; first by exists s2.
case: s2=>[/(_ 0 x erefl)//|y ys /Prefix_cons' [?]].
by subst y=>/IH [s3 ->]; exists s3.
Qed.

End SeqPrefix.

#[export] Hint Resolve Prefix_refl : core.

(* when A : eqType *)

Section SeqPrefixEq.
Variable A : eqType.
Implicit Type s : seq A.

Lemma onth_mem s n x :
        onth s n = Some x -> 
        x \in s.
Proof.
by elim: s n=>//= a s IH [[->]|n /IH]; rewrite inE ?eq_refl // orbC =>->.
Qed.

Lemma onth_index (s : seq A) x :
        onth s (index x s) = 
          if x \in s then Some x else None.
Proof.
by elim: s=>//=h s IH; rewrite inE eq_sym; case: eqP=>//= ->.
Qed.

Lemma PrefixP (s1 s2 : seq A) :
        reflect (Prefix s1 s2) (prefix s1 s2).
Proof.
apply/(equivP (prefixP (s1:=s1) (s2:=s2))).
by apply: iff_sym; exact: PrefixE.
Qed.

End SeqPrefixEq.

(******************************)
(* Some commuting conversions *)
(******************************)

Lemma fun_op A B C (b : option A) (vS : A -> B) (vN : B)  (f : B -> C) :
        f (if b is Some v then vS v else vN) =
        if b is Some v then f (vS v) else f vN.
Proof. by case: b=>//. Qed.

Lemma op_if A B (b : bool) (vS vN : option A)  (vS1 : A -> B) (vN1 : B) :
        (if (if b then vS else vN) is Some v then vS1 v else vN1) =
        if b then if vS is Some v then vS1 v else vN1
        else if vN is Some v then vS1 v else vN1.
Proof. by case: b. Qed.

Lemma if_triv b : (if b then true else false) = b.
Proof. by case: b. Qed.

(*************************************************************)
(* quick ways to extract projections and transitivity proofs *)
(* out of iterated inequalities                              *)
(*************************************************************)

Lemma ltn13 a b c : a < b < c -> a < c.
Proof. by case/andP; apply: ltn_trans. Qed.

Lemma ltn12 a b c : a < b < c -> a < b.
Proof. by case/andP. Qed.

Lemma ltn23 a b c : a < b < c -> b < c.
Proof. by case/andP. Qed.

Lemma leq13 a b c : a <= b <= c -> a <= c.
Proof. by case/andP; apply: leq_trans. Qed.

Lemma leq12 a b c : a <= b <= c -> a <= b.
Proof. by case/andP. Qed.

Lemma leq23 a b c : a <= b <= c -> b <= c.
Proof. by case/andP. Qed.

Lemma lqt13 a b c : a <= b < c -> a < c.
Proof. by case/andP; apply: leq_ltn_trans. Qed.

Lemma lqt12 a b c : a <= b < c -> a <= b.
Proof. by case/andP. Qed.

Lemma lqt23 a b c : a <= b < c -> b < c.
Proof. by case/andP. Qed.

(********************)
(* Finite functions *)
(********************)

Section FinFun.
Variables (T : finType) (Us : T -> Type).
Implicit Type f : {dffun forall t, Us t}.

(* Explicit name for finite function application. *)
(* Will be used to hang canonical projections onto. *)
(* The function/argument order is reversed to facilitate rewriting. *)
Definition sel tg f : Us tg := f tg.

Lemma ffinP f1 f2 : (forall t, sel t f1 = sel t f2) <-> f1 = f2.
Proof. by rewrite ffunP. Qed. 

(* beta equality *)
Lemma sel_fin t (f : forall t, Us t) : sel t (finfun f) = f t.
Proof. by rewrite /sel ffunE. Qed.

(* eta equality *)
Lemma fin_eta f : f = finfun (sel^~ f).
Proof. by apply/ffinP=>t; rewrite sel_fin. Qed.

(* function *)
Definition splice tg f (v : Us tg) : {dffun _} := 
  finfun (fun x => 
    if decP (x =P tg) is left pf then cast Us pf v 
    else sel x f).

Lemma sel_splice t f x (v : Us x) : 
        sel t (splice f v) = 
        if decP (t =P x) is left pf then cast Us pf v
        else sel t f.
Proof. by rewrite sel_fin. Qed.

Lemma sel_spliceE t f v : sel t (splice f v) = v. 
Proof. by rewrite sel_fin; case: eqP=>//= pf; rewrite eqd. Qed.

Lemma sel_spliceN t x f (w : Us x) :
        t <> x -> sel t (splice f w) = sel t f.
Proof. by move=>N; rewrite sel_fin; case: eqP. Qed.

Lemma splice_eta t f : splice f (sel t f) = f.
Proof.
apply/ffinP=>x; rewrite sel_fin; case: eqP=>//=.
by move/[dup]=>-> pf; rewrite eqd.
Qed.

End FinFun.

Arguments sel {T Us} tg f.
Arguments splice {T Us tg} f v.

(* notation for building finfuns *)
(* DEVCOMMENT *)
(*   copied from finfun to fix some bad spacing in formatting *)
(* /DEVCOMMENT *)

Notation "[ 'ffun' x : aT => E ]" := (finfun (fun x : aT => E))
  (at level 0, x name, format "[ 'ffun'  x  :  aT  =>  E ]") : fun_scope.

Notation "[ 'ffun' x => E ]" := (@finfun _ (fun=> _) (fun x => E))
  (at level 0, x name, format "[ 'ffun'  x  =>  E ]") : fun_scope.

Notation "['ffun' => E ]" := [ffun _ => E]
  (at level 0, format "['ffun' =>  E ]") : fun_scope.

Section IteratedNotation.
Variables (T : finType) (Us : T -> Type).

Variant dfun_delta : Type := DFunDelta t of Us t.

(* for iteration that starts with function ends with function *)
Definition dapp_fdelta df (f : forall t, Us t) z :=
  let: DFunDelta t v := df in 
    if decP (z =P t) is left pf then cast Us pf v 
    else f z.

(* for iteration that starts with finfun ends with function *)
Definition splice' df (f : {ffun forall t, Us t}) z := 
  dapp_fdelta df f z.

End IteratedNotation.

Delimit Scope fun_delta_scope with FUN_DELTA.
Arguments dapp_fdelta {T Us} df%_FUN_DELTA f.

Notation "y \\ x" := (@DFunDelta _ _ x y) (at level 1).

(* notation for simultaneous update of f with d1,..,dn *)
(* rewrite by sel_fin peels all layers *)
Notation "[ 'ext' f 'with' d1 , .. , dn ]" :=
  (finfun (
     dapp_fdelta d1%_FUN_DELTA .. (dapp_fdelta dn%_FUN_DELTA f) ..))
  (at level 0, format
  "'[hv' [ '[' 'ext' '/ '  f ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'"
  ) : fun_scope.

(* notation for iterated update of f with d1, then d2, ... *)
(* rewrite by sel_fin peels top layer only *)
Notation "[ 'splice' F 'with' d1 , .. , dn ]" :=
  (finfun (splice'
     d1%_FUN_DELTA .. (finfun (splice' dn%_FUN_DELTA (finfun F))) ..))
  (at level 0, format
  "'[hv' [ '[' 'splice' '/ '  F ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'"
  ) : fun_scope.

Section TestingNotation.
Variables (T : finType) (Us : T -> Type).
Variables (f : {dffun forall t, Us t}) (t1 t2 : T) (v1 : Us t1) (v2 : Us t2).

(* we have three different options in displaying splices *)
(* splice, [splice], and [ext] *)
Lemma test :
  [/\ sel t2 [splice f with v1 \\ t1, v2 \\ t2] = v2,
      sel t2 (splice (splice f v1) v2) = v2,
      sel t2 [ext f with v1 \\ t1, v2 \\ t2] = v2 &
(* and we can use underscores to elide some info *)
      sel t2 [ext f with v1 \\ _, v2 \\ _] = v2].   
Abort.
End TestingNotation.

(* mapping over simply-typed finite functions *)

Section FinFunMap.
Variables (T : finType) (A B : Type).
Implicit Types (f : A -> B) (x : {ffun T -> A}).

Definition fmap f x := [ffun tg => f (sel tg x)].
               
Lemma sel_fmap f x tg : sel tg (fmap f x) = f (sel tg x).
Proof. exact: sel_fin. Qed.

Lemma fmap_splice f x tg (v : A) :
        fmap f (splice (tg:=tg) x v) = splice (tg:=tg) (fmap f x) (f v).
Proof.
apply/ffinP=>t; rewrite !sel_fin; case: eqP=>//= ?; subst t.
by rewrite !eqc.
Qed.

End FinFunMap.

(* surgery on tuples and finfuns *)

Section OnthCodom.
Variable A : Type.

Lemma onth_tnth {n} (s : n.-tuple A) (i : 'I_n) : 
        onth s i = Some (tnth s i).
Proof.
elim: n s i =>[|n IH] s i; first by case: i.
case/tupleP: s=>/=x s; case: (unliftP ord0 i)=>[j|]-> /=.
- by rewrite tnthS.
by rewrite tnth0.
Qed.

Lemma onth_codom {n} (i : 'I_n) (f: {ffun 'I_n -> A}) : 
        onth (fgraph f) i = Some (f i).
Proof.
pose i' := cast_ord (esym (card_ord n)) i.
move: (@tnth_fgraph _ _ f i'); rewrite (enum_val_ord) {2}/i' cast_ordKV=><-.
by rewrite (onth_tnth (fgraph f) i').
Qed.

End OnthCodom.

(* ffun and permutation *)
Section PermFfun.
Variables (I : finType) (A : Type).

Definition pffun (p : {perm I}) (f : {ffun I -> A}) :=
  [ffun i => f (p i)].

Lemma pffunE1 (f : {ffun I -> A}) : pffun 1%g f = f.
Proof. by apply/ffunP=>i; rewrite !ffunE permE. Qed.

Lemma pffunEM (p p' : {perm I}) (f : {ffun I -> A}) :
  pffun (p * p') f = pffun p (pffun p' f).
Proof. by apply/ffunP => i; rewrite !ffunE permM. Qed.

End PermFfun.


(* Tagging *)

Notation Tag := (@existT _ _).

Lemma Tag_inj T Us (t1 t2 : T) i1 i2 : 
        Tag t1 i1 = Tag t2 i2 -> 
        t1 = t2 /\ jmeq Us i1 i2.
Proof. by case=>?; subst t2=>/inj_pair2 ->. Qed.
Arguments Tag_inj {T Us t1 t2 i1 i2}.

(* tagged union of equality types is equality type *)

Section TaggedEq.
Variables (T : eqType) (Us : T -> eqType).

Definition tag_eq : sigT Us -> sigT Us -> bool :=
  fun '(Tag tx opx) '(Tag ty opy) =>
    if decP (tx =P ty) is left pf then opx == cast Us pf opy
    else false.

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
case=>tx opx [ty opy] /=; case: (tx =P ty)=>pf; last first. 
- by constructor; case=>/pf.
subst ty; rewrite /= eqc; case: eqP=>pf; constructor; 
by [rewrite pf|case=>/inj_pair2/pf].
Qed.

HB.instance Definition _ := hasDecEq.Build (sigT Us) tag_eqP.
End TaggedEq.

