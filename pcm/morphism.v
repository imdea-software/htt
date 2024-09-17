(*
Copyright 2017 IMDEA Software Institute
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

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype fintype finfun.
From pcm Require Import options pred axioms prelude.
From pcm Require Import pcm.

(*****************)
(*****************)
(* PCM Morphisms *)
(*****************)
(*****************)

(* Orthogonality relations (in the POPL21 paper called separating relations) *)
Definition orth_axiom (U : pcm) (orth : rel U) :=
  [/\ (* unit is separated from unit *)
      orth Unit Unit,
      (* sep is commutative *)
      forall x y, orth x y = orth y x,
      (* sep implies validity *)
      forall x y, orth x y -> valid (x \+ y),
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall x y, orth x y -> orth x Unit &
      (* associativity *)
      forall x y z, orth x y -> orth (x \+ y) z -> 
        orth y z && orth x (y \+ z)].

(* Here, by separating relation we take a somewhat different definition *)
Definition seprel_axiom (U : pcm) (sep : rel U) :=
  [/\ (* unit is separated from unit *)
      sep Unit Unit,
      (* sep is commutative *)
      (* the validity pre is necessary to get equivalence with orth *)
      (* will it be bothersome in practice? *)
      forall x y, valid (x \+ y) -> sep x y = sep y x,
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall x y, valid (x \+ y) -> sep x y -> sep x Unit &
      (* associativity *)
      forall x y z, valid (x \+ y \+ z) ->
         sep x y -> sep (x \+ y) z -> sep y z && sep x (y \+ z)].

(* The two definitions differ in that seprel elide the validity requirement. *)
(* This is pragmatic distinction, because in practice we often have *)
(* the validity in context so we don't have to bother proving it. *)
(* Hence, given a separating relation R *)
(* we say that x \orth_R y iff valid (x \+ y) and R x y *)
(* Similarly, when R is the sep relation of a morphism f *)
(* we will write x \orth_f y iff valid (x \+ y) and sep f x y *)
Lemma orth_sep (U : pcm) (sep : rel U) :
        seprel_axiom sep <-> 
        orth_axiom (fun x y => valid (x \+ y) && sep x y).
Proof.
split.
- case=>H1 H2 H3 H4; split=>[|x y|x y|x y|x y z].
  - by rewrite unitL valid_unit H1.
  - by apply/andP/andP; case=> V; rewrite H2 (validE2 V).
  - by case/andP.
  - by case/andP=> V S; rewrite unitR (H3 x y) ?(validE2 V).
  case/andP=>_ S1 /andP [V2 S2].
  by rewrite !(andX (H4 _ _ _ V2 S1 S2)) !(validLE3 V2).
case=>H1 H2 H3 H4 H5; split=>[|x y V|x y V S|x y z V H S].
- by case/andP: H1.
- by move: (H2 x y); rewrite !(validE2 V).
- by rewrite (andX (H4 x y _)) // V S.
by move: (@H5 x y z); rewrite !(validLE3 V) H S => /(_ erefl erefl).
Qed.

(* seprel equality *)

(* because we have stripped sperels of the requirement *)
(* that valid (x \+ y), we have to put it back before we can prove *)
(* that cinv equals the equalizer between the given morphisms *)
Definition seprel_eq (U : pcm) (D1 D2 : rel U) :=
  forall x y, valid (x \+ y) -> D1 x y = D2 x y.

Notation "D1 =s D2" := (seprel_eq D1 D2) (at level 30).

Lemma sepEQ (U : pcm) (D1 D2 : rel U) :
        D1 =s D2 <->
        (fun x y => valid (x \+ y) && D1 x y) =2
        (fun x y => valid (x \+ y) && D2 x y).
Proof.
split; first by move=>S=>x y; case: (valid (x \+ y)) (S x y)=>// ->.
by move=>S x y V; move: (S x y); rewrite V.
Qed.

Lemma orthXEQ (U : pcm) (D1 D2 : rel U) :
        D1 =2 D2 -> 
        orth_axiom D1 <-> orth_axiom D2.
Proof.
move=>H; split; case=>H1 H2 H3 H4 H5.
- by split=>[|x y|x y|x y|x y z]; rewrite -!H;
     [apply: H1 | apply: H2 | apply: H3 | apply: H4 | apply: H5].
by split=>[|x y|x y|x y|x y z]; rewrite !H;
   [apply: H1 | apply: H2 | apply: H3 | apply: H4 | apply: H5].
Qed.

Lemma sepXEQ (U : pcm) (D1 D2 : rel U) :
        D1 =s D2 -> 
        seprel_axiom D1 <-> seprel_axiom D2.
Proof. by move/sepEQ=>H; rewrite !orth_sep; apply: orthXEQ. Qed.

HB.mixin Record isSeprel (U : pcm) (sep : rel U) := {
  seprel_subproof : seprel_axiom sep}.

#[short(type="seprel")]
HB.structure Definition Seprel (U : pcm) := {sep of isSeprel U sep}.

Section Repack.
Variables (U : pcm) (sep : seprel U).

Lemma sep00 : sep Unit Unit.
Proof. by case: (@seprel_subproof U sep). Qed.

Lemma sepC x y : 
        valid (x \+ y) -> 
        sep x y = sep y x.
Proof. by case: (@seprel_subproof U sep)=>_ H _ _; apply: H. Qed.

Lemma sepx0 x y : 
        valid (x \+ y) -> 
        sep x y -> 
        sep x Unit.
Proof. by case: (@seprel_subproof U sep)=>_ _ H _; apply: H. Qed.

(* The order of the rewrite rules in the conclusion is important for
   backwards reasoning: [sep x (y \+ z)] is more specific than [sep y z] and
   hence [rewrite] should be able to do its work;
   had we chosen to put [sep y z] first, [rewrite] would fail because of
   the indefinite pattern *)
Lemma sepAx x y z :
        valid (x \+ y \+ z) ->
        sep x y -> 
        sep (x \+ y) z -> 
        sep x (y \+ z) * sep y z.
Proof.
case: (@seprel_subproof U sep)=>_ _ _ H V R1 R2.
by rewrite !(andX (H _ _ _ V R1 R2)).
Qed.

(* derived lemmas *)

Lemma sep0x x y : 
        valid (x \+ y) -> 
        sep x y -> 
        sep Unit y.
Proof.
rewrite joinC=>V; rewrite -!(@sepC y) ?unitR ?(validE2 V) //.
by apply: sepx0.
Qed.

Lemma sep0E x y : 
        valid (x \+ y) -> 
        sep x y -> 
        sep x Unit * sep y Unit.
Proof.
by move=>V S; rewrite (sepx0 V S) sepC ?unitR ?(validE2 V) // (sep0x V S).
Qed.

(* This is a helper lemma -- in most cases you may want to use
   sepAxx or sepxxA instead *)
Lemma sepAx23_helper x y z :
        valid (x \+ y \+ z) ->
        sep x y -> 
        sep (x \+ y) z ->
        ((sep x z * sep z x) * (sep y z * sep z y)) *
        ((sep x (y \+ z) * sep x (z \+ y)) *
         (sep y (x \+ z) * sep y (z \+ x))).
Proof.
move=>V S1 S2.
rewrite !(@sepC z) ?(validLE3 V) // !(joinC z) !(sepAx V S1 S2).
rewrite sepC ?(validLE3 V) // in S1; rewrite (joinC x) in V S2.
by rewrite !(sepAx V S1 S2).
Qed.

(* This is useful for backward reasoning, because we don't want to
   depend on the exact permutation of x, y, z the rewrite rules (see below)
   will choose *)
Lemma sepxA x y z :
        valid (x \+ (y \+ z)) ->
        sep y z -> 
        sep x (y \+ z) -> 
        sep (x \+ y) z * sep x y.
Proof.
move=>V S1; rewrite sepC // => S2.
rewrite (@sepC _ z) -?joinA //; rewrite joinC in V.
by rewrite (@sepC _ y) ?(validLE3 V) // !(sepAx23_helper V S1 S2).
Qed.

(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma sepAxx x y z :
        valid (x \+ y \+ z) ->
        sep x y -> 
        sep (x \+ y) z ->
        (((sep x (y \+ z) * sep x (z \+ y)) *
          (sep y (x \+ z) * sep y (z \+ x))) *
         ((sep z (x \+ y) * sep z (y \+ x)) *
          (sep (y \+ z) x * sep (z \+ y) x))) *
        (((sep (x \+ z) y * sep (z \+ x) y) *
          (sep (x \+ y) z * sep (y \+ x) z)) *
         (((sep x y * sep y x) *
           (sep x z * sep z x)))) *
        (sep y z * sep z y).
Proof.
move=>V S1 S2; rewrite S1 S2 !(sepAx23_helper V S1 S2).
rewrite -(sepC (validL V)) S1.
rewrite (joinC y) -sepC // S2;
rewrite -(joinC y) sepC 1?joinC ?joinA // (sepAx23_helper V S1 S2).
by rewrite -(joinC x) sepC 1?joinAC // (sepAx23_helper V S1 S2).
Qed.

(* same results, flipped hypotheses *)
(* nested pairs are a workaround for https://github.com/coq/coq/issues/8304 *)
Lemma sepxxA x y z :
        valid (x \+ (y \+ z)) ->
        sep y z -> 
        sep x (y \+ z) ->
        (((sep x (y \+ z) * sep x (z \+ y)) *
          (sep y (x \+ z) * sep y (z \+ x))) *
         ((sep z (x \+ y) * sep z (y \+ x)) *
          (sep (y \+ z) x * sep (z \+ y) x))) *
        (((sep (x \+ z) y * sep (z \+ x) y) *
          (sep (x \+ y) z * sep (y \+ x) z)) *
         (((sep x y * sep y x) *
           (sep x z * sep z x)))) *
        (sep y z * sep z y).
Proof.
rewrite joinA=> V; rewrite {1}(@sepC x) ?(validLE3 V) // => S1 S2.
by apply: (sepAxx V); rewrite (joinC x) joinAC in V; rewrite !(sepAxx V S1 S2).
Qed.

Lemma sepU0 x y : 
        valid (x \+ y) -> 
        sep x y -> 
        sep (x \+ y) Unit.
Proof.
move=>V S1; move/(sepx0 V): S1 (S1)=>S1 S2.
rewrite -[x]unitR in V S2.
by rewrite sepC ?(sepAxx V S1 S2) // joinAC.
Qed.

Lemma sep0U x y : 
        valid (x \+ y) -> 
        sep x y -> 
        sep Unit (x \+ y).
Proof. by move=>V S; rewrite sepC ?unitL //; apply: sepU0. Qed.

End Repack.


(***********************************)
(* Sep relations and constructions *)
(***********************************)

(* always-true relation *)

Definition relT {U} : rel U := fun x y => true.

Lemma relT_is_seprel {U : pcm} : seprel_axiom (@relT U). Proof. by []. Qed.
HB.instance Definition _ U := isSeprel.Build U relT relT_is_seprel.


(* always-unit relation *)
(* always-false relation is not seprel, because we need sep0 Unit Unit *)
(* i.e., sepU is really the smallest seprel we can have *)

Definition sepU {U : pcm} : rel U := fun x y => unitb x && unitb y.

Section SepU.
Variable U : pcm.

Lemma sepU_is_seprel : seprel_axiom (@sepU U). 
Proof. 
rewrite /sepU; split=>[|x y|x y|x y z].
- by rewrite pcmE.
- by rewrite andbC.
- by move=>V /andP [->]; rewrite pcmE.
move=>V /andP [/unitbP -> /unitbP ->] /andP [_ /unitbP ->].
by rewrite unitL !pcmE.
Qed.

HB.instance Definition _ := isSeprel.Build U sepU sepU_is_seprel.
End SepU.


(************************************)
(* Conjunction of seprels is seprel *)
(************************************)

(* first conjunction of plain rels *)
Definition relI U (X Y : rel U) (x y : U) := X x y && Y x y.
(* and iterated variants *)
Definition rel3I U (X Y Z : rel U) (x y : U) := 
  [&& X x y, Y x y & Z x y].
Definition rel4I U (X Y Z W : rel U) (x y : U) := 
  [&& X x y, Y x y, Z x y & W x y].

Arguments relI {U} X Y x y /. 
Arguments rel3I {U} X Y Z x y /.
Arguments rel4I {U} X Y Z W x y /.

Section SepI.
Variables (U : pcm) (X Y : seprel U).

Lemma relI_is_seprel : seprel_axiom (relI X Y).
Proof.
split=>[|x y|x y|x y z] /=.
- by rewrite !sep00.
- by move=>V; rewrite !(sepC _ V).
- by move=>V /andP []; do ![move/(sepx0 V) ->].
move=>V /andP [X1 Y1] /andP [X2 Y2].
by rewrite !(sepAxx V X1 X2, sepAxx V Y1 Y2).
Qed.

HB.instance Definition _ := isSeprel.Build U (relI X Y) relI_is_seprel.
End SepI.

(* 3-way conjunction *)
Section Sep3I.
Variables (U : pcm) (X Y Z : seprel U).

Lemma rel3I_is_seprel : seprel_axiom (rel3I X Y Z).
Proof.
split=>[|x y|x y|x y z] /=.
- by rewrite !sep00.
- by move=>V; rewrite !(sepC _ V).
- by move=>V /and3P []; do ![move/(sepx0 V) ->]. 
move=>V /and3P [X1 Y1 Z1] /and3P [X2 Y2 Z2].
by rewrite !(sepAxx V X1 X2, sepAxx V Y1 Y2, sepAxx V Z1 Z2).
Qed.

HB.instance Definition _ := isSeprel.Build U (rel3I X Y Z) rel3I_is_seprel.
End Sep3I.

(* 4-way conjunction *)
Section Sep4I.
Variables (U : pcm) (X Y Z W : seprel U).

Lemma rel4I_is_seprel : seprel_axiom (rel4I X Y Z W).
Proof.
split=>[|x y|x y|x y z] /=.
- by rewrite !sep00.
- by move=>V; rewrite !(sepC _ V). 
- by move=>V /and4P []; do ![move/(sepx0 V) ->].
move=>V /and4P [X1 Y1 Z1 W1] /and4P [X2 Y2 Z2 W2].
by rewrite !(sepAxx V X1 X2, sepAxx V Y1 Y2, sepAxx V Z1 Z2, sepAxx V W1 W2).
Qed.

HB.instance Definition _ := isSeprel.Build U (rel4I X Y Z W) rel4I_is_seprel.
End Sep4I.

(************************************)
(* projections and pairwise product *)
(************************************)

Definition rel_fst U V (X : rel U) (x y : U * V) := X x.1 y.1.
Arguments rel_fst {U V} X x y /.
Definition rel_snd U V (Y : rel V) (x y : U * V) := Y x.2 y.2.
Arguments rel_snd {U V} Y x y /.

Section SepFst.
Variables (U V : pcm) (X : seprel U).
Lemma relfst_is_seprel : seprel_axiom (@rel_fst U V X).
Proof.
split=>[|x y|x y|x y z] //=.
- by rewrite !sep00.
- by case/andP=>V1 _; rewrite sepC.
- by case/andP=>V1 _ /(sepx0 V1).
by case/andP=>V1 V2 X1 Y1; rewrite !(sepAxx V1 X1 Y1).
Qed.
HB.instance Definition _ := 
  isSeprel.Build (U * V)%type (rel_fst X) relfst_is_seprel.
End SepFst.

Section SepSnd.
Variables (U V : pcm) (Y : seprel V).
Lemma relsnd_is_seprel : seprel_axiom (@rel_snd U V Y).
Proof.
split=>[|x y|x y|x y z] //=.
- by rewrite !sep00.
- by case/andP=>_ V2; rewrite sepC.
- by case/andP=>_ V2 /(sepx0 V2).
by case/andP=>V1 V2 X2 Y2; rewrite !(sepAxx V2 X2 Y2).
Qed.
HB.instance Definition _ := 
  isSeprel.Build (U * V)%type (rel_snd Y) relsnd_is_seprel.
End SepSnd.

Definition rel_prod U V (X : rel U) (Y : rel V) :=
  relI (rel_fst X) (rel_snd Y).
Arguments rel_prod {U V} X Y /.

HB.instance Definition _ (U V : pcm) (X : seprel U) (Y : seprel V) := 
  Seprel.copy (rel_prod X Y) (rel_prod X Y).

(**********************)
(**********************)
(* Classes of seprels *)
(**********************)
(**********************)

(* Non-symmetric seprels *)

(* Often times, we build a seprel out of a non-symmetric relation *)
(* by taking the symmetric closure of the relation explicitly. *)
(* This is such a common approach, that its useful *)
(* to introduce a class of primitive non-symmetric seprels that *)
(* are made full seprels by closing up. *)

Definition nseprel_axiom (U : pcm) (nsep : rel U) :=
  [/\ (* unit is separated from unit *)
      nsep Unit Unit,
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall x y, valid (x \+ y) -> nsep x y -> nsep x Unit,
      (* if the first arguments is Unit, then nsep trivially holds *)
      forall y, valid y -> nsep Unit y,
      (* associativity 1 *)
      forall x y z, valid (x \+ y \+ z) ->
         nsep x y -> nsep (x \+ y) z -> nsep x (y \+ z) &
      (* associativity 2 *)
      forall x y z, valid (x \+ y \+ z) ->
         nsep x (y \+ z) -> nsep y (x \+ z) -> nsep x y /\ nsep (x \+ y) z].

Lemma orth_nsep (U : pcm) (nsep : rel U) :
        nseprel_axiom nsep -> 
        seprel_axiom (fun x y => nsep x y && nsep y x).
Proof.
case=>H1 H2 H3 H4 H5; split=>[|x y V|x y V|x y z V].
- by rewrite H1.
- by rewrite andbC.
- by case/andP=>/(H2 _ _ V) -> _; rewrite (H3 _ (validL V)).
case/andP=>X1 X2 /andP [X3 X4].
move: (H4 x y z V X1 X3)=>X5; rewrite X5 /=.
rewrite joinC in X3.
move: (H4 y x z); rewrite (validLE3 V)=>/(_ erefl X2 X3) X6.
rewrite joinC in X4; rewrite joinC in X6.
move: (H5 y z x); rewrite (validLE3 V)=>/(_ erefl X6 X4) [->->] /=.
by move: (H5 z y x); rewrite (validLE3 V)=>/(_ erefl X4 X6) [] ->.
Qed.

(* Guarded non-symmetric seprels *)

(* Further optimization, if the nsep has the form forall k, P k x -> Q k x y *)
(* for some P and Q *)

Section GuardedSeprels.
Variable (U : pcm) (X : Type) (P : X -> U -> Prop) (Q : X -> U -> U -> Prop).
Variable (nsep : rel U).

Hypothesis pf1 : forall x y, reflect (forall k, P k x -> Q k x y) (nsep x y).

Definition gseprel_axiom :=
  [/\ (* P is disjunctive *)
      forall k x y, valid (x \+ y) -> P k (x \+ y) <-> P k x \/ P k y,
      (* unit is separated from unit *)
      forall k, P k Unit -> Q k Unit Unit,
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall k x y, valid (x \+ y) -> P k x -> Q k x y -> Q k x Unit,
      (* if the first argument is Unit, then nsep trivially holds *)
      forall k y, valid y -> P k Unit -> Q k Unit y,
      (* associativity 1 *)
      forall k x y z, valid (x \+ y \+ z) ->
        P k x -> Q k x y -> Q k (x \+ y) z -> Q k x (y \+ z) &
      (* associativity 2 *)
      forall k x y z, valid (x \+ y \+ z) ->
        P k x -> Q k x (y \+ z) -> Q k x y /\ Q k (x \+ y) z].

Lemma orth_gsep :
        gseprel_axiom -> 
        seprel_axiom (fun x y => nsep x y && nsep y x).
Proof.
case=>H1 H2 H3 H4 H5 H6; apply: orth_nsep.
split=>[|x y V|y V|x y z V|x y z V].
- by apply/pf1.
- by move/pf1=>H; apply/pf1=>k /[dup] Y /H; apply: H3 V Y.
- by apply/pf1=>x; apply: H4.
- move/pf1=>X1 /pf1 X2; apply/pf1=>k H.
  apply: H5=>//; first by apply: X1 H.
  by apply: X2; apply/H1; [rewrite (validLE3 V)|left].
move/pf1=>X1 /pf1 X2; split; apply/pf1=>k H.
- by case: (H6 k x y z V H (X1 _ H)).
case/H1: H; first by rewrite (validLE3 V).
- by move=>H; case: (H6 k x y z V H (X1 _ H)).
move=>H; rewrite joinC.
case: (H6 k y x z)=>//; first by rewrite (validLE3 V).
by apply: X2 H.
Qed.

End GuardedSeprels.

(* Further optimization *)
(* Most of the time, the guard is not only disjunctive, but *)
(* exclusively disjunctive. This allows to weaken the conditions. *)
(* We have to prove a couple of additional side-conditions however *)
(* so we'll see how useful this is. *)
(* I wasn't able to find a simpler formulation. *)

Section ExclusiveGuardedSeprels.
Variable (U : pcm) (X : Type) (P : X -> U -> Prop) (Q : X -> U -> U -> Prop).
Variable (nsep : rel U).

Hypothesis pf1 : forall x y, reflect (forall k, P k x -> Q k x y) (nsep x y).

Definition xgseprel_axiom :=
  [/\ (* P is disjunctive *)
      forall k x y, valid (x \+ y) -> P k (x \+ y) <-> P k x \/ P k y,
      (* P is exclusive *)
      forall k1 k2 x y, valid (x \+ y) -> P k1 x -> P k2 y -> k1 <> k2,
      forall k1 k2 x y z, valid (x \+ y \+ z) ->
        P k1 x -> Q k1 x y -> Q k2 (x \+ y) z -> k1 = k2,
      forall k1 k2 x y z, valid (x \+ y \+ z) ->
        P k1 x -> Q k1 x (y \+ z) -> P k2 y-> Q k2 y (x \+ z) -> k1 = k2,
      (* unit is separated from unit *)
      forall k, P k Unit -> Q k Unit Unit,
      (* is x is in the domain (i.e., x is considered) *)
      (* then it is separate from at least Unit *)
      forall k x y, valid (x \+ y) -> P k x -> Q k x y -> Q k x Unit,
      (* if the first argument is Unit, then nsep trivially holds *)
      forall k y, valid y -> P k Unit -> Q k Unit y,
      (* associativity 1 *)
      forall k x y z, valid (x \+ y \+ z) ->
        P k x -> (forall k', ~ P k' y) ->
        Q k x y -> Q k (x \+ y) z -> Q k x (y \+ z) &
      (* associativity 2 *)
      forall k x y z, valid (x \+ y \+ z) ->
        P k x -> (forall k', ~ P k' y) ->
        Q k x (y \+ z) -> Q k x y /\ Q k (x \+ y) z].

Lemma xorth_gsep :
        xgseprel_axiom -> 
        seprel_axiom (fun x y => nsep x y && nsep y x).
Proof.
case=>H1 Xp Xq1 Xq2 H2 H3 H4 H5 H6; apply: orth_nsep.
split=>[|x y V|y V|x y z V|x y z V].
- by apply/pf1.
- by move/pf1=>H; apply/pf1=>k /[dup] Y /H; apply: H3 V Y.
- by apply/pf1=>x; apply: H4.
- have V' : valid (x \+ y) by rewrite (validLE3 V).
  move/pf1=>X1 /pf1 X2; apply/pf1=>k Hx; apply: (H5)=>//; last first.
  - by apply: X2; apply/H1=>//; left.
  - by apply: X1.
  move=>k' Hy; apply: Xp (V') (Hx) (Hy) _.
  have Hxy : P k' (x \+ y) by rewrite H1 //; right.
  by apply: Xq1 V (Hx) (X1 _ Hx) (X2 _ Hxy).
have V' : valid (x \+ y) by rewrite (validLE3 V).
move/pf1=>X1 /pf1 X2; split; apply/pf1=>k Hx.
- case: (H6 k x y z V Hx)=>//; last by apply: X1.
  move=>k' Hy; apply: Xp V' (Hx) (Hy) _.
  by apply: Xq2 (X1 _ Hx) _ (X2 _ Hy).
case/H1: Hx; first by rewrite (validLE3 V).
- move=>Hx; case: (H6 k x y z V Hx)=>//; last by apply: X1.
  by move=>k' Hy; apply: Xp V' (Hx) (Hy) _; apply: Xq2 (X1 _ Hx) _ (X2 _ Hy).
move=>Hy; rewrite joinC.
case: (H6 k y x z)=>//; first by rewrite (validLE3 V).
- by move=>k' Hx; apply: Xp V' (Hx) (Hy) _; apply: Xq2 (X1 _ Hx) _ (X2 _ Hy).
by apply: X2.
Qed.

End ExclusiveGuardedSeprels.


(*****************)
(*****************)
(* PCM morphisms *)
(*****************)
(*****************)

(* morphism comes with a seprel on which it is valid *)

Definition pcm_morph_axiom (U V : pcm) (sep : rel U) (f : U -> V) :=
  [/\ (* f preserves unit *)
      f Unit = Unit &
      (* f is defined on the domain and preserves joins on the domain *)
      forall x y, valid (x \+ y) -> sep x y ->
                  valid (f x \+ f y) /\ f (x \+ y) = f x \+ f y].

HB.mixin Record isPCM_morphism (U V : pcm) (f : U -> V) := {
  sep_op : seprel U; 
  pcm_morph_subproof : pcm_morph_axiom sep_op f}.

#[short(type=pcm_morph)]  
HB.structure Definition PCM_morphism (U V : pcm) := 
  {f of isPCM_morphism U V f}.

Arguments sep_op {U V} _ /.
Arguments pcm_morph_subproof {U V}.

(* When sep_op is applied to function f, the system infers *)
(* the pcm_morph structure F of f, as intended. *)
(* However, it then proceeds to display sep_op F instead of sep_op f, *)
(* which is often unreadable, as F is typically large. *)
(* The following arranges that f is printed instead of F. *)

(* There are two options that differ in issues orthogonal to f/F. *)
(* 1. sepx is declared seprel *)
(* 2. sepx is declared rel, with canonical seprel attached *)
(* Option 1 automatically simplifies nested sepx's of composed functions. *)
(* Option 2 makes it easier to attach canonical structures to sepx, *)
(* but simplification requires explicit and often iterated unfolding *)
(* e.g. rewrite /sepx/=/sepx/=/sepx/=. *)
(* Here, choosing (2); if iterated unfolding of some seprel is *)
(* frequently needed, it should be exported as a lemma. *)

(*
(* option 1 *)
Definition sepx U V (f : pcm_morph U V) 
  of phantom (U -> V) f := sep_op f.
Notation sep f := (sepx (Phantom (_ -> _) f)). 
*)

(* option 2 *)
Definition sepx U V (f : pcm_morph U V) 
  of phantom (U -> V) f : rel U := sep_op f.
Notation sep f := (sepx (Phantom (_ -> _) f)). 
HB.instance Definition _ U V (f : pcm_morph U V) := 
  Seprel.on (sep f). 

(* we can similarly get uniform name for the structure itself *)
(* but we won't use this *)
Definition morphx (U V : pcm) (f : pcm_morph U V) 
  of phantom (U -> V) f := f.
Notation morph f := (morphx (Phantom (_ -> _) f)).


Section Laws.
Variables (U V : pcm) (f : pcm_morph U V).

Lemma pfunit : f Unit = Unit.
Proof. by case: (pcm_morph_subproof f). Qed.

Lemma pfjoinV (x y : U) :
        valid (x \+ y) -> 
        sep f x y ->
        valid (f x \+ f y) /\ f (x \+ y) = f x \+ f y.    
Proof. by case: (pcm_morph_subproof f)=>_; apply. Qed.

Lemma pfV2 x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        valid (f x \+ f y).
Proof. by move=>H S; case: (pfjoinV H S). Qed.

Lemma pfjoin x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        f (x \+ y) = f x \+ f y.
Proof. by move=>H S; case: (pfjoinV H S). Qed.

Lemma joinpf x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        f x \+ f y = f (x \+ y).
Proof. by move=>*; rewrite pfjoin. Qed.

Lemma pfV x : 
        valid x -> 
        sep f x Unit -> 
        valid (f x). 
Proof. by rewrite -{1 3}[x]unitR=>W S; rewrite pfjoin // pfV2. Qed.

Lemma pfV3 x y z : 
        valid (x \+ y \+ z) -> 
        sep f x y -> 
        sep f (x \+ y) z -> 
        valid (f x \+ f y \+ f z).
Proof. by move=>W D1 D2; rewrite -pfjoin ?(validL W) // pfV2. Qed.

Lemma pfL (x y z : U) : 
        valid (x \+ z) -> 
        valid (y \+ z) ->
        sep f x z -> 
        sep f y z ->
        f y = f x -> 
        f (y \+ z) = f (x \+ z).
Proof. by move=>V1 V2 S1 S2 E; rewrite !pfjoin // E. Qed.

Lemma pfR (x y z : U) : 
        valid (z \+ x) -> 
        valid (z \+ y) ->
        sep f z x -> 
        sep f z y ->
        f y = f x -> 
        f (z \+ y) = f (z \+ x).
Proof. by move=>V1 V2 S1 S2 E; rewrite !pfjoin // E. Qed.

Lemma pfUnE (x1 y1 x2 y2 : U) :
        valid (x1 \+ y1) ->
        valid (x2 \+ y2) ->
        sep f x1 y1 ->
        sep f x2 y2 ->
        f x2 = f x1 ->
        f y2 = f y1 ->
        f (x2 \+ y2) = f (x1 \+ y1).
Proof.
move=>V1 V2 S1 S2 E1 E2.
by rewrite !pfjoin // E1 E2.
Qed.

Lemma pfunitL x : f Unit \+ x = x.
Proof. by rewrite pfunit unitL. Qed.

Lemma pfunitR x : x \+ f Unit = x.
Proof. by rewrite pfunit unitR. Qed.

End Laws.

Arguments pfunit {U V}.
Arguments pfjoinV {U V}.
Arguments pfV2 {U V}.
Arguments pfjoin {U V}.
Arguments joinpf {U V}.
Arguments pfV {U V}.
Arguments pfV3 {U V}.
Arguments pfL {U V} f {x y}.
Arguments pfR {U V} f {x y}.
Arguments pfunitL {U V}.
Arguments pfunitR {U V}.

(*********************)
(* Morphism equality *)
(*********************)

(* morphisms are equal iff equal as functions and have equal seprels *)

Definition pcm_morph_eq (U V : pcm) (f g : pcm_morph U V) := 
  f =1 g /\ sep f =s sep g.

Notation "f =m g" := (pcm_morph_eq f g) (at level 55).

Lemma pcm_morph_eq_refl {U V} : Reflexive (@pcm_morph_eq U V). 
Proof. by []. Qed.

Lemma pcm_morph_eq_sym {U V} : Symmetric (@pcm_morph_eq U V). 
Proof.
by apply/sym_iff_pre_sym=>f1 f2 [H1 H2]; split=>// x y W; rewrite H2.
Qed.

Lemma pcm_morph_eq_trans {U V} : Transitive (@pcm_morph_eq U V).
Proof.
move=>f2 f1 f3 [H12 S12][H23 S23]; split=>[x|x y W].
- by rewrite H12.
by rewrite S12 // S23.
Qed.

(***************************************)
(* Operations on morphisms and seprels *)
(***************************************)

(* morphism preimage of seprel is seprel *)

Definition preimx (U V : pcm) (f : pcm_morph U V) 
  of phantom (U -> V) f : rel V -> rel U := 
  fun R x y => sep f x y && R (f x) (f y).
Notation preim f := (preimx (Phantom (_ -> _) f)). 
Arguments preimx {U V f} _ _ _ _ /.
  
Section Preim.
Variables (U V : pcm) (f : pcm_morph U V) (R : seprel V).

Lemma preim_is_seprel : seprel_axiom (preim f R).
Proof.
split=>[|x y|x y|x y z] /=. 
- by rewrite !pfunit !sep00.  
- move=>W; rewrite (sepC (sep f))=>//=; case H : (sep f y x)=>//. 
  by rewrite sepC // pfV2 // sepC.
- move=>H /andP [H1 H2].
  by rewrite !pfunit (sep0E H H1) (sep0E _ H2) // pfV2.
move=>W /andP [G1 F1] /andP [G2 F2].
rewrite pfjoin ?(validLE3 W) // in F2.
rewrite pfjoin ?(validLE3 W) ?(sepAxx W G1 G2) //=.
move: (pfV2 _ _ _ W G2); rewrite pfjoin ?(validLE3 W) // => W2.
by rewrite !(sepAxx W2 F1 F2).
Qed.

HB.instance Definition _ := isSeprel.Build U (preim f R) preim_is_seprel.
End Preim.

(* kernel of morphism is seprel *)

Definition kerx (U V : pcm) (f : pcm_morph U V) 
  of phantom (U -> V) f : rel U := 
  fun x y => sep f x y && sepU (f x) (f y).
Notation ker f := (kerx (Phantom (_ -> _) f)). 
HB.instance Definition _ U V (f : pcm_morph U V) := 
  isSeprel.Build U (ker f) (preim_is_seprel f _). 

(* restriction of morphism by seprel is morphism *)
(* restriction has tpcm range because it returns undef results *)
Section Restriction.
Variables (U : pcm) (V : tpcm).

Definition res (f : U -> V) (S : rel U) : U -> V := 
  fun x : U => if S x Unit then f x else undef.

Variables (f : pcm_morph U V) (S : seprel U).

Lemma res_is_morphism : pcm_morph_axiom (relI S (sep f)) (res f S).
Proof.
rewrite /res; split=>[|x y]; first by rewrite sep00 pfunit.
by move=>W /andP [X H]; rewrite !(sep0E W X) (sepU0 W X) pfjoin // pfV2.
Qed.

HB.instance Definition _ := isPCM_morphism.Build U V (res f S) res_is_morphism.
End Restriction.

(* equalizer of morphism is seprel *)

Definition eqlzx (U : pcm) (V : eqpcm) (f1 f2 : pcm_morph U V) 
  of phantom (U -> V) f1 & phantom (U -> V) f2 : rel U := 
  fun x y => [&& sep f1 x y, sep f2 x y, f1 x == f2 x & f1 y == f2 y].
Notation eqlz f1 f2 := (eqlzx (Phantom (_ -> _) f1) (Phantom (_ -> _) f2)). 

Section Equalizer.
Variables (U : pcm) (V : eqpcm) (f1 f2 : pcm_morph U V).

Lemma eqlz_is_seprel : seprel_axiom (eqlz f1 f2).
Proof.
rewrite /eqlzx; split=>[|x y W|x y W|x y z W].
- by rewrite !sep00 !pfunit eq_refl.
- by rewrite !andbA andbAC (sepC (sep f1)) // (sepC (sep f2)).
- by case/and4P=>V1 V2 -> _; rewrite (sepx0 W V1) (sepx0 W V2) !pfunit eq_refl.
case/and4P=>V1 V2 Ex Ey /and4P [W1 W2 _ Ez].
set j1 := (sepAxx W V1 W1); set j2 := (sepAxx W V2 W2).
by rewrite !pfjoin ?j1 ?j2 ?(validLE3 W) //= Ex (eqP Ey) (eqP Ez) !eq_refl.
Qed.

HB.instance Definition _ := isSeprel.Build U (eqlz f1 f2) eqlz_is_seprel.
End Equalizer.

(* join of two morphism is a morphism with an appropriate seprel *)

Definition join_relx (U V : pcm) (f1 f2 : pcm_morph U V) 
  of phantom (U -> V) f1 & phantom (U -> V) f2 : rel U := 
  fun x y => [&& sep f1 x y, sep f2 x y & 
                 valid ((f1 x \+ f2 x) \+ (f1 y \+ f2 y))].
Notation join_rel f1 f2 := 
  (join_relx (Phantom (_ -> _) f1) (Phantom (_ -> _) f2)).

Definition join_fun (U V : pcm) (f1 f2 : U -> V) : U -> V := 
  fun x => f1 x \+ f2 x.

Section JoinMorph.
Variables (U V : pcm) (f1 f2 : pcm_morph U V).

Lemma join_rel_is_seprel : seprel_axiom (join_rel f1 f2).
Proof.
rewrite /join_relx; split=>[|x y W|x y W|x y z W].
- by rewrite !sep00 ?unitL !pfunit ?unitL valid_unit.
- by rewrite (sepC (sep f1)) // (sepC (sep f2)) // (joinC (f1 x \+ f2 x)).
- case/and3P=>V1 V2; rewrite (sepx0 W V1) (sepx0 W V2) !pfunit // !unitR.
  by apply: validL.
case/and3P=>V1 V2 Wa /and3P [W1 W2].
set j1 := (sepAxx W V1 W1); set j2 := (sepAxx W V2 W2).
rewrite !pfjoin ?j1 ?j2 ?(validLE3 W) //=.
rewrite !(pull (f2 y)) !joinA !(pull (f1 y)) !joinA.
rewrite !(pull (f2 x)) !joinA  !(pull (f1 x)) -!joinA=>Wb.
by rewrite !(validRE3 Wb).
Qed.

HB.instance Definition _ := 
  isSeprel.Build U (join_rel f1 f2) join_rel_is_seprel.

Lemma join_fun_is_morph : 
        pcm_morph_axiom (join_rel f1 f2) (join_fun f1 f2).
Proof.
rewrite /join_fun; split=>[|x y]; first by rewrite !pfunit unitL.
move=>W /and3P [V1 V2]; rewrite !pfjoin // !joinA.
by rewrite !(pull (f2 x)) !joinA !(pull (f1 x)).
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build U V (join_fun f1 f2) join_fun_is_morph.
End JoinMorph.

(*************************)
(* Categorical morphisms *)
(*************************)

(* identity *)

Lemma id_is_morphism (U : pcm) : pcm_morph_axiom relT (@idfun U). 
Proof. by []. Qed.
HB.instance Definition _ (U : pcm) := 
  isPCM_morphism.Build U U idfun (id_is_morphism U).

(* composition *)

Section CompMorphism.
Variables U V W : pcm.
Variables (f : pcm_morph U V) (g : pcm_morph V W).
Lemma comp_is_morphism : pcm_morph_axiom (preim f (sep g)) (g \o f).
Proof.
split=>[|x y] /=; first by rewrite !pfunit.
by move=>D /andP [H1 H2]; rewrite !pfjoin // !pfV2.
Qed.
HB.instance Definition _ := 
  isPCM_morphism.Build U W (g \o f) comp_is_morphism.
End CompMorphism.


Section CategoricalLaws.
Variables (U V W X : pcm).
Variables (f : pcm_morph V U) (g : pcm_morph W V) (h : pcm_morph X W).

Lemma morph0L : f \o idfun =m f. 
Proof. by []. Qed.

Lemma morph0R : idfun \o f =m f. 
Proof. by split=>// x y; rewrite {1}/sepx /= andbT. Qed.

Lemma morphA : f \o (g \o h) =m (f \o g) \o h. 
Proof. by split=>//= x y H; rewrite /sepx/= andbA. Qed.
End CategoricalLaws.

(***********************)
(* Cartesian morphisms *)
(***********************)

(* always-unit function on valid elements *)
Section UnitFun.
Context {U : pcm} {V : tpcm}.

Definition unit_fun (x : U) : V := 
  if valid x then Unit else undef.

Lemma unitfun_is_pcm_morph : pcm_morph_axiom relT unit_fun.
Proof.
rewrite /unit_fun; split=>[|x y W _].
- by rewrite valid_unit. 
by rewrite W (validL W) (validR W) unitL.
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build U V 
    unit_fun unitfun_is_pcm_morph.
End UnitFun.

(* pairwise product of morphisms is a morphism *)
Section FProdMorph.
Variables U1 U2 V1 V2 : pcm.
Variables (f1 : pcm_morph U1 V1) (f2 : pcm_morph U2 V2).

Lemma fprod_is_morph : 
        pcm_morph_axiom (rel_prod (sep f1) (sep f2)) (f1 \* f2).
Proof.
rewrite /fprod; split=>[|x y]; first by rewrite !pfunit.
by case/andP=>/= W1 W2 /andP [H1 H2]; rewrite pcmE /= !pfV2 //= !pfjoin.
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build (U1 * U2)%type (V1 * V2)%type (f1 \* f2) fprod_is_morph.
End FProdMorph.

(* projections are morphisms *)
Section ProjMorph.
Variables U1 U2 : pcm.

Lemma fst_is_morph : pcm_morph_axiom relT (@fst U1 U2).
Proof. by split=>[|x y] // /andP []. Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build (U1 * U2)%type U1 fst fst_is_morph.

Lemma snd_is_morph : pcm_morph_axiom relT (@snd U1 U2).
Proof. by split=>[|x y] // /andP []. Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build (U1 * U2)%type U2 snd snd_is_morph.
End ProjMorph.

Section Proj3Morph.
Variables U1 U2 U3 : pcm.
Notation tp := (Prod3 U1 U2 U3).

Lemma proj31_morph_ax : pcm_morph_axiom relT (proj31 : tp -> _).
Proof. by split=>[|x y] // /and3P []. Qed.
Lemma proj32_morph_ax : pcm_morph_axiom relT (proj32 : tp -> _).
Proof. by split=>[|x y] // /and3P []. Qed.
Lemma proj33_morph_ax : pcm_morph_axiom relT (proj33 : tp -> _).
Proof. by split=>[|x y] // /and3P []. Qed.

HB.instance Definition _ := isPCM_morphism.Build tp U1 _ proj31_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U2 _ proj32_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U3 _ proj33_morph_ax.
End Proj3Morph.

Section Proj4Morph.
Variables U1 U2 U3 U4 : pcm.
Notation tp := (Prod4 U1 U2 U3 U4).

Lemma proj41_morph_ax : pcm_morph_axiom relT (proj41 : tp -> _).
Proof. by split=>[|x y] // /and4P []. Qed.
Lemma proj42_morph_ax : pcm_morph_axiom relT (proj42 : tp -> _).
Proof. by split=>[|x y] // /and4P []. Qed.
Lemma proj43_morph_ax : pcm_morph_axiom relT (proj43 : tp -> _).
Proof. by split=>[|x y] // /and4P []. Qed.
Lemma proj44_morph_ax : pcm_morph_axiom relT (proj44 : tp -> _).
Proof. by split=>[|x y] // /and4P []. Qed.

HB.instance Definition _ := isPCM_morphism.Build tp U1 _ proj41_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U2 _ proj42_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U3 _ proj43_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U4 _ proj44_morph_ax.
End Proj4Morph.

Section Proj5Morph.
Variables U1 U2 U3 U4 U5 : pcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).

Lemma proj51_morph_ax : pcm_morph_axiom relT (proj51 : tp -> _).
Proof. by split=>[|x y] // /and5P []. Qed.
Lemma proj52_morph_ax : pcm_morph_axiom relT (proj52 : tp -> _).
Proof. by split=>[|x y] // /and5P []. Qed.
Lemma proj53_morph_ax : pcm_morph_axiom relT (proj53 : tp -> _).
Proof. by split=>[|x y] // /and5P []. Qed.
Lemma proj54_morph_ax : pcm_morph_axiom relT (proj54 : tp -> _).
Proof. by split=>[|x y] // /and5P []. Qed.
Lemma proj55_morph_ax : pcm_morph_axiom relT (proj55 : tp -> _).
Proof. by split=>[|x y] // /and5P []. Qed.

HB.instance Definition _ := isPCM_morphism.Build tp U1 _ proj51_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U2 _ proj52_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U3 _ proj53_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U4 _ proj54_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U5 _ proj55_morph_ax.
End Proj5Morph.

Section Proj6Morph.
Variables U1 U2 U3 U4 U5 U6 : pcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).

Lemma proj61_morph_ax : pcm_morph_axiom relT (proj61 : tp -> _).
Proof. by split=>[|x y] // /and6P []. Qed.
Lemma proj62_morph_ax : pcm_morph_axiom relT (proj62 : tp -> _).
Proof. by split=>[|x y] // /and6P []. Qed.
Lemma proj63_morph_ax : pcm_morph_axiom relT (proj63 : tp -> _).
Proof. by split=>[|x y] // /and6P []. Qed.
Lemma proj64_morph_ax : pcm_morph_axiom relT (proj64 : tp -> _).
Proof. by split=>[|x y] // /and6P []. Qed.
Lemma proj65_morph_ax : pcm_morph_axiom relT (proj65 : tp -> _).
Proof. by split=>[|x y] // /and6P []. Qed.
Lemma proj66_morph_ax : pcm_morph_axiom relT (proj66 : tp -> _).
Proof. by split=>[|x y] // /and6P []. Qed.

HB.instance Definition _ := isPCM_morphism.Build tp U1 _ proj61_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U2 _ proj62_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U3 _ proj63_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U4 _ proj64_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U5 _ proj65_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U6 _ proj66_morph_ax.
End Proj6Morph.

Section Proj7Morph.
Variables U1 U2 U3 U4 U5 U6 U7 : pcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).

Lemma proj71_morph_ax : pcm_morph_axiom relT (proj71 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.
Lemma proj72_morph_ax : pcm_morph_axiom relT (proj72 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.
Lemma proj73_morph_ax : pcm_morph_axiom relT (proj73 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.
Lemma proj74_morph_ax : pcm_morph_axiom relT (proj74 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.
Lemma proj75_morph_ax : pcm_morph_axiom relT (proj75 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.
Lemma proj76_morph_ax : pcm_morph_axiom relT (proj76 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.
Lemma proj77_morph_ax : pcm_morph_axiom relT (proj77 : tp -> _).
Proof. by split=>[|x y] // /and7P []. Qed.

HB.instance Definition _ := isPCM_morphism.Build tp U1 _ proj71_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U2 _ proj72_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U3 _ proj73_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U4 _ proj74_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U5 _ proj75_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U6 _ proj76_morph_ax.
HB.instance Definition _ := isPCM_morphism.Build tp U7 _ proj77_morph_ax.
End Proj7Morph.

(* product morphism of morphisms is a morphism *)
Section PMorphMorph.
Variables U V1 V2 : pcm.
Variables (f1 : pcm_morph U V1) (f2 : pcm_morph U V2).

Lemma pmorph_is_morph :  pcm_morph_axiom (relI (sep f1) (sep f2)) (f1 \** f2).
Proof.
rewrite /pmorphism; split=>[|x y] /=; first by rewrite !pcmPE !pfunit.
by move=>V /andP [S1 S2]; rewrite pcmE /= !pfV2 // !pfjoin.
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build U (V1 * V2)%type (f1 \** f2) pmorph_is_morph.
End PMorphMorph.

(* Can we say anything about pairing as a morphism *)
(* (-, -) : U -> V -> U * V *)
(* Because of currying, we first need to define a PCM of functions *)
(* That's easy, as join and unit can be defined pointwise *)
(* In that PCM, we can ask if pairing is a morphism in either argument *)
(* e.g. if we focus on the first argument, is *)
(* (x \+ y, _) = (x, _) \+ (y, _) *)
(* It isn't, since _ has to be replaced by the same value everywhere *)

(* morphisms for finite products *)

Section FinFunMorph.
Variables (T : finType) (Us : T -> pcm).
Implicit Types (f : {dffun forall t, Us t}) (t : T).

Definition app f := [eta f].

Lemma app_is_morph : pcm_morph_axiom relT app.
Proof.
split=>[|x y]; first by apply: fext=>t; rewrite /app ffunE.
move/forallP=>V _; split; last by apply: fext=>t; rewrite /app ffunE.
by apply/forallP=>t; move: (V t); rewrite sel_fin. 
Qed.

(*
HB.instance Definition _ := 
  isPCM_morphism.Build {ffun forall t, Us t} (forall t, Us t) app app_is_morph.
*)

(* above lemma isn't so useful in practice because can't rewrite *)
(* by pfjoin when sel is fully applied (which is always). *)
(* Thus, we need separate lemma for the case of applied sel. *)
(* This doesn't require function extensionality *)

Lemma sel_is_morph t : pcm_morph_axiom relT (@sel T Us t). 
Proof. by split=>[|x y]; [|move/forallP/(_ t)]; rewrite sel_fin. Qed.

HB.instance Definition _ t := 
  isPCM_morphism.Build {dffun forall t, Us t} (Us t) (sel t) (sel_is_morph t).

Lemma finfun_is_morph : pcm_morph_axiom relT (@finfun T Us : _ -> {dffun _}).
Proof.
split=>[|f1 f2]; first by apply/ffinP=>t; rewrite sel_fin.
move/forallP=>V _; split. 
- by apply/forallP=>t; rewrite !sel_fin; apply: V.
by apply/ffunP=>t; rewrite !ffunE !sel_fin. 
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build (forall t, Us t) {dffun forall t, Us t} 
                       (@finfun T Us : _ -> {dffun _}) 
    finfun_is_morph.

(* Now we can prove pcm-like lemmas for splice *)

Lemma valid_spliceUn t (x y : {dffun forall t, Us t}) (v : Us t) :
        valid (x \+ y) -> 
        valid (v \+ sel t y) -> 
        valid (splice x v \+ y).
Proof.
move=>V V'; apply/forallP=>z; rewrite !sel_fin.  
by case: eqP=>/= ?; [subst z; rewrite eqc | rewrite pfV2].
Qed.

Lemma spliceUn t (x y : {dffun forall t, Us t}) (v w : Us t) :
        splice (x \+ y) (v \+ w) = splice x v \+ splice y w.
Proof. 
apply/ffinP=>a; rewrite !sel_fin. 
by case: eqP=>//= ?; subst a; rewrite !eqc. 
Qed.

End FinFunMorph.

(****************************)
(****************************)
(* Classes of PCM morphisms *)
(****************************)
(****************************)

(*********************************)
(* Normal and binormal morphisms *)
(*********************************)

(* Normal morphisms: map invalids to invalids *)
(* contrapositively: valid images -> valid originals *)
(* basic healthiness property ensuring *)
(* that no invalid element is "rehabilitated" *)
(* by having the morphism map it to something valid *)

(* Binormal morphism: map overlapping to overlapping *)
(* contrapositively: separated images -> separated originals *)
(* binary variant of normal -- no overlapping elements *)
(* are rehabilitated by having the morphism map them to *)
(* separated ones *)

(* binormal -> normal but not vice-versa *)

(* Both properties are needed, as there are useful morphisms *)
(* that are normal but not binormal. *)
(* Example is injection xval : U -> V in xsep construction below, *)
(* where new PCM U is created out of old one V by moding out V by *)
(* seprel D. This creates new notion of separatenss *)
(* by adding D to the separateness of V *)
(* But then, if two elements are separate in V (old notion) *)
(* it doesn't mean they should be separate in U (new notion) *)
(* as the whole point is that new separateness in U should be more *)
(* demaning. In other words, xval isn't binormal *)

Definition norm_pcm_morph_axiom (U V : pcm) (f : pcm_morph U V) := 
  forall x : U, valid (f x) -> valid x /\ sep f x Unit.

Definition binorm_pcm_morph_axiom (U V : pcm) (f : pcm_morph U V) :=
  forall x y, valid (f x \+ f y) -> valid (x \+ y) /\ sep f x y.

(* structure definitions *)
HB.mixin Record isNorm_PCM_morphism (U V : pcm) (f : U -> V) 
  of @PCM_morphism U V f := {
  norm_pcm_morph_subproof : norm_pcm_morph_axiom f}.

#[short(type=norm_pcm_morph)]
HB.structure Definition Norm_PCM_morphism (U V : pcm) := 
  {f of isNorm_PCM_morphism U V f & @PCM_morphism U V f}.

(* helper mixin to define binormal structure *)
HB.mixin Record isBinorm_PCM_morphism U V 
     f of @PCM_morphism U V f := {
   binorm_subproof : binorm_pcm_morph_axiom f}.  

(* require both binorm_axiom and norm_axiom for sake of inheritance *)
(* we prove below that binorm_axiom implies norm_axiom *)
(* so we can actually build binorm_pcm_morph just out of binorm_axiom *)
#[short(type=binorm_pcm_morph)]
HB.structure Definition Binorm_PCM_morphism U V := 
  {f of isBinorm_PCM_morphism U V f & @Norm_PCM_morphism U V f}.

(* Norm mixin follows from Binorm mixin *)
HB.builders Context U V f of isBinorm_PCM_morphism U V f.

Lemma binorm_morph_is_norm_morph : norm_pcm_morph_axiom f.
Proof. 
move=>x W; rewrite -{1}[x]unitR; apply: binorm_subproof.
by rewrite pfunit unitR.
Qed.
(* default instance of norm_pcm_morph *)
HB.instance Definition _ := 
  isNorm_PCM_morphism.Build U V f binorm_morph_is_norm_morph.
HB.end.

(* Normality Lemmas *)
(* We use names that start with f to indicate that these lemmas *)
(* all have validity preconditions over f x *)

Lemma fpVI (U V : pcm) (f : norm_pcm_morph U V) (x : U) : 
        valid (f x) -> valid x /\ sep f x Unit.
Proof. exact: norm_pcm_morph_subproof. Qed.

Lemma fpVE (U V : pcm) (f : norm_pcm_morph U V) (x : U) : 
        valid (f x) = valid x && sep f x Unit.
Proof. by apply/idP/idP; [move/fpVI/andP|case/andP; apply: pfV]. Qed.

Lemma fpV (U V : pcm) (f : norm_pcm_morph U V) (x : U) : 
        valid (f x) -> valid x.
Proof. by case/fpVI. Qed.

Lemma fpVS (U V : pcm) (f : norm_pcm_morph U V) (x : U) : 
        valid (f x) -> sep f x Unit.
Proof. by case/fpVI. Qed.

(* Binormality Lemmas *)

Lemma fpV2I (U V : pcm) (f : binorm_pcm_morph U V) (x y : U) :
        valid (f x \+ f y) -> valid (x \+ y) /\ sep f x y. 
Proof. by apply: binorm_subproof. Qed.

Lemma fpV2E (U V : pcm) (f : binorm_pcm_morph U V) (x y : U) :
        valid (f x \+ f y) = valid (x \+ y) && sep f x y.  
Proof. by apply/idP/idP; [move/fpV2I/andP|case/andP; apply: pfV2]. Qed.

Lemma fpV2 (U V : pcm) (f : binorm_pcm_morph U V) (x y : U) : 
         valid (f x \+ f y) -> valid (x \+ y).
Proof. by case/fpV2I. Qed.

Lemma fpV2S (U V : pcm) (f : binorm_pcm_morph U V) (x y : U) : 
         valid (f x \+ f y) -> sep f x y.
Proof. by case/fpV2I. Qed.

Arguments fpVI {U V}.
Arguments fpVE {U V}.
Arguments fpV {U V}.
Arguments fpVS {U V}.
Arguments fpV2I {U V}.
Arguments fpV2E {U V}.
Arguments fpV2 {U V}.
Arguments fpV2S {U V}.

(*******************************************)
(* Categorical morphisms and (bi)normality *)
(*******************************************)

(* id is binormal *)
Lemma id_is_binorm_morphism {U : pcm} : binorm_pcm_morph_axiom (@idfun U). 
Proof. by []. Qed.
HB.instance Definition _ (U : pcm) := 
  isBinorm_PCM_morphism.Build U U idfun id_is_binorm_morphism.

(* composition preserves (bi)normality *)
Section CompMorphism.
Variables U V W : pcm.

Section NormCompIsNormal.
Variables (f : norm_pcm_morph U V) (g : norm_pcm_morph V W).

Lemma comp_is_norm_morphism : norm_pcm_morph_axiom (g \o f).
Proof. 
move=>x /fpVI [] /fpVI [H1 H2] H3 /=. 
by rewrite /sepx/= H1 H2 pfunit H3.
Qed.

HB.instance Definition _ := 
  isNorm_PCM_morphism.Build U W (g \o f) comp_is_norm_morphism.

End NormCompIsNormal.

Section BinormCompIsBinorm.
Variables (f : binorm_pcm_morph U V) (g : binorm_pcm_morph V W).

Lemma comp_is_binorm_morphism : binorm_pcm_morph_axiom (g \o f).
Proof. 
move=>x y /fpV2I [/fpV2I][H1 H2 H3]. 
by rewrite /sepx/= H1 H2 H3.
Qed.

HB.instance Definition _ := 
  isBinorm_PCM_morphism.Build U W (g \o f) comp_is_binorm_morphism.
End BinormCompIsBinorm.
End CompMorphism.

(***************************************)
(* Cartesian morphisms and binormality *)
(***************************************)

(* unit_fun is normal, but not binormal *)
Section UnitFun.
Variables (U : pcm) (V : tpcm).

Lemma unitfun_is_normal : norm_pcm_morph_axiom (@unit_fun U V).
Proof.
move=>x; case W : (valid x)=>//.
by move: (valid_undef V); rewrite /valid/=/unit_fun/= W =>->.  
Qed.

HB.instance Definition _ := 
  isNorm_PCM_morphism.Build U V 
    (@unit_fun U V) unitfun_is_normal.
End UnitFun.

(* projections aren't (bi)normal, but product morphisms are *)

Section FProdMorph.
Variables U1 U2 V1 V2 : pcm.

Section Normal.
Variables (f1 : norm_pcm_morph U1 V1) (f2 : norm_pcm_morph U2 V2).

Lemma fprod_is_norm_pcm_morph : norm_pcm_morph_axiom (f1 \* f2).
Proof. 
move=>x /=; rewrite !pcmPV /sepx /=. 
by case/andP=>/fpVI [->->] /fpVI [->->].
Qed.

HB.instance Definition _ := 
  isNorm_PCM_morphism.Build (U1 * U2)%type (V1 * V2)%type (f1 \* f2) 
    fprod_is_norm_pcm_morph.
End Normal.

Section Binormal.
Variables (f1 : binorm_pcm_morph U1 V1) (f2 : binorm_pcm_morph U2 V2).

Lemma fprod_is_binorm_pcm_morph : binorm_pcm_morph_axiom (f1 \* f2).
Proof. 
move=>x y /=; rewrite !pcmPV /sepx/=.
by case/andP=>/fpV2I [->->] /fpV2I.
Qed.

HB.instance Definition _ := 
isBinorm_PCM_morphism.Build (U1 * U2)%type (V1 * V2)%type (f1 \* f2) 
  fprod_is_binorm_pcm_morph.
End Binormal.
End FProdMorph.

Section PMorphMorph.
Variables U V1 V2 : pcm.

Section Normal.
Variables (f1 : norm_pcm_morph U V1) (f2 : norm_pcm_morph U V2).

Lemma pmorph_is_norm_pcm_morph :  norm_pcm_morph_axiom (f1 \** f2).
Proof. 
move=>x; rewrite /sepx /=.
by case/andP=>/fpVI [->->] /fpVI []. 
Qed.

HB.instance Definition _ := 
  isNorm_PCM_morphism.Build U (V1 * V2)%type (f1 \** f2) 
    pmorph_is_norm_pcm_morph.
End Normal.

Section Binormal.
Variables (f1 : binorm_pcm_morph U V1) (f2 : binorm_pcm_morph U V2).

Lemma pmorph_is_binorm_pcm_morph :  binorm_pcm_morph_axiom (f1 \** f2).
Proof. 
move=>x y /= /andP [] /fpV2I [-> H1] /fpV2I [_ H2].
by rewrite /sepx/= H1 H2.
Qed.

HB.instance Definition _ := 
  isBinorm_PCM_morphism.Build U (V1 * V2)%type (f1 \** f2) 
    pmorph_is_binorm_pcm_morph.
End Binormal.
End PMorphMorph.

Section FinFunMorph.
Variables (T : finType) (Us : T -> pcm).

Lemma finfun_is_binorm_pcm_morph : 
        binorm_pcm_morph_axiom (@finfun T Us : _ -> {dffun _}).
Proof.
move=>f1 f2 /forallP /= V; split=>//; apply/forallP=>t.
by move: (V t); rewrite !sel_fin. 
Qed.

HB.instance Definition _ := 
  isBinorm_PCM_morphism.Build (forall t, Us t) {dffun forall t, Us t} 
    (@finfun T Us : _ -> {dffun _}) finfun_is_binorm_pcm_morph.
End FinFunMorph.


(*****************)
(* Full morphism *)
(*****************)

(* morphism with seprel relT (largest possible) *)
(* an alternative name would be "total" morphism *)
(* as this morphism is defined for all valid elements *)
(* but we keep "total" for functions that are definied on *)
(* *all* elements, valid or not *)

Definition full_pcm_morph_axiom (U V : pcm) (f : pcm_morph U V) := 
  sep f =2 relT.

HB.mixin Record isFull_PCM_morphism (U V : pcm) (f : U -> V) 
  of @PCM_morphism U V f := {
  full_pcm_morphism_subproof : full_pcm_morph_axiom f}.

#[short(type=full_pcm_morph)]  
HB.structure Definition Full_PCM_morphism (U V : pcm) := 
  {f of isFull_PCM_morphism U V f & @PCM_morphism U V f}.

#[short(type=full_norm_pcm_morph)]
HB.structure Definition Full_Norm_PCM_morphism (U V : pcm) := 
  {f of @Norm_PCM_morphism U V f & @Full_PCM_morphism U V f}.

#[short(type=full_binorm_pcm_morph)]
HB.structure Definition Full_Binorm_PCM_morphism (U V : pcm) := 
  {f of @Binorm_PCM_morphism U V f & @Full_PCM_morphism U V f}.

(* fullness lemmas *)

Lemma pfSE (U V : pcm) (f : full_pcm_morph U V) : sep f =2 relT.
Proof. by apply: full_pcm_morphism_subproof. Qed.

Lemma pfT (U V : pcm) (f : full_pcm_morph U V) x y : sep f x y.
Proof. by rewrite pfSE. Qed.

#[export] Hint Resolve pfT : core.

Lemma pfVI (U V : pcm) (f : full_pcm_morph U V) (x : U) : 
        valid x -> 
        valid (f x).
Proof. by move=>W; apply: pfV W _. Qed.

Lemma pfV2I (U V : pcm) (f : full_pcm_morph U V) (x y : U) : 
        valid (x \+ y) -> 
        valid (f x \+ f y).
Proof. by move=>W; apply: pfV2 W _. Qed.

Lemma pfV2IC (U V : pcm) (f : full_pcm_morph U V) (x y : U) : 
        valid (x \+ y) -> 
        valid (f y \+ f x).
Proof. by rewrite joinC=>/pfV2I. Qed.

Lemma pfV3I (U V : pcm) (f : full_pcm_morph U V) (x y z : U) : 
        valid (x \+ y \+ z) -> 
        valid (f x \+ f y \+ f z).
Proof. by move=>W; rewrite -pfjoin ?(validL W) // pfV2. Qed.

Lemma pfVE (U V : pcm) (f : full_norm_pcm_morph U V) (x : U) : 
        valid (f x) = valid x. 
Proof. by rewrite fpVE pfT andbT. Qed.

Lemma pfV2E (U V : pcm) (f : full_binorm_pcm_morph U V) (x y : U) : 
        valid (f x \+ f y) = valid (x \+ y). 
Proof. by rewrite fpV2E pfT andbT. Qed.

Lemma pfjoinT (U V : pcm) (f : full_pcm_morph U V) (x y : U) :
        valid (x \+ y) -> 
        f (x \+ y) = f x \+ f y.
Proof. by move=>D; rewrite pfjoin. Qed.

Lemma pfLT (U V : pcm) (f : full_pcm_morph U V) (x y z : U) : 
        valid (x \+ z) -> 
        valid (y \+ z) ->
        f y = f x -> 
        f (y \+ z) = f (x \+ z).
Proof. by move=>V1 V2 E; rewrite !pfjoinT // E. Qed.

Lemma pfRT (U V : pcm) (f : full_pcm_morph U V) (x y z : U) : 
        valid (z \+ x) -> 
        valid (z \+ y) ->
        f y = f x -> 
        f (z \+ y) = f (z \+ x).
Proof. by move=>V1 V2 E; rewrite !pfjoinT // E. Qed.

Lemma pfUnTE (U V : pcm) (f : full_pcm_morph U V) (x1 y1 x2 y2 : U) : 
        valid (x1 \+ y1) ->
        valid (x2 \+ y2) ->
        f x2 = f x1 ->
        f y2 = f y1 ->
        f (x2 \+ y2) = f (x1 \+ y1).
Proof. by move=>V1 V2 E1 E2; rewrite !pfjoinT // E1 E2. Qed.

Arguments pfVI {U V f x}.
Arguments pfV2I {U V f x y}.
Arguments pfVE {U V f x}.
Arguments pfV2E {U V f x y}.
Arguments pfjoinT {U V f x}.
Arguments pfLT {U V} f {x y}.
Arguments pfRT {U V} f {x y}.

(* Categorical morphisms and fullness *)

(* id is full *)
Lemma id_is_full_morphism {U : pcm} : full_pcm_morph_axiom (@idfun U).
Proof. by []. Qed.
HB.instance Definition _ (U : pcm) := 
  isFull_PCM_morphism.Build U U idfun id_is_full_morphism.

(* composition preserves fullness *)
Section CompMorphism.
Variables U V W : pcm.

Section FullCompIsFull.
Variables (f : full_pcm_morph U V) (g : full_pcm_morph V W).

Lemma comp_is_full_morphism : full_pcm_morph_axiom (g \o f).
Proof. by move=>x y /=; rewrite /sepx/= !pfT. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build U W (g \o f) comp_is_full_morphism.
End FullCompIsFull.

(* instances for combinations must declare PCM_morphism.on *)
(* before declaring fullness structure. *)
(* DEVCOMMENT: *)
(* Alternative is to write the definition explicitly as below, *)
(* but that's too low level. *)
(*
HB.instance Definition _ (f : full_norm_pcm_morph U V) 
                         (g : full_norm_pcm_morph V W) :=
  Full_Norm_PCM_morphism.copy (g \o f) 
    (Full_Norm_PCM_morphism.pack_ 
       (Norm_PCM_morphism.class (g \o f))
       (Full_PCM_morphism.class (g \o f))). *)
(* /DEVCOMMENT *)

HB.instance Definition _  
    (f : full_norm_pcm_morph U V) 
    (g : full_norm_pcm_morph V W) := 
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : full_norm_pcm_morph U V) 
    (g : full_norm_pcm_morph V W) := 
  Full_Norm_PCM_morphism.on (g \o f).

HB.instance Definition _ 
    (f : full_binorm_pcm_morph U V) 
    (g : full_binorm_pcm_morph V W) :=
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : full_binorm_pcm_morph U V) 
    (g : full_binorm_pcm_morph V W) :=
  Full_Binorm_PCM_morphism.on (g \o f).

End CompMorphism.

(* Cartesian morphisms and fullness *)

Section UnitFun.
Variables (U : pcm) (V : tpcm).

Lemma unitfun_is_full_pcm_morph : full_pcm_morph_axiom (@unit_fun U V).
Proof. by []. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build U V 
    (@unit_fun U V) unitfun_is_full_pcm_morph.
End UnitFun.


Section Cartesians.
Notation pf := (fun _ _ => erefl _).

Section FProdMorph.
Variables U1 U2 V1 V2 : pcm.
Variables (f1 : full_pcm_morph U1 V1) (f2 : full_pcm_morph U2 V2).

Lemma fprod_is_full_pcm_morph : full_pcm_morph_axiom (f1 \* f2).
Proof. by move=>x y /=; rewrite /sepx/=!pfT. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build (U1 * U2)%type (V1 * V2)%type (f1 \* f2) 
                             fprod_is_full_pcm_morph.
End FProdMorph.

Section ProjMorph.
Variables U1 U2 : pcm.
HB.instance Definition _ := isFull_PCM_morphism.Build (U1 * U2)%type U1 fst pf.
HB.instance Definition _ := isFull_PCM_morphism.Build (U1 * U2)%type U2 snd pf.
End ProjMorph.

Section Proj3Morph.
Variables U1 U2 U3 : pcm.
Notation tp := (Prod3 U1 U2 U3).
HB.instance Definition _ := isFull_PCM_morphism.Build tp U1 proj31 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U2 proj32 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U3 proj33 pf.
End Proj3Morph.

Section Proj4Morph.
Variables U1 U2 U3 U4 : pcm.
Notation tp := (Prod4 U1 U2 U3 U4).
HB.instance Definition _ := isFull_PCM_morphism.Build tp U1 proj41 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U2 proj42 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U3 proj43 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U4 proj44 pf.
End Proj4Morph.

Section Proj5Morph.
Variables U1 U2 U3 U4 U5 : pcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).
HB.instance Definition _ := isFull_PCM_morphism.Build tp U1 proj51 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U2 proj52 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U3 proj53 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U4 proj54 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U5 proj55 pf.
End Proj5Morph.

Section Proj6Morph.
Variables U1 U2 U3 U4 U5 U6 : pcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).
HB.instance Definition _ := isFull_PCM_morphism.Build tp U1 proj61 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U2 proj62 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U3 proj63 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U4 proj64 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U5 proj65 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U6 proj66 pf.
End Proj6Morph.

Section Proj7Morph.
Variables U1 U2 U3 U4 U5 U6 U7 : pcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).
HB.instance Definition _ := isFull_PCM_morphism.Build tp U1 proj71 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U2 proj72 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U3 proj73 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U4 proj74 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U5 proj75 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U6 proj76 pf.
HB.instance Definition _ := isFull_PCM_morphism.Build tp U7 proj77 pf.
End Proj7Morph.

Section PMorphMorph.
Variables U V1 V2 : pcm.
Variables (f1 : full_pcm_morph U V1) (f2 : full_pcm_morph U V2).

Lemma pmorph_is_full_pcm_morph :  full_pcm_morph_axiom (f1 \** f2).
Proof. by move=>x y /=; rewrite /sepx/= !pfT. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build U (V1 * V2)%type (f1 \** f2) 
    pmorph_is_full_pcm_morph.
End PMorphMorph.

Section FinFunMorph.
HB.instance Definition _ (T : finType) (Us : T -> pcm) (t : T) := 
  isFull_PCM_morphism.Build {dffun forall t, Us t} (Us t) (sel t) pf.

HB.instance Definition _ (T : finType) (Us : T -> pcm) := 
  isFull_PCM_morphism.Build (forall t, Us t) {dffun forall t, Us t} 
  (@finfun T Us : _ -> {dffun _}) pf.
End FinFunMorph.

End Cartesians.

(* fullness and other constructions *)

Section RelApp.
Variables (U V : pcm) (S : seprel V) (f : full_pcm_morph U V).

Lemma relapp_is_seprel : seprel_axiom (rel_app S f).
Proof.
split=>[|x y|x y|x y z] /=.
- by rewrite pfunit sep00.
- by move=>W; rewrite sepC // pfV2I.
- by move=>W; rewrite pfunit; move/sep0E=>-> //; rewrite pfV2I.
move=>W; rewrite !pfjoinT ?(validLE3 W) // => X Y.
by rewrite !(sepAxx _ X Y) // -!pfjoinT ?(validLE3 W) ?pfVI.
Qed.

HB.instance Definition _ := 
  isSeprel.Build U (rel_app S f) relapp_is_seprel.
End RelApp.

Section Pmorph.
Variables (U V1 V2 : pcm).
Variables (f1 : full_pcm_morph U V1) (f2 : full_pcm_morph U V2).

Lemma pmorphism_is_full : full_pcm_morph_axiom (f1 \** f2).
Proof. by move=>x y /=; rewrite !pfT. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build U (V1 * V2)%type 
    (f1 \** f2) pmorphism_is_full.
End Pmorph.

(******************)
(******************)
(* TPCM morphisms *)
(******************)
(******************)

(* tpcm morphisms further preserve undef *)

Definition tpcm_morph_axiom (U V : tpcm) (f : U -> V) := 
  f undef = undef. 

HB.mixin Record isTPCM_morphism (U V : tpcm) (f : U -> V) := {
  tpcm_morphism_subproof : tpcm_morph_axiom f}.

#[short(type=tpcm_morph)]  
HB.structure Definition TPCM_morphism (U V : tpcm) := 
  {f of isTPCM_morphism U V f & @PCM_morphism U V f}.

(* introduce names for the combinations of sub-properties *)

#[short(type=norm_tpcm_morph)]
HB.structure Definition Norm_TPCM_morphism (U V : tpcm) := 
  {f of @Norm_PCM_morphism U V f & @TPCM_morphism U V f}.

#[short(type=binorm_tpcm_morph)]
HB.structure Definition Binorm_TPCM_morphism (U V : tpcm) := 
  {f of @Binorm_PCM_morphism U V f & @TPCM_morphism U V f}.

#[short(type=full_tpcm_morph)]  
HB.structure Definition Full_TPCM_morphism (U V : tpcm) := 
  {f of @Full_PCM_morphism U V f & @TPCM_morphism U V f}.

#[short(type=full_norm_tpcm_morph)]
HB.structure Definition Full_Norm_TPCM_morphism (U V : tpcm) := 
  {f of @Full_PCM_morphism U V f & @Norm_TPCM_morphism U V f}.

#[short(type=full_binorm_tpcm_morph)]
HB.structure Definition Full_Binorm_TPCM_morphism (U V : tpcm) := 
  {f of @Full_PCM_morphism U V f & @Binorm_TPCM_morphism U V f}.

(* TPCM lemmas *)

Lemma pfundef {U V : tpcm} (f : tpcm_morph U V) : f undef = undef.
Proof. by apply: tpcm_morphism_subproof. Qed.

(* full morphism on normal tpcm is normal *)

Lemma fullmorph_is_norm (U : normal_tpcm) V (f : full_tpcm_morph U V) : 
        norm_pcm_morph_axiom f.
Proof.
move=>x; rewrite pfT; case: (normalP x)=>[->|] //=.
by rewrite pfundef valid_undef.
Qed.
Arguments fullmorph_is_norm {U V f}.

(* Following lemma is a crutch whose use is discouraged. *)
(* Instead, declare f as normal, and use pfVE. *)
Lemma pfnVE (U : normal_tpcm) V (f : full_tpcm_morph U V) x : 
        valid (f x) = valid x.
Proof. by apply/idP/idP; [case/fullmorph_is_norm|apply/pfVI]. Qed.

(* Categoricals are tpcm morphism *)

HB.instance Definition _ (U : tpcm) := 
  isTPCM_morphism.Build U U (@idfun U) (erefl _).

Section Comp.
Variables U V W : tpcm.

Section CompTPCM.
Variables (f : tpcm_morph U V) (g : tpcm_morph V W).

Lemma comp_is_tpcm_morphism : tpcm_morph_axiom (g \o f).
Proof. by rewrite /tpcm_morph_axiom /= !pfundef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build U W (g \o f) comp_is_tpcm_morphism.
End CompTPCM.

(* combinations declared explicitly *)

HB.instance Definition _ 
    (f : norm_tpcm_morph U V) 
    (g : norm_tpcm_morph V W) :=
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : norm_tpcm_morph U V) 
    (g : norm_tpcm_morph V W) :=
  Norm_TPCM_morphism.on (g \o f).

HB.instance Definition _ 
    (f : binorm_tpcm_morph U V) 
    (g : binorm_tpcm_morph V W) :=
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : binorm_tpcm_morph U V) 
    (g : binorm_tpcm_morph V W) :=
  Binorm_TPCM_morphism.on (g \o f).

HB.instance Definition _ 
    (f : full_tpcm_morph U V) 
    (g : full_tpcm_morph V W) :=
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : full_tpcm_morph U V) 
    (g : full_tpcm_morph V W) :=
  Full_TPCM_morphism.on (g \o f).

HB.instance Definition _ 
    (f : full_norm_tpcm_morph U V) 
    (g : full_norm_tpcm_morph V W) :=
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : full_norm_tpcm_morph U V) 
    (g : full_norm_tpcm_morph V W) :=
  Full_Norm_TPCM_morphism.on (g \o f).

HB.instance Definition _  
    (f : full_binorm_tpcm_morph U V) 
    (g : full_binorm_tpcm_morph V W) :=
  PCM_morphism.on (g \o f).
HB.instance Definition _ 
    (f : full_binorm_tpcm_morph U V) 
    (g : full_binorm_tpcm_morph V W) :=
  Full_Binorm_TPCM_morphism.on (g \o f).

End Comp. 

(* Cartesians *)

Section UnitFun.
Variables (U V : tpcm).

Lemma unitfun_is_tpcm_morph : tpcm_morph_axiom (@unit_fun U V).
Proof. by rewrite /tpcm_morph_axiom/unit_fun valid_undef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build U V 
    (@unit_fun U V) unitfun_is_tpcm_morph.
End UnitFun.


Section FProdMorph.
Variables U1 U2 V1 V2 : tpcm.
Variables (f1 : tpcm_morph U1 V1) (f2 : tpcm_morph U2 V2).

Lemma fprod_is_tpcm_morph : tpcm_morph_axiom (f1 \* f2).
Proof. by rewrite /tpcm_morph_axiom /fprod !pfundef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build (U1 * U2)%type (V1 * V2)%type (f1 \* f2) 
                        fprod_is_tpcm_morph.
End FProdMorph.

(* projections are tpcm morphisms *)
Section ProjMorph.
Variables U1 U2 : tpcm.

Lemma fst_is_tpcm_morph : tpcm_morph_axiom (@fst U1 U2).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build (U1 * U2)%type U1 fst fst_is_tpcm_morph.

Lemma snd_is_tpcm_morph : tpcm_morph_axiom (@snd U1 U2).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build (U1 * U2)%type U2 snd snd_is_tpcm_morph.
End ProjMorph.

(* projections for iterated products are morphisms *)

Section Proj3Morph.
Variables U1 U2 U3 : tpcm.
Notation tp := (Prod3 U1 U2 U3).

Lemma proj31_is_tpcm_morph : tpcm_morph_axiom (proj31 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj32_is_tpcm_morph : tpcm_morph_axiom (proj32 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj33_is_tpcm_morph : tpcm_morph_axiom (proj33 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := isTPCM_morphism.Build tp U1 _ proj31_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U2 _ proj32_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U3 _ proj33_is_tpcm_morph.
End Proj3Morph.

Section Proj4Morph.
Variables U1 U2 U3 U4 : tpcm.
Notation tp := (Prod4 U1 U2 U3 U4).

Lemma proj41_is_tpcm_morph : tpcm_morph_axiom (proj41 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj42_is_tpcm_morph : tpcm_morph_axiom (proj42 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj43_is_tpcm_morph : tpcm_morph_axiom (proj43 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj44_is_tpcm_morph : tpcm_morph_axiom (proj44 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := isTPCM_morphism.Build tp U1 _ proj41_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U2 _ proj42_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U3 _ proj43_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U4 _ proj44_is_tpcm_morph.
End Proj4Morph.

Section Proj5Morph.
Variables U1 U2 U3 U4 U5 : tpcm.
Notation tp := (Prod5 U1 U2 U3 U4 U5).

Lemma proj51_is_tpcm_morph : tpcm_morph_axiom (proj51 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj52_is_tpcm_morph : tpcm_morph_axiom (proj52 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj53_is_tpcm_morph : tpcm_morph_axiom (proj53 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj54_is_tpcm_morph : tpcm_morph_axiom (proj54 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj55_is_tpcm_morph : tpcm_morph_axiom (proj55 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := isTPCM_morphism.Build tp U1 _ proj51_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U2 _ proj52_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U3 _ proj53_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U4 _ proj54_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U5 _ proj55_is_tpcm_morph.
End Proj5Morph.

Section Proj6Morph.
Variables U1 U2 U3 U4 U5 U6 : tpcm.
Notation tp := (Prod6 U1 U2 U3 U4 U5 U6).

Lemma proj61_is_tpcm_morph : tpcm_morph_axiom (proj61 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj62_is_tpcm_morph : tpcm_morph_axiom (proj62 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj63_is_tpcm_morph : tpcm_morph_axiom (proj63 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj64_is_tpcm_morph : tpcm_morph_axiom (proj64 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj65_is_tpcm_morph : tpcm_morph_axiom (proj65 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj66_is_tpcm_morph : tpcm_morph_axiom (proj66 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := isTPCM_morphism.Build tp U1 _ proj61_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U2 _ proj62_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U3 _ proj63_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U4 _ proj64_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U5 _ proj65_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U6 _ proj66_is_tpcm_morph.
End Proj6Morph.

Section Proj7Morph.
Variables U1 U2 U3 U4 U5 U6 U7 : tpcm.
Notation tp := (Prod7 U1 U2 U3 U4 U5 U6 U7).

Lemma proj71_is_tpcm_morph : tpcm_morph_axiom (proj71 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj72_is_tpcm_morph : tpcm_morph_axiom (proj72 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj73_is_tpcm_morph : tpcm_morph_axiom (proj73 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj74_is_tpcm_morph : tpcm_morph_axiom (proj74 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj75_is_tpcm_morph : tpcm_morph_axiom (proj75 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj76_is_tpcm_morph : tpcm_morph_axiom (proj76 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.
Lemma proj77_is_tpcm_morph : tpcm_morph_axiom (proj77 : tp -> _).
Proof. by rewrite /tpcm_morph_axiom /undef. Qed.

HB.instance Definition _ := isTPCM_morphism.Build tp U1 _ proj71_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U2 _ proj72_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U3 _ proj73_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U4 _ proj74_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U5 _ proj75_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U6 _ proj76_is_tpcm_morph.
HB.instance Definition _ := isTPCM_morphism.Build tp U7 _ proj77_is_tpcm_morph.
End Proj7Morph.

(* product morphism of tpcm morphisms is a tpcm morphism *)
Section PMorphMorph.
Variables U V1 V2 : tpcm.
Variables (f1 : tpcm_morph U V1) (f2 : tpcm_morph U V2).

Lemma pmorph_is_tpcm_morph :  tpcm_morph_axiom (f1 \** f2).
Proof. by rewrite /tpcm_morph_axiom/pmorphism !pfundef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build U (V1 * V2)%type (f1 \** f2) pmorph_is_tpcm_morph.

End PMorphMorph.

(* combination of full and tpcm declared by hand *)
HB.instance Definition _ (U V1 V2 : tpcm) 
  (f1 : full_tpcm_morph U V1) (f2 : full_tpcm_morph U V2) :=
  Full_TPCM_morphism.copy (f1 \** f2) 
    (Full_TPCM_morphism.pack_ 
       (TPCM_morphism.class (f1 \** f2))
       (Full_PCM_morphism.class (f1 \** f2))).

(* finite products *)
Section FinFunMorph.
Variables (T : ifinType) (Us : T -> tpcm).

Lemma sel_is_tpcm_morph t : tpcm_morph_axiom (sel (Us:=Us) t).
Proof. by rewrite /tpcm_morph_axiom sel_fin. Qed.

HB.instance Definition _ (t : T) := 
  isTPCM_morphism.Build {dffun forall t, Us t} (Us t) (sel t) 
    (sel_is_tpcm_morph t).

Lemma finfun_is_tpcm_morph : 
        tpcm_morph_axiom (V:={dffun forall t, Us t}) finfun. 
Proof. by []. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build (forall t, Us t) {dffun forall t, Us t}
    (@finfun T Us : _ -> {dffun _}) finfun_is_tpcm_morph.
End FinFunMorph.

(* restriction *)
Section RestrictionTPCM.
Variables (U V : tpcm) (f : tpcm_morph U V) (S : seprel U).

Lemma res_is_tpcm_morph : tpcm_morph_axiom (res f S).
Proof. by rewrite /tpcm_morph_axiom /res pfundef if_same. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build U V (res f S) res_is_tpcm_morph.
End RestrictionTPCM.

(* join *)
Section JoinFunTPCM.
Variables (U V : tpcm) (f1 f2 : tpcm_morph U V).

Lemma joinfun_is_tpcm_morph : tpcm_morph_axiom (join_fun f1 f2).
Proof. by rewrite /tpcm_morph_axiom/join_fun !pfundef join_undef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build U V (join_fun f1 f2) joinfun_is_tpcm_morph.
End JoinFunTPCM.

(********************)
(* Option morphisms *)
(********************)

Definition odfltu {A : pcm} (x : option A) := odflt Unit x.

(* Some is full binormal morphism *)
Lemma some_is_morph {A : pcm} : pcm_morph_axiom relT (@Some A).
Proof. by []. Qed. 
HB.instance Definition _ A := 
  isPCM_morphism.Build A (option A) Some some_is_morph.
Lemma some_is_binorm {A : pcm} : binorm_pcm_morph_axiom (@Some A). 
Proof. by []. Qed.
HB.instance Definition _ A := 
  isBinorm_PCM_morphism.Build A (option A) Some some_is_binorm. 
HB.instance Definition _ A := 
  isFull_PCM_morphism.Build A (option A) Some (fun _ _ => erefl _).

(* odflt is full morphism, but doesn't preserve undef (hence, not normal) *)
Lemma odfltu_is_morph {A : pcm} : pcm_morph_axiom relT (@odfltu A).
Proof. by split=>//; case=>[x|][y|]. Qed.
HB.instance Definition _ (A : pcm) := 
  isPCM_morphism.Build (option A) A odfltu odfltu_is_morph.
HB.instance Definition _ (A : pcm) := 
  isFull_PCM_morphism.Build (option A) A odfltu (fun _ _ => erefl _).

(* strenghtening of pfjoin for Some morphism (elides validity) *)
Lemma pfsome (A : pcm) (x y : A) : Some x \+ Some y = Some (x \+ y).
Proof. by []. Qed.

Lemma odflt_some (A : pcm) (x : A) : odfltu (Some x) = x. 
Proof. by []. Qed.

Lemma odflt_someUn (A : pcm) (x y : A) : odfltu (Some x \+ Some y) = x \+ y. 
Proof. by []. Qed.

Lemma some_odflt (A : pcm) (x : option A) : valid x -> Some (odfltu x) = x.
Proof. by case: x. Qed.

Lemma some_odfltUn (A : pcm) (x y : option A) : 
        valid (x \+ y) -> Some (odfltu x \+ odfltu y) = x \+ y.
Proof. by case: x; case: y. Qed.

(* constructions for option nat, specifically *)

Lemma option_nat_is_normal : normal_tpcm_axiom (option nat).
Proof. by apply: option_is_normal. Qed.
HB.instance Definition _ := 
  isNormal_TPCM.Build (option nat) option_nat_is_normal.

Lemma onat0E (x y : option nat) : x \+ y = Unit -> (x = Unit) * (y = Unit).
Proof.
case: x=>[x|]; case: y=>[y|] // [] /eqP.
by rewrite addn_eq0=>/andP [/eqP -> /eqP ->].
Qed.


(**********)
(**********)
(* SubPCM *)
(**********)
(**********)

(* Subpcm structure between U and V consists of two morphisms *)
(* pval : U -> V and psub : V -> U with special properties. *)
(* The definition thus resembles Galois connections and adjunctions *)
(* which also postulate existence of morphisms in the opposite directions. *)
(* This formulation allows reasoning about composition *)
(* of subpcm structures *)

(* We thus define the structure collecting the two morphisms *)
(* (with identity and composition) *)

Record sub_struct (U V : Type) := SubStruct {
  pval : U -> V; 
  psub : V -> U}.

Arguments pval : simpl never.
Arguments psub : simpl never.

Definition id_sub {U} := @SubStruct U U idfun idfun.

Definition comp_sub U V W (X : sub_struct U V) (Y : sub_struct V W) := 
  SubStruct (pval Y \o pval X) (psub X \o psub Y).

(* explicit rewrite rules *)
Lemma pval_id U : pval (@id_sub U) = idfun. Proof. by []. Qed.
Lemma psub_id U : psub (@id_sub U) = idfun. Proof. by []. Qed.
Lemma pval_comp U V W X Y : 
        pval (@comp_sub U V W X Y) = pval Y \o pval X.
Proof. by []. Qed.
Lemma psub_comp U V W X Y : 
        psub (@comp_sub U V W X Y) = psub X \o psub Y. 
Proof. by []. Qed.

(* subpcm axoms *)
(* pval - normality needed so that transitions of subresources *)
(*        don't require side condition on validity *)
(* pval - fullness is required for simplicity *)
(* psub - binormality needed so that xsep (defined below) is pcm *)
(* remaining two axioms are expected for injection/retraction pair *)

Definition subpcm_struct_axiom' (U V : pcm) 
    (pval : full_norm_pcm_morph U V) 
    (psub : binorm_pcm_morph V U) := 
  [/\ (* inject then retract is id *)
      forall u, psub (pval u) = u &
      (* retract then inject is id on valid elements *)
      forall v, valid v -> sep psub v Unit -> pval (psub v) = v].

Notation subpcm_struct_axiom S := 
  (subpcm_struct_axiom' (pval S) (psub S)).

HB.mixin Record isSubPCM_struct (U V : pcm) (S : sub_struct U V) := {
  pval_submix : @Full_Norm_PCM_morphism U V (pval S);
  psub_submix : @Binorm_PCM_morphism V U (psub S);
  subpcm_struct_subproof : 
    subpcm_struct_axiom'
      (Full_Norm_PCM_morphism.Pack pval_submix)
      (Binorm_PCM_morphism.Pack psub_submix)}.

#[short(type=subpcm_struct)]
HB.structure Definition SubPCM_struct U V := {S of isSubPCM_struct U V S}.

Arguments subpcm_struct_subproof {U V}.

(* declare pval/psub to be pcm morphisms *)
HB.instance Definition _ (U V : pcm) (S : subpcm_struct U V) := 
  Full_Norm_PCM_morphism.copy (pval S) 
    (Full_Norm_PCM_morphism.Pack pval_submix).
HB.instance Definition _ (U V : pcm) (S : subpcm_struct U V) := 
  Binorm_PCM_morphism.copy (psub S) 
    (Binorm_PCM_morphism.Pack psub_submix).

Notation subsep S := (sep (psub S)).

Section Repack.
Variables (U V : pcm) (S : subpcm_struct U V).

Lemma psub_pval (x : U) : psub S (pval S x) = x.
Proof. by case: (subpcm_struct_subproof S)=>H ?; apply: H. Qed.

Lemma pval_psub (x : V) : 
        valid x -> subsep S x Unit -> pval S (psub S x) = x.
Proof. by case: (subpcm_struct_subproof S)=>?; apply. Qed.

End Repack.

Arguments psub_pval {U V}.
Arguments pval_psub {U V}.

Lemma sep_pval (U V : pcm) (S : subpcm_struct U V) x y : sep (pval S) x y.
Proof. exact: pfT. Qed.

#[export] Hint Resolve sep_pval : core.

Section DerivedLemmas.
Variables (U V : pcm) (S : subpcm_struct U V).

(* unary lemmas *)

Lemma valid_sepE (x : U) : 
        valid x = valid (pval S x) && subsep S (pval S x) Unit.
Proof. by rewrite -fpVE /= psub_pval. Qed.

Lemma valid_sep (x : U) : 
        valid x -> valid (pval S x) /\ subsep S (pval S x) Unit.
Proof. by rewrite valid_sepE=>/andP. Qed.

Lemma valid_pval (x : U) : valid x -> valid (pval S x).
Proof. by case/valid_sep. Qed.

Lemma valid_sepS (x : U) : valid x -> subsep S (pval S x) Unit.
Proof. by case/valid_sep. Qed.

(* pvalE is full and normal *)
Lemma valid_pvalE (x : U) : valid (pval S x) = valid x.
Proof. by rewrite pfVE. Qed.

(* iff variant for convenience *) 
Lemma valid_pvalEP (x : U) : valid (pval S x) <-> valid x.
Proof. by rewrite valid_pvalE. Qed.

Lemma valid_pvalS (x : U) : valid (pval S x) -> subsep S (pval S x) Unit.
Proof. by move/valid_pvalEP/valid_sepS. Qed.

(* we can collect the two conditions of pval_psub into one *) 
Lemma valid_psubS (x : V) : valid (psub S x) -> pval S (psub S x) = x.
Proof. by case/fpVI; apply: pval_psub. Qed.


(* binary lemmas *)

Lemma valid_sepUnE (x y : U) :
         valid (x \+ y) =
         valid (pval S x \+ pval S y) && subsep S (pval S x) (pval S y). 
Proof. by rewrite -fpV2E /= !psub_pval. Qed.

Lemma valid_sepUn (x y : U) :
         valid (x \+ y) ->
         valid (pval S x \+ pval S y) /\ subsep S (pval S x) (pval S y). 
Proof. by rewrite valid_sepUnE=>/andP. Qed.

Lemma valid_pvalUn (x y : U) : 
        valid (x \+ y) -> valid (pval S x \+ pval S y).
Proof. by case/valid_sepUn. Qed.

Lemma valid_sepUnS (x y : U) : valid (x \+ y) -> subsep S (pval S x) (pval S y). 
Proof. by rewrite valid_sepUnE=>/andP []. Qed.

(* binary versions of valid_pvalE, valid_pvalS only hold if *)
(* subsep operates on arguments independently *)
Lemma valid_pvalUnE (x y : U) :
        subsep S (pval S x) (pval S y) = 
          subsep S (pval S x) Unit && subsep S (pval S y) Unit ->
        valid (pval S x \+ pval S y) = valid (x \+ y).
Proof. 
rewrite valid_sepUnE=>->; case W : (valid _)=>//=.
by rewrite !valid_pvalS ?(validL W, validR W).
Qed.

Lemma valid_pvalUnS (x y : U) : 
        subsep S (pval S x) (pval S y) = 
          subsep S (pval S x) Unit && subsep S (pval S y) Unit ->
        valid (pval S x \+ pval S y) -> subsep S (pval S x) (pval S y).
Proof. by move/valid_pvalUnE=>-> /valid_sepUnS. Qed.


(* ternary lemmas (occasionally useful) *)

Lemma valid_sep3E (x y z : U) :
        valid (x \+ y \+ z) =
        [&& valid (pval S x \+ pval S y \+ pval S z),
            subsep S (pval S x) (pval S y) &
            subsep S (pval S x \+ pval S y) (pval S z)].
Proof.
apply/idP/idP=>[/[dup] W /validL D|/and3P [W S1 S2]].
- by rewrite -pfjoin // andbCA -valid_sepUnE W andbT valid_sepUnS.
by rewrite valid_sepUnE pfjoin ?W // valid_sepUnE (validL W) S1.
Qed.

Lemma valid_sep3 (x y z : U) :
        valid (x \+ y \+ z) ->
        [/\ valid (pval S x \+ pval S y \+ pval S z),
            subsep S (pval S x) (pval S y) &
            subsep S (pval S x \+ pval S y) (pval S z)].
Proof. by rewrite valid_sep3E=>/and3P. Qed.


(* lemmas for zig-zag interaction of psub and pval *)

Lemma valid_psubUnX (x : V) (y : U) :
        valid (psub S x \+ y) = valid (x \+ pval S y) && subsep S x (pval S y).
Proof. by rewrite -{1}(psub_pval S y) fpV2E. Qed.

Lemma valid_psubXUn (x : U) (y : V) :
        valid (x \+ psub S y) = valid (pval S x \+ y) && subsep S (pval S x) y.
Proof. by rewrite -{1}(psub_pval S x) fpV2E. Qed.

Lemma psubUnX (x : V) (y : U) :
        valid (psub S x \+ y) -> psub S x \+ y = psub S (x \+ pval S y).
Proof. by rewrite valid_psubUnX=>/andP [W H]; rewrite pfjoin //= psub_pval. Qed.

Lemma psubXUn (x : U) (y : V) :
        valid (x \+ psub S y) -> x \+ psub S y = psub S (pval S x \+ y).
Proof. by rewrite valid_psubXUn=>/andP [W H]; rewrite pfjoin //= psub_pval. Qed.

Lemma pvalXUn (x : V) (y : U) :
        valid (psub S x \+ y) -> x \+ pval S y = pval S (psub S x \+ y).
Proof.
by move/[dup]=>W /validL/fpVI [/= V1 V2]; rewrite pfjoin //= pval_psub.
Qed.

Lemma pvalUnX (x : U) (y : V) :
        valid (x \+ psub S y) -> pval S x \+ y = pval S (x \+ psub S y).
Proof. by rewrite joinC=>/pvalXUn <-; rewrite joinC. Qed.


(* injectivity *)

Lemma pval_inj : injective (pval S).
Proof. by move=>x y E; rewrite -(psub_pval S x) E psub_pval. Qed.

Lemma psub_inj (x y : V) : valid (psub S x) -> psub S x = psub S y -> x = y.
Proof.
move/[swap]=>E /[dup]; rewrite {2}E.
case/fpVI=>/= W1 H1 /fpVI [/= W2 H2].
by rewrite -(pval_psub S _ W1 H1) -(pval_psub S _ W2 H2) E.
Qed.

End DerivedLemmas.

Prenex Implicits valid_sepE valid_pvalE valid_pvalEP valid_pvalS valid_psubS 
valid_sepUnE valid_pvalUnE valid_pvalUnS valid_sep3E valid_psubUnX valid_psubXUn 
psubUnX psubXUn pvalXUn pvalUnX pval_inj psub_inj.


(* properties of V propagate to U *)
Section SubPCMPropagation.
Variable U : pcm.

(* if V is tpcm, psub undef isn't valid *)
Lemma psub_undef (V : tpcm) (S : subpcm_struct U V) : ~~ valid (psub S undef).
Proof. by rewrite fpVE /= valid_undef. Qed.

(* if V is cancellative, so is U *)
Lemma subpcm_is_cpcm (V : cpcm) (S : subpcm_struct U V) : cpcm_axiom U.
Proof.
move=>x1 x2 x W E; move: (W) (W).
rewrite {1}E !(valid_sepUnE S)=>/andP [W2 D2] /andP [W1 D1].
move: E; rewrite -(psub_pval S x1) -(psub_pval S x2) -(psub_pval S x).
rewrite -pfjoin // -[R in _ = R]pfjoin //; move/psub_inj.
by rewrite fpVE W1 sepU0 // => /(_ (erefl _))  /(joinKx W1) ->.
Qed.

(* no canonical projection to latch onto, so no generic inheritance *)
(* but subpcm_is_cpcm can be used for any individual type U *)
(*
HB.instance Definition _ (V : cpcm) (S : subpcm_struct U V) :=
  isCPCM.Build (PCM.pack_ (PCM.class U)) (subpcm_is_cpcm S).
*)
End SubPCMPropagation.


(* identity subpcm structure *)
Lemma id_sub_is_subpcm_struct {U : pcm} : subpcm_struct_axiom (@id_sub U). 
Proof. by []. Qed.
HB.instance Definition _ U := 
  isSubPCM_struct.Build U U id_sub id_sub_is_subpcm_struct.
Lemma subsep_id (U : pcm) : subsep (@id_sub U) = relT. Proof. by []. Qed.

(* Composition of subpcm structures *)
Section SubPCMStructCompose.
Variables U V W : pcm.
Variables (X : subpcm_struct U V) (Y : subpcm_struct V W).

Lemma comp_is_subpcm_struct : subpcm_struct_axiom (comp_sub X Y).
Proof.
split=>x/=; first by rewrite !psub_pval.
rewrite /sepx/= pfunit => D /andP [/= H1 H2].
by rewrite !pval_psub // fpVE /= D H1.
Qed.

HB.instance Definition _ := 
  isSubPCM_struct.Build U W (comp_sub X Y) comp_is_subpcm_struct.

Lemma subsep_comp : 
        subsep (comp_sub X Y) = 
        fun y1 y2 => subsep Y y1 y2 && subsep X (psub Y y1) (psub Y y2).
Proof. by []. Qed.

End SubPCMStructCompose.

(***********)
(* SubTPCM *)
(***********)

(* subtpcm structure is a subpcm struct on tpcms *)
(* where pval is further required to preserve undef *)
(* (i.e., pval is tpcm morphism) *)
(* it then follows that psub preserves undef as well *)

Definition subtpcm_struct_axiom (U V : tpcm) (S : subpcm_struct U V) := 
  pval S undef = undef.

HB.mixin Record isSubTPCM_struct (U V : tpcm) 
    S of @SubPCM_struct U V S := {
  subtpcm_struct_subproof : subtpcm_struct_axiom S}.

#[short(type=subtpcm_struct)]
HB.structure Definition SubTPCM_struct (U V : tpcm) := 
  {S of isSubTPCM_struct U V S & @SubPCM_struct U V S}. 

Arguments subtpcm_struct_subproof {U V}.

(* psub preserves undef *)
Lemma psub_is_tpcm_morph (U V : tpcm) (S : subtpcm_struct U V) : 
        tpcm_morph_axiom (psub S).
Proof. 
by rewrite /tpcm_morph_axiom -(subtpcm_struct_subproof S) psub_pval. 
Qed.

(* declare pval/psub to be tpcm morphisms *)
HB.instance Definition _ (U V : tpcm) (S : subtpcm_struct U V) := 
  isTPCM_morphism.Build U V (pval S) (subtpcm_struct_subproof S).
HB.instance Definition _ (U V : tpcm) (S : subtpcm_struct U V) := 
  isTPCM_morphism.Build V U (psub S) (psub_is_tpcm_morph S).

(* identity subtpcm structure *)
HB.instance Definition _ (U : tpcm) := 
  isSubTPCM_struct.Build U U id_sub (erefl undef).

(* composition of subtpcm structures *)
Section SubTPCMStructCompose.
Variables U V W : tpcm.
Variables (X : subtpcm_struct U V) (Y : subtpcm_struct V W).
Lemma comp_is_subtpcm_struct : subtpcm_struct_axiom (comp_sub X Y).
Proof. by rewrite /subtpcm_struct_axiom/pval /= !pfundef. Qed.
HB.instance Definition _ := 
  isSubTPCM_struct.Build U W (comp_sub X Y) comp_is_subtpcm_struct.
End SubTPCMStructCompose.


(*****************************)
(*****************************)
(* SubPCM/TPCM constructions *)
(*****************************)
(*****************************)


(**********************************)
(* Modding out TPCM V by seprel D *)
(**********************************)

(* requires TPCM, because morphisms need undef *)
(* to return when D not satisfied *)

(* xsep is the type of the subpcm *)
(* xsub is the subpcm structure *)
Definition xsepP (V : tpcm) (D : seprel V) (x : V) := 
  valid x && D x Unit \/ x = undef.
Inductive xsep (V : tpcm) (D : seprel V) := 
  ex_sep x of xsepP D x.

(* makes defs opaque to avoid performance penalty *)

Module Type XSepSig.
Parameter valx : forall (V : tpcm) (D : seprel V), xsep D -> V.
Parameter subx : forall (V : tpcm) (D : seprel V), V -> xsep D.
Definition xsub V D := SubStruct (@valx V D) (@subx V D).

(* pcm operation *)
Parameter xsep_valid : forall (V : tpcm) (D : seprel V), xsep D -> bool.
Parameter xsep_unit : forall (V : tpcm) (D : seprel V), xsep D. 
Parameter xsep_unitb : forall (V : tpcm) (D : seprel V), xsep D -> bool.
Parameter xsep_join' : forall (V : tpcm) (D : seprel V), 
  xsep D -> xsep D -> V.
Parameter xsep_join : forall (V : tpcm) (D : seprel V), 
  xsep D -> xsep D -> xsep D.
(* tpcm operations *)
Parameter xsep_undef : forall (V : tpcm) (D : seprel V), xsep D.
Parameter xsep_undefb : forall (V : tpcm) (D : seprel V), xsep D -> bool.

Parameter valxE : forall (V : tpcm) (D : seprel V),
  @valx V D = fun (x : xsep D) => let: ex_sep v _ := x in v.
Parameter subxE : forall (V : tpcm) (D : seprel V),
  @subx V D = fun x =>
  if decP (valid x && D x Unit =P true) is left pf
  then ex_sep (or_introl pf) 
  else ex_sep (or_intror (erefl undef)).
Parameter xsep_validE : forall (V : tpcm) (D : seprel V),
  @xsep_valid V D = fun x => valid (valx x) && D (valx x) Unit.
Parameter xsep_unitP : forall (V : tpcm) (D : seprel V), 
  xsepP D (Unit : V).
Parameter xsep_unitE : forall (V : tpcm) (D : seprel V), 
  @xsep_unit V D = ex_sep (@xsep_unitP V D).
Parameter xsep_unitbE : forall (V : tpcm) (D : seprel V),
  @xsep_unitb V D = fun x => unitb (valx x).
Parameter xsep_joinE' : forall (V : tpcm) (D : seprel V),
  @xsep_join' V D = fun x y =>
  if valid (valx x \+ valx y) && D (valx x) (valx y) 
  then valx x \+ valx y else undef.
Parameter xsep_joinP : forall (V : tpcm) (D : seprel V) x y, 
  xsepP D (@xsep_join' V D x y).
Parameter xsep_joinE : forall (V : tpcm) (D : seprel V),
  @xsep_join V D = fun x y => ex_sep (xsep_joinP x y).
Parameter xsep_undefP : forall (V : tpcm) (D : seprel V), 
  xsepP D undef. 
Parameter xsep_undefE : forall (V : tpcm) (D : seprel V), 
  @xsep_undef V D = ex_sep (@xsep_undefP V D).
Parameter xsep_undefbE : forall (V : tpcm) (D : seprel V), 
  @xsep_undefb V D = fun x => undefb (valx x).
End XSepSig.

Module XSepSubPCMDef : XSepSig. 
Section XSepSubPCMDef.
Variables (V : tpcm) (D : seprel V).

Definition valx (x : xsep D) := let: ex_sep v _ := x in v.
Definition subx (x : V) := 
  if decP (valid x && D x Unit =P true) is left pf
  then ex_sep (or_introl pf) 
  else ex_sep (or_intror (erefl undef)).
Definition xsep_valid x := valid (valx x) && D (valx x) Unit.
Lemma xsep_unitP : xsepP D (Unit : V).
Proof. by rewrite /xsepP valid_unit sep00; left. Qed.
Definition xsep_unit := ex_sep xsep_unitP. 
Definition xsep_unitb x := unitb (valx x).
Definition xsep_join' x y :=
  if valid (valx x \+ valx y) && D (valx x) (valx y) 
  then valx x \+ valx y else undef.
Lemma xsep_joinP x y : xsepP D (xsep_join' x y).
Proof.
rewrite /xsepP /xsep_join'; case: ifP; last by right.
by case/andP=>W /(sepU0 W) ->; rewrite W; left.
Qed.
Definition xsep_join x y := ex_sep (xsep_joinP x y).
Lemma xsep_undefP : xsepP D undef. Proof. by right. Qed.
Definition xsep_undef := ex_sep xsep_undefP.
Definition xsep_undefb (x : xsep D) := undefb (valx x).

Definition valxE := erefl valx.
Definition subxE := erefl subx.
Definition xsub := SubStruct valx subx.
Definition xsep_validE := erefl xsep_valid.
Definition xsep_unitE := erefl xsep_unit.
Definition xsep_unitbE := erefl xsep_unitb.
Definition xsep_joinE' := erefl xsep_join'.
Definition xsep_joinE := erefl xsep_join.
Definition xsep_undefE := erefl xsep_undef.
Definition xsep_undefbE := erefl xsep_undefb.
End XSepSubPCMDef.
End XSepSubPCMDef.

Export XSepSubPCMDef.

Section XSepSubPCM.
Variables (V : tpcm) (D : seprel V).

(* helper lemma *)
Lemma valx_inj (x y : xsep D) : 
        valx x = valx y -> 
        x = y.
Proof. 
case: x y=>x Hx [y Hy]; rewrite !valxE => E.
by subst y; rewrite (pf_irr Hx). 
Qed.

(* unary and binary orthogonality relations *)
Notation orth1 x := (valid x && D x Unit).
Notation orth2 x y := (valid (x \+ y) && D x y). 

Notation xsep_valid := (@xsep_valid V D).
Notation xsep_join := (@xsep_join V D).
Notation xsep_unit := (@xsep_unit V D).
Notation xsep_unitb := (@xsep_unitb V D).
Notation xsep_undef := (@xsep_undef V D).
Notation xsep_undefb := (@xsep_undefb V D).

(* xsep is pcm *)
Lemma xsep_is_pcm : pcm_axiom xsep_valid xsep_join xsep_unit xsep_unitb.
Proof.
have joinC : commutative xsep_join.
- case=>x Hx [y Hy]; apply: valx_inj; rewrite valxE xsep_joinE xsep_joinE'.
  by rewrite joinC; case W: (valid _)=>//=; rewrite -sepC.
split=>[//||[x Hx]|x y||x]. 
- suff joinAC : right_commutative xsep_join.
  - by move=>a b c; rewrite !(joinC a) joinAC. 
  case=>a Ha [b Hb][c Hc]; apply: valx_inj; rewrite valxE.
  rewrite xsep_joinE; do ![rewrite {1}xsep_joinE' !valxE /=]. 
  case Sab: (orth2 a b); case Sac: (orth2 a c); rewrite ?tpcmE //=; last first.
  - case/andP: Sac=>_ Sac; case: andP=>//; case=>W Sacb.
    by rewrite (sepAxx W Sac Sacb) andbT (validLE3 W) in Sab.
  - case/andP: Sab=>_ Sab; case: andP=>//; case=>W Sabc.
    by rewrite (sepAxx W Sab Sabc) andbT (validLE3 W) in Sac.
  case/andP: Sab=>_ Sab; case/andP: Sac=>_ Sac.
  case Sabc: (orth2 (a \+ b) c).
  - case/andP: Sabc=>W Sabc; rewrite sepC (joinAC a c b) W //=.
    by rewrite (sepAxx W Sab Sabc).
  case Sacb: (orth2 (a \+ c) b)=>//.
  case/andP: Sacb=>W Sacb; rewrite sepC (joinAC a b c) W // in Sabc.
  by rewrite (sepAxx W Sac Sacb) in Sabc.
- apply: valx_inj; rewrite !valxE /=.
  rewrite xsep_joinE xsep_unitE xsep_joinE' !{1}valxE.
  rewrite unitL; case: Hx=>[|->]; last by rewrite tpcmE.
  by case/andP=>W E; rewrite sepC ?unitL // W E.
- rewrite xsep_validE xsep_joinE valxE xsep_joinE' !{1}valxE /=. 
  case: ifP; last by rewrite tpcmE.
  by case/andP=>W E; rewrite !(validE2 W) (sepx0 W E).
- by rewrite xsep_validE xsep_unitE valxE valid_unit sep00. 
rewrite xsep_unitbE xsep_unitE; case: x=>x H /=; rewrite valxE.
case: unitbP=>X; constructor; last by case=>/X.
by rewrite X in H *; rewrite (pf_irr H (@xsep_unitP V D)).
Qed.

HB.instance Definition _ : isPCM (xsep D) := 
  isPCM.Build (xsep D) xsep_is_pcm.

(* xsep is tpcm *)
Lemma xsep_is_tpcm : tpcm_axiom xsep_undef xsep_undefb.
Proof.
split=>[/= x||/= x].
- rewrite xsep_undefbE xsep_undefE valxE; case: x=>x H /=.
  case: undefbP=>X; constructor; last by case=>/X.
  by rewrite X in H *; rewrite (pf_irr H (xsep_undefP D)).
- by rewrite pcmE /= xsep_validE xsep_undefE valxE tpcmE.
apply: valx_inj; rewrite xsep_undefE !valxE.
by rewrite /join/= xsep_joinE xsep_joinE' valxE /= !tpcmE.
Qed.

HB.instance Definition _ : isTPCM (xsep D) := 
  isTPCM.Build (xsep D) xsep_is_tpcm.

(* xsep is normal tpcm *)
Lemma xsep_is_normal : normal_tpcm_axiom (xsep D).
Proof. 
case=>x [] H; [left|right].
- by rewrite /valid/= xsep_validE valxE.
by apply/valx_inj; rewrite !valxE /undef /= xsep_undefE.
Qed.

HB.instance Definition _ : isNormal_TPCM (xsep D) := 
  isNormal_TPCM.Build (xsep D) xsep_is_normal.

(* Next, morphisms *)

(* valx is morphism *)
Lemma valx_is_morph : pcm_morph_axiom relT (@valx V D).
Proof.
split=>[|x y]; first by rewrite valxE /Unit /= xsep_unitE.
rewrite {1}/valid /= xsep_validE !valxE /=.
rewrite pcm_joinE /= xsep_joinE xsep_joinE' !valxE.
by case: ifP; rewrite ?tpcmE //; case/andP.
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build (xsep D) V (@valx V D) valx_is_morph.

(* valx is full morphism *)
Lemma valx_is_full_morph : full_pcm_morph_axiom (@valx V D).
Proof. by []. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build (xsep D) V (@valx V D) valx_is_full_morph.

(* valx is normal morphism *)
Lemma valx_is_norm_morph : norm_pcm_morph_axiom (@valx V D).
Proof.
move=>x; rewrite {2}/valid/= xsep_validE.
rewrite !{1}valxE /= => W; split=>//.
by case: x W=>x /= [/andP [->->]|] // ->; rewrite tpcmE.
Qed.

HB.instance Definition _ := 
  isNorm_PCM_morphism.Build (xsep D) V (@valx V D) valx_is_norm_morph.

(* NOTE: valx is *not* binormal morphism as it doesn't preserve separation. *)
(* The subpcm gives new notion of separation that is more stringent *)
(* compared to super-pcm. If valx were binormal, that would imply that *)
(* the new notion isn't more stringent, and thus defeat the purpose *)
(* of the construction. *)
Lemma valx_is_binorm_morph : binorm_pcm_morph_axiom (@valx V D).
Proof.
case=>x Hx [y Hy] /=; rewrite !{1}valxE => W.
rewrite /valid/=/sepx/= xsep_validE /= !{1}valxE /=.
rewrite pcm_joinE /= xsep_joinE /= xsep_joinE' !{1}valxE.
case H : (D x y); first by rewrite !W (sepU0 W H).
rewrite W /=.
Abort.

(* subx is morphism *)
Lemma subx_is_morph : pcm_morph_axiom D (@subx V D).
Proof.
rewrite subxE; split=>[|x y W E].
- apply: valx_inj; rewrite !valxE /Unit /= xsep_unitE; case: eqP=>//=.
  by rewrite valid_unit /= sep00.
case: eqP=>Hx /=; last by rewrite (sep0E W E) (validE2 W) in Hx.
case: eqP=>Hy /=; last by rewrite (sep0E W E) (validE2 W) in Hy.
case: eqP=>H /=; last by rewrite W (sepU0 W E) in H.
rewrite /valid/= xsep_validE pcm_joinE valxE /= xsep_joinE /=.
do ![rewrite {1}xsep_joinE' valxE].
rewrite {1 2}W {1 2}E {1}W {1}(sepU0 W E) /=.
split=>//; apply: valx_inj; rewrite valxE /=. 
by rewrite xsep_joinE' valxE W E.
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build V (xsep D) (subx D) subx_is_morph.

(* subx is binormal morphism *)
Lemma subx_is_binorm_morph : binorm_pcm_morph_axiom (subx D).
Proof.
move=>x y /=.
rewrite /sepx/= subxE {1}/valid/= xsep_validE valxE !pcm_joinE /= xsep_joinE.
case: eqP=>Hx; case: eqP=>Hy; rewrite xsep_joinE' valxE;
case H: (valid (x \+ y) && D x y) Hx Hy;
by rewrite /= ?tpcmE //=; case/andP: H.
Qed.

HB.instance Definition _ := 
  isBinorm_PCM_morphism.Build V (xsep D) (subx D) subx_is_binorm_morph.

(* Next, substructures *)

(* xsub is subpcm *)
Definition xsub := SubStruct (@valx V D) (subx D).

Lemma xsub_is_subpcm_struct : subpcm_struct_axiom xsub.
Proof.
split=>[x|x] //=; last first.
- rewrite /sepx/= subxE valxE => W H.
  by case: eqP=>//=; rewrite W H.   
apply: valx_inj; rewrite valxE subxE /=.
by case: eqP; case: x=>// x []. 
Qed.

HB.instance Definition _ := 
  isSubPCM_struct.Build (xsep D) V xsub xsub_is_subpcm_struct.

Lemma xsub_is_subtpcm_struct : subtpcm_struct_axiom xsub.
Proof. 
rewrite /subtpcm_struct_axiom. 
by rewrite /pval/= /undef/= xsep_undefE valxE.
Qed.

HB.instance Definition _ := 
  isSubTPCM_struct.Build (xsep D) V xsub xsub_is_subtpcm_struct.
End XSepSubPCM.

Lemma psub_undefN (V : tpcm) (D : seprel V) (x : V) : 
        ~~ D x Unit ->
        psub (xsub D) x = undef.
Proof.
move=>X; apply: valx_inj.
rewrite /undef/= xsep_undefE valxE /psub/= subxE /=.
by case: decP=>//; rewrite (negbTE X) andbF.  
Qed.

(*****************************************)
(* Normalize = mod out trivially by relT *)
(*****************************************)

(* removes non-valid elements != undef *)

Definition normalize (U : tpcm) := xsep (@relT U).
Definition norm_sub {U : tpcm} := xsub (@relT U).

(* redeclare structures for normalize, to save on unfolding *)
HB.instance Definition _ (U : tpcm) := 
  Normal_TPCM.on (normalize U).
HB.instance Definition _ (U : tpcm) := 
  SubTPCM_struct.on (@norm_sub U).
(* psub also becomes full morphism *)
HB.instance Definition _ (U : tpcm) := 
  isFull_PCM_morphism.Build U (normalize U) (psub norm_sub) 
     (fun _ _ => erefl _). 

(***************************)
(* Normal product of TPCMs *)
(***************************)

(* product which is immediately normalized *)
(* to remove spurious invalid elements *)
(* that arose out of pairing invalids of one TPCM *)
(* with valids of the other. *)

Section NormalProd.
Variables U V : tpcm.

Definition nprod := normalize (prod U V).
Definition nprod_sub := @norm_sub (prod U V).

Definition nfst : nprod -> U := fst \o pval nprod_sub.
Definition nsnd : nprod -> V := snd \o pval nprod_sub.
Definition npair : U * V -> nprod := psub nprod_sub.

End NormalProd.

Arguments nprod_sub {U V}.
Prenex Implicits nfst nsnd npair nprod_sub.

(* redeclare again *)
HB.instance Definition _ (U V : tpcm) := 
  Normal_TPCM.on (nprod U V). 
HB.instance Definition _ (U V : tpcm) := 
  SubTPCM_struct.on (@nprod_sub U V).

(* redeclare morphisms *)
HB.instance Definition _ (U V : tpcm) := 
  Full_Binorm_TPCM_morphism.on (@npair U V).

(* nfst and nsnd are full by inheritance *)
HB.instance Definition _ (U V : tpcm) := 
  Full_TPCM_morphism.on (@nfst U V).
HB.instance Definition _ (U V : tpcm) := 
  Full_TPCM_morphism.on (@snd U V).

(* but now they are also normal *)
(* though not binormal (as they shouldn't) *)
Lemma nfst_is_norm_pcm_morphism U V : norm_pcm_morph_axiom (@nfst U V).
Proof.
move=>/= x W; split=>//; case: (normalP x) W=>// ->.
by rewrite pfundef valid_undef.
Qed.

HB.instance Definition _ (U V : tpcm) := 
  isNorm_PCM_morphism.Build (nprod U V) U (@nfst U V) 
    (@nfst_is_norm_pcm_morphism U V).

Lemma nsnd_is_norm_pcm_morphism U V : norm_pcm_morph_axiom (@nsnd U V).
Proof.
move=>/= x W; split=>//; case: (normalP x) W=>// ->.
by rewrite pfundef valid_undef.
Qed.

HB.instance Definition _ (U V : tpcm) := 
  isNorm_PCM_morphism.Build (nprod U V) V (@nsnd U V) 
    (@nsnd_is_norm_pcm_morphism U V).

(* lemmas for normal products *)

Lemma nprod_eta (U V : tpcm) (x : nprod U V) : 
        x = npair (nfst x, nsnd x).
Proof. by rewrite -prod_eta /npair psub_pval. Qed.

Lemma nfst_pair (U V : tpcm) (x : U * V) : 
         valid x -> nfst (npair x) = x.1.
Proof. by move=>W; rewrite /nfst /= pval_psub. Qed.

Lemma nsnd_pair (U V : tpcm) (x : U * V) : 
        valid x -> nsnd (npair x) = x.2.
Proof. by move=>W; rewrite /nsnd /= pval_psub. Qed.

Lemma nprodV (U V : tpcm) (x : nprod U V) : 
        valid x = valid (nfst x) && valid (nsnd x).
Proof. by rewrite {1}[x]nprod_eta pfVE. Qed.

Lemma nprodUnV (U V : tpcm) (x y : nprod U V) :
        valid (x \+ y) = valid (nfst x \+ nfst y) && 
                         valid (nsnd x \+ @nsnd U V y).
Proof. by rewrite {1}[x]nprod_eta {1}[y]nprod_eta pfV2E. Qed.


(***********************)
(* Relativized seprels *)
(***********************)

(* Relation S is seprel-relative-to-morphism-f *)
(* if it becomes seprel once composed with f and paired with sep f. *)
(* Useful when sequencing subpcm constructions *)

Definition seprel_on_axiom U V (f : pcm_morph U V) (S : rel V) := 
  [/\ S Unit Unit, 
      forall x y, valid (x \+ y) -> sep f x y -> 
        S (f x) (f y) = S (f y) (f x),
      forall x y, valid (x \+ y) -> sep f x y -> 
        S (f x) (f y) -> S (f x) Unit &
      forall x y z, valid (x \+ y \+ z) -> 
        sep f x y -> sep f (x \+ y) z -> 
        S (f x) (f y) -> S (f x \+ f y) (f z) -> 
        S (f y) (f z) && S (f x) (f y \+ f z)].

(* S is seprel-on-f iff *)
(* relI (sep f) (rel_app S f) is seprel on U *)
Lemma seprel_on_app U V (f : pcm_morph U V) S : 
        seprel_on_axiom f S <-> 
        seprel_axiom (relI (sep f) (rel_app S f)).
Proof.
split=>[[H1 H2 H3 H4]|[/andP [H1 H2 H3 H4 H5]]].
- split=>[|x y W|x y W|x y z W] /=.
  - by rewrite pfunit sep00 H1.
  - rewrite (sepC _ W) /=.
    by case X: (sep f y x)=>//; rewrite H2 // sepC.
  - by case/andP=>X1 X2; rewrite pfunit (sep0E W) // (H3 _ _ W).
  case/andP=>X1 X2 /andP [X3 X4].
  rewrite pfjoin ?(sepAxx W X1 X3) ?(validLE3 W) //=.
  by rewrite H4 // -pfjoin // (validL W).
rewrite /= !pfunit in H2 H4; split=>[//|x y|x y|x y z] W.
- rewrite (sepC (sep f) W) => X. 
  by move: (H3 x y W); rewrite /= (sepC (sep f) W) /= X.
- by move=>X; move: (H4 x y W); rewrite X (sep0E W).
move=>X1 X2 X3 X4; case: (sepAx W X1 X2)=>/= X5 X6.
move: (H5 x y z W); rewrite /= X1 X2 X5 X6 !pfjoin ?(validLE3 W) //=.
by apply.
Qed.

HB.mixin Record isSeprelOn U V (f : pcm_morph U V) (S : rel V) := {
  seprel_on_subproof : seprel_on_axiom f S}.

#[short(type=seprel_on)]
HB.structure Definition SeprelOn U V f := {S of @isSeprelOn U V f S}.

Section Repack.
Variables (U V : pcm) (f : pcm_morph U V) (S : seprel_on f).

Lemma sepon00 : S Unit Unit.
Proof. by case: (@seprel_on_subproof U V f S). Qed.

Lemma seponC x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        S (f x) (f y) = S (f y) (f x).
Proof. by case: (@seprel_on_subproof U V f S)=>_ H _ _; apply: H. Qed.

Lemma seponx0 x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        S (f x) (f y) -> 
        S (f x) Unit.
Proof. by case: (@seprel_on_subproof U V f S)=>_ _ H _; apply: H. Qed.

Lemma seponAx x y z :
        valid (x \+ y \+ z) -> 
        sep f x y -> 
        sep f (x \+ y) z -> 
        S (f x) (f y) -> 
        S (f x \+ f y) (f z) -> 
        S (f y) (f z) * S (f x) (f y \+ f z).
Proof.
case: (@seprel_on_subproof U V f S)=>_ _ _ H W R1 R2 R3 R4.
by rewrite !(andX (H _ _ _ W R1 R2 R3 R4)).
Qed.

(* derived lemmas *)

Lemma sepon0x x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        S (f x) (f y) ->
        S Unit (f y).
Proof.
move=>W sf; rewrite seponC // => Sf.
rewrite sepC //= in sf; rewrite joinC in W.
rewrite -(pfunit f) -(@seponC y) ?pfunit ?unitR ?(validE2 W) //.
- by apply: seponx0 W sf Sf.
by apply: sepx0 W sf.
Qed.

Lemma sepon0E x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        S (f x) (f y) ->
        S (f x) Unit * S (f y) Unit.
Proof.
move=>W sf Sf; rewrite (seponx0 W sf Sf).
rewrite -(pfunit f) seponC ?pfunit ?unitR ?(validE2 W) //.
- by rewrite (sepon0x W sf Sf).
by rewrite (sep0E W sf).
Qed.

Lemma seponAx23_helper x y z :
        valid (x \+ y \+ z) ->
        sep f x y -> 
        sep f (x \+ y) z ->
        S (f x) (f y) -> 
        S (f x \+ f y) (f z) -> 
        ((S (f x) (f z) * S (f z) (f x)) * (S (f y) (f z) * S (f z) (f y))) *
        ((S (f x) (f y \+ f z) * S (f x) (f z \+ f y)) *
         (S (f y) (f x \+ f z) * S (f y) (f z \+ f x))).
Proof.
move=>W s1 s2 S1 S2.
rewrite !(@seponC z) ?(validLE3 W) ?(sepAxx W s1 s2) ?(joinC (f z)) //.
rewrite !(seponAx W s1 s2 S1 S2).
rewrite seponC ?(validLE3 W) // in S1.
rewrite sepC ?(validLE3 W) //= in s1.
rewrite (joinC x) in W s2; rewrite (joinC (f x)) in S2.
by rewrite !(seponAx W s1 s2 S1 S2).
Qed.

Lemma seponxA x y z :
        valid (x \+ (y \+ z)) ->
        sep f y z -> 
        sep f x (y \+ z) -> 
        S (f y) (f z) ->
        S (f x) (f y \+ f z) ->
        S (f x \+ f y) (f z) * S (f x) (f y).
Proof.
move=>W s1 s2 S1 S2; have /= R := (sepxxA W s1 s2, validRE3 W).
rewrite -pfjoin ?R // seponC ?R // pfjoin ?R // in S2. 
rewrite sepC ?R //= in s2.
rewrite -pfjoin ?R // seponC ?R // pfjoin ?R //.
by rewrite !(seponAx23_helper _ s1 s2 S1 S2) ?R.
Qed.

Lemma seponAxx x y z :
        valid (x \+ y \+ z) ->
        sep f x y -> 
        sep f (x \+ y) z ->
        S (f x) (f y) -> 
        S (f x \+ f y) (f z) ->
        (((S (f x) (f y \+ f z) * S (f x) (f z \+ f y)) *
          (S (f y) (f x \+ f z) * S (f y) (f z \+ f x))) *
         ((S (f z) (f x \+ f y) * S (f z) (f y \+ f x)) *
          (S (f y \+ f z) (f x) * S (f z \+ f y) (f x)))) *
        (((S (f x \+ f z) (f y) * S (f z \+ f x) (f y)) *
          (S (f x \+ f y) (f z) * S (f y \+ f x) (f z))) *
         (((S (f x) (f y) * S (f y) (f x)) *
           (S (f x) (f z) * S (f z) (f x))))) *
        (S (f y) (f z) * S (f z) (f y)).
Proof.
move=>W s1 s2 S1 S2; have /= R := (sepAxx W s1 s2, validLE3 W).
move: (seponAx23_helper W s1 s2 S1 S2)=>E; rewrite S1 S2 !E.
rewrite -!pfjoin ?R // -!(@seponC x) ?R // !pfjoin ?R // S1 !E.
rewrite -!pfjoin ?R // !(@seponC z) ?R // !pfjoin ?R //.
rewrite (joinC (f y)) S2.
rewrite -!pfjoin ?R // -!(@seponC y) ?R // !pfjoin ?R //.
by rewrite (joinC (f z)) E.
Qed.

Lemma seponxxA x y z :
        valid (x \+ (y \+ z)) ->
        sep f y z -> 
        sep f x (y \+ z) ->
        S (f y) (f z) -> 
        S (f x) (f y \+ f z) ->
        (((S (f x) (f y \+ f z) * S (f x) (f z \+ f y)) *
          (S (f y) (f x \+ f z) * S (f y) (f z \+ f x))) *
         ((S (f z) (f x \+ f y) * S (f z) (f y \+ f x)) *
          (S (f y \+ f z) (f x) * S (f z \+ f y) (f x)))) *
        (((S (f x \+ f z) (f y) * S (f z \+ f x) (f y)) *
          (S (f x \+ f y) (f z) * S (f y \+ f x) (f z))) *
         (((S (f x) (f y) * S (f y) (f x)) *
           (S (f x) (f z) * S (f z) (f x))))) *
        (S (f y) (f z) * S (f z) (f y)).
Proof.
move=>W s1 s2 S1 S2; have /= R := (sepxxA W s1 s2, validRE3 W).
rewrite -pfjoin ?R // seponC // pfjoin ?R // in S2.
rewrite sepC //= in s2; rewrite joinC in W.
rewrite !(seponAx23_helper W s1 s2 S1 S2).
by rewrite !(seponAxx W s1 s2 S1 S2).
Qed.

Lemma seponU0 x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        S (f x) (f y) ->
        S (f x \+ f y) Unit.
Proof.
move=>W s1 S1; rewrite -(pfunit f).
rewrite seponAxx ?pfunit ?unitL //.
- by rewrite sepC ?unitL ?(validL W) ?(sepx0 W s1).
rewrite seponC // in S1; rewrite sepC //= in s1; rewrite joinC in W.
by apply: (@sepon0x y).
Qed.

Lemma sepon0U x y : 
        valid (x \+ y) -> 
        sep f x y -> 
        S (f x) (f y) ->
        S Unit (f x \+ f y).
Proof. 
move=>W s1 S1.
rewrite -(pfunit f) -pfjoin // seponC ?unitL ?(sep0U W s1) //.
by rewrite pfjoin ?pfunit ?seponU0.
Qed.

End Repack.


(* if f is full tpcm morphism *)
(* S is seprel-on-f iff (S o f) is seprel on U *)
Lemma seprel_on_full U V (f : full_pcm_morph U V) S : 
        seprel_on_axiom f S <-> 
        seprel_axiom (rel_app S f).
Proof. 
rewrite seprel_on_app; apply/sepXEQ=>x y W. 
by rewrite /relI /= pfSE.
Qed.

Lemma seprel_on_id (U : pcm) (S : rel U) : 
        seprel_on_axiom idfun S <-> 
        seprel_axiom S.
Proof. by rewrite seprel_on_full; apply/sepXEQ. Qed.

(* S is seprel-on-f iff (S o f) is seprel on subpcm U/(sep f) *)
Lemma seprel_on_pval (U : tpcm) V (f : pcm_morph U V) S : 
        seprel_on_axiom f S <->
        seprel_axiom (rel_app S (f \o pval (xsub (sep f)))).
Proof.
set xf := (xsub (sep f)).
split; case=>/= H1 H2 H3 H4.
- split=>[|x y W|x y W|x y z W /= X1 X2] /=.
  - by rewrite !pfunit.
  - by case/(valid_sepUn xf): W=>W /(H2 _ _ W). 
  - by rewrite !pfunit; case/(valid_sepUn xf): W=>W /(H3 _ _ W).  
  case: (valid_sepUn xf W)=>Wxyz Sxyz.  
  case: (valid_sepUn xf (validL W))=>Wxy Sxy.
  case: (valid_sepUn xf (validAR W))=>Wyz Syz. 
  rewrite !pfjoin ?(validLE3 W) //=.
  rewrite H4 ?pfV3 // -!pfjoin ?(validLE3 W) //=. 
  by rewrite pfjoin ?(validLE3 W).
rewrite pfunit in H1 H3.
split=>[|x y W X|x y W X|x y z W X1 X2]. 
- by rewrite pfunit in H1.
- rewrite -(pval_psub xf x) ?(sep0E W X,validL W) //.
  rewrite -(pval_psub xf y) ?(sep0E W X,validR W) //.
  by apply/H2/pfV2.
- rewrite -(pval_psub xf x) ?(sep0E W X,validL W) //.
  rewrite -(pval_psub xf y) ?(sep0E W X,validR W) //. 
  by move/H3; rewrite pfunit; apply; apply: (pfV2 (psub xf)).
rewrite -!pfjoin ?(sepAxx W X1 X2,validLE3 W) //.
rewrite -(pval_psub xf x) ?(sep0E _ X1,validLE3 W) //.
rewrite -(pval_psub xf y) ?(sep0E _ X1,validLE3 W) //.
rewrite -(pval_psub xf z) ?(sep0E _ X2,validLE3 W) //.
rewrite -!(pfjoin (pval xf)) ?(pfV2,sepAxx W X1 X2,validLE3 W) //.
by apply/H4/pfV3.
Qed.

(* when the morphism is restriction of idfun with seprel K *)
(* then S is seprel alongside K *)
Lemma seprel_with_on (U : tpcm) (K : seprel U) (S : rel U) : 
        seprel_on_axiom (res idfun K) S <->
        seprel_axiom (relI K S).
Proof.
rewrite seprel_on_app; apply/sepXEQ=>x y V. 
rewrite /sepx/= /res/= andbT.
by case X: (K x y)=>//=; rewrite !(sep0E _ X).
Qed.

Notation "'seprel_with' K" := (seprel_on (res idfun K))
  (at level 1, format "'seprel_with' K").

(* Every seprel is trivially seprel_on idfun morphism *)
Section SeprelOnIdCoercion.
Variables (U : pcm) (S : seprel U).
(* dummy name to enable inheritance *)
Definition eta_rel : rel U := fun x y => S x y.
Lemma seprel_is_seprelonid : seprel_on_axiom idfun eta_rel.
Proof. by apply/seprel_on_id/seprel_subproof. Qed.
HB.instance Definition _ := 
  isSeprelOn.Build U U idfun eta_rel seprel_is_seprelonid.
Definition seprel_on_idfun : seprel_on idfun := eta_rel.
End SeprelOnIdCoercion.

Coercion seprel_on_idfun : seprel >-> seprel_on.

(* naming the completion seprel for specific case *)
(* of seprel_on relations where the morphism is full *)
Section SeprelOnFull.
Variables (U V : pcm) (f : full_pcm_morph U V) (S : seprel_on f).
Definition onsep := rel_app S f.
Lemma onsep_is_seprel : seprel_axiom onsep.
Proof. by apply/seprel_on_full/seprel_on_subproof. Qed.
HB.instance Definition _ := 
  isSeprel.Build U onsep onsep_is_seprel.
End SeprelOnFull.

(* trivially true seprel is seprel_on for any morphism *)

Lemma relT_is_on U V (f : pcm_morph U V) : seprel_on_axiom f relT.
Proof. by []. Qed.

HB.instance Definition _ U V (f : pcm_morph U V) := 
  isSeprelOn.Build U V f relT (relT_is_on f).

(* conjunction of seprel-on's is seprel-on *)
Section SepOnI.
Variables (U V : pcm) (f : pcm_morph U V) (X Y : seprel_on f).

Lemma relI_is_seprelon : seprel_on_axiom f (relI X Y).
Proof.
split=>[|x y W s|x y W s|x y z W s1 s2] /=.
- by rewrite !sepon00.
- by rewrite !(seponC _ W s).
- by case/andP; do ![move/(seponx0 W s) ->].
case/andP=>X1 Y1 /andP [X2 Y2].
by rewrite !(seponAxx W s1 s2 X1 X2) !(seponAxx W s1 s2 Y1 Y2).
Qed.

HB.instance Definition _ := 
  isSeprelOn.Build U V f (relI X Y) relI_is_seprelon.
End SepOnI.

(* 3-way conjunction *)
Section SepOn3I.
Variables (U V : pcm) (f : pcm_morph U V) (X Y Z : seprel_on f).

Lemma rel3I_is_seprelon : seprel_on_axiom f (rel3I X Y Z).
Proof.
split=>[|x y W s|x y W s|x y z W s1 s2] /=.
- by rewrite !sepon00.
- by rewrite !(seponC _ W s).
- by case/and3P; do ![move/(seponx0 W s) ->]. 
case/and3P=>X1 Y1 Z1 /and3P [X2 Y2 Z2].
by rewrite !(seponAxx W s1 s2 X1 X2, seponAxx W s1 s2 Y1 Y2, 
   seponAxx W s1 s2 Z1 Z2).
Qed.

HB.instance Definition _ := 
  isSeprelOn.Build U V f (rel3I X Y Z) rel3I_is_seprelon.
End SepOn3I.

(* 4-way conjunction *)
Section SepOn4I.
Variables (U V : pcm) (f : pcm_morph U V) (X Y Z W : seprel_on f).

Lemma rel4I_is_seprelon : seprel_on_axiom f (rel4I X Y Z W).
Proof.
split=>[|x y VV s|x y VV s|x y z VV s1 s2] /=.
- by rewrite !sepon00.
- by rewrite !(seponC _ VV s). 
- by case/and4P; do ![move/(seponx0 VV s) ->].
case/and4P=>X1 Y1 Z1 W1 /and4P [X2 Y2 Z2 W2].
by rewrite !(seponAxx VV s1 s2 X1 X2, seponAxx VV s1 s2 Y1 Y2, 
             seponAxx VV s1 s2 Z1 Z2, seponAxx VV s1 s2 W1 W2).
Qed.

HB.instance Definition _ := 
  isSeprelOn.Build U V f (rel4I X Y Z W) rel4I_is_seprelon.
End SepOn4I.

(*******************)
(* Local functions *)
(*******************)

(* Unlike morphisms which operate over a single PCM element *)
(* local functions operate over a pair (self, other) *)
(* and then have to support a form of framing, i.e., moving from other *)
(* to self. I haven't quite yet found a need to develop their theory *)
(* but, they could be something we can call "bimorphisms" *)

(* Transitions should fit into this category of local functions *)

Definition local_fun (U : pcm) (f : U -> U -> option U) :=
  forall p x y r, valid (x \+ (p \+ y)) -> f x (p \+ y) = Some r ->
                  valid (r \+ p \+ y) /\ f (x \+ p) y = Some (r \+ p).

Lemma localV U f x y r :
        @local_fun U f -> valid (x \+ y) -> f x y = Some r -> valid (r \+ y).
Proof. by move=>H V E; move: (H Unit x y r); rewrite unitL !unitR; case. Qed.

Lemma idL (U : pcm) : @local_fun U (fun x y => Some x).
Proof. by move=>p x y _ V [<-]; rewrite -joinA. Qed.

(********************)
(* Global functions *)
(********************)

(* given function over two arguments, make it global *)
(* by making it operate over the join *)

Definition glob (U : pcm) R (f : U -> U -> R) := 
  fun x y => f (x \+ y) Unit.
Arguments glob {U R} f x y /.

(*******************)
(* Local relations *)
(*******************)

(* Local relations are needed at some places *)
(* but are weaker than separating relations *)
(* For example, separating relation would allow moving p from y to x *)
(* only if R p y; this is the associativity property *)
(* of seprels, and is essential for the subPCM construction *)
(* But here we don't require that property, because we won't be *)
(* modding out U by a local rel to obtain a subPCM *)
(* Also, we don't require any special behavior wrt unit. *)
(* And no commutativity (for now) *)
(* Also, its sometimes useful to have a condition under *)
(* which the relation is local *)
(* In practice, it frequently happens that some relation is a seprel *)
(* only if some other seprel already holds. Thus, it makes sense to *)
(* consider locality under a binary condition too. *)

(* Local rel is the main concept *)
Definition local_rel (U : pcm) (R : U -> U -> Prop) (cond : U -> Prop) :=
  forall p x y, cond (x \+ p \+ y) -> R x (p \+ y) -> R (x \+ p) y.


