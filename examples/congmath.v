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

From HB Require Import structures.
From Coq Require Import Recdef Setoid ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype choice ssrnat seq bigop fintype finfun.
From pcm Require Import options prelude ordtype finmap pred seqext.

(**********************)
(* Congruence closure *)
(**********************)

(* Background mathematics for the verification of the *)
(* Barcelogic Congruence Closure algorithm. *)
(* Described in the POPL10 paper: *)
(* Structure the verification of heap-manipulating programs *)
(* by Nanevski, Vafeiadis and Berdine *)

(* This file contains the proofs of the mathematical properties *)
(* needed for the verification. The implementation and the *)
(* proofs of the actual stateful programs is in the *)
(* accompanying file congprog.v *)

(**************************)
(* Constants with arities *)
(**************************)

Inductive constant : Set := const_with_arity of nat & nat.

(* constants are an equality type *)
Definition eqcnst (c1 c2 : constant) : bool :=
  match c1, c2 with
  | const_with_arity s1 n1, const_with_arity s2 n2 => 
    (s1 == s2) && (n1 == n2)
  end.

Lemma eqconstantP : Equality.axiom eqcnst.
Proof.
move=>[s1 n1][s2 n2] /=.
do ![case: eqP=>/=[->|H]; last by apply: ReflectF; case].
by apply: ReflectT.
Qed.

HB.instance Definition _ := hasDecEq.Build constant eqconstantP.

(* constants are a countable type *)

Definition tagconst (p : constant) :=
  let: const_with_arity s n := p in @Tagged nat s (fun _ => nat) n.

Definition consttag (u : {i : nat & nat}) :=
  const_with_arity (tag u) (tagged u).

Lemma tagconstK : cancel tagconst consttag.
Proof. by case. Qed.

Lemma consttagK : cancel consttag tagconst.
Proof. by case. Qed.

HB.instance Definition _ := Countable.copy constant (can_type tagconstK). 

(***********************************************************)
(* The symbols are a predetermined finite set of constants *)
(***********************************************************)

(* Given sequences s, symb s is the type of elements of s. *)
(* One could use seq_sub from fintype.v here, and just set *)
(* Definition symb (s : seq constant) := seq_sub s. *)
(* However, this is expensive in terms of universes, *)
(* as it forces symb to be Type, not Set. *)
(* Thus, it's best here to roll out a bespoke fintype structure *)
(* copying relevant code from seq_sub from fintype.v *)
(* but setting universe to Set from the beginning. *)

Record symb (s : seq constant) : Set := 
  SeqSymb {symb_val : constant; 
           symb_valP : in_mem symb_val (@mem constant _ s)}.

#[warning="-projection-no-head-constant"]
HB.instance Definition _ s := [isSub for (@symb_val s)]. 
HB.instance Definition _ s := [Equality of symb s by <:].
Definition symb_enum s : seq (symb s) := undup (pmap insub s).
Lemma mem_symb_enum s x : x \in symb_enum s.
Proof. by rewrite mem_undup mem_pmap -valK map_f ?symb_valP. Qed.
Lemma val_symb_enum s : uniq s -> map val (symb_enum s) = s.
Proof.
move=> Us; rewrite /symb_enum undup_id ?pmap_sub_uniq //.
rewrite (pmap_filter (insubK _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.
Definition symb_pickle s x := index x (symb_enum s).
Definition symb_unpickle s n := nth None (map some (symb_enum s)) n.
Lemma symb_pickleK s : pcancel (@symb_pickle s) (@symb_unpickle s).
Proof.
rewrite /symb_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_symb_enum.
Qed.
Definition symb_isCountable s := isCountable.Build (symb s) (@symb_pickleK s).
Fact symb_axiom s : Finite.axiom (symb_enum s).
Proof. exact: Finite.uniq_enumP (undup_uniq _) (@mem_symb_enum s). Qed.
Definition symb_isFinite s := isFinite.Build (symb s) (@symb_axiom s).
HB.instance Definition _ s := [Choice of symb s by <:].
HB.instance Definition _ s : isCountable (symb s) := symb_isCountable s.
HB.instance Definition _ s : isFinite (symb s) := symb_isFinite s.
HB.instance Definition symb_ord_mix s := 
  isOrdered.Build (symb s) (fintype_is_ordtype (symb s)). 
(* manual canonical declaration, as HB fails to declare it *)
Canonical symb_ordType s : ordType :=
  Ordered.Pack (sort:=symb s) (Ordered.Class (symb_ord_mix s)).

(****************************)
(* Expressions over symbols *)
(****************************)

(* Consequently, expressions must be Type, not Set *)
Inductive exp s : Set := const of symb s | app of exp s & exp s.

(* expressions are an equality type *)
Fixpoint eqexp s (e1 e2 : exp s) {struct e1} : bool :=
  match e1, e2 with
    | const c1, const c2 => c1 == c2
    | app e1 e2, app e3 e4 => (eqexp e1 e3) && (eqexp e2 e4)
    | _, _ => false
  end.

Lemma eqexpP s : Equality.axiom (@eqexp s).
Proof.
elim=>[c1|e1 IH1 e2 IH2][c2|e3 e4] /=; try by apply: ReflectF.
- case: eqP=>[->|H]; last by apply: ReflectF; case.
  by apply: ReflectT.
case: IH1=>[->|H]; last by apply: ReflectF; case.
case: IH2=>[->|H]; last by apply: ReflectF; case.
by apply: ReflectT.
Qed.

HB.instance Definition _ s := hasDecEq.Build (@exp s) (@eqexpP s).

(****************************************)
(* Congruence relations over expression *)
(****************************************)

(* R is monotone if it is preserved by application *)
Section Congruence.
Variable s : seq constant.
Notation symb := (symb s).
Notation exp := (exp s).

Notation rel_exp := (Pred (exp*exp)).

Definition Reflexive (r : rel_exp) := 
  forall x, (x, x) \In r.
Definition Symmetric (r : rel_exp) := 
  forall x y, (x, y) \In r -> (y, x) \In r.
Definition Transitive (r : rel_exp) := 
  forall y x z, (x, y) \In r -> (y, z) \In r -> (x, z) \In r.
Definition Equivalence (r : rel_exp) := 
  Reflexive r /\ Symmetric r /\ Transitive r.
Definition Antisymmetric (r : rel_exp) := 
  forall x y, (x, y) \In r -> (y, x) \In r -> x = y.

Definition monotone (R : rel_exp) : Prop :=
  forall f1 f2 e1 e2, (f1, f2) \In R -> 
    (e1, e2) \In R -> (app f1 e1, app f2 e2) \In R.

Definition congruence (R : rel_exp) := Equivalence R /\ monotone R.

Definition refl_cong (R : rel_exp) : congruence R -> Reflexive R.
Proof. by move=>[[]]. Qed.

Definition sym_cong (R : rel_exp) : congruence R -> Symmetric R.
Proof. by move=>[][_][]. Qed.

Definition trans_cong (R : rel_exp) : congruence R -> Transitive R.
Proof. by move=>[][_][]. Qed.

Definition mono_cong (R : rel_exp) : congruence R -> monotone R.
Proof. by move=>[[]]. Qed.

Definition closure (R : rel_exp) : rel_exp :=
  [Pred e1 e2 | forall C, R ~> C -> congruence C -> (e1, e2) \In C].

Lemma cong_clos (R : rel_exp) : congruence (closure R).
Proof.
do 3?split.
- by move=>x T H1 H2; apply: refl_cong.
- by move=>e1 e2 H C H1 H2; apply: sym_cong=>//; apply: H.
- move=>x y z H1 H2 C H3 H4.
  by apply: trans_cong (H1 C H3 H4) (H2 C H3 H4).
move=>f1 f2 e1 e2 H1 H2 C H3 H4.
by apply: mono_cong (H1 C H3 H4) (H2 C H3 H4).
Qed.

Hint Resolve cong_clos : core.

Lemma reflC (R : rel_exp) : Reflexive (closure R).
Proof. by apply: refl_cong. Qed.

Lemma symC (R : rel_exp) : Symmetric (closure R).
Proof. by apply: sym_cong. Qed.

Lemma transC (R : rel_exp) : Transitive (closure R).
Proof. by apply: trans_cong. Qed.

Lemma monoC (R : rel_exp) : monotone (closure R).
Proof. by apply: mono_cong. Qed.

Hint Resolve reflC symC : core.

(* lemmas about closure *)

Lemma closE (R1 R2 : rel_exp) : 
        R1 <~> R2 -> 
        closure R1 <~> closure R2.
Proof.
suff H: forall R1 R2, R1 <~> R2 -> closure R1 ~> closure R2.
- by split; apply: H; [| symmetry].
move=>{}R1 {}R2 H [x y] H1 C H2 H3; apply: H1 H3.
by rewrite H.
Qed.

Add Morphism closure with
  signature Morphisms.respectful (fun e1 e2 => e1 <~> e2) 
   (fun e1 e2 => e1 <~> e2) as closure_morph.
Proof. by apply: closE. Qed.

Lemma clos_clos (R Q : rel_exp) : 
        closure (closure R \+p Q) <~> closure (R \+p Q).
Proof.
case=>e1 e2; split=>H1 C H2 H3; apply: H1 =>// [[x y]] H4.
- by case: H4=>H4; [apply: H4=>// [[x1 y1]] H4|]; apply: H2; [left | right].
case: H4=>H4; apply: H2; [left | right]=>//.
by move=>C0 H5 _; apply: H5.
Qed.

Lemma clos_idemp (R : rel_exp) : 
        closure (closure R) <~> closure R.
Proof. by rewrite -(orr0 (closure R)) clos_clos !orr0. Qed.

Lemma closKR (R1 R2 K : rel_exp) :
        closure R1 <~> closure R2 -> 
        closure (K \+p R1) <~> closure (K \+p R2).
Proof.
move=>H.
by rewrite 2!(orrC K) -(clos_clos R1) -(clos_clos R2) H.
Qed.

Lemma closRK (R1 R2 K : rel_exp) :
        closure R1 <~> closure R2 -> 
        closure (R1 \+p K) <~> closure (R2 \+p K).
Proof. by rewrite 2!(orrC _ K); apply: closKR. Qed.

Lemma closI (R : rel_exp) : R ~> closure R.
Proof. by move=>[x y] H1 T H2 H3; apply: H2. Qed.

(* absorption and closure *)
Lemma closKA (K R : rel_exp) :
        closure R <~> closure (K \+p R) <-> K ~> closure R.
Proof.
rewrite -orrAb; split=>[->|].
- by rewrite orrAb; move=>[x y] H; apply: closI; left.
by rewrite (orrC _ R) -clos_clos orrC=><-; rewrite clos_idemp.
Qed.

Lemma closAK (K R : rel_exp) :
        closure R <~> closure (R \+p K) <-> K ~> closure R.
Proof. by rewrite orrC closKA. Qed.

Lemma clos_or (R1 R2 R : rel_exp) :
        closure R1 ~> closure R -> closure R2 ~> closure R ->
        closure (R1 \+p R2) ~> closure R.
Proof.
rewrite -!closAK !(orrC R) !clos_clos -!(orrC R) => H1 H2.
by rewrite H1 -clos_clos H2 clos_clos orrAC orrA.
Qed.

Lemma sub_closKR (R1 R2 K : rel_exp) :
        (closure R1 ~> closure R2) -> 
        closure (K \+p R1) ~> closure (K \+p R2).
Proof.
rewrite -!closAK=>H.
rewrite -(orrC (closure _)) clos_clos orrAC -orrA orrI.
rewrite orrC -clos_clos H clos_clos.
rewrite -(orrC (closure _)) orrA clos_clos.
by rewrite orrC.
Qed.

Lemma sub_closRK (R1 R2 K : rel_exp) :
        (closure R1 ~> closure R2) -> 
        closure (R1 \+p K) ~> closure (R2 \+p K).
Proof. by move=>H; rewrite -!(orrC K); apply: sub_closKR. Qed.

Lemma sub_closI (R1 R2 : rel_exp) :
        R1 ~> R2 -> closure R1 ~> closure R2.
Proof.
rewrite -orrAb -closAK -(orrC (closure _)) clos_clos => ->.
by rewrite (orrC R2) -orrA orrI.
Qed.

(* relation that only relates the constant symbols *)
(* with their image under a function *)
Definition graph (f : symb -> exp) : rel_exp :=
  [Pred e1 e2 | (e1, e2) \in image (fun s => (const s, f s)) predT].

(* Equations in canonical form, as required by the congruence closure     *)
(* algorithm. An equation is in canonical form if it is an equation       *)
(* between two constants, or between a constant and an application of two *)
(* constants. *)

Inductive Eq : Type := simp_eq of symb & symb | comp_eq of symb & symb & symb.

(* equations are an equality type *)
Definition eqEq (eq1 eq2 : Eq) : bool :=
  match eq1, eq2 with
    simp_eq c1 c2, simp_eq d1 d2 => (c1 == d1) && (c2 == d2)
  | comp_eq c c1 c2, comp_eq d d1 d2 => (c == d) && (c1 == d1) && (c2 == d2)
  | _, _ => false
  end.

Lemma eqEqP : Equality.axiom eqEq.
Proof.
move=>[c1 c2|c c1 c2][d1 d2|d d1 d2] /=; try by [apply: ReflectF];
do ![case: eqP=>[->|H]; last by apply: ReflectF; case];
by apply: ReflectT.
Qed.

HB.instance Definition _ := hasDecEq.Build Eq eqEqP.

(* interpreting equations as relations *)
Definition eq2rel (eq : Eq) : rel_exp :=
  match eq with
  | simp_eq c1 c2 => 
      [Pred x y | x = const c1 /\ y = const c2]
  | comp_eq c c1 c2 => 
      [Pred x y | x = const c /\ y = app (const c1) (const c2)]
  end.

Fixpoint eqs2rel (eqs : seq Eq) : rel_exp :=
  if eqs is hd::tl then eq2rel hd \+p eqs2rel tl else Pred0.

(* Coercing triples of symbols into equations *)
Definition symb2eq (t : symb*symb*symb) :=
  let: (c, c1, c2) := t in comp_eq c c1 c2.

(* inverting relations equations represented as triples *)
Definition invert (x y : exp) (ss : seq (symb*symb*symb)) :
  (x, y) \In eqs2rel (map symb2eq ss) <->
  exists c c1 c2,
    [/\ x = const c, y = app (const c1) (const c2) & 
        (c, c1, c2) \in ss].
Proof.
split.
- elim: ss=>[|[[c c1] c2] ss IH] /=; first by case.
  case; first by case=>->->; exists c, c1, c2; rewrite inE eq_refl.
  move/IH=>[d][d1][d2][->->H].
  by exists d, d1, d2; rewrite inE H orbT.
elim: ss=>[|[[c c1] c2] ss IH] [d][d1][d2][H1 H2] //.
rewrite inE; case/orP; first by rewrite H1 H2; case/eqP=>->->->; left.
move=>T; apply: sub_orr; apply: IH.
by exists d, d1, d2; rewrite H1 H2 T.
Qed.

(* One must also keep track of pending equations. These are equations     *)
(* placed into the input list, but have not yet been processed and        *)
(* inserted into the data structure for computing the relation.  The      *)
(* pending equations are either simple equations of the form c1 = c2 or   *)
(* are composite ones of the form (c = c1 c2, d = d1 d2), where c1, d1    *)
(* and c2, d2 are already congruent (and their congruence is encoded by   *)
(* the internals of the data structure. We next define the type of        *)
(* pending equations.                                                     *)

Inductive pend : Type :=
  simp_pend of symb & symb
| comp_pend of (symb * symb * symb) & (symb * symb * symb).

(* pend is an equality type *)
Definition eq_pend (eq1 eq2 : pend) : bool :=
  match eq1, eq2 with
    simp_pend c1 c2, simp_pend c3 c4 => (c1 == c3) && (c2 == c4)
  | comp_pend t1 t2, comp_pend t3 t4 => (t1 == t3) && (t2 == t4)
  | _, _ => false
  end.

Lemma eq_pendP : Equality.axiom eq_pend.
Proof.
move=>[c1 c2|t1 t2][d1 d2|s1 s2] /=; try by [apply: ReflectF];
do ![case: eqP=>[->|H]; last by apply: ReflectF; case];
by apply: ReflectT.
Qed.

HB.instance Definition _ := hasDecEq.Build pend eq_pendP.

(* pending equations are interpreted as follows for *)
(* purposes of computing the relations they encode  *)
Definition pend2eq (p : pend) :=
  match p with
    simp_pend c c1 => simp_eq c c1
  | comp_pend (c, c1, c2) (d, d1, d2) => simp_eq c d
  end.

(********************************************************************)
(* The definition of the data structures involved in the algorithm. *)
(********************************************************************)

Record data : Type :=
  Data {(* An array, indexed by symbs, containing for each symb its *)
        (* current representative (for the relation obtained by the *)
        (* equations that have been processed). *)
        rep : {ffun symb -> symb};
        (* For each representative, the list of all symbs in its class. *)
        (* Essentially, the inversion of rep *)
        class : {ffun symb -> seq symb};
        (* For each representative r, the list of eqs c = c1 c2, such *)
        (* that r is the representative of c1 or of c2 or of both. *)
        use : {ffun symb -> seq (symb * symb * symb)};
        (* For all pairs of reprentatives r1 r2, lookup r1 r2 is some input   *)
        (* equation c = c1 c2 such that r1, r2 are representatives of c1, c2. *)
        (* If lookup r1 r2 = None, such an equation doesn't exist.            *)
        lookup : {finMap symb*symb -> symb*symb*symb};
        (* The list of equations pending to be processed *)
        pending : seq pend}.

(* We can collect the representatives of all the symbols into a finite list. *)
(* We remove the duplicates. *)
Definition reps D : seq symb := undup (map (rep D) (enum predT)).

Lemma uniq_reps D : uniq (reps D).
Proof. by rewrite undup_uniq. Qed.

Hint Resolve uniq_reps : core.

Lemma rep_in_reps D a : rep D a \in reps D.
Proof. by move=>*; rewrite mem_undup; apply: map_f; rewrite mem_enum. Qed.

Hint Resolve rep_in_reps : core.

(* The symbols and their representatives are a base case in defining the closure *)
Definition rep2rel D := graph (fun x => const (rep D x)).

Lemma clos_rep D R a : (const a, const (rep D a)) \In closure (rep2rel D \+p R).
Proof.
apply: (@closI _ (const a, const (rep D a))); apply: sub_orl; rewrite /= /rep2rel /graph /=.
by rewrite mem_map /= ?mem_enum // => x1 x2 [->].
Qed.

Hint Resolve clos_rep : core.

(* relation defined by the lookup table *)
Definition lookup_rel D : rel_exp :=
  [Pred e1 e2 |
    exists a b c c1 c2,
    [/\ e1 = app (const a) (const b),
       a \in reps D, b \in reps D,
       fnd (a, b) (lookup D) = Some (c, c1, c2) & e2 = const (rep D c)]].

(* inverting relations equations represented as triples *)
Lemma invert_look D (x y : exp) :
  (x, y) \In lookup_rel D <->
  exists a b c c1 c2,
    [/\ x = app (const a) (const b),
        y = const (rep D c),
        a \in reps D, b \in reps D &
        fnd (a, b) (lookup D) = Some (c, c1, c2)].
Proof.
split; move=>[a][b][c][c1][c2][H1 H2 H3 H4 H5];
by exists a, b, c, c1, c2.
Qed.

(* The relation defined by the data structure is the following *)
Definition CRel D := closure (rep2rel D \+p
                              lookup_rel D \+p
                              eqs2rel (map pend2eq (pending D))).

Lemma cong_rel D : congruence (CRel D).
Proof. by move=>*; apply: cong_clos. Qed.

Hint Resolve cong_rel : core.

Lemma clos_rel D R a : (const a, const (rep D a)) \In closure (CRel D \+p R).
Proof. by rewrite /CRel clos_clos orrA; apply: clos_rep. Qed.


(*******************************************)
(* Congruence Closure Code and Termination *)
(*******************************************)

(* termination metric is the number of equations in the use and pending lists *)
Definition metric (D : data) : nat :=
  size (pending D) + \sum_(c <- reps D) (size (use D c)).

(* joining two congruence classes *)
(* if we got an equation a' = b', we need to join the equivalence *)
(* class of a' into that of b' *)
Definition join_class (D : data) (a' b' : symb) : data :=
  Data (* the symbols represented by a' are now represented by b' *)
       (finfun ((fun r => if r == a' then b' else r) \o rep D))
       (* the class of a' is emptied, and moved into the class of b' *)
       (finfun (fun r => if r == a' then [::] else
                   if r == b' then (rev (class D a') ++ class D b') else
                     class D r))
       (use D)
       (lookup D)
       (pending D).

(* join_class removes a' from the representatives, but everything else remains the same *)
Lemma join_class_perm (D : data) (a' b' : symb) :
        a' != b' -> b' \in reps D ->
          perm_eq (reps (join_class D a' b'))
                  (filter (predC1 a') (reps D)).
Proof.
have ffun_comp: forall (A B C : finType) (f1 : B -> A) (f2 : C -> B),
  finfun (f1 \o f2) =1 f1 \o f2 :> (C -> A).
- by move=>A B C f1 f2 x; rewrite ffunE.
have maps_ffun_comp : forall (A B C : finType) (f1 : B -> C) (f2 : A -> B) s,
     map (finfun (comp f1 f2)) s = map f1 (map f2 s).
- by move=>A B C f1 f2 ss; elim: ss=>[|x ss IH] //=; rewrite IH /= ffunE.
move=>H H2.
apply: uniq_perm; [|apply: filter_uniq|]; try by rewrite undup_uniq.
move: H2.
rewrite /join_class /reps /= maps_ffun_comp mem_undup filter_undup.
set f := (fun e => if e == a' then b' else e).
have L1 : forall x, a' != f x.
- rewrite /f=>x; case: (x =P a') H=>//.
  by case: (a' =P x)=>//->.
have L2 : forall x, x != a' -> x = f x.
- by rewrite /f=>x; case: eqP.
rewrite eq_sym in H.
move: (map _ _)=>ss H1 x.
rewrite !mem_undup.
case E1 : (x == a').
- rewrite (eqP E1) mem_filter /= eq_refl /=.
  elim: ss {H1} =>// t ss H1.
  by rewrite inE /= (negbTE (L1 t)) H1.
case E2 : (x == b').
- rewrite mem_filter /= E1 (eqP E2) H1 (L2 b') //=.
  by apply: map_f.
rewrite mem_filter /= E1 /=.
elim: ss {H1}=>// t ss; rewrite /= 2!inE=>->.
case: (t =P a')=>[->|H2].
- by rewrite E1 /f eq_refl E2.
by rewrite -(L2 t) //; case: eqP H2.
Qed.

(* the same equation as above but done when lists of reps are viewed as sets *)
(* useful for rewriting *)
Lemma join_class_eq (D : data) (a' b' : symb) :
        a' != b' -> b' \in reps D ->
        reps (join_class D a' b') =i filter (predC1 a') (reps D).
Proof. by move=>*; apply: perm_mem; apply: join_class_perm. Qed.

(* join_class doesn't change the termination metric *)
Lemma join_class_metric (D : data) (a' b' : symb) :
        a' \in reps D -> b' \in reps D -> a' != b' ->
        metric D = metric (join_class D a' b') + size (use D a').
Proof.
move=>H1 H2 H3; rewrite /metric /= -addnA; congr plus.
by rewrite (perm_big _ (join_class_perm H3 H2))
       -(perm_big _ (permEl (perm_filterC (pred1 a') (reps D))))
       big_cat filter_pred1_uniq // !big_filter big_cons /= big_nil addn0 addnC.
Qed.

(* joining the use lists *)
Fixpoint join_use' (D : data) (a' b' : symb)
   (old_use : seq (symb * symb * symb)) {struct old_use} : data :=
  match old_use with
    | [::] => D
    | (c, c1, c2)::p' =>
        if fnd (rep D c1, rep D c2) (lookup D) is Some (d, d1, d2) then
        let: newD := 
          Data (rep D) (class D)
               (finfun (fun r => if r == a' then behead (use D r) 
                                 else use D r))
               (lookup D)
               (comp_pend (c, c1, c2) (d, d1, d2) :: pending D)
        in join_use' newD a' b' p'
        else
        let: newD := 
          Data (rep D) (class D)
               (finfun (fun r => if r == a' then behead (use D r) else
                          if r == b' then (c, c1, c2) :: use D r 
                          else use D r))
               (ins (rep D c1, rep D c2) (c, c1, c2) (lookup D))
               (pending D)
        in join_use' newD a' b' p'
  end.

Definition join_use D a' b' := join_use' D a' b' (use D a').

(* join_use doesn't change the metric either *)
Lemma join_use_metric (D : data) (a' b' : symb) :
        a' \notin reps D -> b' \in reps D -> a' != b' ->
          metric (join_use D a' b') = (metric D) + size (use D a').
Proof.
rewrite /join_use; move E: (use D a')=>old_use.
elim: old_use D E=>[|[[c c1] c2] old_use IH] D E H1 H2 H3 /=.
- by rewrite addn0.
move: (mem_split_uniq H2 (uniq_reps D))=>[s1][s2][L1 L2 L3].
have L4 : undup (map (rep D) (enum predT)) = reps D by [].
case: (fnd _ _)=>[[[d d1] d2]|]; last first.
- rewrite IH //=; last by rewrite ffunE eq_refl E.
  rewrite -addSnnS; congr plus.
  rewrite /metric /= -addnS {1}/reps L4 /=; congr plus.
  rewrite -(filter_predC1 H1).
  rewrite !big_filter L1 !(perm_big _ (permEl (perm_catCA _ [::b'] _))) /=.
  rewrite !big_cons eq_sym H3 ffunE eq_sym (negbTE H3) eq_refl /=.
  rewrite addSn; congr (_ + _).+1.
  rewrite -(filter_predC1 L3) !big_filter_cond /=.
  apply: eq_bigr=>x /=.
  case S1: (x == b')=>//=.
  case S2: (x == a')=>//=.
  by rewrite ffunE S1 S2.
rewrite IH //=; last by rewrite ffunE eq_refl E.
rewrite /metric /reps /= L4 addnAC addSnnS -addnAC; congr (_ + _ + _).
rewrite -(filter_predC1 H1).
rewrite !big_filter L1 !(perm_big _ (permEl (perm_catCA _ [::b'] _))) /=.
rewrite !big_cons eq_sym H3 /= ffunE (eq_sym b') (negbTE H3).
congr plus.
rewrite -(filter_predC1 L3) !big_filter_cond /=.
apply: eq_bigr=>x /=.
case S1: (x == b')=>//=.
case S2: (x == a')=>//=.
by rewrite ffunE S2.
Qed.

Let pend0 (e : pend) :=
  match e with simp_pend a b => a | comp_pend (a,_,_) (b,_,_) => a end.
Let pend1 (e : pend) :=
  match e with simp_pend a b => b | comp_pend (a,_,_) (b,_,_) => b end.
Notation "e ..0" := (pend0 e) (at level 2).
Notation "e ..1" := (pend1 e) (at level 2).

(* loop through the equations in the pending list *)
Function propagate (D : data) {measure metric D} : data :=
  match (pending D) with
    | [::] => D
    | e :: p' =>
        let: a' := rep D (e..0) in
        let: b' := rep D (e..1) in
        let: D' := Data (rep D) (class D) (use D) (lookup D) p' in
          if a' == b' then propagate D'
          else
            (* first join the classes *)
            let: D'' := join_class D' a' b' in
            (* then readjust the use lists and recurse *)
            propagate (join_use D'' a' b')
  end.
Proof.
- move=>D e p' eq E.
  by rewrite /metric eq addSn; apply: ltP; apply: ltnSn.
move=>D e p' eq H.
rewrite join_use_metric ?H //; last first.
- by rewrite join_class_eq ?mem_filter ?rep_in_reps //= ?(eq_sym (rep D e..1)) H.
- by rewrite join_class_eq ?mem_filter ?rep_in_reps ?H //= eq_refl.
rewrite -join_class_metric ?H ?rep_in_reps //.
by apply: ltP; rewrite /metric /reps /= eq /= addSn.
Qed.

(* normalization routine *)
Fixpoint norm (D : data) (t : exp) {struct t} : exp :=
  match t with
    const s => const (rep D s)
  | app t1 t2 =>
     let: (u1, u2) := (norm D t1, norm D t2) in
       match u1, u2 with
         const w1, const w2 =>
          if fnd (w1, w2) (lookup D) is Some (a, a1, a2) then (const (rep D a))
          else app u1 u2
       | _, _ => app u1 u2
       end
     end.

(************************************)
(* Some invariants of the algorithm *)
(************************************)

(* the rep function is idempotent *)
Definition rep_idemp D := forall a, rep D (rep D a) = rep D a.

(* class lists invert the rep function *)
Definition class_inv D := forall x a, (rep D x == a) = (x \in class D a).

(* use lists only store equations with appropriate representatives *)
Definition use_inv D :=
  forall a c c1 c2, a \in reps D -> (c, c1, c2) \in use D a -> 
    rep D c1 = a \/ rep D c2 = a.

(* intermediary invariant which holds after *)
(* the class of a' has been joined to b' *)
Definition use_inv1 D a' b' :=
  forall c c1 c2,
    (forall a, a \in reps D -> (c, c1, c2) \in use D a -> 
       rep D c1 = a \/ rep D c2 = a) /\
    ((c, c1, c2) \in use D a' -> rep D c1 = b' \/ rep D c2 = b').

(* lookup table only stores equations with *)
(* appropriate representatives *)
Definition lookup_inv D :=
  forall a b c c1 c2, a \in reps D -> b \in reps D ->
    fnd (a, b) (lookup D) = Some (c, c1, c2) -> 
    rep D c1 = a /\ rep D c2 = b.

(* two symbols are similar if they are either related by representatives *)
(* or are to be related after the pending list is processed *)
Definition similar D a b :=
  (const a, const b) \In closure (rep2rel D \+p eqs2rel 
                                 (map pend2eq (pending D))).

Definition similar1 D a' b' a b :=
  (const a, const b) \In 
     closure (rep2rel D \+p [Pred x y | x = const a' /\ y = const b'] \+p
             eqs2rel (map pend2eq (pending D))).

(* invariants tying use lists with the lookup table *)
Definition use_lookup_inv D :=
  forall a c c1 c2, a \in reps D -> (c, c1, c2) \in use D a ->
    exists d d1 d2,
      fnd (rep D c1, rep D c2) (lookup D) = Some (d, d1, d2) /\
      rep D c1 = rep D d1 /\ rep D c2 = rep D d2 /\ similar D c d.

Definition lookup_use_inv D :=
  forall a b d d1 d2,
    a \in reps D -> b \in reps D -> 
    fnd (a, b) (lookup D) = Some (d, d1, d2) ->
    [/\ exists c c1 c2,
          (c, c1, c2) \in use D a /\ rep D c1 = a /\ 
          rep D c2 = b /\ similar D c d &
        exists c c1 c2,
          (c, c1, c2) \in use D b /\ rep D c1 = a /\ 
          rep D c2 = b /\ similar D c d].

(* intermediary invariants after removing an equation from the pending list *)
Definition use_lookup_inv1 D a' b' :=
  forall a c c1 c2, a \in reps D -> (c, c1, c2) \in use D a ->
    exists d d1 d2,
      fnd (rep D c1, rep D c2) (lookup D) = Some (d, d1, d2) /\
      rep D c1 = rep D d1 /\ rep D c2 = rep D d2 /\ similar1 D a' b' c d.

Definition lookup_use_inv1 D a' b' :=
  forall a b d d1 d2,
    a \in reps D -> b \in reps D -> fnd (a, b) (lookup D) = Some (d, d1, d2) ->
    [/\ exists c c1 c2,
          (c, c1, c2) \in use D a /\ rep D c1 = a /\ 
          rep D c2 = b /\ similar1 D a' b' c d &
        exists c c1 c2,
          (c, c1, c2) \in use D b /\ rep D c1 = a /\ 
          rep D c2 = b /\ similar1 D a' b' c d].

(* intermediary invariants after join_class and during join_use *)
Definition use_lookup_inv2 D a' b' :=
  (forall c c1 c2, (c, c1, c2) \in use D a' ->
    [\/ rep D c1 = b' /\
          exists d d1 d2,
            fnd (a', rep D c2) (lookup D) = Some (d, d1, d2) /\
            rep D d1 = b' /\ rep D d2 = rep D c2 /\ similar D c d,
        rep D c2 = b' /\
          exists d d1 d2,
            fnd (rep D c1, a') (lookup D) = Some (d, d1, d2) /\
            rep D d1 = rep D c1 /\ rep D d2 = b' /\ similar D c d |
        rep D c1 = b' /\ rep D c2 = b' /\
          exists d d1 d2,
            fnd (a', a') (lookup D) = Some (d, d1, d2) /\
            rep D d1 = b' /\ rep D d2 = b' /\ similar D c d]) /\
  forall a c c1 c2, a \in reps D -> (c, c1, c2) \in use D a ->
    [\/ rep D c1 = a /\ rep D c2 = b' /\
          (exists d d1 d2,
            (d, d1, d2) \in use D a' /\
            rep D d1 = a /\ rep D d2 = b' /\ similar D c d) /\
          exists d d1 d2,
            fnd (a, a') (lookup D) = Some (d, d1, d2) /\
            rep D d1 = a /\ rep D d2 = b' /\ similar D c d,
        rep D c1 = a /\
          exists d d1 d2,
            fnd (a, rep D c2) (lookup D) = Some (d, d1, d2) /\
            rep D d1 = a /\ rep D d2 = rep D c2 /\ similar D c d,
        rep D c1 = b' /\ rep D c2 = a /\
          (exists d d1 d2,
            (d, d1, d2) \in use D a' /\
            rep D d1 = b' /\ rep D d2 = a /\ similar D c d) /\
          exists d d1 d2,
            fnd (a', a) (lookup D) = Some (d, d1, d2) /\
            rep D d1 = b' /\ rep D d2 = a /\ similar D c d |
        rep D c2 = a /\
          exists d d1 d2,
            fnd (rep D c1, a) (lookup D) = Some (d, d1, d2) /\
            rep D d1 = rep D c1 /\ rep D d2 = a /\ similar D c d].

Definition lookup_use_inv2 D a' b' :=
  forall d d1 d2,
    [/\ forall b, b \in reps D -> 
        fnd (a', b) (lookup D) = Some (d, d1, d2) ->
        rep D d1 = b' /\
        exists c c1 c2,
          (c, c1, c2) \in use D b /\ rep D c1 = b' /\ 
          rep D c2 = b /\ similar D c d,
        forall a, a \in reps D -> 
        fnd (a, a') (lookup D) = Some (d, d1, d2) ->
        rep D d2 = b' /\
        exists c c1 c2,
          (c, c1, c2) \in use D a /\ rep D c1 = a /\ 
          rep D c2 = b' /\ similar D c d &
        forall a b, a \in reps D -> b \in reps D ->
        fnd (a, b) (lookup D) = Some (d, d1, d2) ->
        [/\ exists c c1 c2,
              (c, c1, c2) \in use D a /\ rep D c1 = a  /\ 
              rep D c2 = b /\ similar D c d &
            exists c c1 c2,
              (c, c1, c2) \in use D b /\ rep D c1 = a  /\ 
              rep D c2 = b /\ similar D c d]].

(* the invariant of the propagate routine *)
Definition propagate_inv D :=
  rep_idemp D /\ use_inv D /\ lookup_inv D /\ 
  use_lookup_inv D /\ lookup_use_inv D.

(****************)
(* Verification *)
(****************)

(* first some basic rewrite rules *)

Lemma reps_rep (D : data) (a : symb) : 
        rep_idemp D -> a \in reps D -> rep D a = a.
Proof. by move=>H; rewrite mem_undup; case/mapP=>x _ ->; apply: H. Qed.

Lemma symR R x y : (x, y) \In closure R <-> (y, x) \In closure R.
Proof. by split=>T; apply: symC. Qed.

Lemma app_rep D R a b x :
        (x, app (const a) (const b)) \In closure (rep2rel D \+p R) <->
        (x, app (const (rep D a)) (const (rep D b))) 
          \In closure (rep2rel D \+p R).
Proof.
split=>T.
- apply: (transC (y:= app (const a) (const (rep D b)))); last first.
  - by apply: monoC; [apply: clos_rep | apply: reflC].
  apply: (transC (y:= app (const a) (const b)))=>//.
  by apply: monoC; [ apply: reflC | apply: clos_rep].
apply: (transC (y:= app (const a) (const (rep D b)))); last first.
- by apply: monoC; [apply: reflC | apply: symC; apply: clos_rep].
apply: (transC (y:= app (const (rep D a)) (const (rep D b))))=>//.
by apply: monoC; [apply: symC; apply: clos_rep | apply: reflC].
Qed.

Lemma app_rel D R a b x :
        (x, app (const a) (const b)) \In closure (CRel D \+p R) <->
        (x, app (const (rep D a)) (const (rep D b))) \In closure (CRel D \+p R).
Proof. by rewrite /CRel !clos_clos !orrA; apply: app_rep. Qed.

Lemma const_rep D R a x :
        (const a, x) \In closure (rep2rel D \+p R) <->
        (const (rep D a), x) \In closure (rep2rel D \+p R).
Proof. by split=>T; apply: transC T; [apply: symC|]; apply: clos_rep. Qed.

Lemma const_rel D R a x :
        (const a, x) \In closure (CRel D \+p R) <->
        (const (rep D a), x) \In closure (CRel D \+p R).
Proof. by rewrite /CRel !clos_clos !orrA; apply: const_rep. Qed.

(* Now the lemmas *)

(* Initially, each symbol represents only itself, and the class of each *)
(* symbol contains only the symbol itself. The use lists, the lookup    *)
(* table and the pending list all start empty.                          *)

Definition init : data :=
  Data [ffun x => x] [ffun c => [:: c]] [ffun c => [::]] (nil _ _) [::].

Lemma initP : propagate_inv init /\ CRel init <~> closure (graph (@const s)).
Proof.
have S: lookup_rel init <~> Pred0.
- by split=>//; case: x=> ??[?][?][?][?][?][].
have E: graph (@const s) <~> graph (fun x => const ([ffun x => x] x)).
- by split; case: x =>x1 x2 /=; case/imageP=>[x] _ [->->];
     apply/imageP; exists x; rewrite ?ffunE.
rewrite /CRel /= S 2!orr0 /=; split; last by rewrite E.
do!split=>//.
- by rewrite /rep_idemp=>a; rewrite ffunE.
- by rewrite /use_inv=>a c c1 c2; rewrite ffunE.
by rewrite /use_lookup_inv=>a c c1 c2; rewrite ffunE.
Qed.

(* Lemmas about join_class *)

Lemma join_class_repE (D : data) (a' b' : symb) :
        a' \in reps D -> b' \in reps D -> rep_idemp D ->
        closure (rep2rel (join_class D a' b')) <~>
        closure (rep2rel D \+p [Pred x y | x = const a' /\ y = const b']).
Proof.
move=>H2 H3 H1 [x y]; split=>/= T.
- pose ty z := PredU (rep2rel D) [Pred x0 y0 | x0 = const z /\ y0 = const b'].
  move: (clos_idemp (ty a') (x,y))=>/=<-.
  apply: sub_closI T=>{x y} [[x y]].
  case/imageP=>z _ /= [->->] {x y}; rewrite ffunE /=.
  case: eqP=>[<-|_]; last by apply: clos_rep.
  apply: (transC (y:=const (rep D z))); first by apply: clos_rep.
  by apply: (@closI _ (const (rep D z), const b')); right.
move: (clos_idemp (rep2rel (join_class D a' b')) (x,y))=>/=<-.
apply: sub_closI T=>{x y} [[x y]].
case; last first.
- case=>->->; apply: closI; apply/imageP; exists a'=>//.
  by rewrite /= !ffunE /= reps_rep // eq_refl.
case/imageP=>z _ /= [->->] {x y}.
case E: (rep D z == a'); last first.
- apply: (@closI _ (const z, const (rep D z))); apply/imageP.
  by exists z; rewrite // ffunE /= E.
apply: (transC (y:=const b')).
- apply: (@closI _ (const z, const b')); apply/imageP. 
  by exists z; rewrite // ffunE /= E.
apply: symC; apply: (@closI _ (const (rep D z), const b')); apply/imageP.
by exists (rep D z); rewrite // ffunE /= H1 // E.
Qed.

Lemma join_class_useP (D : data) (a' b' : symb) :
        a' \in reps D -> b' \in reps D -> a' != b' ->
        use_inv D -> use_inv1 (join_class D a' b') a' b'.
Proof.
move=>H1 H2 H3 H4 c c1 c2; split=>/= [a|H5]; rewrite !ffunE /=; last first.
- by case: (H4 _ _ _ _ H1 H5)=>->; [left | right]; rewrite /= eq_refl.
rewrite join_class_eq // mem_filter /=.
case/andP=>H5 H6 H7.
by case: (H4 _ _ _ _ H6 H7)=>->; [left | right]; rewrite (negbTE H5).
Qed.

Lemma join_class_lookupP (D : data) (a' b' : symb) :
        a' \in reps D -> b' \in reps D -> a' != b' ->
        lookup_inv D -> lookup_inv (join_class D a' b').
Proof.
move=>H1 H2 H3 H a b c c1 c2.
rewrite !join_class_eq // !mem_filter /= !ffunE /=.
case/andP=>T1 T2; case/andP=>Q1 Q2.
case/(H a b c c1 c2 T2 Q2)=>->->.
by rewrite (negbTE T1) (negbTE Q1).
Qed.

Lemma join_class_simE (D : data) (a' b' : symb) :
        a' \in reps D -> b' \in reps D -> rep_idemp D ->
        forall a b, similar1 D a' b' a b <-> similar (join_class D a' b') a b.
Proof.
move=>H1 H2 H a b.
by rewrite /similar /similar1 -orrA -clos_clos -join_class_repE // clos_clos.
Qed.

Lemma join_class_classP (D : data) (a' b' : symb) :
        a' != b' -> 
        class_inv D -> 
        class_inv (join_class D a' b').
Proof.
rewrite /join_class /class_inv=>E /= => H x a; rewrite !ffunE /=.
case: ifP=>H1.
- case: ifP=>H2; first by rewrite (eqP H2) (eq_sym b') (negbTE E).
  case: ifP=>H3; first by rewrite (eq_sym b') H3 mem_cat mem_rev -H H1.
  by rewrite (eq_sym b') H3 -H (eqP H1) eq_sym H2.
case: ifP=>H2; first by rewrite (eqP H2) H1.
case: ifP=>H3; first by rewrite mem_cat mem_rev -!H H1 (eqP H3).
by rewrite H.
Qed.

Lemma join_classP (D : data) (a' b' : symb) :
        a' \in reps D -> 
        b' \in reps D -> 
        a' != b' ->
        rep_idemp D -> 
        use_inv D -> 
        lookup_inv D ->
        use_lookup_inv1 D a' b' -> 
        lookup_use_inv1 D a' b' ->
        use_lookup_inv2 (join_class D a' b') a' b' /\
        lookup_use_inv2 (join_class D a' b') a' b'.
Proof.
move=>H1 H2 H3 L0 L1 L2 T1 T2.
split; last first.
- split=>[b|a|a b]; rewrite !join_class_eq // !mem_filter /=;
  case/andP=>H4 H5.
  - move=>F; rewrite ffunE /=.
    case: (L2 a' b d d1 d2 H1 H5 F)=>R1 R2; rewrite R1 eq_refl; do !split=>//.
    case: (T2 a' b d d1 d2 H1 H5 F)=>_ [c][c1][c2][Q1][Q2][Q3]Q4.
    exists c, c1, c2; rewrite !ffunE /= Q2 Q3 eq_refl (negbTE H4).
    by do !split=>//; rewrite -join_class_simE.
  - move=>F; rewrite ffunE /=.
    case: (L2 a a' d d1 d2 H5 H1 F)=>R1 R2; rewrite R2 eq_refl; do !split=>//.
    case: (T2 a a' d d1 d2 H5 H1 F)=>[[c][c1][c2][Q1][Q2][Q3]Q4 _].
    exists c, c1, c2; rewrite !ffunE /= Q2 Q3 eq_refl (negbTE H4).
    by do !split=>//; rewrite -join_class_simE.
  case/andP=>H6 H7 F.
  case: (T2 a b d d1 d2 H5 H7 F).
  move=>[c][c1][c2][Q1][Q2][Q3] Q4.
  move=>[e][e1][e2][F1][F2][F3] F4.
  split.
  - exists c, c1, c2; rewrite !ffunE /= Q2 Q3 (negbTE H4) (negbTE H6).
    by do !split=>//; rewrite -join_class_simE.
  exists e, e1, e2; rewrite !ffunE /= F2 F3 (negbTE H4) (negbTE H6).
  by do !split=>//; rewrite -join_class_simE.
split=>[c c1 c2 /= H4 | a c c1 c2]; last first.
- rewrite join_class_eq // mem_filter /=.
  case/andP=>H4 H5 H6.
  case: (L1 a c c1 c2 H5 H6)=>H7; rewrite !ffunE /=;
  [ case H8: (rep D c2 == a'); [apply: Or41 | apply: Or42] |
    case H8: (rep D c1 == a'); [apply: Or43 | apply: Or44] ];
    move: (T1 a c c1 c2 H5 H6); rewrite H7 ?(eqP H8) (negbTE H4);
    move=>[d][d1][d2][Q1][Q2][Q3] Q4; do !split=>//;
    try by [exists d, d1, d2; rewrite !ffunE /=;
            rewrite -Q2 -Q3 ?eq_refl (negbTE H4) ?H8; split=>//;
            rewrite -?join_class_simE];
  [ case: (T2 a a' d d1 d2 H5 H1 Q1)=>_ [e][e1][e2][F1][F][F2] F4 |
    case: (T2 a' a d d1 d2 H1 H5 Q1)=>[[e][e1][e2][F1][F2][F] F4] _];
    exists e, e1, e2; rewrite !ffunE /=;
    rewrite F F2 ?eq_refl (negbTE H4) -join_class_simE //; do !split=>//;
    by apply: (transC Q4); apply: symC F4.
move: (L1 a' c c1 c2 H1 H4)=>H5.
case H6: (rep D c1 == rep D c2); last first.
- case: H5=>H5; rewrite -H5; [apply: Or31 | apply: Or32];
  rewrite !ffunE /= eq_refl; do ![split=>//];
  move: (T1 a' c c1 c2 H1 H4)=>[d][d1][d2][Q1][Q2][Q3] Q4;
  exists d, d1, d2; rewrite !ffunE /= -Q2 -Q3 ?(eq_sym (rep D c2)) H6 eq_refl;
  by do ![split=>//]; rewrite -join_class_simE=>//; rewrite H5.
apply: Or33.
case: H5 H1 H3 H4 T1=><- H1 H3 H4 T1; rewrite !ffunE /=
                       eq_refl ?(eq_sym (rep D c2)) H6; do ![split=>//];
move: (T1 _ c c1 c2 H1 H4)=>[d][d1][d2][Q1][Q2][Q3] Q4;
exists d, d1, d2; rewrite !ffunE /=;
rewrite -Q2 -Q3 -(eqP H6) eq_refl in Q1 *; do !split=>//;
rewrite -join_class_simE=>//.
by rewrite (eqP H6).
Qed.

Definition rpull {T : Type} (r : Pred T) := (orrC r, orrCA r).

Lemma join_classE (D : data) (a' b' : symb) :
        a' \in reps D -> 
        b' \in reps D -> 
        a' != b' ->
        rep_idemp D -> 
        use_lookup_inv1 D a' b' -> 
        lookup_use_inv1 D a' b' ->
        closure (CRel (join_class D a' b') \+p 
                       eqs2rel (map symb2eq (use D a'))) <~>
        closure (CRel D \+p [Pred x y | x = const a' /\ y = const b']).
Proof.
pose ty := [Pred x0 y0 | x0 = const a' /\ y0 = const b'].
move=>L1 L2 L3 H1 H4 H5 [x y]; split.
- apply: clos_or; move=>{x y}[x y]; last first.
  - move: (clos_idemp (CRel D \+p ty) (x,y))=><-.
    apply: sub_closI=>{x y}[[x y]] /=.
    move/invert=>[c][c1][c2][->->H6].
    move: (H4 a' c c1 c2 L1 H6)=>[d][d1][d2][Q1][Q2][Q3] Q4.
    apply/app_rel.
    apply: (transC (y := const d)).
    - rewrite /CRel clos_clos !orrA.
      rewrite -!(rpull (eqs2rel _)) -3!(rpull ty) -!(rpull (rep2rel _)) -!orrA.
      move: Q4; apply: sub_closI=>{x y} [[x y]] Q4; apply: sub_orl.
      by rewrite !toPredE in Q4 *; rewrite orrA.
    rewrite const_rel /CRel clos_clos !orrA symR.
    apply: (@closI _ (app (const (rep D c1))  
                     (const (rep D c2)), const (rep D d))).
    apply: sub_orr; apply: sub_orl.
    rewrite toPredE invert_look.
    exists (rep D d1), (rep D d2), d, d1, d2.
    by rewrite -Q2 -Q3 !rep_in_reps.
  rewrite /CRel !toPredE clos_idemp clos_clos !orrA /=.
  rewrite -clos_clos join_class_repE // clos_clos orrA.
  rewrite -!(rpull (eqs2rel (map pend2eq _))).
  apply: sub_closKR=>{x y}; apply: sub_closKR=>[[x y]] T1.
  rewrite toPredE -clos_idemp.
  apply: sub_closI T1=>{x y} [[x y]].
  rewrite toPredE.
  case=>[T|]; first by apply: closI; right.
  case=>a[b][c][c1][c2][-> +++ ->].
  rewrite !join_class_eq //= !mem_filter /=.
  case/andP=>T1 T1'; case/andP=>T2 T2' T3; rewrite ffunE /=.
  case: eqP=>[H6|_];
  [apply: (transC (y:= const a')); last by [apply closI; right] |];
  apply closI; apply: sub_orl; rewrite toPredE invert_look;
  exists a, b, c, c1, c2=>//.
  by rewrite H6.
rewrite /CRel !toPredE !clos_clos !orrA /= => {H4} T.
rewrite -clos_clos join_class_repE // clos_clos !orrA -(rpull ty).
rewrite -3!(rpull ty) -!(rpull (rep2rel _)) -!(rpull (lookup_rel _)) in T *.
rewrite -clos_idemp; apply: sub_closI T=>{x y} [[x y]].
case=>[|T]; last by apply closI; apply: sub_orr;
  rewrite toPredE -!orrA; apply: sub_orl; rewrite toPredE !orrA.
case=>a[b][c][c1][c2][-> T1 T2 T3 ->].
case: (H5 a b c c1 c2 T1 T2 T3).
move=>[d][d1][d2][Q1][Q2][Q3] Q4 [f][f1][f2][F1][F2][F3] F4.
case E1: (a == a').
- rewrite toPredE !(rpull (lookup_rel _)) !orrA -Q2 -Q3 symR 
    -app_rep -const_rep symR.
  apply: (transC (y:= const d)); last first.
  - move: Q4; apply: sub_closI=>{x y} [[x y]].
    by rewrite !toPredE -!orrA=>Q4; do 2!apply: sub_orl.
  apply: symC; apply closI; do 3!apply: sub_orr; apply: sub_orl.
  rewrite toPredE invert -(eqP E1).
  by exists d, d1, d2.
case E2: (b == a').
- rewrite toPredE !(rpull (lookup_rel _)) !orrA.
  rewrite -F2 -F3 symR -app_rep -const_rep symR.
  apply: (transC (y:= const f)); last first.
  - move: F4; apply: sub_closI=>{x y} [[x y]].
    by rewrite !toPredE -!orrA=>F4; do 2!apply: sub_orl.
  apply: symC; apply closI; do 3!apply: sub_orr; apply: sub_orl.
  rewrite toPredE invert -(eqP E2).
  by exists f, f1, f2.
case E3: (rep D c == a'); last first.
- apply: closI; apply: sub_orl; rewrite toPredE invert_look.
  exists a, b, c, c1, c2.
  by rewrite !join_class_eq // !mem_filter /= E1 E2 !ffunE /= E3.
rewrite (eqP E3).
apply: (transC (y := const b')); last first.
- by apply: symC; apply closI; do 2!apply: sub_orr; apply: sub_orl.
apply closI; apply: sub_orl; rewrite toPredE invert_look.
exists a, b, c, c1, c2.
by rewrite !join_class_eq // !mem_filter /= E1 E2 !ffunE /= E3.
Qed.

(* Lemmas about join_use *)

Lemma join_use_classP (D : data) (a' b' : symb) :
        a' != b' -> 
        class_inv D -> 
        class_inv (join_use D a' b').
Proof.
rewrite /class_inv /join_use; move E: (use _ _)=>x.
elim: x D E=>[|[[c c1] c2] ss IH] D E H1 H2 x a //=.
by case F : (fnd _ _)=>[[[d d1] d2]|]; rewrite IH //= ffunE eq_refl E.
Qed.

Lemma join_useT t (D : data) (a' b' : symb) (l1 l2 : seq (symb*symb*symb)) :
        use D a' = l1 ++ l2 ++ t ->
        join_use' D a' b' (l1 ++ l2) =
        join_use' (join_use' D a' b' l1) a' b' l2.
Proof.
elim: l1 D a' b'=>[|[[c1 c2] c] l1 IH] D a' b' //= H.
by case F: (fnd _ _)=>[[[d d1] d2]|] /=; rewrite IH //= ffunE eq_refl H /=; eauto.
Qed.

Lemma join_use_useE (D : data) (a' b' : symb) (l1 l2 : seq (symb*symb*symb)) :
        use D a' = l1 ++ l2 -> 
        use (join_use' D a' b' l1) a' = l2.
Proof.
elim: l1 D a' b'=>[|[[c1 c2] c] l1 IH] D a' b' //= H.
by case F: (fnd _ _)=>[[[d d1] d2]|] //=; apply: IH; rewrite /= ffunE eq_refl H.
Qed.

Lemma join_use_useP (D : data) (a' b' : symb) :
        a' \notin reps D -> 
        b' \in reps D ->
        use_inv1 D a' b' -> 
        use_inv1 (join_use D a' b') a' b'.
Proof.
rewrite /join_use; move E: (use _ _)=>x.
elim: x D E=>[|[[c c1] c2] ss IH] D E H1 H2 H3 //=.
case F: (fnd _ _)=>[[[d d1] d2]|];
(apply: IH=>//=; first by [rewrite ffunE eq_refl E];
 move=>e e1 e2; rewrite /reps /=; split=>[a|]; rewrite ffunE;
 [case: eqP=>[->|_]; first by rewrite (negbTE H1) |
  by rewrite eq_refl=>H4; apply: (H3 e e1 e2).2; rewrite mem_behead]).
- by apply: (H3 e e1 e2).1.
case: eqP=>[->|_]; last by apply: (H3 e e1 e2).1.
rewrite inE=>H4.
case/orP; last by apply: (H3 e e1 e2).1.
case/eqP=>_ -> ->.
apply: (H3 c c1 c2).2.
by rewrite E inE eq_refl.
Qed.

Lemma join_use_lookupP (D : data) (a' b' : symb) :
        a' \notin reps D -> 
        b' \in reps D ->
        lookup_inv D -> 
        lookup_inv (join_use D a' b').
Proof.
rewrite /join_use; move E: (use _ _)=>x.
elim: x D E=>[|[[c c1] c2] ss IH] D E H1 H2 H3 //=.
case F: (fnd _ _)=>[[[d d1] d2]|].
- by apply: IH=>//=; first by rewrite ffunE eq_refl E.
apply: IH=>//=; first by rewrite ffunE eq_refl E.
move=>a b d d1 d2; rewrite /reps /= fnd_ins.
by case: eqP=>[[-> -> _ _] [_ -> ->]|_]; last by apply: H3.
Qed.

Lemma join_usePE (D : data) (a' b' : symb) :
        a' \notin reps D -> 
        b' \in reps D ->
        rep_idemp D -> 
        use_inv1 D a' b' -> 
        lookup_inv D ->
        use_lookup_inv2 D a' b' -> 
        lookup_use_inv2 D a' b' ->
        rep_idemp (join_use D a' b') /\
        use_inv1 (join_use D a' b') a' b' /\
        lookup_inv (join_use D a' b') /\
        use_lookup_inv2 (join_use D a' b') a' b' /\
        lookup_use_inv2 (join_use D a' b') a' b' /\
        closure (CRel D \+p eqs2rel (map symb2eq (use D a'))) <~>
                 CRel (join_use D a' b').
Proof.
rewrite /join_use; move E: (use _ _)=>x.
elim: x D E=>[|[[c c1] c2] ss IH] D E L1 L2 H1 H2 H3 H4 H5 /=.
- by rewrite orr0 /CRel clos_idemp.
case F: (fnd _ _)=>[[[d d1] d2]|]; set D' := Data _ _ _ _ _.
- have S1: closure (rep2rel D' \+p eqs2rel (map pend2eq (pending D'))) <~>
           closure (rep2rel D \+p [Pred x y | x = const c /\ y = const d] \+p
                    eqs2rel (map pend2eq (pending D))) by [].
  have S2: forall e1 e2, similar D e1 e2 -> similar D' e1 e2.
  - rewrite /similar=>e1 e2; move: (const e1) (const e2)=>{e1 e2} x y.
    by rewrite S1; apply: sub_closI=>{x y} [[x y]]; 
       case; [left | right; right].
  have T2 : closure (CRel D' \+p eqs2rel (map symb2eq ss)) <~>
            closure (CRel D \+p [Pred x y | x = const c /\ 
     y = app (const c1) (const c2)] \+p eqs2rel (map symb2eq ss)).
  - rewrite /CRel {2 3}/D' /= !clos_clos !orrA.
    rewrite -!(rpull (eqs2rel (map pend2eq _))).
    rewrite -!(rpull (eqs2rel (map symb2eq ss))).
    do 2!apply: closKR.
    rewrite -!orrA=>[[x y]]; split=>T;
    rewrite toPredE -clos_idemp; apply: sub_closI T=>{x y} [[x y]].
    - case; first by move=>H7; apply: closI; apply: sub_orl.
      case=>->->; rewrite toPredE !orrA symR const_rep symR.
      apply: (transC (y:= app (const (rep D c1)) (const (rep D c2)))); 
      last first.
      - apply closI; apply: sub_orr; apply: sub_orl.
        rewrite toPredE invert_look.
        by exists (rep D c1), (rep D c2), d, d1, d2.
      by rewrite -app_rep; apply closI; do 2!right.
    case; first by move=>H7; apply closI; apply: sub_orl.
    case=>->->; rewrite toPredE !orrA app_rep.
    apply: (transC (y := const d)); first by apply closI; right; right.
    apply: (transC (y := const (rep D d))); first by apply: clos_rep.
    apply: symC; apply closI; apply: sub_orr; apply: sub_orl.
    rewrite toPredE invert_look.
    exists (rep D c1), (rep D c2), d, d1, d2.
    by rewrite !rep_in_reps.
  rewrite -T2.
  apply: IH=>//=; first by rewrite !ffunE eq_refl E.
  - move=>e e1 e2; split=>/= [a|]; rewrite !ffunE; last first.
    - by rewrite eq_refl=>?; apply: (H2 e e1 e2).2; rewrite mem_behead.
    case: eqP=>[->|_]; first by rewrite (negbTE L1).
    by apply: (H2 e e1 e2).1.
  - split=>/= [e e1 e2 | a e e1 e2 L3]; rewrite !ffunE.
    - rewrite eq_refl=>L4.
      have H6: (e, e1, e2) \in use D a' by rewrite mem_behead.
      case: (H4.1 e e1 e2 H6)=>[[R]|[R]|[R1][R2]];
      move=>[f][f1][f2][Q1][Q2][Q3] Q4;
      [apply: Or31 | apply: Or32 | apply: Or33]; do ![split=>//];
      by exists f, f1, f2; rewrite Q2 Q3; do ![split=>//]; apply: S2.
    case: eqP L3 L1=>[->-> //|_] L3 L1 H6.
    case: (H4.2 a e e1 e2 L3 H6)=>[[R1][R2]|[R]|[R1][R2]|[R]];
    [move=>[[h][h1][h2][F1][F2][F3] F4]| idtac | 
     move=>[[h][h1][h2][F1][F2][F3] F4]| idtac];
     move=>[f][f1][f2][Q1][Q2][Q3] Q4; 
       [idtac | apply: Or42 | idtac | apply: Or44];
       try by [do !split=>//; exists f, f1, f2; do !split=>//; apply: S2];
    rewrite E inE in F1; case/orP: F1=>F1;
    [apply: Or42 | apply: Or41 | apply: Or44 | apply: Or43];
       try by [do !split=>//; [exists h, h1, h2; rewrite /= eq_refl E /= |
                               exists f, f1, f2]; do !split=>//; apply: S2];
    do !split=>//; exists d, d1, d2;
    case/eqP: F1 F2 F3 F4=>->->-> F2 F3 F4;
    [move: {H3} (H3 a b' d d1 d2 L3 L2) | move: {H3} (H3 b' a d d1 d2 L2 L3) ];
    rewrite ?R1 ?R2 -F2 -F3; case/(_ F)=>->->; do !split=>//;
    apply: (transC (y := const c)); try by [apply: S2];
    by apply closI; right; left.
  move=>e e1 e2; split.
  - case: {H5} (H5 e e1 e2)=> H5 _ _ b H6 H7.
    move: {H5} (H5 b H6 H7)=>[R][f][f1][f2][Q1][Q2][Q3] Q4; do !split=>//.
    exists f, f1, f2; rewrite {1}/D' /= !ffunE.
    by case: eqP H6 L1=>[->-> //| _] H6 L1; do !split=>//; apply: S2.
  - case: {H5} (H5 e e1 e2)=> _ H5 _ a H6 H7.
    move: {H5} (H5 a H6 H7)=>[R][f][f1][f2][Q1][Q2][Q3] Q4; do !split=>//.
    exists f, f1, f2; rewrite {1}/D' /= !ffunE.
    by case: eqP H6 L1=>[->-> //| _] H6 L1; do !split=>//; apply: S2.
  case: {H5} (H5 e e1 e2) => _ _ H5 a b H6 H7 H8.
  case: {H5} (H5 a b H6 H7 H8).
  move=>[f][f1][f2][Q1][Q2][Q3] Q4 [h][h1][h2][G1][G2][G3] G4.
  split.
  - exists f, f1, f2; rewrite {1}/D' /= !ffunE.
    by case: eqP H6 L1=>[->-> //| _] H6 L1; do !split=>//; apply: S2.
  exists h, h1, h2; rewrite {1}/D' /= !ffunE.
  by case: eqP H7 L1=>[->-> //| _] H7 L1; do !split=>//; apply: S2.
have T1: lookup_rel D' <~> lookup_rel D \+p
  [Pred x y | x = app (const (rep D c1)) (const (rep D c2)) /\
              y = const (rep D c)].
- rewrite /lookup_rel /D' /= /reps /= =>[[x y]]; split.
  - move=>[a][b][d][d1][d2][-> T2 T3].
    rewrite fnd_ins.
    case: eqP=>[[->->] [<- _ _] ->|_ T4 T5]; [by right | left].
    by exists a, b, d, d1, d2.
  case.
  - move=>[a][b][d][d1][d2][T1 T2 T3 T4 T5].
    exists a, b, d, d1, d2.
    rewrite fnd_ins.
    case: eqP T4=>[[->->]|//].
    by rewrite F.
  case=>T1 T2.
  exists (rep D c1), (rep D c2), c, c1, c2.
  rewrite fnd_ins !rep_in_reps.
  by case: eqP.
have T2: closure (CRel D' \+p eqs2rel (map symb2eq ss)) <~>
  closure (CRel D \+p [Pred x y | x = const c /\ 
    y = app (const c1) (const c2)] \+p eqs2rel (map symb2eq ss)).
- pose ty1 := [Pred x y | x = app (const (rep D c1)) 
    (const (rep D c2)) /\ y = const (rep D c)].
  pose ty2 := [Pred x y | x = const c /\ y = app (const c1) (const c2)].
  rewrite /CRel {3}/D' /= T1 !clos_clos !orrA -2!(rpull ty1) 
    -3!(rpull ty2) -!orrA -!(rpull (rep2rel _)).
  do 3!apply: closRK; move=>[x y]; split=>T;
  rewrite toPredE -clos_idemp; apply: sub_closI T=>{x y} [[x y]].
  - case; first by move=>T; apply: closI; left.
    case=>->->; rewrite toPredE symR -const_rep -app_rep.
    by apply closI; right.
  case=>[T|[->->]]; first by apply: closI; left.
  by rewrite toPredE const_rep app_rep symR; apply closI; right.
rewrite -T2.
apply: IH=>//=; first by rewrite ffunE eq_refl E.
- move=>e e1 e2; split=>/= [a H6|]; rewrite !ffunE; last first.
  - by rewrite eq_refl=>H6; apply: (H2 e e1 e2).2; rewrite mem_behead.
  case: eqP H6 L1=>[->-> //|_] H6 L1.
  case: eqP=>[->|_]; last by apply: (H2 e e1 e2).1.
  rewrite inE; case/orP; last by apply: (H2 e e1 e2).1.
  case/eqP=>_ ->->.
  apply: (H2 c c1 c2).2=>//.
  by rewrite E inE eq_refl.
- move=>a b d d1 d2; rewrite /= fnd_ins.
  by case: eqP=>[[-> -> _ _] [_ -> ->]|_]; last by apply: H3.
- split=>[d d1 d2 | a d d1 d2 H6].
  - rewrite {1}/D' /= !ffunE eq_refl => H7.
    have H8: (d, d1, d2) \in use D a' by rewrite mem_behead.
    case: {H4} (H4.1 d d1 d2 H8)=>[[R]|[R]|[R1][R2]];
    move=>[e][e1][e2][Q1][Q2][Q3] Q4;
    [apply: Or31 | apply: Or32 | apply: Or33]; do ![split=>//];
    exists e, e1, e2; rewrite fnd_ins;
    by case: eqP L1=>[[-> ->]|_ L1]; first by rewrite rep_in_reps.
  rewrite {1}/D' /= !ffunE.
  case: eqP H6 L1=>[->-> //|_] H6 L1.
  case: eqP=>[->|H7 H8]; [rewrite inE; case/orP=>[|H8] | idtac].
  - case/eqP=>->->->.
    have H8: (c, c1, c2) \in use D a' by [rewrite E inE eq_refl].
    case: ((H2 c c1 c2).2 H8)=>H9; [apply: Or42 | apply: Or44]; 
    do ![split=>//]; exists c, c1, c2; rewrite fnd_ins -H9 eq_refl;
    by do !split=>//; apply: reflC.
  - case: (H4.2 b' d d1 d2 L2 H8)=>[[R1][R2]|[R]|[R1][R2]|[R]];
    [move=>[[f][f1][f2][F1][F2][F3] F4]|idtac|
     move=>[[f][f1][f2][F1][F2][F3] F4]| idtac];
     move=>[e][e1][e2][Q1][Q2][Q3] Q4; 
     [idtac | apply: Or42 | idtac | apply: Or44];
       try by [do !split=>//; exists e, e1, e2; rewrite fnd_ins;
               case: eqP Q1=>[[->->]|]; first by rewrite F];
     rewrite E inE in F1; case/orP: F1=>F1;
     [apply: Or42 | apply: Or41 | apply: Or44 | apply: Or43]; do !split=>//;
     rewrite ?ffunE ?fnd_ins ?eq_refl ?E /=;
       try by [exists f, f1, f2];
       try by [exists e, e1, e2;
               case: eqP Q1=>[[->->]|]; first by rewrite F];
     exists c, c1, c2;
     case/eqP: F1 F4=><-<-<- F4;
     by rewrite F3 F2 ?R1 ?R2 eq_refl.
  case: (H4.2 a d d1 d2 H6 H8)=>[[R1][R2]|[R]|[R1][R2]|[R]];
  [move=>[[f][f1][f2][F1][F2][F3] F4]|idtac|
   move=>[[f][f1][f2][F1][F2][F3] F4]| idtac];
   move=>[e][e1][e2][Q1][Q2][Q3] Q4; 
   [idtac | apply: Or42 | idtac | apply: Or44];
     try by [do !split=>//; exists e, e1, e2; rewrite fnd_ins;
             case: eqP Q1=>[[->->]|]; first by rewrite F];
   rewrite E inE in F1; case/orP: F1=>F1;
   [apply: Or42 | apply: Or41 | apply: Or44 | apply: Or43]; do !split=>//;
   rewrite ?ffunE ?fnd_ins ?eq_refl ?E /=;
     try by [exists f, f1, f2];
     try by [exists e, e1, e2;
             case: eqP Q1=>[[->->]|]; first by rewrite F];
   exists c, c1, c2;
   case/eqP: F1 F4=><-<-<- F4;
   by rewrite F3 F2 ?R1 ?R2 eq_refl.
move=>d d1 d2;split=>[b H6|a H6| a b H6 H7];
rewrite {1}/D' /= fnd_ins !ffunE.
- case: eqP L1=>[[->->]|_ L1 H8]; first by [rewrite rep_in_reps].
  case: eqP H6 L1=>[->->//|_ H6 L1].
  case: {H5} (H5 d d1 d2)=>H5 _ _.
  move: {H5} (H5 b H6 H8)=>[R][e][e1][e2][Q1][Q2][Q3] Q4; do !split=>//.
  exists e, e1, e2; do !split=>//.
  by case: eqP=>//; rewrite inE Q1 orbT.
- case: eqP L1=>[[->->]|_ L1 H8]; first by rewrite rep_in_reps.
  case: eqP H6 L1=>[->->//|_ H6 L1].
  case: {H5} (H5 d d1 d2)=>_ H5 _.
  move: {H5} (H5 a H6 H8)=>[R][e][e1][e2][Q1][Q2][Q3] Q4; do !split=>//.
  exists e, e1, e2; do !split=>//.
  by case: eqP=>//; rewrite inE Q1 orbT.
move=>T.
case H: (a == a') H6 L1; [by rewrite (eqP H)=>-> | move=>{H} H6 L1].
case H: (b == a') H7 L1; [by rewrite (eqP H)=>-> | move=>{H} H7 L1].
have [S1 S2]:
     [/\ exists e e1 e2,
           (e, e1, e2) \in (c, c1, c2) :: use D a /\
           rep D e1 = a /\ rep D e2 = b /\ similar D' e d &
         exists e e1 e2,
           (e, e1, e2) \in (c, c1, c2) :: use D b /\
         rep D e1 = a /\ rep D e2 = b /\ similar D' e d].
- case: eqP T=>[[->->][<- _ _]| _ H8].
  - split; exists c, c1, c2;
    by rewrite inE eq_refl; do !split=>//; apply: reflC.
  case: {H5} (H5 d d1 d2)=>_ _; case/(_ a b H6 H7 H8).
  move=>[e][e1][e2][Q1][Q2][Q3] Q4.
  move=>[f][f1][f2][F1][F2][F3] F4.
  split; [exists e, e1, e2 | exists f, f1, f2];
  by rewrite inE ?Q1 ?F1 orbT.
case: eqP T S1 S2=>[[->->][<- _ _]| _ H8] S1 S2; last first.
- case: {H5} (H5 d d1 d2)=>_ _; case/(_ a b H6 H7 H8).
  move=>[e][e1][e2][Q1][Q2][Q3] Q4.
  move=>[f][f1][f2][F1][F2][F3] F4.
  do 2!case: eqP=>_.
  - by split; [apply: S1 | apply: S2].
  - by split; [apply: S1 | exists f, f1, f2].
  - by split; [exists e, e1, e2 | apply: S2].
  by split; [exists e, e1, e2 | exists f, f1, f2].
have H11: (c, c1, c2) \in use D a' by rewrite E inE eq_refl.
case: eqP=>H8; case: eqP=>H9; last 1 first.
- by case: (H4.1 c c1 c2 H11) H8 H9=>[[->]|[->]|[->][->]].
- by split; [apply: S1 | apply: S2].
- split; first by apply: S1.
  case: (H4.1 c c1 c2 H11) H8 H9=>[[->]|[->]|[->][->]] //;
  move=>[e][e1][e2][Q1][Q2][Q3] Q4 _ _.
  case: {H5} (H5 e e1 e2)=>H5 _ _.
  have H12: rep D c2 \in reps D by rewrite rep_in_reps.
  move: (H5 (rep D c2) H12 Q1)=>[_][f][f1][f2][F1][F2][F3] F4.
  exists f, f1, f2; do !split=>//.
  by apply: (transC (y:= const e))=>//; apply: symC.
split; last by apply: S2.
case: (H4.1 c c1 c2 H11) H8 H9=>[[->]|[->]|[->][->]] //;
move=>[e][e1][e2][Q1][Q2][Q3] Q4 _ _.
case: {H5} (H5 e e1 e2)=>_ H5 _.
have H12: rep D c1 \in reps D by rewrite rep_in_reps.
move: (H5 (rep D c1) H12 Q1)=>[_][f][f1][f2][F1][F2][F3] F4.
exists f, f1, f2; do !split=>//.
by apply: (transC (y:= const e))=>//; apply: symC.
Qed.

(* Lemmas about propagate *)

Lemma propagatePE (D : data) :
        propagate_inv D -> 
        propagate_inv (propagate D) /\
        pending (propagate D) = [::] /\
        CRel D <~> CRel (propagate D).
Proof.
move: D.
pose ty x0 y0 := [Pred x y | x = @const s x0 /\ y = @const s y0].
have L: forall D a b,
  closure (rep2rel D \+p ty a b) <~>
  closure (rep2rel D \+p ty (rep D a) (rep D b)).
- move=>D a b [x y]; split=>T; rewrite toPredE -clos_idemp;
  apply: sub_closI T=>{x y} [[x y]];
  (case; first by move=>H; apply: closI; left); case=>->->;
  [rewrite toPredE const_rep symR const_rep symR | 
   rewrite toPredE -const_rep symR -const_rep symR];
  by apply closI; right.
pose inv D := propagate_inv D.
have L1: forall D pend_eq p' a b a' b' D',
  pending D = pend_eq :: p' -> pend2eq pend_eq = simp_eq a b ->
  rep D a = a' -> rep D b = b' -> 
  Data (rep D) (class D) (use D) (lookup D) p' = D' ->
  (a' == b') ->
  (inv D' -> inv (propagate D') /\ pending (propagate D') = [::] /\
             CRel D' <~> CRel (propagate D')) ->
   inv D -> inv (propagate D') /\ pending (propagate D') = [::] /\
            CRel D <~> CRel (propagate D').
- move=>D pend_eq p' a b a' b' D' H1 H H2 H3 H4 H5 IH [H6][H7][H8][H9] H10.
  have L2: forall a1 b1, similar D a1 b1 -> similar D' a1 b1.
  - move=>a1 b1; rewrite /similar -{2}H4 H1 /= H /= -(rpull (ty a b)) => T.
    rewrite -clos_idemp; move: T; apply: sub_closI=>{a1 b1} [[x y]]; 
    rewrite -H4; case=>[[->->]|T]; last by apply: closI.
    rewrite toPredE const_rep symR const_rep symR /=.
    by rewrite H2 H3 (eqP H5); apply: reflC.
  suff T: CRel D <~> CRel D'.
  - rewrite T; apply: IH; rewrite -H4; do 4!split=>//.
    - move=>a1 c c1 c2 H11 H12; move: (H9 a1 c c1 c2 H11 H12);
      move=>[d][d1][d2][Q1][Q2][Q3] Q4.
      exists d, d1, d2; do !split=>//.
      by rewrite H4; apply: L2.
    move=>a1 b1 c c1 c2 H11 H12 H13; case: (H10 a1 b1 c c1 c2 H11 H12 H13).
    move=>[d][d1][d2][Q1][Q2][Q3] Q4 [e][e1][e2][F1][F2][F3] F4.
    split; [exists d, d1, d2 | exists e, e1, e2];
    by do !split=>//; rewrite H4; apply: L2.
  rewrite /CRel H1 /= -{-1}H4 /=.
  rewrite -!(rpull (lookup_rel _)) -!(rpull (eqs2rel (map pend2eq _))).
  do 2![apply: closKR]; rewrite H /= L -H4.
  symmetry; rewrite closAK=>[[x y]]; case=>->->.
  by rewrite H2 H3 (eqP H5); apply: reflC.
have L2: forall D pend_eq p' a b a' b' D' D'',
  pending D = pend_eq :: p' -> pend2eq pend_eq = simp_eq a b ->
  rep D a = a' -> rep D b = b' ->
  Data (rep D) (class D) (use D) (lookup D) p' = D' -> a' != b' ->
  join_class D' a' b' = D'' ->
  (inv (join_use D'' a' b') -> inv (propagate (join_use D'' a' b')) /\
  pending (propagate (join_use D'' a' b')) = [::] /\
  CRel (join_use D'' a' b') <~> CRel (propagate (join_use D'' a' b'))) ->
  inv D -> inv (propagate (join_use D'' a' b')) /\
  pending (propagate (join_use D'' a' b')) = [::] /\
  CRel D <~> CRel (propagate (join_use D'' a' b')).
- move=>D pend_eq p' a b a' b' D' D'' H1 H H2 H3 H4 H5 H6 IH 
  [H7][H8][H9][H10] H11.
  have T: CRel D <~> closure (CRel D' \+p 
    [Pred x y | x = const a' /\ y = const b']).
  - rewrite /CRel H1 -{2 3}H4 /= clos_clos !orrA H /=.
    rewrite -!(rpull (lookup_rel _)) -!(rpull (eqs2rel (map pend2eq _))).
    by do 2![apply: closKR]; rewrite L H2 H3 -H4 /= /rep2rel.
  have S2: forall a1 b1, similar D a1 b1 -> similar1 D' a' b' a1 b1.
  - move=>a1 b1.
    rewrite /similar /similar1 H1 -H4 /= H /=.
    rewrite (rpull (ty a b)) (rpull (ty a' b')) -!orrA => Q4.
    rewrite -clos_idemp.
    move: Q4; apply: sub_closI=>[[x y]].
    case; first by move=>Q4; apply: closI; left.
    case=>->->; rewrite toPredE !orrA const_rep symR const_rep symR /= H2 H3.
    by apply closI; do 2!right.
  have [L2' L3']: a' \in reps D' /\ b' \in reps D'
    by rewrite -H2 -H3 -H4 !rep_in_reps.
  have L2'': a' \notin reps D''.
  - by rewrite -H6 (join_class_eq H5 L3') mem_filter /= eq_refl.
  have L3'': b' \in reps D''.
  - by rewrite -H6 (join_class_eq H5 L3') mem_filter /= eq_sym H5.
  have L6' : rep_idemp D' by rewrite -H4.
  have L6'': rep_idemp D''.
  - rewrite -H6=>a1 /=; rewrite !ffunE /=.
    case T1: (rep D' a1 == a'); rewrite reps_rep ?T1 //.
    by case: ifP.
  have L7': use_inv D' by rewrite -H4.
  have L7'': use_inv1 D'' a' b'.
  - by rewrite -H6; apply: join_class_useP.
  have L8' : lookup_inv D' by rewrite -H4.
  have L8'' : lookup_inv D'' by rewrite -H6; apply: join_class_lookupP.
  have L9' : use_lookup_inv1 D' a' b'.
  - move=>a1 c c1 c2 H12 H13; rewrite -H4 /= in H12 H13 *.
    move: (H10 a1 c c1 c2 H12 H13)=>[d][d1][d2][Q1][Q2][Q3] Q4.
    exists d, d1, d2; do !split=>//.
    by rewrite H4; apply: S2.
  have L10': lookup_use_inv1 D' a' b'.
  - move=>a1 b1 c c1 c2 H12 H13 H14; rewrite -H4 /= in H12 H13 H14 *.
    case: (H11 a1 b1 c c1 c2 H12 H13 H14).
    move=>[d][d1][d2][Q1][Q2][Q3] Q4.
    move=>[e][e1][e2][F1][F2][F3] F4.
    split; [exists d, d1, d2 | exists e, e1, e2];
    by rewrite H4; do !split=>//; apply: S2.
  case: (join_classP L2' L3' H5 L6' L7' L8' L9' L10').
  rewrite H6=>L9'' L10''.
  move: (join_usePE L2'' L3'' L6'' L7'' L8'' L9'' L10'').
  move=>[T6][T7][T8][T9][T10].
  have L11'' : lookup_use_inv (join_use D'' a' b').
  - move=>a1 b1 d d1 d2 H12 H13 H14.
    case: {T10} (T10 d d1 d2)=> _ _ T10.
    by apply: (T10 a1 b1 H12 H13 H14).
  have L12'' : use_inv (join_use D'' a' b').
  - move=>a1 c c1 c2 H12 H13.
    by apply: ((T7 c c1 c2).1 a1 H12 H13).
  have L13'' : use_lookup_inv (join_use D'' a' b').
  - have U: forall D, use (join_use D a' b') a' = [::].
    - rewrite /join_use=>D1; move E: (use D1 _)=>x.
      elim: x D1 E=>[|[[f f1] f2] ss IH1] D1 E //=.
      case F: (fnd _ _)=>[[[d d1] d2]|]; apply: IH1; 
      by rewrite /= !ffunE eq_refl E.
    move=>a1 c c1 c2 H12 H13.
    case: (T9.2 a1 c c1 c2 H12 H13); first 1 last;
    try by [case=><- [d][d1][d2][Q1][Q2][Q3] Q4; exists d, d1, d2];
    by case=>[_][_][[d][d1][d2]][]; rewrite U.
  rewrite -H6 /= join_classE // T H6=>->.
  by apply: IH.
apply/(@propagate_ind (fun d d' => inv d -> inv d' /\ 
  pending d' = [::] /\ CRel d <~> CRel d')); first by [].
- by move=>D e p' H1 a' H2 b' H3 D'; apply: L1 H1 _ H2 H3;
     case: e=>// [[[c c1]] c2] [[d d1] d2].
move=>D e p' H1 a' H2 b' H3 D' E [] // H _ D''; 
apply: L2 H1 _ H2 H3 E (negbT H).
by case: e=>// [[[c c1]] c2] [[d d1] d2].
Qed.

(* Lemmas about interaction of propagate with pending and closure *)

Lemma propagate_pendP d eq : propagate_inv d ->
        propagate_inv (Data (rep d) (class d) (use d) 
                            (lookup d) (eq :: pending d)).
Proof.
move=>H; set d' := Data _ _ _ _ _.
have L: forall a b, similar d a b -> similar d' a b.
- move=>a1 b1; rewrite /similar /= -!orrA -orrAC.
  by apply: sub_closI; apply: sub_orl.
move: H=>[R][C][U][UL] LU.
do 4!split=>//.
- move=>a c c1 c2 T1 T2; move: (UL a c c1 c2 T1 T2).
  move=>[e][e1][e2][T3][T4][T5] T6; eauto 10.
move=>a b c c1 c2 T1 T2 T3; move: (LU a b c c1 c2 T1 T2 T3)=>[Y1 Y2].
by split; [move: Y1| move: Y2]; move=>[e][e1][e2][T4][T5][T6] T7; eauto 10.
Qed.

Lemma propagate_clos_pendP d c c1 c2 e e1 e2 :
        propagate_inv d ->
        fnd (rep d c1, rep d c2) (lookup d) = Some (e, e1, e2) ->
          CRel (Data (rep d) (class d) (use d) (lookup d)
                     (comp_pend (c, c1, c2) (e, e1, e2) :: pending d))
         <~> closure (CRel d \+p
                     [Pred x y | x = const c /\ y = app (const c1) (const c2)]).
Proof.
move=>PI H.
have [R1 R2]: rep d e1 = rep d c1 /\ rep d e2 = rep d c2.
- by move: PI=>[_][_][L1] _; apply: (L1 _ _ e).
rewrite /CRel /= /eq2rel /=.
rewrite clos_clos -!(rpull (eqs2rel _)) !orrA; apply: closKR.
move=>[z y]; split=>O; rewrite toPredE -clos_idemp; move: O; apply: sub_closI;
  move=>{z y} [z y].
- case=>[O|]; first by apply: closI; left.
  case=>[O|]; first by apply: closI; right; left.
  case=>->->; rewrite toPredE symR const_rep symR.
  apply: (transC (y := app (const (rep d e1)) (const (rep d e2)))).
  - by rewrite R1 R2 -app_rep; apply closI; right; right.
  apply closI; right; left; rewrite R1 R2.
  by exists (rep d c1), (rep d c2), e, e1, e2.
case=>[O|]; first by apply: closI; left.
case=>[O|]; first by apply: closI; right; left.
case=>->->; apply: (transC (y := const e)); first by apply closI; right; right.
rewrite app_rep const_rep symR /=; apply closI; right; left.
exists (rep d c1), (rep d c2), e, e1, e2.
by rewrite !rep_in_reps.
Qed.

Section NoPend.
Variables (d : data) (c c1 c2 : symb).
Hypotheses (PI : propagate_inv d)
           (Ev : fnd (rep d c1, rep d c2) (lookup d) = None).
Notation u1' := [ffun z => if z == rep d c1 then (c, c1, c2) :: use d z
                           else use d z].
Notation u2' := [ffun z => if z == rep d c2 then (c, c1, c2) :: u1' z
                           else u1' z].

Lemma propagate_nopendP :
        propagate_inv (Data (rep d) (class d) u2'
                      (ins (rep d c1, rep d c2) (c, c1, c2) 
                      (lookup d)) (pending d)).
Proof.
have E : forall (a c c1 c2 : symb) l,
  (c, c1, c2) :: (if a == rep d c1 then (c, c1, c2) :: l else l) =i 
  (c, c1, c2) :: l.
- move=>a f f1 f2 l z; rewrite !inE; case: ifP=>H //.
  by rewrite inE orbA orbb.
move: PI=>[R1][U1][L1][UL1] LU1; do 2!split=>//.
- move=>a e e1 e2; rewrite /reps /= !ffunE /= => T1.
  case: ifP=>E1.
  - rewrite E (eqP E1) inE.
    by case/orP=>[|O]; [case/eqP=>_->->; right | apply: U1 O].
  case: ifP=>E2; last by apply: U1 T1.
  rewrite (eqP E2) inE.
  by case/orP=>[|O]; [case/eqP=>_->->; left | apply: U1 O].
split=>[a b e e1 e2|].
- rewrite /reps /= fnd_ins.
  by case: ifP=>E1; [case/eqP: E1=>->-> T1 T2 [_->->] | apply: L1].
split=>[a e e1 e2|].
- rewrite /reps /= !ffunE /= => T1.
  case: ifP=>E1.
  - rewrite E inE; case/orP=>[|O].
    - case/eqP=>->->->; exists c, c1, c2.
      by rewrite fnd_ins eq_refl; do !split; apply: reflC.
    move: (UL1 a e e1 e2 T1 O)=>[f][f1][f2][F1][F2][F3] F4.
    exists f, f1, f2; rewrite fnd_ins.
    by case: eqP=>[[Y1 Y2]|] //; rewrite Y1 Y2 Ev in F1.
  case: ifP=>[E2|E2 O].
  - rewrite inE; case/orP=>[|O].
    - case/eqP=>->->->; exists c, c1, c2.
      by rewrite fnd_ins eq_refl; do !split=>//; apply: reflC.
    move: (UL1 a e e1 e2 T1 O)=>[f][f1][f2][F1][F2][F3] F4.
    exists f, f1, f2; rewrite fnd_ins.
    by case: eqP=>[[Y1 Y2]|] //; rewrite Y1 Y2 Ev in F1.
  move: (UL1 a e e1 e2 T1 O)=>[f][f1][f2][F1][F2][F3] F.
  exists f, f1, f2; rewrite fnd_ins.
  by case: eqP=>[[Y1 Y2]|] //; rewrite Y1 Y2 Ev in F1.
move=>a b e e1 e2; rewrite /reps !ffunE /= fnd_ins => T1 T2.
case: ifP=>[E1|E1 O].
- case/eqP: E1=>->->[->->->]; split; exists e, e1, e2;
  rewrite eq_refl ?inE ?eq_refl; (do !split=>//; last by apply: reflC).
  by case: eqP; rewrite inE eq_refl.
have [EQ1 EQ2]: rep d e1 = a /\ rep d e2 = b by apply: L1 O.
move: (LU1 a b e e1 e2 T1 T2 O)=>[Y1 Y2]; split; [move: Y1| move: Y2];
move=>[f][f1][f2][F1][F2][F3] F4; exists f, f1, f2;
(case: ifP=>S1; first by rewrite E inE -(eqP S1) F1 orbT);
by case: ifP=>S2; first by rewrite inE -(eqP S2) F1 orbT.
Qed.

Lemma propagate_clos_nopendP :
        CRel (Data (rep d) (class d) u2'
             (ins (rep d c1, rep d c2) (c, c1, c2) (lookup d)) 
             (pending d)) <~>
        closure (CRel d \+p 
          [Pred x y | x = const c /\ y = app (const c1) (const c2)]).
Proof.
rewrite /CRel clos_clos orrA orrAC -!orrA; apply: closRK; rewrite !orrA.
move=>[xx yy]; split=>O; rewrite toPredE -clos_idemp; move: O; apply: sub_closI;
move=>{xx yy} [xx yy].
- case=>[O|]; first by apply: closI; left.
  rewrite /lookup_rel =>[[a]][b][e][e1][e2][-> R1 R2 T1 ->].
  rewrite fnd_ins in T1; case: ifP T1=>[|O T1].
  - case/eqP=>->->[->->->]; rewrite toPredE symR -app_rep -const_rep.
    by apply closI; right; right.
  by apply: closI; right; left; exists a, b, e, e1, e2.
case=>[O|]; first by apply: closI; left.
case=>[O|[->->]].
- apply: closI; right; move: O=>[a][b][e][e1][e2][-> R1 R2 O ->].
  exists a, b, e, e1, e2; do !split=>//.
  by rewrite fnd_ins; case: eqP O=>//; case=>->->; rewrite Ev.
rewrite toPredE app_rep const_rep symR; apply closI; right.
exists (rep d c1), (rep d c2), c, c1, c2.
by rewrite !rep_in_reps fnd_ins eq_refl.
Qed.

End NoPend.

(* Lemma about normalization *)

Lemma norm_const (D : data) (t : exp) (ss : symb) :
        norm D t = const ss -> 
        ss \in reps D.
Proof.
elim: t=>[t|t1 IH1 t2 IH2] /=; first by case=><-.
do 2![case: (norm D _)=>//] => q2 q1.
by case: (fnd _ _)=>[[[c c1] c2] [<-]|//].
Qed.

Lemma norm_app (D : data) (t : exp) (s1 s2 : symb) :
        norm D t = app (const s1) (const s2) ->
        s1 \in reps D /\ s2 \in reps D.
Proof.
elim: t =>[t |t1 IH1 t2 IH2] //=.
case E1: (norm D t1)=>[q1|//]; case E2: (norm D t2)=>[q2|//].
case: (fnd _ _)=> [[[c c1] c2]//|[<-<-]].
by rewrite (norm_const E1) (norm_const E2).
Qed.

Lemma norm_rel (D : data) (t : exp) :
        rep_idemp D -> 
        (t, norm D t) \In CRel D.
Proof.
move=>H; elim: t=>[t|t1 IH1 t2 IH2] /=; first by apply: clos_rep.
case E1: (norm D t1) IH1=>[q1|] IH1; last by apply: monoC.
case E2: (norm D t2) IH2=>[q2|] IH2; last by apply: monoC.
case F: (fnd _ _)=>[[[c c1] c2]|]; last by apply: monoC.
apply: (transC (y:= app (const q1) (const q2))); first by apply: monoC.
apply closI; right; left.
exists q1, q2, c, c1, c2.
by rewrite (norm_const E1) (norm_const E2).
Qed.

Lemma normP (D : data) (x y : exp) :
        rep_idemp D -> 
        pending D = [::] ->
        reflect ((x, y) \In CRel D) (norm D x == norm D y).
Proof.
move=> H1 H2; case: eqP=>H; constructor.
- apply: (transC (y := norm D x)); first by apply: norm_rel.
  apply: (transC (y := norm D y)); last by apply: symC; apply: norm_rel.
  by rewrite H; apply: reflC.
rewrite /CRel H2 /= orr0 => H3; case: H.
suff: (x, y) \In [Pred e1 e2 | norm D e1 = norm D e2] by [].
apply: {x y} H3; last first.
- split; last by move=>????; rewrite !InE /= => -> ->.
  by do !split=>//; move=> x y z; rewrite !InE /= => ->.
move=>[x y]; case.
- by case/imageP=>a _ [->] ->; rewrite /= H1.
move=>[a][b][c][c1][c2][-> Q1 Q2 Q3 ->] /=; do 2!rewrite reps_rep //.
by rewrite Q3 H1.
Qed.

End Congruence.

Notation rel_exp s := (Pred (exp s * exp s)).

(* repeat the morphism declaration outside the section *)
Add Parametric Morphism s : (@closure s) with
  signature Morphisms.respectful (fun e1 e2 => e1 <~> e2) 
   (fun e1 e2 => e1 <~> e2) as closure_morph'.
Proof. by apply: closE. Qed.

