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
(* This file defines ordType - the structure for types with a decidable       *)
(* (strict) order relation.                                                   *)
(* ordType is a subclass of mathcomp's eqType                                 *)
(* This file also defines some important instances of ordType                 *)
(******************************************************************************)

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path fintype.
From pcm Require Import options seqext.

Definition connected (T : eqType) (ord : rel T) := 
  forall x y, x != y -> ord x y || ord y x.

Definition ordtype_axiom (T : eqType) (ord : rel T) := 
  [/\ irreflexive ord, transitive ord & connected ord].

HB.mixin Record isOrdered T of Equality T := {
  ord : rel T;
  ordtype_subproof : ordtype_axiom ord}.

(* Ideally, we would just generate the structure thus. *)
(* But, we need to insert some Universe Polymorphism declaration *)
(* so we switch to plan B: print the generated code using #[log] *)
(* command, then cut-and-paste it and decorate by hand. *)
(* Unfortunately, this doesn't quite work, HB manuals notwithstanding, *)
(* because custom declarations of log code impoverish the Elpi state *)
(* making subsequent invocations of HB work only partially. *)
(* In this file in particular, the canonicals for each instance *)
(* must be declared by hand as HB.instance does that *)
(* only if Ordered is declared by HB.structure *)
(*
#[log(raw)]
#[short(type="ordType")]
HB.structure Definition Ordered := 
  {T of Equality T & isOrdered T}.
*)

(* cut-and-pasted code starts *)
Module Ordered.
Section axioms_.
Local Unset Implicit Arguments.

Record axioms_ (T : Type) : Type := Class {
    eqtype_hasDecEq_mixin : Equality.mixin_of T;
    ordtype_isOrdered_mixin : isOrdered.axioms_ T eqtype_hasDecEq_mixin}.
End axioms_.

Global Arguments axioms_ : clear implicits.
Global Arguments Class [_] [_] _.
Global Arguments eqtype_hasDecEq_mixin [_] _.
Global Arguments ordtype_isOrdered_mixin [_] _.

Section type.
Local Unset Implicit Arguments.
(* Polymorphic Cumulative *) Record 
  type : Type := Pack { sort : Type; _ : axioms_ sort; }.
End type.

Definition class (cT : type) := 
  let: Pack _ c as cT' := cT return axioms_ (sort cT') in c.

Global Arguments type : clear implicits.
Global Arguments Pack [_] _.
Global Arguments sort : clear implicits.
Global Arguments class : clear implicits.

(* DEVCOMMENT *)
(* The polymorphism annotations here and below are needed for storing *)
(* ordType instances in finMaps which have an ordType constraint of *)
(* their own. An example of this is KVMap from HTT. *)
(* Ultimately there should be a better solution if we want to switch *)
(* to Mathcomp's orders. *)
(* /DEVCOMMENT *)

(* Polymorphic Universe annotations added *)
Section PolymorphicClonePack.
(* Polymorphic Universe ou. *)
(* Polymorphic Variables (T : Type@{ou}) (cT : type@{ou}). *)
Variables (T : Type) (cT : type). 

(* Polymorphic *) Definition phant_clone : forall (c : axioms_ T),
  unify Type Type T (sort cT) nomsg ->
  unify type type cT (Pack (sort:=T) c) nomsg -> type :=
  fun (c : axioms_ T) =>
    fun=> (fun=> (Pack (sort:=T) c)).

(* Polymorphic *) Definition pack_ := fun (m : Equality.mixin_of T)
  (m0 : isOrdered.axioms_ T m) => 
  Pack (sort:=T)
       {|eqtype_hasDecEq_mixin := m; ordtype_isOrdered_mixin := m0 |}.
  
End PolymorphicClonePack.

Local Arguments phant_clone : clear implicits.
Notation clone X2 X1 := (phant_clone X2 X1 _ id_phant id_phant).
Local Arguments pack_ : clear implicits.

Module Exports.
Notation ordType := Ordered.type.
#[reversible] Coercion sort : Ordered.type >-> Sortclass.

(* Polymorphic annotation added *)
(* Polymorphic *) Definition ordtype_Ordered_class__to__eqtype_Equality_class : 
 forall T : Type, axioms_ T -> Equality.axioms_ T :=
   fun (T : Type) (c : axioms_ T) =>
     {| Equality.eqtype_hasDecEq_mixin := eqtype_hasDecEq_mixin c |}.

Local Arguments ordtype_Ordered_class__to__eqtype_Equality_class : 
  clear implicits.

#[reversible] Coercion ordtype_Ordered_class__to__eqtype_Equality_class : 
  ordtype.Ordered.axioms_ >-> eqtype.Equality.axioms_.

(* Polymorphic *) Definition ordtype_Ordered__to__eqtype_Equality : 
  ordType -> eqType :=
  fun s : ordType => {| Equality.sort := s; Equality.class := class s |}.

Local Arguments ordtype_Ordered__to__eqtype_Equality : 
  clear implicits.

#[reversible] Coercion ordtype_Ordered__to__eqtype_Equality : 
  ordtype.Ordered.type >-> eqtype.Equality.type.

Global Canonical ordtype_Ordered__to__eqtype_Equality.

#[reversible] Coercion eqtype_hasDecEq_mixin : 
  ordtype.Ordered.axioms_ >-> eqtype.hasDecEq.axioms_.

#[reversible] Coercion ordtype_isOrdered_mixin : 
  ordtype.Ordered.axioms_ >-> ordtype.isOrdered.axioms_.

End Exports.
Import Exports.

Definition phant_on_ : forall T : ordType, phant T -> axioms_ T :=
  fun T : ordType => fun=> class T.
Local Arguments phant_on_ : clear implicits.

Notation on_ X1 := ( phant_on_ _ (Phant X1)).
Notation copy X2 X1 := ( phant_on_ _ (Phant X1) : axioms_ X2).
Notation on X1 := ( phant_on_ _ (Phant _) : axioms_ X1).

Module EtaAndMixinExports.
Section hb_instance_91.
Variable T : ordType.
Local Arguments T : clear implicits.

Definition HB_unnamed_factory_92 : axioms_ (eta T) := class T.
Local Arguments HB_unnamed_factory_92 : clear implicits.
Definition ordtype_Ordered__to__eqtype_hasDecEq : 
  Equality.mixin_of (eta T) := Equality.class T.
Local Arguments ordtype_Ordered__to__eqtype_hasDecEq : 
  clear implicits.

Definition ordtype_Ordered__to__ordtype_isOrdered :
  isOrdered.axioms_ (eta T) HB_unnamed_factory_92 :=
  ordtype_isOrdered_mixin HB_unnamed_factory_92.
Local Arguments ordtype_Ordered__to__ordtype_isOrdered : 
  clear implicits.

Definition HB_unnamed_mixin_95 :=
  ordtype_isOrdered_mixin HB_unnamed_factory_92.
Local Arguments HB_unnamed_mixin_95 : clear implicits.

Definition structures_eta__canonical__ordtype_Ordered : ordType :=
  Pack (sort := eta T)
      {|
        eqtype_hasDecEq_mixin := Equality.class T;
        ordtype_isOrdered_mixin := HB_unnamed_mixin_95
      |}.

Local Arguments structures_eta__canonical__ordtype_Ordered : 
  clear implicits.
Global Canonical structures_eta__canonical__ordtype_Ordered.
End hb_instance_91.
End EtaAndMixinExports.
End Ordered.

HB.export Ordered.Exports.
HB.export Ordered.EtaAndMixinExports.

Definition ord : forall s : ordType, rel s :=
  fun s : ordType => isOrdered.ord (Ordered.class s).
Local Arguments ord : clear implicits.
Global Arguments ord {_}.

Definition ordtype_subproof : forall s : ordType, ordtype_axiom ord :=
  fun s : ordType => isOrdered.ordtype_subproof (Ordered.class s).
Local Arguments ordtype_subproof : clear implicits.
Global Arguments ordtype_subproof {_}.

Notation Ordered X1 := (Ordered.axioms_ X1). 
(* end of generated and changed code *)


(* Repacking *)

Lemma irr {T : ordType} : irreflexive (@ord T).
Proof. by case: (@ordtype_subproof T). Qed.

Lemma trans {T : ordType} : transitive (@ord T).
Proof. by case: (@ordtype_subproof T). Qed.

Lemma connex {T : ordType} : connected (@ord T).
Proof. by case: (@ordtype_subproof T). Qed.

Definition oleq (T : ordType) (t1 t2 : T) := ord t1 t2 || (t1 == t2).

Prenex Implicits ord oleq.

Section Lemmas.
Context {T : ordType}.
Implicit Types x y : T.

Lemma ord_total x y : [|| ord x y, x == y | ord y x].
Proof.
case E: (x == y)=>/=; first by rewrite orbT.
by apply: connex; rewrite negbT.
Qed.

Lemma ord_neq (x y : T) : 
        ord x y -> 
        x != y.
Proof.
move=>H; apply/negP=>/eqP E.
by rewrite E irr in H.
Qed.

Lemma nsym x y : 
        ord x y -> 
        ~ ord y x.
Proof. by move=>E1 E2; move: (trans E1 E2); rewrite irr. Qed.

Lemma antisym : antisymmetric (@ord T).
Proof. by move=>x y /andP [H] /(nsym H). Qed.

Lemma orefl x : oleq x x.
Proof. by rewrite /oleq eq_refl orbT. Qed.

Lemma otrans : transitive (@oleq T).
Proof.
move=>x y z /=; case/orP; last by move/eqP=>->.
rewrite /oleq; move=>T1; case/orP; first by move/(trans T1)=>->.
by move/eqP=><-; rewrite T1.
Qed.

Lemma oantisym : antisymmetric (@oleq T).
Proof.
move=>x y; rewrite /oleq (eq_sym x).
case: eqP=>// _; rewrite !orbF=>/andP [H1 H2].
by move: (trans H1 H2); rewrite irr.
Qed.

Lemma subrel_ord : subrel (@ord T) oleq.
Proof. exact: subrelUl. Qed.

Lemma sorted_oleq s : 
        sorted (@ord T) s -> 
        sorted (@oleq T) s.
Proof. case: s=>//= x s; apply/sub_path/subrel_ord. Qed.

Lemma path_filter (r : rel T) (tr : transitive r) s (p : pred T) x :
        path r x s -> 
        path r x (filter p s).
Proof. exact: (subseq_path tr (filter_subseq p s)). Qed.

Lemma ord_sorted_eq (s1 s2 : seq T) :
        sorted ord s1 -> 
        sorted ord s2 -> 
        s1 =i s2 -> 
        s1 = s2.
Proof. exact/irr_sorted_eq/irr/(@trans _). Qed.

Lemma oleq_ord_trans (n m p : T) :
        oleq m n -> 
        ord n p -> 
        ord m p.
Proof. by case/orP; [apply: trans | move/eqP=>->]. Qed.

Lemma ord_oleq_trans (n m p : T) :
        ord m n -> 
        oleq n p -> 
        ord m p.
Proof. by move=>H /orP [|/eqP <- //]; apply: trans. Qed.

End Lemmas.

#[export] Hint Resolve orefl irr trans connex 
otrans oantisym oleq_ord_trans : core.

Section Totality.
Variable K : ordType.

Variant total_spec (x y : K) : bool -> bool -> bool -> Type :=
| total_spec_lt of ord x y : total_spec x y true false false
| total_spec_eq of x == y : total_spec x y false true false
| total_spec_gt of ord y x : total_spec x y false false true.

Lemma ordP x y : total_spec x y (ord x y) (x == y) (ord y x).
Proof.
case H1: (x == y).
- by rewrite (eqP H1) irr; apply: total_spec_eq.
case H2: (ord x y); case H3: (ord y x).
- by case: (nsym H2 H3).
- by apply: total_spec_lt H2.
- by apply: total_spec_gt H3.
by move: (ord_total x y); rewrite H1 H2 H3.
Qed.
End Totality.

Lemma eq_oleq (K : ordType) (x y : K) : (x == y) = oleq x y && oleq y x.
Proof. by rewrite /oleq (eq_sym x); case: ordP. Qed.

(* Monotone (i.e. strictly increasing) functions for ordType *)
Section Mono.
Variables A B : ordType.

Definition strictly_increasing f x y := @ord A x y -> @ord B (f x) (f y).

Structure mono : Type := Mono {
  fun_of: A -> B; 
  _: forall x y, strictly_increasing fun_of x y}.

End Mono.
Arguments strictly_increasing {A B} f x y.
Arguments Mono {A B _} _.

Section Weakening.
Variable T : ordType.
Implicit Types x y : T.

Lemma ordW x y: ord x y -> oleq x y.
Proof. by rewrite /oleq =>->//. Qed.

Lemma oleqNord x y: oleq x y = ~~ (ord y x).
Proof. by rewrite/oleq; case:(ordP x y)=>//. Qed.

Lemma oleq_eqVord x y : oleq x y = (x == y) || ord x y.
Proof. by rewrite /oleq orbC. Qed.

Variant oleq_spec x y : bool -> bool -> Type :=
| oleq_spec_le of oleq x y : oleq_spec x y true false
| oleq_spec_gt of ord y x : oleq_spec x y false true.

Lemma oleqP x y : oleq_spec x y (oleq x y) (ord y x).
Proof.
case: (ordP x y).
- by move=>/ordW O; rewrite O; apply: oleq_spec_le.
- by move=>/eqP E; rewrite E orefl; apply: oleq_spec_le; apply: orefl.
by move=>O; rewrite oleqNord O //=; apply: oleq_spec_gt.
Qed.

Lemma oleq_total x y: oleq x y || oleq y x.
Proof. by case:oleqP=>// /ordW ->//. Qed.

End Weakening.

(**********************************************)
(* Building hierarchies for some basic orders *)
(**********************************************)

(* trivial total order for unit type *)
Definition unit_ord (x y : unit) := false.
Lemma unit_is_ordtype : ordtype_axiom unit_ord. Proof. by []. Qed.
HB.instance Definition unit_ord_mix := isOrdered.Build unit unit_is_ordtype.
(* manual canonical declaration, as HB fails to declare it *)
Canonical unit_ordType : ordType :=
  Ordered.Pack (sort:=unit) (Ordered.Class unit_ord_mix).

(* trivial total order for nat *)
Lemma nat_is_ordtype : ordtype_axiom ltn.
Proof. by split=>[x||x y] /=; [rewrite ltnn|apply: ltn_trans|case: ltngtP]. Qed.
HB.instance Definition nat_ord_mix := isOrdered.Build nat nat_is_ordtype.
Canonical nat_ordType : ordType :=
  Ordered.Pack (sort:=nat) (Ordered.Class nat_ord_mix).

Lemma nat_ord : ord =2 ltn. Proof. by []. Qed.
Lemma nat_oleq : oleq =2 leq. 
Proof. by move=>x y; rewrite /oleq nat_ord /=; case: ltngtP. Qed.

(* product order *)
Section ProdOrdType.
Variables K T : ordType.

(* lexicographic ordering *)
Definition lex : rel (K * T) :=
  fun x y => if x.1 == y.1 then ord x.2 y.2 else ord x.1 y.1.

Lemma prod_is_ordtype : ordtype_axiom lex.
Proof.
split=>[x|[x1 x2][y1 y2][z1 z2]|[x1 x2][y1 y2]]; rewrite /lex /=.
- by rewrite eq_refl irr.
- case: ifP=>H1; first by rewrite (eqP H1); case: eqP=>// _; apply: trans.
  case: ifP=>H2; first by rewrite (eqP H2) in H1 *; rewrite H1.
  case: ifP=>H3; last by apply: trans.
  by rewrite (eqP H3)=>R1; move/(nsym R1).
by rewrite -pair_eqE /= -(eq_sym x1 y1); case: ifPn=>[_|] /connex.
Qed.

HB.instance Definition prod_ord_mix :=  
  isOrdered.Build (K * T)%type prod_is_ordtype.
(* manual canonical declaration, as HB fails to declare it *)
Canonical prod_ordType : ordType :=
  Ordered.Pack (sort:=prod K T) (Ordered.Class prod_ord_mix).
End ProdOrdType.


(* Every fintype is ordered *)
Section FinTypeOrd.
Variable T : finType.

Definition ordf : rel T :=
  fun x y => index x (enum T) < index y (enum T).

Lemma fintype_is_ordtype : ordtype_axiom ordf.
Proof.
split=>[x|x y z|x y]; rewrite /ordf /=.
- by rewrite ltnn.
- by apply: ltn_trans.
case: ltngtP=>//= H.
have [H1 H2]: x \in enum T /\ y \in enum T by rewrite !mem_enum.
by rewrite -(nth_index x H1) -(nth_index x H2) H eq_refl.
Qed.

(* There isn't canonical projection to latch onto *)
(* so we can't have generic inheritance. *)
(*
HB.instance Definition _ := 
  isOrdered.Build T%type fintype_is_ordtype.
*)

End FinTypeOrd.

(* However, we can get ordtype for any individual fintype *)
(* e.g. ordinals 'I_n *)
HB.instance Definition ordinal_ord_mix n := 
  isOrdered.Build 'I_n (fintype_is_ordtype 'I_n). 
(* manual canonical declaration, as HB fails to declare it *)
Canonical ordinal_ordType n : ordType :=
  Ordered.Pack (sort:='I_n) (Ordered.Class (ordinal_ord_mix n)).

Section SeqOrdType.
Variable T : ordType.

Fixpoint ords x : pred (seq T) :=
  fun y => match x , y with
                 | [::] , [::] => false
                 | [::] ,  t :: ts => true
                 | x :: xs , y :: ys => if x == y then ords xs ys
                                        else ord x y
                 | _ :: _ , [::] => false
             end.

Lemma seq_is_ordtype : ordtype_axiom ords.
Proof.
split.
- by elim=>[|x xs IH] //=; rewrite eq_refl.
- elim=>[|y ys /= IH][|x xs][|z zs] //=.  
  case: (eqVneq x y)=>[->{x}|Hxy]; first by case: ifP=>// _; apply: IH.
  case: (eqVneq y z)=>[<-{z}|Hyz]; first by rewrite (negbTE Hxy). 
  by case: (x =P z)=>[<-{Hyz z} H /(nsym H)//|_]; apply: trans.
elim=>[|x xs IH][|y ys] //=; rewrite (eq_sym y).
case: (x =P y)=>[-> H|/eqP/connex //]. 
by apply: IH; apply: contra H=>/eqP ->.
Qed.

HB.instance Definition seq_ord_mix := isOrdered.Build (seq T) seq_is_ordtype.
(* manual canonical declaration, as HB fails to declare it *)
Canonical seq_ordType : ordType :=
  Ordered.Pack (sort:=seq T) (Ordered.Class seq_ord_mix).
End SeqOrdType.

Lemma sorted_cat_cons_cat (A : ordType) (l r : seq A) x :
        sorted ord (l ++ x :: r) = 
        sorted ord (l ++ [::x]) && sorted ord (x::r).
Proof.
rewrite !(sorted_pairwise (@trans A)) cats1 pairwise_cat.
rewrite pairwise_rcons allrel_consr !pairwise_cons.
case/boolP: (all (ord^~ x) l)=>//= Hl.
case/boolP: (all (ord x) r)=>/= [Hr|_]; last by rewrite !andbF.
by rewrite (allrel_trans (@trans A) Hl Hr).
Qed.

