(*
Copyright 2013 IMDEA Software Institute
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
(* This file contains the reference implementation of finite maps with keys   *)
(* satisfying condition p and supporting disjoint union via a top element.    *)
(*                                                                            *)
(* Union maps signature definitions:                                          *)
(*       from f == union map f converted to a base finite map.                *)
(*         to m == finite map m converted to a union map.                     *)
(*    defined f == union map f is valid.                                      *)
(*     um_undef == an undefined (i.e., invalid) instance of a union map.      *)
(*        empty == a valid empty instance of a union map.                     *)
(*    upd k v f == union map f with key-value pair (k,v) inserted. If key k   *)
(*                 already exists in t, its corresponding value is            *)
(*                 overwritten with v.                                        *)
(*        dom f == a sequence of keys for union map f.                        *)
(* dom_eq f1 f2 == the sets of keys are equal for union maps f1 and f2.       *)
(*     assocs t == a sequence of key-value pairs in union map t.              *)
(*     free f k == union map f without the key k and its corresponding value. *)
(*     find k f == a value corresponding to key k in union map f, wrapped in  *)
(*                 an option type.                                            *)
(*  union f1 f2 == a union map formed by taking a disjoint union of maps f1   *)
(*                 and f2. If the maps are not disjoint, the result is        *)
(*                 undefined.                                                 *)
(*       empb f == union map f is valid and empty.                            *)
(*     undefb f == union map f is undefined.                                  *)
(*      pts k v == a fresh instance of a union map containing a single        *)
(*                 key-value pair (k,v).                                      *)
(*                                                                            *)
(* Defined notions:                                                           *)
(*    um_preim p f k == a value corresponding to key k exists in union map f  *)
(*                      and satisfies predicate p.                            *)
(*           range f == a sequence of values for union map f.                 *)
(*         um_mono f == values of union map f are in a monotonically          *)
(*                      increasing order.                                     *)
(* um_foldl a z0 d f == if f is valid, a result of a left fold over its       *)
(*                      key-value pairs using function a and starting         *)
(*                      value z0, d otherwise.                                *)
(* um_foldr a z0 d f == if f is valid, a result of a right fold over its      *)
(*                      key-value pairs using function a and starting         *)
(*                      value z0, d otherise.                                 *)
(*          omap a f == the result of applying a generalized                  *)
(*                      mapping/filtering function a to union map t. The      *)
(*                      function may inspect both the key and the value and   *)
(*                      return either a new value wrapped in Some, or None if *)
(*                      the key-value pair is to be excluded.                 *)
(*         omapv a f == same as omap, but function a may only inspect the     *)
(*                      value.                                                *)
(*          mapv a f == same as omapv, but function a may only return the new *)
(*                      value, i.e. it is a standard functional mapping.      *)
(*     um_filter p f == the result of applying a filtering function p to      *)
(*                      union map f. Function f may inspect both the key and  *)
(*                      the value.                                            *)
(*    um_filterk p f == same as um_filter, but function p may only inspect    *)
(*                      the key.                                              *)
(*    um_filterv p f == same as um_filter, but function p may only inspect    *)
(*                      the value.                                            *)
(*   oeval a ks f z0 == the result of iteratively applying function a to      *)
(*                      key-value pairs in union map f, in the order          *)
(*                      indicated by sequence of keys ks.                     *)
(*     eval a p f z0 == the result of iteratively applying function a to      *)
(*                      all key-value pairs satisfying predicate p in union   *)
(*                      map f.                                                *)
(*      um_count p f == the number of key-values pairs satisfying predicate p *)
(*                      in union map f.                                       *)
(*         dom_map f == a union map f converted to a finite set, i.e., all    *)
(*                      its values are replaced by tt.                        *)
(*         inverse f == a union map f with its keys and values swapped, i.e., *)
(*                      the values are now serving as keys and vice versa.    *)
(*       um_comp g f == a union map obtained by composing union maps g and f. *)
(*                      The keys taken from f, and their corresponding values *)
(*                      are treated as keys in g for looking up the final     *)
(*                      values.                                               *)
(*        um_all P f == type-level predicate P holds for all key-value pairs  *)
(*                      in union map f.                                       *)
(*       um_allb p f == predicate p holds for all key-value pairs in union    *)
(*                      map f.                                                *)
(*   um_all2 P f1 f2 == binary type-level predicate P holds for all values of *)
(*                      equal keys in union maps f1 and f2.                   *)
(******************************************************************************)

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path bigop.
From pcm Require Import options axioms prelude finmap seqperm pred seqext.
From pcm Require Export ordtype.
From pcm Require Import pcm morphism.

(****************************)
(****************************)
(* Reference Implementation *)
(****************************)
(****************************)

(* UM.base type is reference implementation of union_maps. *)
(* Type has union_map structure if it exhibits isomorphism with UM.base. *)
(* Tying to reference implementation is alternative to axiomatizing *)
(* union maps, which seems unwieldy. *)
(* Thus, the underlying type of all union_maps instances will be *)
(* (copy of) UM.base. Different copies will *)
(* correspond to different canonical structures. *)
(* Copying further enables using different types for different *)
(* instances, as long as there is isomorphism between them. *)
(* This will allow mixing large and small types and *)
(* storing union maps into union maps (e.g., histories into heaps) *)
(* without universe errors. *)

Module UM.
Section UM.
Variables (K : ordType) (C : pred K) (V : Type).

Inductive base :=
  Undef | Def (f : finMap K V) of all C (supp f).

Section FormationLemmas.
Variable (f g : finMap K V).

Lemma all_supp_insP (k : K) v :
        C k -> all C (supp f) -> all C (supp (ins k v f)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_ins inE /=.
by case: eqP=>[->|_] //=; move/(allP H2).
Qed.

Lemma all_supp_remP k : all C (supp f) -> all C (supp (rem k f)).
Proof.
move=>H; apply/allP=>x; rewrite supp_rem inE /=.
by case: eqP=>[->|_] //=; move/(allP H).
Qed.

Lemma all_supp_fcatP :
        all C (supp f) -> all C (supp g) -> all C (supp (fcat f g)).
Proof.
move=>H1 H2; apply/allP=>x; rewrite supp_fcat inE /=.
by case/orP; [move/(allP H1) | move/(allP H2)].
Qed.

Lemma all_supp_kfilterP q :
        all C (supp f) -> all C (supp (kfilter q f)).
Proof.
move=>H; apply/allP=>x; rewrite supp_kfilt mem_filter.
by case/andP=>_ /(allP H).
Qed.

Lemma all_supp_mapfP (a : K -> V -> V) :
        all C (supp f) -> all C (supp (mapf a f)).
Proof.
by move=>H; apply/allP=>x; rewrite supp_mapf; move/(allP H).
Qed.

End FormationLemmas.

Implicit Types (k : K) (v : V) (f g : base).

Lemma umapE (f g : base) :
        f = g <-> match f, g with
                    Def f' pf, Def g' pg => f' = g'
                  | Undef, Undef => true
                  | _, _ => false
                  end.
Proof.
split; first by move=>->; case: g.
case: f; case: g=>// f pf g pg E; rewrite {g}E in pg *.
by congr Def; apply: eq_irrelevance.
Qed.

Definition valid f := if f is Def _ _ then true else false.

Definition empty := @Def (@finmap.nil K V) is_true_true.

Definition upd k v f :=
  if f is Def fs fpf then
    if decP (@idP (C k)) is left pf then
      Def (all_supp_insP v pf fpf)
    else Undef
  else Undef.

Definition dom f : seq K :=
  if f is Def fs _ then supp fs else [::].

Definition assocs f : seq (K * V) :=
  if f is Def fs _ then seq_of fs else [::].

Definition free f k :=
  if f is Def fs pf then Def (all_supp_remP k pf) else Undef.

Definition find k f := if f is Def fs _ then fnd (K:=K) k fs else None.

Definition union f1 f2 :=
  if (f1, f2) is (Def fs1 pf1, Def fs2 pf2) then
    if disj fs1 fs2 then
      Def (all_supp_fcatP pf1 pf2)
    else Undef
  else Undef.

Definition empb f := if f is Def fs _ then supp fs == [::] else false.

Definition undefb f := if f is Undef then true else false.

Definition pts k v := upd k v empty.

(* forward induction *)
Lemma base_indf (P : base -> Prop) :
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union (pts k v) f) ->
                        path ord k (dom f) ->
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//.
apply: fmap_ind'=>[|k v f S IH] H.
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply: notin_path S.
have [T1 T2] : C k /\ all C (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).
  by rewrite supp_ins inE /= T orbT.
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (pts k v) (Def T2)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disjC disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H).
- by apply.
rewrite umapE /union /pts /upd /=.
case: decP=>// T; rewrite /disj /= N /=.
by rewrite E fcat_inss // fcat0s.
Qed.

(* backward induction *)
Lemma base_indb (P : base -> Prop) :
         P Undef -> P empty ->
         (forall k v f, P f -> valid (union f (pts k v)) ->
                        (forall x, x \in dom f -> ord x k) ->
                        P (union (pts k v) f)) ->
         forall f, P f.
Proof.
rewrite /empty => H1 H2 H3; apply: base_ind=>//.
apply: fmap_ind''=>[|k v f S IH] H.
- by set f := Def _ in H2; rewrite (_ : Def H = f) // /f umapE.
have N : k \notin supp f by apply/negP; move/S; rewrite ordtype.irr.
have [T1 T2] : C k /\ all C (supp f).
- split; first by apply: (allP H k); rewrite supp_ins inE /= eq_refl.
- apply/allP=>x T; apply: (allP H x).
  by rewrite supp_ins inE /= T orbT.
have E : FinMap (sorted_ins' k v (sorted_nil K V)) = ins k v (@nil K V) by [].
have: valid (union (Def T2) (pts k v)).
- rewrite /valid /union /pts /upd /=.
  case: decP; last by rewrite T1.
  by move=>T; case: ifP=>//; rewrite E disj_ins N disj_nil.
move/(H3 k v _ (IH T2)).
rewrite (_ : union (pts k v) (Def T2) = Def H); first by apply; apply: S.
rewrite umapE /union /pts /upd /=.
case: decP=>// T; rewrite /disj /= N /=.
by rewrite E fcat_inss // fcat0s.
Qed.

End UM.
End UM.


(***********************)
(***********************)
(* Union Map structure *)
(***********************)
(***********************)

(* type T has union_map structure is it's cancellative TPCM *)
(* with an isomorphism to UM.base *)

Definition union_map_axiom (K : ordType) (C : pred K) V T 
 (defined : T -> bool) (empty : T) (undef : T) (upd : K -> V -> T -> T)
 (dom : T -> seq K) (assocs : T -> seq (K * V)) (free : T -> K -> T) 
 (find : K -> T -> option V) (union : T -> T -> T)
 (empb : T -> bool) (undefb : T -> bool) (pts : K -> V -> T)
 (from : T -> UM.base C V) (to : UM.base C V -> T) := 
 (((forall b, from (to b) = b) *
   (forall f, to (from f) = f)) *
  (((forall f, defined f = UM.valid (from f)) *
    (undef = to (UM.Undef C V)) *
    (empty = to (UM.empty C V))) *
   ((forall k v f, upd k v f = to (UM.upd k v (from f))) *
    (forall f, dom f = UM.dom (from f)) *
    (forall f, assocs f = UM.assocs (from f)) *
    (forall f k, free f k = to (UM.free (from f) k))) *
   ((forall k f, find k f = UM.find k (from f)) *
    (forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2))) *
    (forall f, empb f = UM.empb (from f)) *
    (forall f, undefb f = UM.undefb (from f)) *
    (forall k v, pts k v = to (UM.pts C k v)))))%type.
 
HB.mixin Record isUnionMap_helper (K : ordType) (C : pred K) V T of 
  Normal_CTPCM T := {
    upd : K -> V -> T -> T;
    dom : T -> seq K;
    assocs : T -> seq (K * V);
    free : T -> K -> T;
    find : K -> T -> option V;
    pts_op : K -> V -> T;
    UMC_from : T -> UM.base C V;
    UMC_to : UM.base C V -> T;
    union_map_helper_subproof : 
      union_map_axiom valid Unit undef upd dom assocs 
                      free find join unitb undefb pts_op UMC_from UMC_to}.

(* embed cancellative topped PCM structure to enable inheritance *)
(* we prove later that this isn't needed *)
#[short(type="union_map")]
HB.structure Definition UMC K C V := 
  {T of @isUnionMap_helper K C V T & Normal_TPCM T & CTPCM T}.

Lemma ftE K C V (U : @union_map K C V) b : UMC_from (UMC_to b : U) = b.
Proof. by rewrite union_map_helper_subproof. Qed.

Lemma tfE K C V (U : @union_map K C V) b : UMC_to (UMC_from b) = b :> U.
Proof. by rewrite union_map_helper_subproof. Qed.

Lemma eqE K C V (U : @union_map K C V) (b1 b2 : UM.base C V) :
        UMC_to b1 = UMC_to b2 :> U <-> b1 = b2.
Proof. by split=>[E|->//]; rewrite -(ftE U b1) -(ftE U b2) E. Qed.

Definition umEX K C V (U : @union_map K C V) := 
  (@union_map_helper_subproof K C V U, eqE, UM.umapE).

(* Build CTCPM structure from the rest *)
HB.factory Record isUnion_map (K : ordType) (C : pred K) V T := {
  um_defined : T -> bool; 
  um_empty : T; um_undef : T; 
  um_upd : K -> V -> T -> T;
  um_dom : T -> seq K; 
  um_assocs : T -> seq (K * V);
  um_free : T -> K -> T; 
  um_find : K -> T -> option V; 
  um_union : T -> T -> T;
  um_empb : T -> bool; 
  um_undefb : T -> bool; 
  um_pts : K -> V -> T;
  um_from : T -> UM.base C V; 
  um_to : UM.base C V -> T;
  union_map_subproof : 
    union_map_axiom um_defined um_empty um_undef um_upd um_dom um_assocs 
                    um_free um_find um_union um_empb um_undefb um_pts 
                    um_from um_to}.
  
HB.builders Context K C V T of isUnion_map K C V T.

Definition umEX := snd union_map_subproof.

Lemma ftE b : um_from (um_to b) = b.
Proof. by rewrite union_map_subproof. Qed.

Lemma tfE b : um_to (um_from b) = b.
Proof. by rewrite union_map_subproof. Qed.

Lemma eqE (b1 b2 : UM.base C V) :
        um_to b1 = um_to b2 :> T <-> b1 = b2.
Proof. by split=>[E|->//]; rewrite -[b1]ftE -[b2]ftE E. Qed.

Lemma union_map_is_pcm : pcm_axiom um_defined um_union um_empty um_empb.
Proof.
have joinC f1 f2 : um_union f1 f2 = um_union f2 f1.
- rewrite !umEX !eqE UM.umapE /UM.union.
  case: (um_from f1)=>[|f1' H1]; case: (um_from f2)=>[|f2' H2] //.
  by case: ifP=>E; rewrite disjC E // fcatC.
have joinCA f1 f2 f3 : um_union f1 (um_union f2 f3) = 
  um_union f2 (um_union f1 f3).
- rewrite !umEX !eqE !ftE UM.umapE /UM.union.
  case: (um_from f1) (um_from f2) (um_from f3)=>[|f1' H1][|f2' H2][|f3' H3] //.
  case E1: (disj f2' f3'); last first.
  - by case E2: (disj f1' f3')=>//; rewrite disj_fcat E1 andbF.
  rewrite disj_fcat andbC.
  case E2: (disj f1' f3')=>//; rewrite disj_fcat (disjC f2') E1 /= andbT.
  by case E3: (disj f1' f2')=>//; rewrite fcatAC // E1 E2 E3.
split=>[//|f1 f2 f3|f|f1 f2||f].
- by rewrite (joinC f2) joinCA joinC. 
- rewrite !umEX !ftE -[RHS]tfE eqE UM.umapE /UM.union /UM.empty. 
  by case: (um_from f)=>[//|f' H]; rewrite disjC disj_nil fcat0s.
- by rewrite !umEX !ftE; case: (um_from f1).
- by rewrite !umEX ftE.
rewrite !umEX /= /UM.empty /UM.empb -{1}[f]tfE.
case: (um_from f)=>[|f' F]; first by apply: ReflectF; rewrite eqE.
case: eqP=>E; constructor; rewrite eqE UM.umapE.
- by move/supp_nilE: E=>->.
by move=>H; rewrite H in E.
Qed.

HB.instance Definition _ := isPCM.Build T union_map_is_pcm.

Lemma union_map_is_cpcm : cpcm_axiom T.
Proof.
move=>f1 f2 f.
rewrite -{3}[f1]tfE -{2}[f2]tfE !pcmE /= !umEX /= !ftE !eqE.
rewrite !UM.umapE /UM.valid /UM.union.
case: (um_from f) (um_from f1) (um_from f2)=>
[|f' H]; case=>[|f1' H1]; case=>[|f2' H2] //;
case: ifP=>//; case: ifP=>// D1 D2 _ E. 
by apply: fcatsK E; rewrite D1 D2.
Qed.

HB.instance Definition _ := isCPCM.Build T union_map_is_cpcm.

Lemma union_map_is_tpcm : tpcm_axiom um_undef um_undefb.
Proof.
split=>[/= x||/= x].
- rewrite !umEX /= /UM.undefb -{1}[x]tfE.
  case: (um_from x)=>[|f' F]; first by apply: ReflectT.
  by apply: ReflectF; rewrite eqE.
- by rewrite pcmE /= !umEX ftE.
by rewrite pcmE /= !umEX ftE.
Qed.

HB.instance Definition _ := isTPCM.Build T union_map_is_tpcm.

Lemma union_map_is_normal : @normal_tpcm_axiom T.
Proof.
move=>/= x; rewrite pcmE /= /undef /= -{2}[x]tfE !umEX /UM.valid.
by case: (um_from x)=>[|f' H]; [right|left].
Qed.

HB.instance Definition _ := isNormal_TPCM.Build T union_map_is_normal.
HB.instance Definition _ := isUnionMap_helper.Build K C V T union_map_subproof.
HB.end.

(* Making pts infer union_map structure *)
Definition ptsx K C V (U : union_map C V) k v of phant U : U := 
  @pts_op K C V U k v.

(* use ptsT to pass map type explicitly *)
(* use pts when type inferrable or for printing *)
Notation ptsT U k v := (ptsx k v (Phant U)) (only parsing).
Notation pts k v := (ptsT _ k v). 

(*************************************)
(* Union map with decidable equality *)
(*************************************)

(* union_map has decidable equality if V does *)

Section UnionMapEq.
Variables (K : ordType) (C : pred K) (V : eqType).
Variable (U : union_map C V).

Definition union_map_eq (f1 f2 : U) := 
  match (UMC_from f1), (UMC_from f2) with
  | UM.Undef, UM.Undef => true
  | UM.Def f1' _, UM.Def f2' _ => f1' == f2'
  | _, _ => false
  end.

Lemma union_map_eqP : Equality.axiom union_map_eq.
Proof.
move=>x y; rewrite -{1}[x]tfE -{1}[y]tfE /union_map_eq.
case: (UMC_from x)=>[|f1 H1]; case: (UMC_from y)=>[|f2 H2] /=.
- by constructor.
- by constructor=>/eqE.
- by constructor=>/eqE.
case: eqP=>E; constructor; rewrite eqE.
- by rewrite UM.umapE.
by case.
Qed.

(* no canonical projection to latch onto, so no generic inheritance *)
(* but unionmap_eqP can be used for any individual U *)
(*
HB.instance Definition _ := hasDecEq.Build U union_map_eqP.
*)
End UnionMapEq.


(*********************************)
(* Instance of union maps        *)
(* with trivially true condition *)
(*********************************)

Record umap K V := UMap {umap_base : @UM.base K xpredT V}.

Section UmapUMC.
Variables (K : ordType) (V : Type).
Implicit Type f : umap K V.
Local Coercion umap_base : umap >-> UM.base.

Let um_valid f := @UM.valid K xpredT V f.
Let um_empty := UMap (@UM.empty K xpredT V).
Let um_undef := UMap (@UM.Undef K xpredT V).
Let um_upd k v f := UMap (@UM.upd K xpredT V k v f).
Let um_dom f := @UM.dom K xpredT V f. 
Let um_assocs f := @UM.assocs K xpredT V f. 
Let um_free f k := UMap (@UM.free K xpredT V f k).
Let um_find k f := @UM.find K xpredT V k f. 
Let um_union f1 f2 := UMap (@UM.union K xpredT V f1 f2).
Let um_empb f := @UM.empb K xpredT V f. 
Let um_undefb f := @UM.undefb K xpredT V f.
Let um_from (f : umap K V) : UM.base _ _ := f. 
Let um_to (b : @UM.base K xpredT V) : umap K V := UMap b.
Let um_pts k v := UMap (@UM.pts K xpredT V k v).

Lemma umap_is_umc : 
        union_map_axiom um_valid um_empty um_undef um_upd um_dom 
                        um_assocs um_free um_find um_union um_empb 
                        um_undefb um_pts um_from um_to. 
Proof. by split=>//; split=>[|[]]. Qed.

HB.instance Definition _ := isUnion_map.Build K xpredT V (umap K V) umap_is_umc. 
End UmapUMC.

(* if V is eqtype so is umap K V *)
HB.instance Definition _ (K : ordType) (V : eqType) := 
  hasDecEq.Build (umap K V) (@union_map_eqP K xpredT V (umap K V)).

Notation "x \\-> v" := (ptsT (umap _ _) x v) (at level 30).

(* DEVCOMMENT *)
(* remove these "tests" for release *)
(* Does the notation work? *)
Lemma xx : 1 \\-> true = 1 \\-> false.    
Abort.

(* does the pcm and the equality type work? *)
Lemma xx : ((1 \\-> true) \+ (2 \\-> false)) == (1 \\-> false).  
rewrite joinC. 
Abort.

(* can we use the base type? *)
Lemma xx (x : umap nat nat) : x \+ x == x \+ x. 
Abort.

(* can maps be stored into maps without universe inconsistencies? *)
(* yes, the idea of the class works *)
Lemma xx : 1 \\-> (1 \\-> 3) = 2 \\-> (7 \\-> 3). 
Abort.

(* /DEVCOMMENT *)


(***************)
(* Finite sets *)
(***************)

(* like umaps with unit range *)
(* but we give them their own copy of the type *)

Record fset K := FSet {fset_base : @UM.base K xpredT unit}.

Section FsetUMC.
Variable K : ordType.
Implicit Type f : fset K.
Local Coercion fset_base : fset >-> UM.base.

Let fs_valid f := @UM.valid K xpredT unit f.
Let fs_empty := FSet (@UM.empty K xpredT unit).
Let fs_undef := FSet (@UM.Undef K xpredT unit).
Let fs_upd k v f := FSet (@UM.upd K xpredT unit k v f).
Let fs_dom f := @UM.dom K xpredT unit f. 
Let fs_assocs f := @UM.assocs K xpredT unit f. 
Let fs_free f k := FSet (@UM.free K xpredT unit f k).
Let fs_find k f := @UM.find K xpredT unit k f. 
Let fs_union f1 f2 := FSet (@UM.union K xpredT unit f1 f2).
Let fs_empb f := @UM.empb K xpredT unit f. 
Let fs_undefb f := @UM.undefb K xpredT unit f.
Let fs_from (f : fset K) : UM.base _ _ := f. 
Let fs_to (b : @UM.base K xpredT unit) : fset K := FSet b.
Let fs_pts k v := FSet (@UM.pts K xpredT unit k v).

Lemma fset_is_umc : 
        union_map_axiom fs_valid fs_empty fs_undef fs_upd fs_dom 
                        fs_assocs fs_free fs_find fs_union fs_empb 
                        fs_undefb fs_pts fs_from fs_to. 
Proof. by split=>//; split=>[|[]]. Qed.

HB.instance Definition _ := 
  isUnion_map.Build K xpredT unit (fset K) fset_is_umc. 
HB.instance Definition _ := 
  hasDecEq.Build (fset K) (@union_map_eqP K xpredT unit (fset K)).
End FsetUMC.

Notation "# x" := (ptsT (fset _) x tt) (at level 30, format "# x").

(* DEVCOMMENT *)
(* test *)
(* /DECOMMENT *)
Lemma xx : #1 \+ #2 = Unit. 
Abort.

(*******)
(* dom *)
(*******)

Section DomLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f g : U).

Lemma dom_undef : dom (undef : U) = [::].
Proof. by rewrite !umEX. Qed.

Lemma dom0 : dom (Unit : U) = [::].
Proof. by rewrite !umEX. Qed.

Lemma dom0E f : valid f -> dom f =i pred0 -> f = Unit.
Proof.
rewrite !umEX /UM.valid /UM.dom /UM.empty -{3}[f]tfE !eqE UM.umapE.
case: (UMC_from f)=>[|f' S] //= _; rewrite fmapE /= {S}.
by case: f'; case=>[|kv s] //= P /= /(_ kv.1); rewrite inE eq_refl.
Qed.

Lemma domNE f : reflect (dom f = [::]) (unitb f || undefb f).
Proof.
case: (normalP0 f)=>[->|->|W N]; constructor; rewrite ?dom0 ?dom_undef //.
by move=>M; apply: N; apply: dom0E W _; rewrite M.
Qed.

Lemma dom0NP f : reflect (exists k, k \in dom f) (dom f != [::]).
Proof.
case: has_nilP=>X; constructor.
- by case/hasP: X=>x; exists x.
by case=>k D; apply: X; apply/hasP; exists k.
Qed.

Lemma domU k v f :
        dom (upd k v f) =i
        [pred x | C k & if x == k then valid f else x \in dom f].
Proof.
rewrite !umEX /UM.dom /UM.upd /UM.valid /=. 
case: (UMC_from f)=>[|f' H] /= x.
- by rewrite !inE andbC; case: ifP.
case: decP=>[->|/(introF idP)->//].
by rewrite supp_ins.
Qed.

Lemma domF k f :
        dom (free f k) =i
        [pred x | if k == x then false else x \in dom f].
Proof.
rewrite !umEX; case: (UMC_from f)=>[|f' H] x; rewrite inE /=;
by case: ifP=>// E; rewrite supp_rem inE /= eq_sym E.
Qed.

Lemma subdomF k f : {subset dom (free f k) <= dom f}.
Proof. by move=>x; rewrite domF inE; case: eqP. Qed.

Lemma domUn f1 f2 :
        dom (f1 \+ f2) =i
        [pred x | valid (f1 \+ f2) & (x \in dom f1) || (x \in dom f2)].
Proof.
rewrite !umEX /UM.dom /UM.valid /UM.union.
case: (UMC_from f1) (UMC_from f2)=>[|f1' H1] // [|f2' H2] // x.
by case: ifP=>E //; rewrite supp_fcat.
Qed.

(* bidirectional version of domUn *)
Lemma domUnE f1 f2 x :
        valid (f1 \+ f2) ->
        x \in dom (f1 \+ f2) = (x \in dom f1) || (x \in dom f2).
Proof. by move=>W; rewrite domUn inE W. Qed.

Lemma dom_valid k f : k \in dom f -> valid f.
Proof. by rewrite !umEX; case: (UMC_from f). Qed.

Lemma dom_cond k f : k \in dom f -> C k.
Proof. by rewrite !umEX; case: (UMC_from f)=>[|f' F] // /(allP F). Qed.

Lemma cond_dom k f : ~~ C k -> k \in dom f = false.
Proof. by apply: contraTF=>/dom_cond ->. Qed.

Lemma dom_inIL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> k \in dom (f1 \+ f2).
Proof. by rewrite domUn inE => ->->. Qed.

Lemma dom_inIR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> k \in dom (f1 \+ f2).
Proof. by rewrite joinC; apply: dom_inIL. Qed.

Lemma dom_NNL k f1 f2 :
        valid (f1 \+ f2) -> k \notin dom (f1 \+ f2) -> k \notin dom f1.
Proof. by move=> D; apply/contra/dom_inIL. Qed.

Lemma dom_NNR k f1 f2 :
        valid (f1 \+ f2) -> k \notin dom (f1 \+ f2) -> k \notin dom f2.
Proof. by move=> D; apply/contra/dom_inIR. Qed.

Lemma dom_free k f : k \notin dom f -> free f k = f.
Proof.
rewrite -{3}[f]tfE !umEX /UM.dom /UM.free /=.
by case: (UMC_from f)=>[|f' H] //; apply: rem_supp.
Qed.

Variant dom_find_spec k f : option V -> bool -> Type :=
| dom_find_none'' of find k f = None : dom_find_spec k f None false
| dom_find_some'' v of find k f = Some v &
    f = upd k v (free f k) : dom_find_spec k f (Some v) true.

Lemma dom_find k f : dom_find_spec k f (find k f) (k \in dom f).
Proof.
rewrite !umEX /UM.dom -{1}[f]tfE.
case: (UMC_from f)=>[|f' H].
- by apply: dom_find_none''; rewrite !umEX.
case: suppP (allP H k)=>[v|] /[dup] H1 /= -> I; last first.
- by apply: dom_find_none''; rewrite !umEX.
apply: (dom_find_some'' (v:=v)); rewrite !umEX // /UM.upd /UM.free.
case: decP=>H2; last by rewrite I in H2.
apply/fmapP=>k'; rewrite fnd_ins.
by case: ifP=>[/eqP-> //|]; rewrite fnd_rem => ->.
Qed.

Lemma find_some k v f : find k f = Some v -> k \in dom f.
Proof. by case: dom_find =>// ->. Qed.

Lemma find_none k f : find k f = None <-> k \notin dom f.
Proof. by case: dom_find=>// v ->. Qed.

Lemma cond_find k f : ~~ C k -> find k f = None.
Proof. by move/(cond_dom f); case: dom_find. Qed.

Lemma dom_prec f1 f2 g1 g2 :
        valid (f1 \+ g1) ->
        f1 \+ g1 = f2 \+ g2 ->
        dom f1 =i dom f2 -> f1 = f2.
Proof.
rewrite -{4}[f1]tfE -{3}[f2]tfE /= !umEX.
rewrite /UM.valid /UM.union /UM.dom; move=>D E.
case: (UMC_from f1) (UMC_from f2) (UMC_from g1) (UMC_from g2) E D=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //;
case: ifP=>// D1; case: ifP=>// D2 E _ E1; apply/fmapP=>k.
move/(_ k): E1=>E1.
case E2: (k \in supp f2') in E1; last first.
- by move/negbT/fnd_supp: E1=>->; move/negbT/fnd_supp: E2=>->.
suff L: forall m s, k \in supp m -> disj m s ->
          fnd k m = fnd k (fcat m s) :> option V.
- by rewrite (L _ _ E1 D1) (L _ _ E2 D2) E.
by move=>m s S; case: disjP=>//; move/(_ _ S)/negbTE; rewrite fnd_fcat=>->.
Qed.

Lemma sorted_dom f : sorted (@ord K) (dom f).
Proof. by rewrite !umEX; case: (UMC_from f)=>[|[]]. Qed.

Lemma sorted_dom_oleq f : sorted (@oleq K) (dom f).
Proof. by apply: sorted_oleq (sorted_dom f). Qed.

Lemma uniq_dom f : uniq (dom f).
Proof.
apply: sorted_uniq (sorted_dom f);
by [apply: ordtype.trans | apply: ordtype.irr].
Qed.

Lemma all_dom f : all C (dom f).
Proof. by rewrite !umEX; case: (UMC_from f). Qed.

Lemma perm_domUn f1 f2 :
        valid (f1 \+ f2) -> perm_eq (dom (f1 \+ f2)) (dom f1 ++ dom f2).
Proof.
move=>Vh; apply: uniq_perm; last 1 first.
- by move=>x; rewrite mem_cat domUn inE Vh.
- by apply: uniq_dom.
rewrite cat_uniq !uniq_dom /= andbT; apply/hasPn=>x.
rewrite !umEX /UM.valid /UM.union /UM.dom in Vh *.
case: (UMC_from f1) (UMC_from f2) Vh=>// f1' H1 [//|f2' H2].
by case: disjP=>// H _; apply: contraL (H x).
Qed.

Lemma size_domUn f1 f2 :
        valid (f1 \+ f2) ->
        size (dom (f1 \+ f2)) = size (dom f1) + size (dom f2).
Proof. by move/perm_domUn/seq.perm_size; rewrite size_cat. Qed.

Lemma size_domF k f :
        k \in dom f -> size (dom (free f k)) = (size (dom f)).-1.
Proof.
rewrite !umEX; case: (UMC_from f)=>[|f'] //=; case: f'=>f' F /= _.
rewrite /supp /= !size_map size_filter=>H.
move/(sorted_uniq (@trans K) (@irr K))/count_uniq_mem: F=>/(_ k).
rewrite {}H count_map /ssrbool.preim /= => H.
by rewrite -(count_predC [pred x | key x == k]) H addnC addn1.
Qed.

Lemma size_domU k v f :
        valid (upd k v f) ->
        size (dom (upd k v f)) =
        if k \in dom f then size (dom f) else (size (dom f)).+1.
Proof.
rewrite !umEX /UM.valid /UM.upd /UM.dom.
case: (UMC_from f)=>[|f'] //= H; case: decP=>// P _.
by case: f' H=>f' F H; rewrite /supp /= !size_map size_ins'.
Qed.

End DomLemmas.

Arguments subdomF {K C V U k f}.

#[export]
Hint Resolve sorted_dom uniq_dom all_dom : core.
Prenex Implicits find_some find_none subdomF.

(* lemmas for comparing doms of two differently-typed maps *)
Section DomLemmas2.
Variables (K : ordType) (C1 C2 : pred K) (V1 V2 : Type).
Variables (U1 : union_map C1 V1) (U2 : union_map C2 V2).

Lemma domE (f1 : U1) (f2 : U2) : dom f1 =i dom f2 <-> dom f1 = dom f2.
Proof. by split=>[|->] //; apply/ord_sorted_eq/sorted_dom/sorted_dom. Qed.

Lemma domKi (f1 g1 : U1) (f2 g2 : U2) :
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        dom (f1 \+ g1) =i dom (f2 \+ g2) ->
        dom f1 =i dom f2 -> dom g1 =i dom g2.
Proof.
rewrite !umEX /UM.valid /UM.union /UM.dom.
case: (UMC_from f1) (UMC_from f2) (UMC_from g1) (UMC_from g2)=>
[|f1' F1][|f2' F2][|g1' G1][|g2' G2] //.
case: disjP=>// D1 _; case: disjP=>// D2 _ E1 E2 x.
move: {E1 E2} (E2 x) (E1 x); rewrite !supp_fcat !inE /= => E.
move: {D1 D2} E (D1 x) (D2 x)=><- /implyP D1 /implyP D2.
case _ : (x \in supp f1') => //= in D1 D2 *.
by move/negbTE: D1=>->; move/negbTE: D2=>->.
Qed.

Lemma domK (f1 g1 : U1) (f2 g2 : U2) :
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        dom (f1 \+ g1) = dom (f2 \+ g2) ->
        dom f1 = dom f2 -> dom g1 = dom g2.
Proof. by move=>D1 D2 /domE H1 /domE H2; apply/domE; apply: domKi H2. Qed.

Lemma domKUni (f1 g1 : U1) (f2 g2 : U2) : 
        valid (f1 \+ g1) = valid (f2 \+ g2) ->
        dom f1 =i dom f2 -> dom g1 =i dom g2 ->
        dom (f1 \+ g1) =i dom (f2 \+ g2).
Proof. by move=>E D1 D2 x; rewrite !domUn !inE E D1 D2. Qed.

Lemma domKUn (f1 g1 : U1) (f2 g2 : U2) : 
        valid (f1 \+ g1) = valid (f2 \+ g2) ->
        dom f1 = dom f2 -> dom g1 = dom g2 ->
        dom (f1 \+ g1) = dom (f2 \+ g2).
Proof. by move=>E /domE D1 /domE D2; apply/domE/domKUni. Qed.

Lemma subdom_filter (f1 : U1) (f2 : U2) : 
        {subset dom f1 <= dom f2} ->
        dom f1 = filter (mem (dom f1)) (dom f2).
Proof. 
have Tx : transitive (@ord K) by apply: trans.
move=>S; apply: (sorted_eq (leT := @ord K))=>//.
- by apply: antisym.
- by apply: sorted_dom.
- by rewrite sorted_filter // sorted_dom.
apply: uniq_perm; rewrite ?filter_uniq ?uniq_dom // => y.
rewrite mem_filter /=; case E: (y \in dom _)=>//=.
by move/S: E=>->.
Qed.

End DomLemmas2.

(*********)
(* valid *)
(*********)

Section ValidLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f g : U).

Lemma invalidE f : ~~ valid f <-> f = undef.
Proof. by rewrite undefVN negbK; case: undefbP. Qed.

Lemma validU k v f : valid (upd k v f) = C k && valid f.
Proof.
rewrite !umEX /UM.valid /UM.upd.
case: (UMC_from f)=>[|f' F]; first by rewrite andbF.
by case: decP=>[|/(introF idP)] ->.
Qed.

Lemma validF k f : valid (free f k) = valid f.
Proof. by rewrite !umEX; case: (UMC_from f). Qed.

Variant validUn_spec f1 f2 : bool -> Type :=
| valid_false1 of ~~ valid f1 : validUn_spec f1 f2 false
| valid_false2 of ~~ valid f2 : validUn_spec f1 f2 false
| valid_false3 k of k \in dom f1 & k \in dom f2 : validUn_spec f1 f2 false
| valid_true of valid f1 & valid f2 &
    (forall x, x \in dom f1 -> x \notin dom f2) : validUn_spec f1 f2 true.

Lemma validUn f1 f2 : validUn_spec f1 f2 (valid (f1 \+ f2)).
Proof.
rewrite !umEX -{1}[f1]tfE -{1}[f2]tfE. 
rewrite /UM.valid /UM.union /=.
case: (UMC_from f1) (UMC_from f2)=>[|f1' F1][|f2' F2] /=.
- by apply: valid_false1; rewrite !umEX.
- by apply: valid_false1; rewrite !umEX.
- by apply: valid_false2; rewrite !umEX.
case: ifP=>E.
- apply: valid_true; try by rewrite !umEX.
  by move=>k; rewrite !umEX => H; case: disjP E=>//; move/(_ _ H).
case: disjP E=>// k T1 T2 _.
by apply: (valid_false3 (k:=k)); rewrite !umEX.
Qed.

Lemma validUnAE f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & all [predC dom f1] (dom f2)].
Proof.
apply/idP/idP.
- case: validUn=>// ->-> H _; apply/allP=>k.
  by apply: contraL (H _).
case/and3P=>V1 V2 /allP /= D; case: validUn=>//.
- by rewrite V1.
- by rewrite V2.
by move=>k X1 X2; move: (D k X2); rewrite X1.
Qed.

Lemma validUnAEC f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & all [predC dom f2] (dom f1)].
Proof. by rewrite validUnAE all_predC_sym. Qed.

Lemma validUnHE f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & ~~ has [mem dom f1] (dom f2)].
Proof. by rewrite validUnAE all_predC. Qed.

Lemma validUnHC f1 f2 :
        valid (f1 \+ f2) =
        [&& valid f1, valid f2 & ~~ has [mem dom f2] (dom f1)].
Proof. by rewrite validUnHE has_sym. Qed.

Lemma validFUn k f1 f2 :
        valid (f1 \+ f2) -> valid (free f1 k \+ f2).
Proof.
case: validUn=>// V1 V2 H _; case: validUn=>//; last 1 first.
- by move=>k'; rewrite domF inE; case: eqP=>// _ /H/negbTE ->.
by rewrite validF V1.
by rewrite V2.
Qed.

Lemma validUnF k f1 f2 :
        valid (f1 \+ f2) -> valid (f1 \+ free f2 k).
Proof. by rewrite !(joinC f1); apply: validFUn. Qed.

Lemma validUnU k v f1 f2 :
        k \in dom f2 -> valid (f1 \+ upd k v f2) = valid (f1 \+ f2).
Proof.
move=>D; apply/esym; move: D; case: validUn.
- by move=>V' _; apply/esym/negbTE; apply: contra V'; move/validL.
- move=>V' _; apply/esym/negbTE; apply: contra V'; move/validR.
  by rewrite validU; case/andP.
- move=>k' H1 H2 _; case: validUn=>//; rewrite validU => D1 /andP [/= H D2].
  by move/(_ k' H1); rewrite domU !inE H D2 H2; case: ifP.
move=>V1 V2 H1 H2; case: validUn=>//.
- by rewrite V1.
- by rewrite validU V2 (dom_cond H2).
move=>k'; rewrite domU (dom_cond H2) inE /= V2; move/H1=>H3.
by rewrite (negbTE H3); case: ifP H2 H3=>// /eqP ->->.
Qed.

Lemma validUUn k v f1 f2 :
        k \in dom f1 -> valid (upd k v f1 \+ f2) = valid (f1 \+ f2).
Proof. by move=>D; rewrite -!(joinC f2); apply: validUnU D. Qed.

Lemma dom_inNL k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> k \notin dom f2.
Proof. by case: validUn=>//_ _ H _; apply: H. Qed.

Lemma dom_inNR k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> k \notin dom f1.
Proof. by rewrite joinC; apply: dom_inNL. Qed.

Lemma dom_inNLX k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f1 -> ~ k \in dom f2.
Proof. by move=>W /(dom_inNL W)/negbTE ->. Qed.

Lemma dom_inNRX k f1 f2 :
        valid (f1 \+ f2) -> k \in dom f2 -> ~ k \in dom f1.
Proof. by move=>W /(dom_inNR W)/negbTE ->. Qed.

(* a more symmetric version of the above *)
Lemma dom_inN k1 k2 f1 f2 :
        valid (f1 \+ f2) ->
        k1 \in dom f1 -> k2 \in dom f2 -> k1 != k2.
Proof. by case: (k1 =P k2) =>// <- W H /(dom_inNLX W H). Qed.

Lemma dom_inNX k1 k2 f1 f2 :
        valid (f1 \+ f2) ->
        k1 \in dom f1 -> k2 \in dom f2 -> k1 <> k2.
Proof. by move=>W K1 K2; apply/eqP; apply: dom_inN K1 K2. Qed.

End ValidLemmas.


(************)
(* um_unitb *)
(************)

(* AKA empb *)

Section UnitbLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma um_unitbU k v f : unitb (upd k v f) = false.
Proof.
rewrite !umEX /UM.empb /UM.upd.
case: (UMC_from f)=>[|f' F] //; case: decP=>// H.
suff: k \in supp (ins k v f') by case: (supp _).
by rewrite supp_ins inE /= eq_refl.
Qed.

Lemma um_unitbUn f1 f2 : unitb (f1 \+ f2) = unitb f1 && unitb f2.
Proof.
rewrite !umEX /UM.empb /UM.union.
case: (UMC_from f1) (UMC_from f2)=>[|f1' F1][|f2' F2] //.
- by rewrite andbF.
case: ifP=>E; case: eqP=>E1; case: eqP=>E2 //; last 2 first.
- by move: E2 E1; move/supp_nilE=>->; rewrite fcat0s; case: eqP.
- by move: E1 E2 E; do 2![move/supp_nilE=>->]; case: disjP.
- by move/supp_nilE: E2 E1=>-> <-; rewrite fcat0s eq_refl.
have [k H3]: exists k, k \in supp f1'.
- case: (supp f1') {E1 E} E2=>[|x s _] //.
  by exists x; rewrite inE eq_refl.
suff: k \in supp (fcat f1' f2') by rewrite E1.
by rewrite supp_fcat inE /= H3.
Qed.

(* some transformation lemmas *)

(* AKA conicity *)
Lemma umap0E f1 f2 : f1 \+ f2 = Unit -> f1 = Unit /\ f2 = Unit.
Proof. 
by move/unitbP; rewrite um_unitbUn=>/andP [H1 H2]; split; apply/unitbP.
Qed.

Lemma validEb f : reflect (valid f /\ forall k, k \notin dom f) (unitb f).
Proof.
case: unitbP=>E; constructor; first by rewrite E valid_unit dom0.
case=>V' H; apply: E; move: V' H.
rewrite !umEX /UM.valid /UM.dom /UM.empty -{3}[f]tfE.
case: (UMC_from f)=>[|f' F] // _ H; rewrite !umEX.
apply/supp_nilE; case: (supp f') H=>// x s /(_ x).
by rewrite inE eq_refl.
Qed.

Lemma validUnEb f : valid (f \+ f) = unitb f.
Proof.
case E : (unitb f); first by move/unitbP: E=>->; rewrite unitL valid_unit.
case: validUn=>// W _ H; move/validEb: E; elim; split=>// k.
by apply/negP=>/[dup]/H/negbTE ->.
Qed.

End UnitbLemmas.


(**********)
(* undefb *)
(**********)

Section UndefbLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma undefb_undef : undefb (undef : U).
Proof. by rewrite !umEX. Qed.

Lemma undefbP f : reflect (f = undef) (undefb f).
Proof.
rewrite !umEX /UM.undefb -{1}[f]tfE.
by case: (UMC_from f)=>[|f' F]; constructor; rewrite !umEX.
Qed.

Lemma undefbE f : f = undef <-> undefb f.
Proof. by case: undefbP. Qed.

Lemma undefb0 : undefb (Unit : U) = false.
Proof. by case: undefbP=>// /esym/undef0. Qed.

Lemma valid_undefbI f : valid f -> undefb f = false.
Proof.
move=>W; apply/negP=>/undefbP E.
by move: E W=>->; rewrite valid_undef.
Qed.

End UndefbLemmas.


(**********)
(* dom_eq *)
(**********)

Section DomEqDef.
Variables (K : ordType) (C1 C2 : pred K) (V1 V2 : Type).
Variable U1 : union_map C1 V1.
Variable U2 : union_map C2 V2.

Definition dom_eq (f1 : U1) (f2 : U2) :=
  (valid f1 == valid f2) && (dom f1 == dom f2).

End DomEqDef.

Section DomEqLemmas.
Variables (K : ordType) (C1 C2 C3 : pred K) (V1 V2 V3 : Type).
Variable U1 : union_map C1 V1.
Variable U2 : union_map C2 V2.
Variable U3 : union_map C3 V3.

Lemma domeqP (f1 : U1) (f2 : U2) :
        reflect (valid f1 = valid f2 /\ dom f1 = dom f2) (dom_eq f1 f2).
Proof. by rewrite /dom_eq; apply/andPP/eqP/eqP. Qed.

Lemma domeqVE (f1 : U1) (f2 : U2) : dom_eq f1 f2 -> valid f1 = valid f2.
Proof. by case/domeqP. Qed.

Lemma domeqDE (f1 : U1) (f2 : U2) : dom_eq f1 f2 -> dom f1 = dom f2.
Proof. by case/domeqP. Qed.

Lemma domeqE (f1 : U1) (f2 : U2) :
        dom_eq f1 f2 -> (valid f1 = valid f2) * (dom f1 = dom f2).
Proof. by move=>H; rewrite (domeqVE H) (domeqDE H). Qed.

Lemma domeq0E (f : U1) : dom_eq f (Unit : U1) -> f = Unit.
Proof.
case/andP=>/eqP; rewrite valid_unit dom0=>H1 H2. 
by apply: dom0E=>//; rewrite (eqP H2).
Qed.

Lemma domeq_unit : dom_eq (Unit : U1) (Unit : U2).
Proof. by rewrite /dom_eq !valid_unit !dom0. Qed.

Lemma domeq_undef : dom_eq (undef : U1) (undef : U2).
Proof. by rewrite /dom_eq !valid_undef !dom_undef. Qed.

Lemma domeq_refl (f : U1) : dom_eq f f.
Proof. by rewrite /dom_eq !eqxx. Qed.

Lemma domeq_sym (f1 : U1) (f2 : U2) : dom_eq f1 f2 -> dom_eq f2 f1.
Proof. by case/andP=>V D; apply/andP; rewrite (eqP V) (eqP D). Qed.

Lemma domeq_trans (f1 : U1) (f2 : U2) (f3 : U3) :
        dom_eq f1 f2 -> dom_eq f2 f3 -> dom_eq f1 f3.
Proof. by rewrite /dom_eq=>/andP [/eqP -> /eqP ->]. Qed.

Lemma domeqVUnE (f1 f1' : U1) (f2 f2' : U2) :
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        valid (f1 \+ f1') = valid (f2 \+ f2').
Proof.
suff L (C1' C2' : pred K) V1' V2' (U1' : union_map C1' V1')
  (U2' : union_map C2' V2') (g1 g1' :  U1') (g2 g2' : U2') :
  dom_eq g1 g2 -> dom_eq g1' g2' ->
  valid (g1 \+ g1') -> valid (g2 \+ g2').
- by move=>D D'; apply/idP/idP; apply: L=>//; apply: domeq_sym.
case/andP=>/eqP E /eqP D /andP [/eqP E' /eqP D']; case: validUn=>// V V' G _.
case: validUn=>//; rewrite -?E ?V -?E' ?V' //.
by move=>k; rewrite -D -D'=>/G/negbTE ->.
Qed.

Lemma domeqVUn (f1 f1' : U1) (f2 f2' : U2) :
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        valid (f1 \+ f1') -> valid (f2 \+ f2').
Proof. by move=>D D'; rewrite -(domeqVUnE D D'). Qed.

Lemma domeqUn (f1 f1' : U1) (f2 f2' : U2) :
        dom_eq f1 f2 -> dom_eq f1' f2' ->
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
move/[dup]=>D /domeqP [V E] /[dup] D' /domeqP [V' E'].
move: (domeqVUnE D D')=>Ex; apply/domeqP=>//.
by rewrite Ex (domKUn Ex E E').
Qed.

Lemma domeqK (f1 f1' : U1) (f2 f2' : U2) :
        valid (f1 \+ f1') ->
        dom_eq (f1 \+ f1') (f2 \+ f2') ->
        dom_eq f1 f2 -> dom_eq f1' f2'.
Proof.
move=>D1 /domeqP [E1 H1] /domeqP [E2 H2]; move: (D1); rewrite E1=>D2.
apply/domeqP; split; first by rewrite (validE2 D1) (validE2 D2).
by apply: domK D1 D2 H1 H2. 
Qed.

Lemma big_domeqUn A (xs : seq A) (f1 : A -> U1) (f2 : A -> U2) :
        (forall x, x \In xs -> dom_eq (f1 x) (f2 x)) ->
        dom_eq (\big[join/Unit]_(i <- xs) (f1 i))
               (\big[join/Unit]_(i <- xs) (f2 i)).
Proof.
elim: xs=>[|x xs IH] D; first by rewrite !big_nil domeq_unit.
rewrite !big_cons; apply: domeqUn.
- by apply: D; rewrite InE; left.
by apply: IH=>z Z; apply: D; rewrite InE; right.
Qed.

End DomEqLemmas.

#[export]
Hint Resolve domeq_refl : core.

Section DomEq1Lemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).

Lemma domeqfU k v (f : U) : k \in dom f -> dom_eq f (upd k v f).
Proof.
move=>D; rewrite /dom_eq validU (dom_cond D) (dom_valid D) /=.
apply/eqP/domE=>x; rewrite domU inE (dom_cond D) (dom_valid D).
by case: eqP=>// ->.
Qed.

Lemma domeqUf k v (f : U) : k \in dom f -> dom_eq (upd k v f) f.
Proof. by move=>D; apply/domeq_sym/domeqfU. Qed.

Lemma domeqfUn (f f1 f2 f1' f2' : U) :
        dom_eq (f \+ f1) f2 -> 
        dom_eq f1' (f \+ f2') ->
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof.
move=>D1 D2; apply: (domeq_trans (f2:=f1 \+ f \+ f2')).
- by rewrite -joinA; apply: domeqUn.
by rewrite -joinA joinCA joinA; apply: domeqUn.
Qed.

Lemma domeqUnf (f f1 f2 f1' f2' : U) :
        dom_eq f1 (f \+ f2) -> dom_eq (f \+ f1') f2' ->
        dom_eq (f1 \+ f1') (f2 \+ f2').
Proof. 
by move=>D1 D2; rewrite (joinC f1) (joinC f2); apply: domeqfUn D2 D1. 
Qed.

End DomEq1Lemmas.

Section DomEq2Lemmas.
Variables (K : ordType) (C1 C2 : pred K) (V1 V2 : Type). 
Variables (U1 : union_map C1 V1) (U2 : union_map C2 V2).

Lemma domeq_symE (f1 : U1) (f2 : U2) : dom_eq f1 f2 = dom_eq f2 f1.
Proof. by apply/idP/idP; apply: domeq_sym. Qed.

End DomEq2Lemmas.


(**********)
(* update *)
(**********)

Section UpdateLemmas.
Variable (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma upd_undef k v : upd k v undef = undef :> U.
Proof. by rewrite !umEX. Qed.

Lemma upd_condN k v f : ~~ C k -> upd k v f = undef.
Proof.
rewrite !umEX /UM.upd.
case: (UMC_from f)=>[|f' H']=>//.
by case: decP=>//= ->.
Qed.

Lemma upd_inj k v1 v2 f :
        valid f -> C k -> upd k v1 f = upd k v2 f -> v1 = v2.
Proof.
rewrite !umEX /UM.valid /UM.upd.
case: (UMC_from f)=>[|f' F] // _; case: decP=>// H _ E.
have: fnd k (ins k v1 f') = fnd k (ins k v2 f') by rewrite E.
by rewrite !fnd_ins eq_refl; case.
Qed.

Lemma updU k1 k2 v1 v2 f :
        upd k1 v1 (upd k2 v2 f) =
        if k1 == k2 then upd k1 v1 f else upd k2 v2 (upd k1 v1 f).
Proof.
rewrite !umEX /UM.upd.
case: (UMC_from f)=>[|f' H']; case: ifP=>// E;
case: decP=>H1; case: decP=>H2 //; rewrite !umEX.
- by rewrite ins_ins E.
- by rewrite (eqP E) in H2 *.
by rewrite ins_ins E.
Qed.

Lemma updF k1 k2 v f :
        upd k1 v (free f k2) =
        if k1 == k2 then upd k1 v f else free (upd k1 v f) k2.
Proof.
rewrite !umEX /UM.dom /UM.upd /UM.free.
case: (UMC_from f)=>[|f' F] //; case: ifP=>// H1;
by case: decP=>H2 //; rewrite !umEX ins_rem H1.
Qed.

Lemma updUnL k v f1 f2 :
        upd k v (f1 \+ f2) =
        if k \in dom f1 then upd k v f1 \+ f2 else f1 \+ upd k v f2.
Proof.
rewrite !umEX /UM.upd /UM.union /UM.dom.
case: (UMC_from f1) (UMC_from f2)=>[|f1' F1][|f2' F2] //=.
- by case: ifP=>//; case: decP.
case: ifP=>// D; case: ifP=>// H1; case: decP=>// H2.
- rewrite disjC disj_ins disjC D !umEX; case: disjP D=>// H _.
  by rewrite (H _ H1) /= fcat_inss // (H _ H1).
- by rewrite disj_ins H1 D /= !umEX fcat_sins.
- by rewrite disjC disj_ins disjC D andbF.
by rewrite disj_ins D andbF.
Qed.

Lemma updUnR k v f1 f2 :
        upd k v (f1 \+ f2) =
        if k \in dom f2 then f1 \+ upd k v f2 else upd k v f1 \+ f2.
Proof. by rewrite joinC updUnL (joinC f1) (joinC f2). Qed.

Lemma updL k v f1 f2 :
        k \in dom f1 -> upd k v (f1 \+ f2) = upd k v f1 \+ f2.
Proof. by move=>D; rewrite updUnL D. Qed.

Lemma updR k v f1 f2 :
        k \in dom f2 -> upd k v (f1 \+ f2) = f1 \+ upd k v f2.
Proof. by move=>D; rewrite updUnR D. Qed.

Lemma domUE k e f : k \in dom f -> dom (upd k e f) = dom f.
Proof.
move=>H; apply/domE=>x; rewrite domU inE (dom_cond H) /=.
by case: eqP=>// ->; rewrite H (dom_valid H).
Qed.

End UpdateLemmas.


(********)
(* free *)
(********)

Section FreeLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma free0 k : free Unit k = Unit :> U.
Proof. by rewrite !umEX /UM.free /UM.empty rem_empty. Qed.

Lemma free_undef k : free undef k = undef :> U.
Proof. by rewrite !umEX. Qed.

Lemma freeU k1 k2 v f :
        free (upd k2 v f) k1 =
        if k1 == k2 then
          if C k2 then free f k1 else undef
        else upd k2 v (free f k1).
Proof.
rewrite !umEX /UM.free /UM.upd.
case: (UMC_from f)=>[|f' F]; first by case: ifP=>H1 //; case: ifP.
case: ifP=>H1; case: decP=>H2 //=.
- by rewrite H2 !umEX rem_ins H1.
- by case: ifP H2.
by rewrite !umEX rem_ins H1.
Qed.

Lemma freeF k1 k2 f :
        free (free f k2) k1 =
        if k1 == k2 then free f k1 else free (free f k1) k2.
Proof.
rewrite !umEX /UM.free.
by case: (UMC_from f)=>[|f' F]; case: ifP=>// E; rewrite !umEX rem_rem E.
Qed.

Lemma freeUn k f1 f2 :
        free (f1 \+ f2) k =
        if k \in dom (f1 \+ f2) then free f1 k \+ free f2 k
        else f1 \+ f2.
Proof.
rewrite !umEX /UM.free /UM.union /UM.dom.
case: (UMC_from f1) (UMC_from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// E1; rewrite supp_fcat inE /=.
case: ifP=>E2; last by rewrite !umEX rem_supp // supp_fcat inE E2.
rewrite disj_rem; last by rewrite disjC disj_rem // disjC.
rewrite !umEX; case/orP: E2=>E2.
- suff E3: k \notin supp f2' by rewrite -fcat_rems // (rem_supp E3).
  by case: disjP E1 E2=>// H _; move/H.
suff E3: k \notin supp f1' by rewrite -fcat_srem // (rem_supp E3).
by case: disjP E1 E2=>// H _; move/contra: (H k); rewrite negbK.
Qed.

Lemma freeUnV k f1 f2 :
        valid (f1 \+ f2) -> 
        free (f1 \+ f2) k = free f1 k \+ free f2 k.
Proof.
move=>V'; rewrite freeUn domUn V' /=; case: ifP=>//.
by move/negbT; rewrite negb_or; case/andP=>H1 H2; rewrite !dom_free.
Qed.

Lemma freeUnR k f1 f2 : 
        k \notin dom f1 -> 
        free (f1 \+ f2) k = f1 \+ free f2 k.
Proof.
move=>V1; rewrite freeUn domUn inE (negbTE V1) /=.
case: ifP; first by case/andP; rewrite dom_free.
move/negbT; rewrite negb_and; case/orP=>V2; last by rewrite dom_free.
suff: ~~ valid (f1 \+ free f2 k) by move/invalidE: V2=>-> /invalidE ->.
apply: contra V2; case: validUn=>// H1 H2 H _.
case: validUn=>//; first by rewrite H1.
- by move: H2; rewrite validF => ->.
move=>x H3; move: (H _ H3); rewrite domF inE /=.
by case: ifP H3 V1=>[|_ _ _]; [move/eqP=><- -> | move/negbTE=>->].
Qed.

Lemma freeUnL k f1 f2 : 
        k \notin dom f2 -> 
        free (f1 \+ f2) k = free f1 k \+ f2.
Proof. by move=>H; rewrite joinC freeUnR // joinC. Qed.

(* positive re-statement of freeUnL, but requires validity *)
Lemma freeL k f1 f2 :
        valid (f1 \+ f2) -> 
        k \in dom f1 -> 
        free (f1 \+ f2) k = free f1 k \+ f2.
Proof. by move=>W /(dom_inNL W) D; rewrite freeUnL. Qed.

(* positive re-statement of freeUnR, but requires validity *)
Lemma freeR k f1 f2 :
        valid (f1 \+ f2) -> 
        k \in dom f2 -> 
        free (f1 \+ f2) k = f1 \+ free f2 k.
Proof. by rewrite !(joinC f1); apply: freeL. Qed.

Lemma freeND k f : k \notin dom f -> free f k = f.
Proof. by move=>W; rewrite -[f]unitR freeUnR // free0. Qed.

End FreeLemmas.


(********)
(* find *)
(********)

Section FindLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma find0E k : find k (Unit : U) = None.
Proof. by rewrite !umEX /UM.find /= fnd_empty. Qed.

Lemma find_undef k : find k (undef : U) = None.
Proof. by rewrite !umEX /UM.find. Qed.

Lemma find_cond k f : ~~ C k -> find k f = None.
Proof.
rewrite !umEX /UM.find; case: (UMC_from f)=>[|f' F] // H.
suff: k \notin supp f' by case: suppP.
by apply: contra H; case: allP F=>// F _ /F.
Qed.

Lemma findU k1 k2 v f :
        find k1 (upd k2 v f) =
        if k1 == k2 then
          if C k2 && valid f then Some v else None
        else if C k2 then find k1 f else None.
Proof.
rewrite !umEX /UM.valid /UM.find /UM.upd.
case: (UMC_from f)=>[|f' F]; first by rewrite andbF !if_same.
case: decP=>H; first by rewrite H /= fnd_ins.
by rewrite (introF idP H) /= if_same.
Qed.

Lemma findF k1 k2 f :
        find k1 (free f k2) = if k1 == k2 then None else find k1 f.
Proof.
rewrite !umEX /UM.find /UM.free.
case: (UMC_from f)=>[|f' F]; first by rewrite if_same.
by rewrite fnd_rem.
Qed.

Lemma findUnL k f1 f2 :
        valid (f1 \+ f2) ->
        find k (f1 \+ f2) = if k \in dom f1 then find k f1 else find k f2.
Proof.
rewrite !umEX /UM.valid /UM.find /UM.union /UM.dom.
case: (UMC_from f1) (UMC_from f2)=>[|f1' F1][|f2' F2] //.
case: ifP=>// D _; case: ifP=>E1; last first.
- rewrite fnd_fcat; case: ifP=>// E2.
  by rewrite fnd_supp ?E1 // fnd_supp ?E2.
suff E2: k \notin supp f2' by rewrite fnd_fcat (negbTE E2).
by case: disjP D E1=>// H _; apply: H.
Qed.

Lemma findUnR k f1 f2 :
        valid (f1 \+ f2) ->
        find k (f1 \+ f2) = if k \in dom f2 then find k f2 else find k f1.
Proof. by rewrite joinC=>D; rewrite findUnL. Qed.

Lemma find_eta f1 f2 :
        valid f1 -> valid f2 ->
        (forall k, find k f1 = find k f2) -> f1 = f2.
Proof.
rewrite !umEX /UM.valid /UM.find -{2 3}[f1]tfE -{2 3}[f2]tfE.
case: (UMC_from f1) (UMC_from f2)=>[|f1' F1][|f2' F2] // _ _ H.
by rewrite !umEX; apply/fmapP=>k; move: (H k); rewrite !umEX.
Qed.

End FindLemmas.

(* if maps store units, i.e., we keep them just for sets *)
(* then we can simplify the find_eta lemma a bit *)

Lemma domeq_eta (K : ordType) (C : pred K) (U : union_map C unit) (f1 f2 : U) :
        dom_eq f1 f2 -> f1 = f2.
Proof.
case/domeqP=>V E; case V1 : (valid f1); last first.
- by move: V1 (V1); rewrite {1}V; do 2![move/negbT/invalidE=>->].
apply: find_eta=>//; first by rewrite -V.
move=>k; case D : (k \in dom f1); move: D (D); rewrite {1}E.
- by do 2![case: dom_find=>// [[_ _]]].
by do 2![case: dom_find=>// _].
Qed.

(**********)
(* assocs *)
(**********)

Section AssocsLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Type f : U.

Lemma assocs_valid k f : k \In assocs f -> valid f.
Proof. by rewrite !umEX; case: (UMC_from f). Qed.

Lemma assocs0 : assocs (Unit : U) = [::].
Proof. by rewrite !umEX. Qed.

Lemma assocs_undef : assocs (undef : U) = [::].
Proof. by rewrite !umEX. Qed.

Lemma assocsF f x :
        assocs (free f x) = filter (fun kv => kv.1 != x) (assocs f).
Proof. by rewrite !umEX /UM.assocs; case: (UMC_from f)=>//=; case. Qed.

Lemma assocs_perm f1 f2 :
        valid (f1 \+ f2) -> perm (assocs (f1 \+ f2)) (assocs f1 ++ assocs f2).
Proof.
rewrite !umEX /UM.assocs/UM.union/UM.pts/UM.dom/supp /=.
case: (UMC_from f1)=>//= g1 H1; case: (UMC_from f2)=>//= g2 H2.
by case: ifP=>// D _; apply: seqof_fcat_perm D.
Qed.

Lemma assocs_dom f : dom f = map fst (assocs f).
Proof. by rewrite !umEX; case: (UMC_from f). Qed.

Lemma size_assocs f : size (assocs f) = size (dom f).
Proof. by rewrite assocs_dom size_map. Qed.

End AssocsLemmas.

Lemma uniq_assocs K C (V : eqType) (U : @union_map K C V) (f : U) :
        uniq (assocs f).
Proof.
rewrite !umEX /UM.assocs /=; case: (UMC_from f)=>[|[s H _]] //=.
by move/(sorted_uniq (@trans K) (@irr K)): H; apply: map_uniq.
Qed.

Lemma assocs_map K C (V : Type) (U : @union_map K C V) (f : U) k v1 v2 :
        (k, v1) \In assocs f -> (k, v2) \In assocs f -> v1 = v2.
Proof.
rewrite !umEX; case: (UMC_from f)=>//= g _; case: g=>g S /= H1 H2.
have {S} S' : uniq [seq key i | i <- g].
- by apply: sorted_uniq S; [apply: trans | apply: irr].
have X : forall (g : seq (K*V)) k v, (k, v) \In g -> k \in map fst g.
- elim=>[|[ka va] h IH] // kb vb.
  - rewrite !InE; case; first by case=>-> _; rewrite inE eq_refl.
  by move/IH; rewrite inE=>->; rewrite orbT.
elim: g k v1 v2 S' H1 H2=>[|[ka va] g IH] //= k v1 v2.
case/andP=>U1 U2; rewrite !InE.
case; first by case=>->->; case=>[[]|/X] //; rewrite (negbTE U1).
move=>H1 H2; case: H2 H1.
- by case=>->-> /X; rewrite (negbTE U1).
by move=>H1 H2; apply: IH H2 H1.
Qed.

(*********************************)
(* Interaction of subset and dom *)
(*********************************)

Section Interaction.
Variables (K : ordType) (C : pred K) (A : Type) (U : union_map C A).
Implicit Types (x y a b : U) (p q : pred K).

(* Some equivalent forms for subset with dom *)

Lemma subdom_indomE p x : {subset dom x <= p} = {in dom x, p =1 predT}.
Proof. by []. Qed.

(* Some equivalent forms for subset expressing disjointness *)

Lemma subset_disjE p q : {subset p <= predC q} <-> [predI p & q] =1 pred0.
Proof.
split=>H a /=; first by case X: (a \in p)=>//; move/H/negbTE: X.
by move=>D; move: (H a); rewrite inE /= D; move/negbT.
Qed.

Lemma valid_subdom x y : valid (x \+ y) -> {subset dom x <= [predC dom y]}.
Proof. by case: validUn. Qed.

Lemma subdom_valid x y :
        {subset dom x <= [predC dom y]} ->
        valid x -> valid y -> valid (x \+ y).
Proof. by move=>H X Y; case: validUn; rewrite ?X ?Y=>// k /H /negbTE /= ->. Qed.

Lemma subdom_validL x y a :
        valid a ->
        valid (x \+ y) -> {subset dom a <= dom x} -> valid (a \+ y).
Proof.
rewrite !validUnAE=>-> /and3P [_ -> D] S.
by apply: sub_all D=>z /(contra (S z)).
Qed.

End Interaction.


(****************************)
(* Generic points-to lemmas *)
(****************************)

Section PointsToLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U).

Lemma ptsU k v : pts k v = upd k v Unit :> U.
Proof. by rewrite /ptsx !umEX /UM.pts /UM.upd; case: decP. Qed.

Lemma pts_condN k v : ~~ C k -> pts k v = undef :> U.
Proof. by move=>C'; rewrite ptsU upd_condN. Qed.

Lemma domPtK k v : dom (pts k v : U) = if C k then [:: k] else [::].
Proof.
rewrite /ptsx !umEX /= /UM.dom /supp /UM.pts /UM.upd /UM.empty /=.
by case D : (decP _)=>[a|a] /=; rewrite ?a ?(introF idP a).
Qed.

(* a weaker legacy version of domPtK *)
Lemma domPt k v : dom (pts k v : U) =i [pred x | C k & k == x].
Proof. 
by move=>x; rewrite ptsU domU !inE eq_sym valid_unit dom0; case: eqP.
Qed.

Lemma validPt k v : valid (pts k v : U) = C k.
Proof. by rewrite ptsU validU valid_unit andbT. Qed.

Lemma domPtV k v : valid (pts k v : U) -> k \in dom (pts k v : U).
Proof. by move=>D; rewrite domPtK -(validPt k v) D inE. Qed.

Lemma findPt k v : find k (pts k v : U) = if C k then Some v else None.
Proof. by rewrite ptsU findU eq_refl /= valid_unit andbT. Qed.

Lemma findPt2 k1 k2 v :
        find k1 (pts k2 v : U) =
        if (k1 == k2) && C k2 then Some v else None.
Proof.
by rewrite ptsU findU valid_unit andbT find0E; case: ifP=>//=; case: ifP.
Qed.

Lemma findPt_inv k1 k2 v w :
        find k1 (pts k2 v : U) = Some w -> [/\ k1 = k2, v = w & C k2].
Proof.
rewrite ptsU findU; case: eqP; last by case: ifP=>//; rewrite find0E.
by move=>->; rewrite valid_unit andbT; case: ifP=>// _ [->].
Qed.

Lemma freePt2 k1 k2 v :
        C k2 ->
        free (pts k2 v) k1 = if k1 == k2 then Unit else pts k2 v :> U.
Proof. by move=>N; rewrite ptsU freeU free0 N. Qed.

Lemma freePt k v :
        C k -> free (pts k v : U) k = Unit.
Proof. by move=>N; rewrite freePt2 // eq_refl. Qed.

Lemma cancelPt k v1 v2 :
        valid (pts k v1 : U) -> pts k v1 = pts k v2 :> U -> v1 = v2.
Proof. by rewrite validPt !ptsU; apply: upd_inj. Qed.

Lemma cancelPt2 k1 k2 v1 v2 :
        valid (pts k1 v1 : U) ->
        pts k1 v1 = pts k2 v2 :> U -> (k1, v1) = (k2, v2).
Proof.
move=>H E; have : dom (pts k1 v1 : U) = dom (pts k2 v2 : U) by rewrite E.
rewrite !domPtK -(validPt _ v1) -(validPt _ v2) -E H.
by case=>E'; rewrite -{k2}E' in E *; rewrite (cancelPt H E).
Qed.

Lemma updPt k v1 v2 : upd k v1 (pts k v2) = pts k v1 :> U.
Proof. by rewrite !ptsU updU eq_refl. Qed.

Lemma um_unitbPt k v : unitb (pts k v : U) = false.
Proof. by rewrite ptsU um_unitbU. Qed.

(* assocs *)

Lemma assocsPt k v :
        assocs (pts k v : U) =
        if C k then [:: (k, v)] else [::].
Proof.
rewrite /ptsx !umEX /UM.assocs/UM.pts /=.
by case E: decP=>[a|a] /=; [rewrite a | case: ifP].
Qed.

Lemma assocsUnPt f k v :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        assocs (f \+ pts k v) = rcons (assocs f) (k, v).
Proof.
rewrite /ptsx !umEX /UM.assocs/UM.union/UM.pts/UM.dom/supp /=.
case: (UMC_from f)=>//=; case: decP=>//= H1 g H2; case: ifP=>//= _ _.
by case: allP=>//; case: g H2=>// s1 H2 H3 H4 _; apply: first_ins' H4.
Qed.

Lemma assocsPtUn f k v :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        assocs (pts k v \+ f) = (k, v) :: (assocs f).
Proof.
rewrite /ptsx !umEX /UM.assocs/UM.union/UM.pts/UM.dom/supp /=.
case: decP=>// H1; case: (UMC_from f)=>//= g H2.
rewrite /disj /= andbT; case: ifP=>//= D _ H3.
rewrite (fcat_inss _ (@nil K V) D) fcat0s.
case: g H2 D H3=>//= g P H2 D H3.
by apply: last_ins'; rewrite path_min_sorted.
Qed.

(* valid *)

Lemma validPtUn k v f :
        valid (pts k v \+ f) = [&& C k, valid f & k \notin dom f].
Proof.
case: validUn=>//; last 1 first.
- rewrite validPt=>H1 -> H2; rewrite H1 (H2 k) //.
  by rewrite domPtK H1 inE.
- by rewrite validPt; move/negbTE=>->.
- by move/negbTE=>->; rewrite andbF.
rewrite domPtK=>x; case: ifP=>// _.
by rewrite inE=>/eqP ->->; rewrite andbF.
Qed.

Lemma validUnPt k v f :
        valid (f \+ pts k v) = [&& C k, valid f & k \notin dom f].
Proof. by rewrite joinC; apply: validPtUn. Qed.

Lemma validPtUnE v2 v1 k f : valid (pts k v1 \+ f) = valid (pts k v2 \+ f).
Proof. by rewrite !validPtUn. Qed.

Lemma validUnPtE v2 v1 k f : valid (f \+ pts k v1) = valid (f \+ pts k v2).
Proof. by rewrite !validUnPt. Qed.

Lemma validPtPt v1 v2 k : valid (pts k v1 \+ pts k v2 : U) = false.
Proof. by rewrite (validPtUnE v2) validUnEb um_unitbPt. Qed.

Lemma validPt2 k1 k2 v1 v2 : 
        valid (pts k1 v1 \+ pts k2 v2 : U) = 
        [&& C k1, C k2 & k1 != k2].
Proof.
rewrite validPtUn validPt domPt inE negb_and.
by case: (C k2)=>//=; rewrite eq_sym.
Qed.

(* the projections from validPtUn are often useful *)

Lemma validPtUnI v1 k f :
        valid (pts k v1 \+ f) -> [&& C k, valid f & k \notin dom f].
Proof. by rewrite validPtUn. Qed.

Lemma validUnPtI v1 k f :
        valid (f \+ pts k v1) -> [&& C k, valid f & k \notin dom f].
Proof. by rewrite validUnPt. Qed.

Lemma validPtUn_cond k v f : valid (pts k v \+ f) -> C k.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPt_cond k v f : valid (f \+ pts k v) -> C k.
Proof. by rewrite joinC; apply: validPtUn_cond. Qed.

Lemma validPtUnD k v f : valid (pts k v \+ f) -> k \notin dom f.
Proof. by rewrite validPtUn; case/and3P. Qed.

Lemma validUnPtD k v f : valid (f \+ pts k v) -> k \notin dom f.
Proof. by rewrite joinC; apply: validPtUnD. Qed.

(* dom *)

Lemma domPtUn k v f :
        dom (pts k v \+ f) =i
        [pred x | valid (pts k v \+ f) & (k == x) || (x \in dom f)].
Proof.
move=>x; rewrite domUn !inE !validPtUn domPt !inE.
by rewrite -!andbA; case: (C k).
Qed.

Lemma domUnPt k v f :
        dom (f \+ pts k v) =i
        [pred x | valid (f \+ pts k v) & (k == x) || (x \in dom f)].
Proof. by rewrite joinC; apply: domPtUn. Qed.

Lemma domPtUnE k v f : k \in dom (pts k v \+ f) = valid (pts k v \+ f).
Proof. by rewrite domPtUn inE eq_refl andbT. Qed.

Lemma domUnPtE k v f : k \in dom (f \+ pts k v) = valid (f \+ pts k v).
Proof. by rewrite joinC; apply: domPtUnE. Qed.

Lemma domPtUnE2 k v1 v2 f : dom (pts k v1 \+ f) = dom (pts k v2 \+ f).
Proof. by apply/domE=>x; rewrite !domPtUn !validPtUn. Qed.

Lemma domUnPtE2 k v1 v2 f : dom (f \+ pts k v1) = dom (f \+ pts k v2).
Proof. by rewrite !(joinC f); apply: domPtUnE2. Qed.

Lemma domPt2 k1 k2 v1 v2 x : 
        x \in dom (pts k1 v1 \+ pts k2 v2 : U) =
        [&& C k1, C k2, k1 != k2 & x \in pred2 k1 k2].
Proof.
rewrite domPtUn !inE validPt2 domPt inE !(eq_sym x).
by case: (C k1)=>//=; case: (C k2).
Qed.

Lemma validxx f : valid (f \+ f) -> dom f =i pred0.
Proof. by case: validUn=>// _ _ L _ z; case: (_ \in _) (L z)=>//; elim. Qed.

Lemma domPtUnK k v f :
        valid (pts k v \+ f) ->
        all (ord k) (dom f) ->
        dom (pts k v \+ f) = k :: dom f.
Proof.
move=>W H; apply: ord_sorted_eq=>//=.
- by rewrite path_min_sorted //; apply: sorted_dom.
by move=>x; rewrite domPtUn !inE W eq_sym.
Qed.

Lemma domUnPtK k v f :
        valid (f \+ pts k v) ->
        all (ord^~k) (dom f) ->
        dom (f \+ pts k v) = rcons (dom f) k.
Proof.
move=>W H; apply: ord_sorted_eq=>//=.
- rewrite -(rev_sorted (fun x=>ord^~x)) rev_rcons /=.
  by rewrite path_min_sorted ?rev_sorted // all_rev.
by move=>x; rewrite domUnPt inE W mem_rcons inE eq_sym.
Qed.

Lemma size_domPtUn k v f :
        valid (pts k v \+ f) -> 
        size (dom (pts k v \+ f)) = 1 + size (dom f).
Proof. by move=>W; rewrite size_domUn // domPtK (validPtUn_cond W). Qed.

(* find *)

Lemma findPtUn k v f :
        valid (pts k v \+ f) -> find k (pts k v \+ f) = Some v.
Proof.
move=>V'; rewrite findUnL // domPt inE.
by rewrite ptsU findU eq_refl valid_unit (validPtUn_cond V').
Qed.

Lemma findUnPt k v f :
        valid (f \+ pts k v) -> find k (f \+ pts k v) = Some v.
Proof. by rewrite joinC; apply: findPtUn. Qed.

Lemma findPtUn2 k1 k2 v f :
         valid (pts k2 v \+ f) ->
         find k1 (pts k2 v \+ f) =
         if k1 == k2 then Some v else find k1 f.
Proof.
move=>V'; rewrite findUnL // domPt inE eq_sym.
by rewrite findPt2 (validPtUn_cond V') andbT /=; case: ifP=>// ->.
Qed.

Lemma findUnPt2 k1 k2 v f :
         valid (f \+ pts k2 v) ->
         find k1 (f \+ pts k2 v) =
         if k1 == k2 then Some v else find k1 f.
Proof. by rewrite joinC; apply: findPtUn2. Qed.

(* free *)

Lemma freePtUn2 k1 k2 v f :
        valid (pts k2 v \+ f) ->
        free (pts k2 v \+ f) k1 =
        if k1 == k2 then f else pts k2 v \+ free f k1.
Proof.
move=>V'; rewrite freeUn domPtUn inE V' /= eq_sym.
rewrite ptsU freeU (validPtUn_cond V') free0.
case: eqP=>/= E; first by rewrite E unitL (dom_free (validPtUnD V')).
by case: ifP=>// N; rewrite dom_free // N.
Qed.

Lemma freeUnPt2 k1 k2 v f :
        valid (f \+ pts k2 v) ->
        free (f \+ pts k2 v) k1 =
        if k1 == k2 then f else free f k1 \+ pts k2 v.
Proof. by rewrite !(joinC _ (pts k2 v)); apply: freePtUn2. Qed.

Lemma freePtUn k v f :
        valid (pts k v \+ f) -> free (pts k v \+ f) k = f.
Proof. by move=>V'; rewrite freePtUn2 // eq_refl. Qed.

Lemma freeUnPt k v f :
        valid (f \+ pts k v) -> free (f \+ pts k v) k = f.
Proof. by rewrite joinC; apply: freePtUn. Qed.

Lemma freeX k v f1 f2 : valid f1 -> f1 = pts k v \+ f2 -> f2 = free f1 k.
Proof. by move=>W E; rewrite E freePtUn // -E. Qed.

(* upd *)

Lemma updPtUn k v1 v2 f : upd k v1 (pts k v2 \+ f) = pts k v1 \+ f.
Proof.
case V1 : (valid (pts k v2 \+ f)).
- by rewrite updUnL domPt inE eq_refl updPt (validPtUn_cond V1).
have V2 : valid (pts k v1 \+ f) = false.
- by rewrite !validPtUn in V1 *.
move/negbT/invalidE: V1=>->; move/negbT/invalidE: V2=>->.
by apply: upd_undef.
Qed.

Lemma updUnPt k v1 v2 f : upd k v1 (f \+ pts k v2) = f \+ pts k v1.
Proof. by rewrite !(joinC f); apply: updPtUn. Qed.

Lemma upd_eta k v f : upd k v f = pts k v \+ free f k.
Proof.
case: (normalP f)=>[->|W]; first by rewrite upd_undef free_undef join_undef.
case H : (C k); last first.
- by move/negbT: H=>H; rewrite (upd_condN v) // pts_condN // undef_join.
have W' : valid (pts k v \+ free f k).
- by rewrite validPtUn H validF W domF inE eq_refl.
apply: find_eta=>//; first by rewrite validU H W.
by move=>k'; rewrite findU H W findPtUn2 // findF; case: eqP.
Qed.

Lemma upd_eta2 k v f : k \notin dom f -> upd k v f = pts k v \+ f.
Proof. by move=>D; rewrite upd_eta freeND. Qed.

(* um_unitb *)

Lemma um_unitbPtUn k v f : unitb (pts k v \+ f) = false.
Proof. by rewrite um_unitbUn um_unitbPt. Qed.

Lemma um_unitbUnPt k v f : unitb (f \+ pts k v) = false.
Proof. by rewrite joinC; apply: um_unitbPtUn. Qed.

(* undef *)

Lemma pts_undef k v : pts k v = undef :> U <-> ~~ C k.
Proof. by rewrite -(validPt k v) invalidE. Qed.

Lemma pts_undef2 k v1 v2 : pts k v1 \+ pts k v2 = undef :> U.
Proof.
apply/invalidE; rewrite validPtUn validPt domPt !negb_and negb_or eq_refl.
by case: (C k).
Qed.

(* umpleq *)

Lemma umpleq_dom k v f : valid f -> [pcm pts k v <= f] -> k \in dom f.
Proof. by move=>W [z E]; subst f; rewrite domPtUn inE W eq_refl. Qed.

(* others *)

Lemma um_eta k f :
        k \in dom f -> exists v, find k f = Some v /\ f = pts k v \+ free f k.
Proof.
case: dom_find=>// v E1 E2 _; exists v; split=>//.
by rewrite {1}E2 -{1}[free f k]unitL updUnR domF inE /= eq_refl ptsU.
Qed.

Lemma um_eta2 k v f : find k f = Some v -> f = pts k v \+ free f k.
Proof. by move=>E; case/um_eta: (find_some E)=>v' []; rewrite E; case=><-. Qed.

Lemma cancel k v1 v2 f1 f2 :
        valid (pts k v1 \+ f1) ->
        pts k v1 \+ f1 = pts k v2 \+ f2 -> [/\ v1 = v2, valid f1 & f1 = f2].
Proof.
move=>V' E.
have: find k (pts k v1 \+ f1) = find k (pts k v2 \+ f2) by rewrite E.
rewrite !findPtUn -?E //; case=>X.
by rewrite -{}X in E *; rewrite -(joinxK V' E) (validE2 V').
Qed.

Lemma cancel2 k1 k2 f1 f2 v1 v2 :
        valid (pts k1 v1 \+ f1) ->
        pts k1 v1 \+ f1 = pts k2 v2 \+ f2 ->
        if k1 == k2 then v1 = v2 /\ f1 = f2
        else [/\ free f2 k1 = free f1 k2,
                 f1 = pts k2 v2 \+ free f2 k1 &
                 f2 = pts k1 v1 \+ free f1 k2].
Proof.
move=>V1 E; case: ifP=>X.
- by rewrite -(eqP X) in E; case/(cancel V1): E.
move: (V1); rewrite E => V2.
have E' : f2 = pts k1 v1 \+ free f1 k2.
- move: (erefl (free (pts k1 v1 \+ f1) k2)).
  rewrite {2}E freeUn E domPtUn inE V2 eq_refl /=.
  by rewrite ptsU freeU eq_sym X free0 -ptsU freePtUn.
suff E'' : free f1 k2 = free f2 k1.
- by rewrite -E''; rewrite E' joinCA in E; case/(cancel V1): E.
move: (erefl (free f2 k1)).
by rewrite {1}E' freePtUn // -E' (validE2 V2).
Qed.

Lemma um_contra k v f g : f = pts k v \+ g \+ f -> ~~ valid f.
Proof.
move=>E; rewrite E -joinAC -joinA validPtUn.
rewrite {2}E -!joinA domPtUn !inE.
by rewrite eq_refl andbT !joinA -E andbN andbF.
Qed.

(* induction over union maps, expressed with pts and \+ *)

(* forward progressing over keys *)
Lemma um_indf (P : U -> Prop) :
         P undef -> P Unit ->
         (forall k v f, P f -> valid (pts k v \+ f) ->
             path ord k (dom f) ->
             P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite /ptsx !umEX => H1 H2 H3 f; rewrite -[f]tfE.
apply: (UM.base_indf (P := (fun b => P (UMC_to b))))=>//.
move=>k v g H V1; move: (H3 k v _ H); rewrite !umEX.
by apply.
Qed.

(* backward progressing over keys *)
Lemma um_indb (P : U -> Prop) :
         P undef -> P Unit ->
         (forall k v f, P f -> valid (f \+ pts k v) ->
            (forall x, x \in dom f -> ord x k) ->
            P (pts k v \+ f)) ->
         forall f, P f.
Proof.
rewrite /ptsx !umEX => H1 H2 H3 f; rewrite -[f]tfE.
apply: (UM.base_indb (P := (fun b => P (UMC_to b))))=>//.
move=>k v g H V1; move: (H3 k v _ H); rewrite !umEX.
by apply.
Qed.

(* validity holds pairwise *)
Lemma um_valid3 f1 f2 f3 :
        valid (f1 \+ f2 \+ f3) =
        [&& valid (f1 \+ f2), valid (f2 \+ f3) & valid (f1 \+ f3)].
Proof.
apply/idP/and3P; first by move=>W; rewrite !(validLE3 W).
case=>V1 V2 V3; case: validUn=>//; rewrite ?V1 ?(validE2 V2) // => k.
by rewrite domUn inE V1; case/orP; [move: V3 | move: V2];
   case: validUn =>// _ _ X _ /X /negbTE ->.
Qed.

(* points-to is a prime element of the monoid *)
Lemma um_prime f1 f2 k v :
        C k ->
        f1 \+ f2 = pts k v ->
        f1 = pts k v /\ f2 = Unit \/
        f1 = Unit /\ f2 = pts k v.
Proof.
move: f1 f2; apply: um_indf=>[f1|f2 _|k2 w2 f1 _ _ _ f X E].
- rewrite undef_join -(validPt _ v)=>W E.
  by rewrite -E in W; rewrite valid_undef in W.
- by rewrite unitL=>->; right.
have W : valid (pts k2 w2 \+ (f1 \+ f)).
- by rewrite -(validPt _ v) -E -joinA in X.
rewrite -[pts k v]unitR -joinA in E.
move/(cancel2 W): E; case: ifP.
- by move/eqP=>-> [->] /umap0E [->->]; rewrite unitR; left.
by move=>_ [_ _] /esym/unitbP; rewrite um_unitbPtUn.
Qed.

(* also a simple rearrangment equation *)
Definition pullk (k : K) (v : V) (f : U) := pull (pts k v) f.

End PointsToLemmas.

Prenex Implicits validPtUn_cond findPt_inv um_eta2 um_contra.
Prenex Implicits validPtUnD validUnPtD cancelPt cancelPt2 um_prime.

(* dom_eq *)

Section DomeqPtLemmas.
Variables (K : ordType) (C1 C2 : pred K) (V1 V2 : Type).
Variables (U1 : union_map C1 V1) (U2 : union_map C2 V2).

Lemma domeqPt (k : K) (v1 : V1) (v2 : V2) :
        C1 k = C2 k ->
        dom_eq (pts k v1 : U1) (pts k v2 : U2).
Proof. by move=>E; apply/domeqP; rewrite !validPt !domPtK E. Qed.

Lemma domeqPtUn k v1 v2 (f1 : U1) (f2 : U2) : 
        C1 k = C2 k ->
        dom_eq f1 f2 -> dom_eq (pts k v1 \+ f1) (pts k v2 \+ f2).
Proof. by move=>E; apply: domeqUn=>//; apply: domeqPt. Qed.

Lemma domeqUnPt k v1 v2 (f1 : U1) (f2 : U2) :
        C1 k = C2 k -> 
        dom_eq f1 f2 -> dom_eq (f1 \+ pts k v1) (f2 \+ pts k v2).
Proof. by rewrite (joinC f1) (joinC f2); apply: domeqPtUn. Qed.

End DomeqPtLemmas.

#[export]
Hint Resolve domeqPt domeqPtUn domeqUnPt : core.

(* decidable equality for umaps *)

Section EqPtLemmas.
Variables (K : ordType) (C : pred K) (V : eqType).
Variables (U : union_map C V).
Notation Ue := 
  (Equality.pack_ (Equality.Mixin (union_map_eqP (U:=U)))).

Lemma umPtPtE (k1 k2 : K) (v1 v2 : V) :
        (pts k1 v1 == pts k2 v2 :> Ue) = 
        if C k1 then [&& C k2, k1 == k2 & v1 == v2] else ~~ C k2.
Proof.
case D1 : (C k1); last first.
- case D2 : (C k2); rewrite pts_condN ?D1 //.  
  - by apply/eqP/nesym; rewrite pts_undef D2. 
  by rewrite pts_condN ?D2 // eq_refl.
rewrite -(validPt U k1 v1) -(validPt U k2 v2) in D1 *.
apply/idP/idP.
- by case/eqP/(cancelPt2 D1)=><-<-; rewrite D1 !eq_refl.
by case/and3P=>_ /eqP -> /eqP ->.
Qed.

Lemma umPtPtEq (k1 k2 : K) (v1 v2 : V) :
        (pts k1 v1 == pts k2 v2 :> Ue) = 
        [&& C k1 == C k2, k1 == k2 & v1 == v2] || 
        (~~ C k1 && ~~ C k2).
Proof.
rewrite umPtPtE.
case D1 : (C k1); case D2 : (C k2)=>//=.
- by rewrite orbF.
by rewrite orbT.
Qed.

Lemma umPt0E (k : K) (v : V) : (pts k v == Unit :> Ue) = false.
Proof. by apply/eqP=>/unitbP; rewrite um_unitbPt. Qed.

Lemma um0PtE (k : K) (v : V) : (Unit == pts k v :> Ue) = false.
Proof. by rewrite eq_sym umPt0E. Qed.

Lemma umPtUndefE (k : K) (v : V) : (pts k v == undef :> Ue) = ~~ C k.
Proof. by apply/idP/idP=>[|H]; [move/eqP/pts_undef|apply/eqP/pts_undef]. Qed.

Lemma umUndefPtE (k : K) (v : V) : (undef == pts k v :> Ue) = ~~ C k.
Proof. by rewrite eq_sym umPtUndefE. Qed.

Lemma umUndef0E : (undef == Unit :> Ue) = false.
Proof. by apply/eqP/undef0. Qed.

Lemma um0UndefE : (Unit == undef :> Ue) = false.
Proof. by rewrite eq_sym umUndef0E. Qed.

Lemma umPtUE (k : K) (v : V) f : (pts k v \+ f == Unit :> Ue) = false.
Proof. by apply/eqP=>/umap0E/proj1/unitbP; rewrite um_unitbPt. Qed.

Lemma umUPtE (k : K) (v : V) f : (f \+ pts k v == Unit :> Ue) = false.
Proof. by rewrite joinC umPtUE. Qed.

Lemma umPtUPtE (k1 k2 : K) (v1 v2 : V) f :
        pts k1 v1 \+ f == pts k2 v2 :> Ue = 
        if C k1 then 
          if C k2 then [&& k1 == k2, v1 == v2 & unitb f]
          else ~~ valid (pts k1 v1 \+ f)
        else ~~ C k2.
Proof.
case D1 : (C k1); last first.
- rewrite pts_condN ?D1 //= undef_join eq_sym.
  case D2 : (C k2).
  - by apply/eqP=>/=; rewrite pts_undef D2.
  by rewrite pts_condN ?D2 // eq_refl.
case D2 : (C k2); last first.
- rewrite (pts_condN U v2) ?D2 //=; apply/idP/idP.
  - by move/eqP=>/undefbP; rewrite undefNV. 
  by move=>D; apply/eqP/undefbP; rewrite undefNV.
apply/idP/idP; last first.
- by case/and3P=>/eqP -> /eqP -> /unitbP ->; rewrite unitR.
case/eqP/(um_prime D2); case. 
- move/(cancelPt2 _); rewrite validPt=>/(_ D1) [->->->].
  by rewrite !eq_refl unitb0.
by move/unitbP; rewrite um_unitbPt. 
Qed.

Lemma umPtPtUE (k1 k2 : K) (v1 v2 : V) f :
        pts k1 v1 == pts k2 v2 \+ f :> Ue = 
        if C k2 then 
          if C k1 then [&& k1 == k2, v1 == v2 & unitb f]
          else ~~ valid (pts k2 v2 \+ f)
        else ~~ C k1.
Proof. by rewrite eq_sym umPtUPtE (eq_sym k1) (eq_sym v1). Qed.

Lemma umUPtPtE (k1 k2 : K) (v1 v2 : V) f :
        f \+ pts k1 v1 == pts k2 v2 :> Ue = 
        if C k1 then 
          if C k2 then [&& k1 == k2, v1 == v2 & unitb f]
          else ~~ valid (pts k1 v1 \+ f)
        else ~~ C k2.
Proof. by rewrite joinC umPtUPtE. Qed.

Lemma umPtUPt2E (k1 k2 : K) (v1 v2 : V) f :
        pts k1 v1 == f \+ pts k2 v2 :> Ue = 
        if C k2 then 
          if C k1 then [&& k1 == k2, v1 == v2 & unitb f]
          else ~~ valid (pts k2 v2 \+ f)
        else ~~ C k1.
Proof. by rewrite joinC umPtPtUE. Qed.

Definition umE := ((((umPtPtE, umPt0E), (um0PtE, umPtUndefE)),
                    ((umUndefPtE, um0UndefE), (umUndef0E, umPtUE))),
                   (((umUPtE, umPtUPtE), (umPtPtUE, umUPtPtE, umPtUPt2E)),
                    (* plus a bunch of safe simplifications *)
                    ((@unitL U, @unitR U), (validPt, @valid_unit U))), 
                    (((eq_refl, unitb0),
                   (um_unitbPt, undef_join)), (join_undef, unitb_undef))).
End EqPtLemmas.


(*****************)
(* Other notions *)
(*****************)

(************)
(* um_preim *)
(************)

Section PreimDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (k : K) (v : V) (f : U) (p : pred V).

Definition um_preim p f k := oapp p false (find k f).

Lemma umpreim_undef p : um_preim p undef =1 pred0.
Proof. by move=>x; rewrite /um_preim find_undef. Qed.

Lemma umpreim0 p : um_preim p Unit =1 pred0.
Proof. by move=>x; rewrite /um_preim find0E. Qed.

Lemma umpreim_cond p f k : um_preim p f k -> C k.
Proof.
rewrite /um_preim; case E: (find k f)=>[v|] //= _.
by move/find_some/dom_cond: E.
Qed.

Lemma umpreimPt p k v : 
        C k -> 
        um_preim p (pts k v) =1 [pred x | (x == k) && p v].
Proof.
move=>Hk x; rewrite /um_preim /= findPt2.
by case: eqP=>//= _; rewrite Hk.
Qed.

Lemma umpreimUn p f1 f2 :
        valid (f1 \+ f2) ->
        um_preim p (f1 \+ f2) =1 predU (um_preim p f1) (um_preim p f2).
Proof.
move=>v x; rewrite /um_preim findUnL //=.
case X: (find x f1)=>[a|]; case Y: (find x f2)=>[b|] /=.
- by move: (dom_inNL v (find_some X)); rewrite (find_some Y).
- by rewrite ifT ?(find_some X) // orbC.
- by rewrite ifN //; apply/find_none.
by rewrite ifN //; apply/find_none.
Qed.

Lemma umpreim_pred0 f : um_preim pred0 f =1 pred0.
Proof. by move=>x; rewrite /um_preim; by case: (find x f). Qed.

Lemma umpreim_dom f : um_preim predT f =1 mem (dom f).
Proof.
move=>x; rewrite /um_preim /=.
case X: (find x f)=>[a|] /=; first by rewrite (find_some X).
by apply/esym/negbTE/find_none.
Qed.

End PreimDefLemmas.


(****************************)
(* map membership predicate *)
(****************************)

Section MapMembership.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Type f : U.

Definition Mem_UmMap f :=
  fun x : K * V => valid f /\ [pcm pts x.1 x.2 <= f].
Canonical um_PredType := PropPredType Mem_UmMap.

Lemma In_undef x : x \In (undef : U) -> False.
Proof. by case; rewrite valid_undef. Qed.

Lemma In0 x : x \In (Unit : U) -> False.
Proof. by case=>_; case=>z /esym/unitbP; rewrite um_unitbPtUn. Qed.

Lemma In_find k v f : (k, v) \In f <-> find k f = Some v.
Proof.
split=>[[W] /= [z E]|E]; first by rewrite E findPtUn // -E.
split; first by move/find_some/dom_valid: E.
by move/um_eta2: E=>->; exists (free f k).
Qed.

(* for inlined rewriting *)
Lemma In_findE k v f : (k, v) \In f -> find k f = Some v.
Proof. by move/In_find. Qed.

Lemma In_fun k v1 v2 f : (k, v1) \In f -> (k, v2) \In f -> v1 = v2.
Proof. by move/In_find=>H1 /In_find; rewrite H1; case. Qed.

Lemma InUn x f1 f2 : x \In (f1 \+ f2) -> x \In f1 \/ x \In f2.
Proof.
move/In_find=>F; move/find_some: (F); rewrite domUn inE=>/andP [W D].
case/orP: D F=>D; first by rewrite findUnL // D=>/In_find; left.
by rewrite findUnR // D=>/In_find; right.
Qed.

Lemma InL x f1 f2 : valid (f1 \+ f2) -> x \In f1 -> x \In (f1 \+ f2).
Proof. 
by move=>W /In_find E; apply/In_find; rewrite findUnL // (find_some E). 
Qed.

Lemma InR x f1 f2 : valid (f1 \+ f2) -> x \In f2 -> x \In (f1 \+ f2).
Proof. by rewrite joinC; apply: InL. Qed.

Lemma InPt x k v : x \In pts k v -> x = (k, v) /\ C k.
Proof.
case: x=>a b /In_find; rewrite findPt2.
by case: ifP=>//; case/andP=>/eqP ->-> [->].
Qed.

Lemma In_condPt k v : C k -> (k, v) \In pts k v.
Proof. by split; [rewrite validPt | exists Unit; rewrite unitR]. Qed.

Lemma InPtE k v f :
        C k -> 
        f = pts k v -> (k, v) \In f.
Proof. by move=>W ->; apply: In_condPt W. Qed.

Lemma In_dom f x : x \In f -> x.1 \in dom f.
Proof. by case=>W [z E]; subst f; rewrite domPtUn inE W eq_refl. Qed.

Lemma In_cond f x : x \In f -> C x.1.
Proof. by move/In_dom/dom_cond. Qed.

Lemma In_valid x f : x \In f -> valid f.
Proof. by case. Qed.

Lemma In_domN x f : x \In f -> dom f <> [::].
Proof. by move/In_dom=>H; apply/eqP/dom0NP; exists x.1. Qed.

Lemma In_unitN x f : x \In f -> f <> Unit.
Proof. by move/[swap]=>-> /In0. Qed.

Lemma In_inj_fun k1 k2 v f :
        {in dom f, injective (fun x => find x f)} -> 
        (k1, v) \In f -> (k2, v) \In f -> k1 = k2.
Proof.
move=>H H1 H2; apply: H. 
- by move/In_dom: H1.
by move/In_find: H1 H2=>-> /In_find ->.
Qed.

Lemma In_domX k f : reflect (exists v, (k, v) \In f) (k \in dom f).
Proof.
case: dom_find=>[E|v /In_find H E]; constructor; last by exists v.
by case=>v /In_find; rewrite E.
Qed.

(* this is just find_none stated as reflection *)
Lemma In_findN k f : reflect (find k f = None) (k \notin dom f).
Proof.
case: In_domX=>H; constructor.
- by case: H=>x /In_find ->.
by apply/find_none/negP=>/In_domX [v X]; apply: H; exists v.
Qed.

Lemma In_findNE k f : k \notin dom f -> find k f = None.
Proof. by move/In_findN. Qed.

Lemma InPtUnE x k v f :
        valid (pts k v \+ f) ->
        x \In pts k v \+ f <-> x = (k, v) \/ x \In f.
Proof.
move=>W; split; last by case=>[->|/(InR W)].
by case/InUn; [case/InPt=>->; left|right].
Qed.

Lemma InPtUnL k v f : valid (pts k v \+ f) -> (k, v) \In pts k v \+ f.
Proof. by move/InPtUnE=>->; left. Qed.

(* a frequently used pattern *)
Lemma InPtUnEL k v f f' :
        valid f -> f = pts k v \+ f' -> (k, v) \In f.
Proof. by move/[swap] ->; apply: InPtUnL. Qed.

Lemma InPtUnEN k v x f :
        valid (pts k v \+ f) ->
        x \In (pts k v \+ f) <-> x = (k, v) \/ x \In f /\ x.1 != k.
Proof.
move=>W; rewrite InPtUnE //; split; last by case; [left|case; right].
case=>[->|H]; first by left.
right; split=>//; move/In_dom: H=>H.
case: validUn W=>//; rewrite validPt=>W W' /(_ k).
rewrite domPt inE W eq_refl /= => /(_ (erefl _)).
by case: eqP H=>// ->->.
Qed.

Lemma InPtUn x k v f :
        x \In pts k v \+ f ->
        [/\ [&& C k, valid f & k \notin dom f] &
            (x = (k, v) /\ C k \/ x \In f /\ x.1 != k)].
Proof.
move=>H; have W w : valid (pts k w \+ f).
- by rewrite (validPtUnE v); apply: dom_valid (In_dom H).
rewrite (validPtUnI (W v)); split=>//; move/(InPtUnEN _ (W v)): H (W v).
by case=>[-> /validPtUn_cond|]; [left | right].
Qed.

Lemma InPtUnK k v w f :
        valid (pts k v \+ f) ->
        (k, w) \In (pts k v \+ f) <-> v = w.
Proof.
move=>W; rewrite InPtUnEN //; split=>[|->]; last by left.
by case=>[[->]|[]] //=; rewrite eq_refl.
Qed.

Lemma In_domY k f : k \in dom f -> sigT (fun v => (k, v) \In f).
Proof. by case: dom_find=>// v /In_find; exists v. Qed.

Lemma In_assocs f x : x \In assocs f <-> x \In f.
Proof.
move: f; apply: um_indf=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite assocs_undef; split=>// /In_undef.
- by rewrite assocs0; split=>// /In0.
by rewrite assocsPtUn ?InE // InPtUnE // IH.
Qed.

Lemma umem_eq f1 f2 :
        valid f1 -> valid f2 ->
        (forall x, x \In f1 <-> x \In f2) -> f1 = f2.
Proof.
move=>V1 V2 H; apply: find_eta=>// k.
case K1 : (find k f1)=>[a1|]; case K2 : (find k f2)=>[a2|] //.
- by move/In_find/H/In_find: K1; rewrite K2.
- by move/In_find/H/In_find: K1; rewrite K2.
by move/In_find/H/In_find: K2; rewrite K1.
Qed.

(* if we have equality of domains, we can get rid of one direction *)
(* in the hypothesis in umem_eq *)

Lemma umem_eqD f1 f2 :
        valid f1 -> valid f2 ->
        dom f1 =i dom f2 ->
        (forall x, x \In f1 -> x \In f2) -> f1 = f2.
Proof.
move=>V1 V2 E H; apply: umem_eq=>//; case=>k v; split; first by apply: H.
move=>H2; move: (In_dom H2); rewrite -E /= =>/In_domX [w H1].
by move/H/(In_fun H2): (H1)=>->.
Qed.

Lemma umem_eq_assocs f1 f2 :
        valid f1 -> valid f2 ->
        assocs f1 = assocs f2 ->
        f1 = f2.
Proof.
move=>V1 V2 E; apply: umem_eqD V1 V2 _ _.
- by rewrite !assocs_dom E.
by move=>x /In_assocs; rewrite E=>/In_assocs.
Qed.

Lemma InU x k v f :
        x \In upd k v f <->
        [/\ valid (upd k v f) & if x.1 == k then x.2 = v else x \In f].
Proof.
case: x=>x1 v1; split; last first.
- case=>W /= H; split=>//=; exists (free (upd k v f) x1); apply: um_eta2.
  move: (W); rewrite validU=>/andP [C' W']; rewrite findU C' W' /=.
  by case: eqP H=>[_ ->|_ /In_find].
move=>H; move: (In_dom H)=>/= D; move: (dom_valid D) (dom_valid D)=>W.
rewrite {1}validU=>/andP [C' W']; split=>//.
move: (D); rewrite domU inE C'  /= W'; case: H=>/= _ [z E].
case: ifP D E=>[/eqP -> D E _|N _ E D].
- have: find k (upd k v f) = Some v by rewrite findU eq_refl C' W'.
  by rewrite E findPtUn -?E //; case=>->.
have: find x1 (pts x1 v1 \+ z) = Some v1 by rewrite findPtUn // -E.
by rewrite -E findU N C'=>/In_find.
Qed.

(* different format that avoids conditionals *)
Lemma In_U x k v f :
        x \In upd k v f <->
        valid (upd k v f) /\
        [\/ x.1 == k /\ x.2 = v |
            x.1 != k /\ x \In f].
Proof.
rewrite InU; split; case=>W H; split=>//.
- by case: eqP H; [left | right].
by case: H=>[[->]//|[/negbTE ->]].
Qed.

Lemma InF x k f :
        x \In free f k <->
        [/\ valid (free f k), x.1 != k & x \In f].
Proof.
case: x=>x1 v1; split; last first.
- by case=>W /= N /In_find E; apply/In_find; rewrite findF (negbTE N).
case=>W /= H; rewrite W; case: H=>z E.
have : find x1 (pts x1 v1 \+ z) = Some v1 by rewrite findPtUn // -E.
by rewrite -E findF; case: eqP=>//= _ /In_find.
Qed.

Lemma In_eta k v f : (k, v) \In f -> f = pts k v \+ free f k.
Proof. by move=>H; case/In_dom/um_eta: (H)=>w [/In_find/(In_fun H) ->]. Qed.

End MapMembership.

Arguments In_condPt {K C V U k}.
Prenex Implicits InPt In_eta InPtUn In_dom InPtUnEL In_findE.

(* Umap and fset are special cases of union_map but are *)
(* defined before membership structure is declared. *)
(* Their membership structures aren't directly inheritted from that *)
(* of union_map, but must be declared separately *)
Canonical umap_PredType (K : ordType) V : PredType (K * V) :=
  um_PredType (umap K V).
Coercion Pred_of_umap K V (x : umap K V) : {Pred _} := 
  [eta Mem_UmMap x].
Canonical fset_PredType (K : ordType) : PredType (K * unit) :=
  um_PredType (fset K).
Coercion Pred_of_fset K (x : fset K) : {Pred _} := 
  [eta Mem_UmMap x].

Section MorphMembership.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U1 : pcm) (U2 : union_map C V).

Section PlainMorph.
Variable f : pcm_morph U1 U2.

Lemma InpfL e (x y : U1) :
        valid (x \+ y) -> 
        sep f x y -> 
        e \In f x -> 
        e \In f (x \+ y).
Proof. by move=>W H1 H2; rewrite pfjoin //=; apply: InL=>//; rewrite pfV2. Qed.

Lemma InpfR e (x y : U1) :
        valid (x \+ y) -> 
        sep f x y -> 
        e \In f y -> 
        e \In f (x \+ y).
Proof. by move=>W H1 H2; rewrite pfjoin //=; apply: InR=>//; rewrite pfV2. Qed.

Lemma InpfUn e (x y : U1) :
        valid (x \+ y) -> 
        sep f x y -> 
        e \In f (x \+ y) <-> e \In f x \/ e \In f y.
Proof. 
move=>W H; rewrite pfjoin //; split; first by case/InUn; eauto.
by case; [apply: InL|apply: InR]; rewrite pfV2.
Qed.

End PlainMorph.

Section FullMorph.
Variable f : full_pcm_morph U1 U2.

Lemma InpfLT e (x y : U1) : 
        valid (x \+ y) -> 
        e \In f x -> 
        e \In f (x \+ y).
Proof. by move=>W; apply: InpfL. Qed.

Lemma InpfRT e (x y : U1) : 
        valid (x \+ y) -> 
        e \In f y -> 
        e \In f (x \+ y).
Proof. by move=>W; apply: InpfR. Qed.

Lemma InpfUnT e (x y : U1) : 
        valid (x \+ y) -> 
        e \In f (x \+ y) <-> e \In f x \/ e \In f y.
Proof. by move=>W; apply: InpfUn. Qed.
End FullMorph.

End MorphMembership.

(*********)
(* range *)
(*********)

Section Range.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types f : U.

Definition range f := map snd (assocs f).

Lemma size_range f : size (range f) = size (dom f).
Proof. by rewrite assocs_dom !size_map. Qed.

Lemma range_undef : range undef = [::].
Proof. by rewrite /range assocs_undef. Qed.

Lemma range0 : range Unit = [::].
Proof. by rewrite /range assocs0. Qed.

Lemma In_rangeX v f : v \In range f <-> exists k, (k, v) \In f.
Proof.
elim/um_indf: f v=>[v|v|k w f IH W P v].
- by rewrite range_undef; split=>//; case=>x /In_undef.
- by rewrite range0; split=>//; case=>x /In0.
move: (order_path_min (@trans K) P)=>A.
rewrite /range assocsPtUn //= InE; split.
- case=>[->|/IH [k' H]]; first by exists k; rewrite InPtUnE //; left.
  by exists k'; rewrite InPtUnE //; right.
case=>k'; rewrite InPtUnE //; case; first by case; left.
by move=>H; right; apply/IH; exists k'.
Qed.

Lemma In_range_valid k f : k \In range f -> valid f.
Proof. by case/In_rangeX=>v /In_dom/dom_valid. Qed.

Lemma In_range k v f : (k, v) \In f -> v \In range f.
Proof. by move=>H; apply/In_rangeX; exists k. Qed.

Lemma In_rangeUn f1 f2 x :
        x \In range (f1 \+ f2) ->
        x \In range f1 \/ x \In range f2.
Proof. by rewrite !In_rangeX; case=>k /InUn [] H; [left | right]; exists k. Qed.

Lemma In_rangeL f1 f2 x :
        valid (f1 \+ f2) -> x \In range f1 -> x \In range (f1 \+ f2).
Proof. by move=>W; rewrite !In_rangeX; case=>k H; exists k; apply/InL. Qed.

Lemma In_rangeR f1 f2 x :
        valid (f1 \+ f2) -> x \In range f2 -> x \In range (f1 \+ f2).
Proof. by move=>W; rewrite !In_rangeX; case=>k H; exists k; apply/InR. Qed.

Lemma In_rangePt k :
        C k -> forall v x, x \In range (pts k v) <-> (x = v).
Proof.
move=>C' v x; rewrite In_rangeX. split.
- by case=>w /InPt [[]].
by move=>->; exists k; apply: In_condPt.
Qed.

Lemma In_rangePtUn k v f x :
        valid (pts k v \+ f) ->
        x \In range (pts k v \+ f) <-> x = v \/ x \In range f.
Proof.
move=>W; split.
- case/In_rangeUn; last by right.
  by move/(In_rangePt (validPtUn_cond W)); left.
case=>[->|]; last by apply: In_rangeR.
by apply/(In_rangeL W)/(In_rangePt (validPtUn_cond W)).
Qed.

Lemma rangePtK k v : C k -> range (pts k v) = [:: v].
Proof. by move=>C'; rewrite /range assocsPt C'. Qed.

Lemma rangePtUnK k v f :
        valid (pts k v \+ f) ->
        all (ord k) (dom f) ->
        range (pts k v \+ f) = v :: range f.
Proof. by move=>W H; rewrite /range assocsPtUn. Qed.

Lemma rangeUnPtK k v f :
        valid (f \+ pts k v) ->
        all (ord^~ k) (dom f) ->
        range (f \+ pts k v) = rcons (range f) v.
Proof. by move=>W H; rewrite /range assocsUnPt // map_rcons. Qed.

End Range.

Prenex Implicits In_range_valid In_range In_rangeUn.

(* decidable versions, when V is eqtype *)

Section DecidableRange.
Variables (K : ordType) (C : pred K) (V : eqType) (U : union_map C V).
Implicit Types f : U.

Lemma uniq_rangeP f :
        reflect (forall k1 k2 v, (k1, v) \In f -> (k2, v) \In f -> k1 = k2)
                (uniq (range f)).
Proof.
case: (normalP f)=>[->|W]. 
- by rewrite range_undef; constructor=>k1 k2 v /In_undef.
case H : (uniq (range f)); constructor; last first.
- move=>H'; move/negbT/negP: H; elim.
  rewrite map_inj_in_uniq; first by apply: uniq_assocs.
  case=>/= k1 v [k2 v'] /mem_seqP/In_assocs H1 /mem_seqP/In_assocs H2 /= H3.
  by rewrite -H3 in H2 *; rewrite (H' _ _ _ H1 H2).
move/uniqP: H=>H k1 k2 v H1 H2.
set j1 := index k1 (dom f).
set j2 := index k2 (dom f).
have [D1 D2] : k1 \in dom f /\ k2 \in dom f.
- by move/In_dom: H1; move/In_dom: H2.
have [R1 R2] : j1 < size (assocs f) /\ j2 < size (assocs f).
- by rewrite size_assocs !index_mem.
have [M1 M2] : j1 < size (dom f) /\ j2 < size (dom f).
- by rewrite !index_mem.
have [A1 A2] : (k1, v) \in assocs f /\ (k2, v) \in assocs f.
- by move/In_assocs/mem_seqP: H1=>->; move/In_assocs/mem_seqP: H2=>->.
have InjF : {in assocs f &, injective fst}.
- case=>a1 v1 [a2 v2] /mem_seqP X1 /mem_seqP X2 /= E.
  by move: E X1 X2 => -> X1 /(assocs_map X1) ->.
have /eqP E1 : j1 == index (k1,v) (assocs f).
- rewrite -(nth_uniq (k1,v) R1 _ (uniq_assocs _)); last by rewrite index_mem.
  by rewrite /j1 assocs_dom (nth_index_map _ InjF A1) nth_index.
have /eqP E2 : j2 == index (k2,v) (assocs f).
- rewrite -(nth_uniq (k2,v) R2 _ (uniq_assocs _)); last by rewrite index_mem.
  by rewrite /j2 assocs_dom (nth_index_map _ InjF A2) nth_index.
have E : nth v (range f) j1 = nth v (range f) j2.
- rewrite /range (nth_map (k1,v) v _ R1) (nth_map (k2,v) v _ R2).
  by rewrite E1 E2 !nth_index.
have : j1 = j2 by apply: H E; rewrite inE size_range.
by move/eqP; rewrite -(nth_uniq k1 M1 M2 (uniq_dom _)) !nth_index // =>/eqP.
Qed.

(* this is just a renaming of mem_seqP for easier finding *)
Lemma mem_rangeP x f : reflect (x \In range f) (x \in range f).
Proof. by apply: mem_seqP. Qed.

Lemma mem_rangeX v f : v \in range f <-> exists k, (k, v) \In f.
Proof. by split; [move/mem_seqP/In_rangeX|move/In_rangeX/mem_seqP]. Qed.

Lemma range_valid k f : k \in range f -> valid f.
Proof. by move/mem_seqP/In_range_valid. Qed.

Lemma mem_range k v f : (k, v) \In f -> v \in range f.
Proof. by move/In_range/mem_seqP. Qed.

Lemma rangeUn f1 f2 :
        range (f1 \+ f2) =i
        [pred x | valid (f1 \+ f2) && ((x \in range f1) || (x \in range f2))].
Proof.
move=>k; apply/idP/idP; last first.
- case/andP=>W /orP [] /mem_seqP H; apply/mem_seqP;
  by [apply/(In_rangeL W) | apply/(In_rangeR W)].
move/mem_seqP=>H; rewrite (In_range_valid H) inE /=.
by case/In_rangeUn: H=>/mem_seqP -> //; rewrite orbT.
Qed.

Lemma rangePt x k v : C k -> x \in range (U:=U) (pts k v) = (x == v).
Proof. by move=>C'; rewrite /range assocsPt C' inE. Qed.

Lemma rangePtUn k v f :
        range (pts k v \+ f) =i
        [pred x | valid (pts k v \+ f) & (v == x) || (x \in range f)].
Proof.
move=>x; rewrite rangeUn !inE; case W : (valid _)=>//=.
by rewrite rangePt ?(validPtUn_cond W) // eq_sym.
Qed.

Lemma rangeF k (f : U) : {subset range (free f k) <= range f}.
Proof.
case: (normalP f)=>[->|W]; first by rewrite free_undef !range_undef.
case D: (k \in dom f); last by move/negbT/dom_free: D=>->.
case: (um_eta D) W=>x [_] {1 3}-> Vf p.
by rewrite rangePtUn inE Vf=>->; rewrite orbT.
Qed.

Lemma uniq_rangeUn f1 f2 :
        valid (f1 \+ f2) ->
        uniq (range (f1 \+ f2)) = uniq (range f1 ++ range f2).
Proof.
move=>W; apply/esym; case: uniq_rangeP=>H; last first.
- apply/negP; rewrite cat_uniq=>/and3P [H1 /hasP H2 H3].
  elim: H=>k1 k2 v /InUn [] F1 /InUn []; move: F1.
  - by move/uniq_rangeP: H1; apply.
  - by move/mem_range=>F1 /mem_range F2; elim: H2; exists v.
  - by move/mem_range=>F1 /mem_range F2; elim: H2; exists v.
  by move/uniq_rangeP: H3; apply.
rewrite cat_uniq; apply/and3P; split; last 1 first.
- by apply/uniq_rangeP=>k1 k2 v F1 F2; apply: (H k1 k2 v); apply/InR.
- by apply/uniq_rangeP=>k1 k2 v F1 F2; apply: (H k1 k2 v); apply/InL.
case: hasP=>//; case=>x /mem_rangeX [k1 H1] /mem_rangeX [k2 H2].
have [G1 G2] : (k1, x) \In f1 \+ f2 /\ (k2, x) \In f1 \+ f2.
- by split; [apply/InR|apply/InL].
rewrite -(H k1 k2 x G1 G2) in H2.
by move: (dom_inNR W (In_dom H1)); rewrite (In_dom H2).
Qed.

Lemma uniq_rangePtUn k v f :
        valid (pts k v \+ f) ->
        uniq (range (pts k v \+ f)) = uniq (v :: range f).
Proof. by move=>W; rewrite uniq_rangeUn // rangePtK // (validPtUn_cond W). Qed.

Lemma uniq_rangeL f1 f2 :
        valid (f1 \+ f2) -> uniq (range (f1 \+ f2)) -> uniq (range f1).
Proof. by move=>W; rewrite uniq_rangeUn // cat_uniq; case/and3P. Qed.

Lemma uniq_rangeR f1 f2 :
        valid (f1 \+ f2) -> uniq (range (f1 \+ f2)) -> uniq (range f2).
Proof. by move=>W; rewrite uniq_rangeUn // cat_uniq; case/and3P. Qed.

Lemma uniq_rangeF k f : uniq (range f) -> uniq (range (free f k)).
Proof.
case: (normalP f)=>[->|W]; first by rewrite free_undef !range_undef.
case D : (k \in dom f); last by move/negbT/dom_free: D=>E; rewrite -{1}E.
by case: (um_eta D) W=>x [_] E; rewrite {1 2}E; apply: uniq_rangeR.
Qed.

End DecidableRange.


(********************)
(* Map monotonicity *)
(********************)

Section MapMonotonicity.
Variables (K V : ordType) (C : pred K) (U : union_map C V).
Implicit Types f : U.

Definition um_mono f := sorted ord (range f).
Definition um_mono_lt f := forall k k' v v',
  (k, v) \In f -> (k', v') \In f -> ord k k' -> ord v v'.
Definition um_mono_ltE f := forall k k' v v',
  (k, v) \In f -> (k', v') \In f -> ord k k' <-> ord v v'.
Definition um_mono_leE f := forall k k' v v',
  (k, v) \In f -> (k', v') \In f -> oleq k k' <-> oleq v v'.

Lemma ummonoP f : reflect (um_mono_lt f) (um_mono f).
Proof.
rewrite /um_mono/um_mono_lt/range.
apply/(equivP idP); elim/um_indf: f=>[||k v f IH W P].
- by rewrite assocs_undef; split=>// _ ???? /In_undef.
- by rewrite assocs0; split=>// _ ???? /In0.
rewrite assocsPtUn ?(order_path_min (@trans _) P) //=; split=>H; last first.
- rewrite path_min_sorted; first by apply/IH=>??????; apply: H; apply/InR.
  apply/allP=>x /mapP [[y w]] /mem_seqP/In_assocs X ->.
  by apply: H (path_mem (@trans K) P (In_dom X)); [apply/InPtUnL|apply/InR].
move=>x x' w w'; rewrite !InPtUnE //.
case=>[[->->]|H1]; case=>[[->->]|H2]; first by rewrite irr.
- suff: w' \in [seq i.2 | i <- assocs f] by move/(path_mem (@trans V) H).
  by move/In_assocs/mem_seqP: H2=>H2; apply/mapP; exists (x',w').
- by move/In_dom/(path_mem (@trans K) P): H1; case: ordP.
by move/path_sorted/IH: H; apply.
Qed.

Lemma ummono_undef : um_mono undef.
Proof. by apply/ummonoP=>???? /In_undef. Qed.

Lemma ummono0 : um_mono Unit.
Proof. by apply/ummonoP=>???? /In0. Qed.

Lemma ummonoUnL f1 f2 : valid (f1 \+ f2) -> um_mono (f1 \+ f2) -> um_mono f1.
Proof. by move=>W /ummonoP H; apply/ummonoP=>??????; apply: H; apply/InL. Qed.

Lemma ummonoUnR f1 f2 : valid (f1 \+ f2) -> um_mono (f1 \+ f2) -> um_mono f2.
Proof. by rewrite joinC; apply: ummonoUnL. Qed.

Lemma ummonoPtUn k' v' f :
        valid (pts k' v' \+ f) ->
        (forall k v, (k, v) \In f -> ord k k' /\ ord v v') ->
        um_mono (pts k' v' \+ f) = um_mono f.
Proof.
move=>W H; apply/idP/idP=>/ummonoP X; apply/ummonoP=>x x' w w' Y Y'.
- by apply: X; apply/InR.
case/(InPtUnE _ W): Y'=>[[->->]|]; case/(InPtUnE _ W): Y=>[[->->]|];
by [rewrite irr|case/H|case/H; case: ordP|apply: X].
Qed.

Lemma In_mono_fun k1 k2 v f :
        um_mono f -> (k1, v) \In f -> (k2, v) \In f -> k1 = k2.
Proof.
move/ummonoP=>M H1 H2; case: (ordP k1 k2).
- by move/(M _ _ _ _ H1 H2); rewrite irr.
- by move/eqP.
by move/(M _ _ _ _ H2 H1); rewrite irr.
Qed.

Lemma In_mono_range v f1 f2 :
        valid (f1 \+ f2) -> um_mono (f1 \+ f2) ->
        v \in range f1 -> v \in range f2 -> false.
Proof.
move=>W M /mem_seqP/In_rangeX [k1 H1] /mem_seqP/In_rangeX [k2 H2].
have H1' : (k1, v) \In f1 \+ f2 by apply/InL.
have H2' : (k2, v) \In f1 \+ f2 by apply/InR.
rewrite -{k2 H1' H2'}(In_mono_fun M H1' H2') in H2.
move/In_dom: H2; move/In_dom: H1=>H1.
by rewrite (negbTE (dom_inNL W H1)).
Qed.

Lemma ummono_ltP f : reflect (um_mono_ltE f) (um_mono f).
Proof.
case: ummonoP=>M; constructor; last first.
- by move=>N; elim: M=>x x' y y' X1 X2 /N; apply.
move=>x x' y y' X1 X2.
move: (M _ _ _ _ X1 X2) (M _ _ _ _ X2 X1)=>O1 O2.
split=>// N; case: ordP=>// Y1.
- by move/O2: Y1; case: ordP N.
by move/eqP: Y1=>?; subst x'; rewrite (In_fun X1 X2) irr in N.
Qed.

Lemma ummono_leP f : um_mono f -> um_mono_leE f.
Proof.
move/ummonoP=>M x x' y y' X1 X2.
move: (M _ _ _ _ X1 X2) (M _ _ _ _ X2 X1)=>O1 O2.
rewrite /oleq (eq_sym x) (eq_sym y).
case: ordP=>Y1; case: ordP=>Y2 //=.
- by move/O2: Y1; rewrite (eqP Y2) irr.
- by move/O2: Y1; case: ordP Y2.
- by rewrite (eqP Y1) in X2; rewrite (In_fun X1 X2) irr in Y2.
by move/O1: Y1; case: ordP Y2.
Qed.

Lemma ummono_inj_find f :
        um_mono f -> {in dom f & predT, injective (fun x => find x f)}.
Proof.
move/ummono_leP=>H k1 k2 /In_domX [x1 F1] _ E.
have /In_domX [x2 F2] : k2 \in dom f.
- by case: (dom_find k2) F1 E=>// _ /In_find ->.
move/In_find: (F1) E=>->; move/In_find: (F2)=>-> [?]; subst x2.
move: (H _ _ _ _ F1 F2) (H _ _ _ _ F2 F1); rewrite orefl=>{H} H1 H2.
case: (equivP idP H1) (@oantisym K k1 k2)=>// _.
by case: (equivP idP H2)=>// _; apply.
Qed.

Lemma index_mem_dom_range f k t :
        (k, t) \In f -> uniq (range f) -> index k (dom f) = index t (range f).
Proof.
rewrite /range assocs_dom.
elim/um_indf: f k t=>[||k' t' f IH W /(order_path_min (@trans K)) P] k t.
- by move/In_undef.
- by move/In0.
rewrite assocsPtUn // !map_cons /= InPtUnE //=.
case=>[[->->]|H1 H2]; first by rewrite !eq_refl.
case: eqP (In_dom H1) W=>[-> D|_ _ W].
- by rewrite validPtUn D !andbF.
case: eqP (In_range H1) H2=>[-> /mem_seqP ->//|_ _ /andP [H2 H3]].
by rewrite (IH _ _ H1).
Qed.

Lemma index_dom_range_mem f k t :
        index k (dom f) = index t (range f) ->
        index k (dom f) != size (dom f) -> (k, t) \In f.
Proof.
rewrite /range assocs_dom.
elim/um_indf: f k t=>[||k' t' f IH W /(order_path_min (@trans K)) P] k t.
- by rewrite assocs_undef.
- by rewrite assocs0.
rewrite assocsPtUn // map_cons /=.
case: eqP=>[|_]; first by case: eqP=>// <-<- _ _; apply/InPtUnE=>//; left.
case: eqP=>// _ [H1]; rewrite eqSS=>H2.
by apply/InPtUnE=>//; right; apply: IH H1 H2.
Qed.

Lemma ummonoF f x : um_mono f -> um_mono (free f x).
Proof.
move/ummonoP=>X; apply/ummonoP=>k k' v v'.
by case/InF=>_ _ F /InF [_ _]; apply: X F.
Qed.

End MapMonotonicity.


(**********************)
(* um_foldl, um_foldr *)
(**********************)

(* Induction lemmas over PCMs in the proofs *)

Section FoldDefAndLemmas.
Variables (K : ordType) (C : pred K) (V R : Type) (U : union_map C V).
Implicit Type f : U.

Definition um_foldl (a : R -> K -> V -> R) (z0 d : R) f :=
  if valid f then foldl (fun z kv => a z kv.1 kv.2) z0 (assocs f) else d.

Definition um_foldr (a : K -> V -> R -> R) (z0 d : R) f :=
  if valid f then foldr (fun kv z => a kv.1 kv.2 z) z0 (assocs f) else d.

Lemma umfoldl_undef a z0 d : um_foldl a z0 d undef = d.
Proof. by rewrite /um_foldl valid_undef. Qed.

Lemma umfoldr_undef a z0 d : um_foldr a z0 d undef = d.
Proof. by rewrite /um_foldr valid_undef. Qed.

Lemma umfoldl0 a z0 d : um_foldl a z0 d Unit = z0.
Proof. by rewrite /um_foldl assocs0 valid_unit. Qed.

Lemma umfoldr0 a z0 d : um_foldr a z0 d Unit = z0.
Proof. by rewrite /um_foldr assocs0 valid_unit. Qed.

Lemma umfoldlPt a (z0 d : R) k v :
        um_foldl a z0 d (pts k v) =
        if C k then a z0 k v else d.
Proof. by rewrite /um_foldl validPt assocsPt; case: (C k). Qed.

Lemma umfoldrPt a (z0 d : R) k v :
        um_foldr a z0 d (pts k v) =
        if C k then a k v z0 else d.
Proof. by rewrite /um_foldr validPt assocsPt; case: (C k). Qed.

Lemma umfoldlPtUn a k v z0 d f :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        um_foldl a z0 d (pts k v \+ f) = um_foldl a (a z0 k v) d f.
Proof. by move=>W H; rewrite /um_foldl /= W (validR W) assocsPtUn. Qed.

Lemma umfoldrPtUn a k v z0 d f :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        um_foldr a z0 d (pts k v \+ f) = a k v (um_foldr a z0 d f).
Proof. by move=>W H; rewrite /um_foldr W (validR W) assocsPtUn. Qed.

Lemma umfoldlUnPt a k v z0 d f :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        um_foldl a z0 d (f \+ pts k v) = a (um_foldl a z0 d f) k v.
Proof.
by move=>W H; rewrite /um_foldl W (validL W) assocsUnPt // -cats1 foldl_cat.
Qed.

Lemma umfoldrUnPt a k v z0 d f :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        um_foldr a z0 d (f \+ pts k v) = um_foldr a (a k v z0) d f.
Proof.
by move=>W H; rewrite /um_foldr W (validL W) assocsUnPt // -cats1 foldr_cat.
Qed.

Lemma umfoldlUn a z0 d f1 f2 :
        valid (f1 \+ f2) -> {in dom f1 & dom f2, forall x y, ord x y} ->
        um_foldl a z0 d (f1 \+ f2) = um_foldl a (um_foldl a z0 d f1) d f2.
Proof.
move: f2; apply: um_indb=>[W H|W H|k v f2 IH W' P W H].
- by rewrite join_undef !umfoldl_undef.
- by rewrite unitR umfoldl0.
rewrite -(joinC f2) joinA in W *; rewrite umfoldlUnPt //; last first.
- apply/allP=>x; rewrite domUn inE (validL W).
  case/orP=>[/H|]; last by apply: P.
  by apply; rewrite domPtUn inE joinC W' eq_refl.
rewrite umfoldlUnPt ?(validAR W) //; last by apply/allP.
rewrite (IH (validL W)) // => k1 k2 D1 D2; apply: H D1 _.
by rewrite domPtUn inE joinC W' D2 orbT.
Qed.

Lemma umfoldrUn a z0 d f1 f2 :
        valid (f1 \+ f2) -> {in dom f1 & dom f2, forall x y, ord x y} ->
        um_foldr a z0 d (f1 \+ f2) = um_foldr a (um_foldr a z0 d f2) d f1.
Proof.
move: f1; apply: um_indf=>[W H|W H|k v f1 IH W' P W H].
- by rewrite undef_join !umfoldr_undef.
- by rewrite unitL umfoldr0.
rewrite -!joinA in W *; rewrite umfoldrPtUn //.
- rewrite umfoldrPtUn ?(order_path_min (@trans K) P) // (IH (validR W)) //.
  by move=>k1 k2 D1; apply: H; rewrite domPtUn inE W' D1 orbT.
apply/allP=>x; rewrite domUn inE (validR W) /=.
case/orP; last by apply: H; rewrite domPtUn inE W' eq_refl.
by apply/allP/(order_path_min (@trans K) P).
Qed.

Lemma umfoldlPtUnE v2 v1 a t (z0 d : R) f :
        (forall r, a r t v1 = a r t v2) ->
        um_foldl a z0 d (pts t v1 \+ f) =
        um_foldl a z0 d (pts t v2 \+ f).
Proof.
move=>H.
case W : (valid (pts t v1 \+ f)); last first.
- move/invalidE: (negbT W)=>->; rewrite umfoldl_undef.
  rewrite (validPtUnE v2) in W.
  by move/invalidE: (negbT W)=>->; rewrite umfoldl_undef.
elim/um_indf: f z0 W=>[|z0|k v f IH V' P z0 W];
rewrite ?join_undef ?unitR ?umfoldlPt ?(H z0) //.
case: (ordP k t) W=>E W; last 2 first.
- by move/validAL: W; rewrite (eqP E) (validPtUnE v) validUnEb um_unitbPt.
- have D w : all (ord t) (dom (pts k w \+ f)).
  - apply/allP=>x; rewrite domPtUn inE=>/andP [_] /orP [/eqP <-|] //.
    by apply: path_mem (@trans K) _; apply: ord_path (@trans K) E P.
  by rewrite !(umfoldlPtUn a (k:=t)) ?(validPtUnE v1) // H.
have D w : all (ord k) (dom (pts t w \+ f)).
- apply/allP=>x; rewrite domPtUn inE=>/andP [_] /orP [/eqP <-|] //.
  by apply: path_mem (@trans K) P.
rewrite !(joinCA _ (pts k v)) in W *.
rewrite !(umfoldlPtUn a (k:=k)) // ?IH ?(validR W) //.
by rewrite joinCA (validPtUnE v1) joinCA.
Qed.

Lemma umfoldlUnPtE v2 v1 a t (z0 d : R) f :
        (forall r, a r t v1 = a r t v2) ->
        um_foldl a z0 d (f \+ pts t v1) =
        um_foldl a z0 d (f \+ pts t v2).
Proof. by rewrite !(joinC f); apply: umfoldlPtUnE. Qed.

Lemma umfoldl_defE a z0 d1 d2 f :
        valid f -> um_foldl a z0 d1 f = um_foldl a z0 d2 f.
Proof.
move: f z0; elim/um_indf=>[z0|z0|k v f IH W /(order_path_min (@trans K)) P z0 _];
by rewrite ?valid_undef ?umfoldl0 // !umfoldlPtUn // IH // (validR W).
Qed.

Lemma umfoldl_ind (P : R -> Prop) a z0 d f :
        valid f -> P z0 ->
        (forall z0 k v, (k, v) \In f -> P z0 -> P (a z0 k v)) ->
        P (um_foldl a z0 d f).
Proof.
move=>W H1 H2; elim/um_indf: f z0 W H1 H2=>[||k v f IH W O] z0;
rewrite ?valid_undef ?umfoldl0 // => _ H1 H2; rewrite umfoldlPtUn //;
last by apply: order_path_min O; apply: trans.
apply: IH (validR W) _ _; first by apply: H2 (InPtUnL W) H1.
by move=>z1 k0 v0 F; apply: H2 (InR W F).
Qed.

Lemma umfoldr_ind (P : R -> Prop) a z0 d f :
        valid f -> P z0 ->
        (forall z0 k v, (k, v) \In f -> P z0 -> P (a k v z0)) ->
        P (um_foldr a z0 d f).
Proof.
move=>W H1 H2; elim/um_indb: f z0 W H1 H2=>[||k v f IH W /allP O] z0;
rewrite ?valid_undef ?umfoldr0 // => _ H1 H2.
rewrite joinC umfoldrUnPt //; rewrite joinC in W.
apply: IH (validR W) _ _; first by apply: H2 (InPtUnL W) H1.
by move=>z1 k0 v0 F; apply: H2 (InR W F).
Qed.

End FoldDefAndLemmas.

Section PCMFold.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Variables (R : pcm) (a : R -> K -> V -> R).
Hypothesis frame : forall x y k v, a (x \+ y) k v = a x k v \+ y.

Lemma umfoldl0_frame z0 d (f : U) :
        valid f -> um_foldl a z0 d f = um_foldl a Unit d f \+ z0.
Proof.
move=>W; elim/um_indf: f W d z0
  =>[||k v f IH _ /(order_path_min (@trans K)) P] W d z0.
- by rewrite valid_undef in W.
- by rewrite !umfoldl0 unitL.
rewrite !umfoldlPtUn // IH 1?[in X in _ = X]IH ?(validR W) //.
by rewrite -joinA -frame unitL.
Qed.

Lemma umfoldlUn_frame z0 d (f1 f2 : U) :
        valid (f1 \+ f2) ->
        um_foldl a z0 d (f1 \+ f2) =
        um_foldl a Unit d f1 \+ um_foldl a Unit d f2 \+ z0.
Proof.
move=>W; rewrite /um_foldl W (validL W) (validR W).
set b := fun z kv => _.
have X x y kv : b (x \+ y) kv = b x kv \+ y by rewrite /b frame.
rewrite (foldl_perm X _ (assocs_perm W)).
rewrite foldl_cat -{1}[z0]unitL (foldl_init X).
rewrite (foldl_init X) -{1}[foldl b _ (assocs f1)]unitL.
by rewrite (foldl_init X) -!joinA joinCA.
Qed.

Lemma In_umfoldl z0 d (f : U) (k : K) (v : V) :
        (k, v) \In f -> [pcm a Unit k v <= um_foldl a z0 d f].
Proof.
move=>H; move: (H); rewrite (In_eta H); case=>W _.
by rewrite umfoldlUn_frame // umfoldlPt (validPtUn_cond W) /= -joinA; eauto.
Qed.

End PCMFold.

(* Fold when the function produces a map *)

Section FoldMap.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Variable (a : U -> K -> V -> U).
Hypothesis frame : forall x y k v, a (x \+ y) k v = a x k v \+ y.

Lemma In_umfoldlMX (f : U) (k : K) (v : V) :
        (k, v) \In um_foldl a Unit undef f ->
        exists k1 (v1 : V), (k, v) \In a Unit k1 v1 /\ (k1, v1) \In f.
Proof.
elim/um_indf: f.
- by rewrite umfoldl_undef=>/In_undef.
- by rewrite umfoldl0=>/In0.
move=>k1 v1 f IH W P.
rewrite umfoldlUn_frame // umfoldlPt (validPtUn_cond W) unitR.
case/InUn=>[H|/IH [k2][v2][H2 R2]]; first by exists k1, v1.
by exists k2, v2; split=>//; apply/InPtUnE=>//; right.
Qed.

Lemma In_umfoldlM (f : U) (k : K) (v : V) k1 v1 :
        valid (um_foldl a Unit undef f) ->
        (k, v) \In a Unit k1 v1 -> (k1, v1) \In f ->
        (k, v) \In um_foldl a Unit undef f.
Proof.
move=>W H /(In_umfoldl frame Unit undef) [x E].
by move: E W=>-> W; apply/InL.
Qed.

End FoldMap.

(**************)
(* Map prefix *)
(**************)

Section MapPrefix.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map C V).

Definition um_prefix (h1 h2 : U) := Prefix (assocs h1) (assocs h2).

Lemma umpfx_undef h : um_prefix undef h.
Proof.
by rewrite /um_prefix assocs_undef; apply/PrefixE; exists (assocs h).
Qed.

Lemma umpfx0 h : um_prefix Unit h.
Proof.
by rewrite /um_prefix assocs0; apply/PrefixE; exists (assocs h).
Qed.

Lemma umpfxD h1 h2 : um_prefix h1 h2 -> Prefix (dom h1) (dom h2).
Proof.
by case/PrefixE=>x E; rewrite !assocs_dom E map_cat; apply: Prefix_cat.
Qed.

(* we next need a helper lemma, which should be in assocs section *)
(* but couldn't be proved there, because um_indf appears later *)
Lemma assocsUn (h1 h2 : U) :
        valid (h1 \+ h2) ->
        (forall k1 k2, k1 \in dom h1 -> k2 \in dom h2 -> ord k1 k2) ->
        assocs (h1 \+ h2) = assocs h1 ++ assocs h2.
Proof.
move: h1 h2; apply: um_indf=>[h1|h2 W H|
  k v f IH W1 /(order_path_min (@trans _)) P h2 W2 H].
- by rewrite undef_join valid_undef.
- by rewrite assocs0 unitL.
rewrite -joinA in W2; rewrite -joinA !assocsPtUn //= ?IH //.
- by rewrite (validR W2).
- by move=>k1 k2 K1 K2; apply: H=>//; rewrite domPtUn inE K1 orbT W1.
apply/allP=>x; rewrite domUn inE (validR W2) /=.
by case/orP=>[/(allP P)//|]; apply: H; rewrite domPtUnE.
Qed.

Lemma umpfxI h1 h2 :
        valid (h1 \+ h2) ->
        (forall x y, x \in dom h1 -> y \in dom h2 -> ord x y) ->
        um_prefix h1 (h1 \+ h2).
Proof. by move=>W X; rewrite /um_prefix assocsUn //; apply: Prefix_cat. Qed.

Lemma umpfxE h1 h :
        valid h1 ->
        um_prefix h1 h ->
        exists2 h2, h = h1 \+ h2 &
                    forall x y, x \in dom h1 -> y \in dom h2 -> ord x y.
Proof.
move=>V1; case: (normalP h)=>[->|W].
- by exists undef; rewrite ?join_undef ?dom_undef.
move: h1 h V1 W; apply: um_indf=>[h|h _ W|
k v h1 IH W1 /(order_path_min (@trans _)) P h _ W].
- by rewrite valid_undef.
- by exists h; [rewrite unitL | rewrite dom0].
case/PrefixE=>h2'; rewrite assocsPtUn //= => Eh.
set h' := free h k; have W' : valid h' by rewrite validF.
have : um_prefix h1 h'.
- rewrite /um_prefix assocsF Eh /= eq_refl filter_cat /=.
  have : forall kv, kv \In assocs h1 -> kv.1 != k.
  - move=>kv /In_assocs/In_dom H; move/allP/(_ _ H): P.
    by case: eqP=>// ->; rewrite irr.
  by move/eq_In_filter=>->; rewrite filter_predT; apply: Prefix_cat.
case/(IH _ (validR W1) W')=>h2 Eh' H; exists h2.
- rewrite -joinA -Eh'; apply/um_eta2/In_find/In_assocs.
  by rewrite Eh In_cons; left.
move=>x y; rewrite domPtUn inE W1 /=; case/orP; last by apply: H.
move/eqP=><-{x} Dy.
have : y \in dom h' by rewrite Eh' domUn inE -Eh' W' /= Dy orbT.
rewrite domF inE; case: (k =P y)=>// /eqP N.
rewrite assocs_dom Eh /= inE eq_sym (negbTE N) /=.
case/mem_seqP/MapP; case=>a b X -> /=.
have {}P : path ord k (map fst (assocs h1 ++ h2')).
- by move: (sorted_dom h); rewrite assocs_dom Eh /=.
suff {X} : forall x, x \In assocs h1 ++ h2' -> ord k x.1 by move/(_ _ X).
apply/allPIn/(order_path_min (x:=(k,v)) (leT:=fun k x=>ord k.1 x.1)).
- by move=>???; apply: trans.
by rewrite -path_map.
Qed.

End MapPrefix.


(********)
(* omap *)
(********)

(* Combines map and filter by having filtering function return option. *)
(* This is very common form, so we also build structure for it. *)

(* Definition and basic properties *)
Section OmapDefs.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').
Variable f : K * V -> option V'.

Definition omap (x : U) : U' :=
  if valid x then
    foldl (fun z kv => if f kv is Some v' then z \+ pts kv.1 v' else z)
          Unit (assocs x)
  else undef.

Lemma omap0 : omap Unit = Unit.
Proof. by rewrite /omap valid_unit assocs0. Qed.

Lemma omap_undef : omap undef = undef.
Proof. by rewrite /omap valid_undef. Qed.

Lemma omapPt k v :
        omap (pts k v) =
        if C k then
          if f (k, v) is Some w then pts k w else Unit
        else undef.
Proof.
rewrite /omap validPt assocsPt; case D : (C k)=>//=. 
by case: (f _)=>// w; rewrite unitL.
Qed.

Lemma omapUn x1 x2 : 
        valid (x1 \+ x2) -> 
        omap (x1 \+ x2) = omap x1 \+ omap x2.
Proof.
move=>W; rewrite /omap W (validL W) (validR W); set o := fun z kv => _.
have H (x y : U') kv : o (x \+ y) kv = o x kv \+ y.
- by rewrite /o; case: (f kv)=>// w; rewrite joinAC.
rewrite (foldl_perm H _ (assocs_perm W)) foldl_cat.
by rewrite joinC -(foldl_init H) unitL.
Qed.

Lemma omapVUn x1 x2 : 
        omap (x1 \+ x2) =
        if valid (x1 \+ x2) then omap x1 \+ omap x2 else undef.
Proof.
case: (normalP (x1 \+ x2))=>[->|W]; 
by [rewrite omap_undef|apply: omapUn].
Qed.

Lemma omapPtUn k v x :
        omap (pts k v \+ x) =
        if valid (pts k v \+ x) then
          if f (k, v) is Some v' then pts k v' \+ omap x else omap x
        else undef.
Proof.
case: ifP=>D; last first.
- by move/invalidE: (negbT D)=>->; rewrite omap_undef.
rewrite omapUn // omapPt (validPtUn_cond D).
by case: (f _)=>//; rewrite unitL.
Qed.

Lemma omap_subdom x : {subset dom (omap x) <= dom x}.
Proof.
elim/um_indf: x=>[||k v x IH W P] t.
- by rewrite omap_undef dom_undef.
- by rewrite omap0 dom0.
rewrite omapPtUn W domPtUn W !inE /=.
case E : (f _)=>[b|]; last by move/IH=>->; rewrite orbT.
rewrite domPtUn inE; case/andP=>W2.
by case/orP=>[->//|/IH ->]; rewrite orbT.
Qed.

Lemma valid_omap x : valid (omap x) = valid x.
Proof.
elim/um_indf: x=>[||k v x IH W P].
- by rewrite omap_undef !valid_undef.
- by rewrite omap0 !valid_unit.
rewrite omapPtUn W; case E : (f _)=>[b|]; last by rewrite IH (validR W).
rewrite validPtUn (validPtUn_cond W) IH (validR W).
by apply: contra (notin_path P); apply: omap_subdom.
Qed.

End OmapDefs.

Arguments omap {K C V V' U U'}.

(* Structure definition *)

Definition omap_fun_axiom (K : ordType) (C : pred K) (V V' : Type)
    (U : union_map C V) (U' : union_map C V') 
    (f : U -> U') (omf : K * V -> option V') := 
  f =1 omap omf.

(* factory to use if full/norm/tpcm morphism property already proved *)
(* (omap_fun isn't binormal as it can drop timestamps) *)
HB.mixin Record isOmapFun_morph (K : ordType) (C : pred K) (V V' : Type)
    (U : union_map C V) (U' : union_map C V') (f : U -> U') of 
    @Full_Norm_TPCM_morphism U U' f := { 
  omf_op : K * V -> option V';  
  omfE_op : omap_fun_axiom f omf_op}.

#[short(type=omap_fun)]
HB.structure Definition OmapFun (K : ordType) (C : pred K) (V V' : Type)
    (U : union_map C V) (U' : union_map C V') := 
  {f of isOmapFun_morph K C V V' U U' f &}. 

Arguments omfE_op {K C V V' U U'}.
Arguments omf_op {K C V V' U U'} _ _ /.

(* factory to use when full/norm/tpcm morphism property *)
(* hasn't been established *)
HB.factory Record isOmapFun (K : ordType) (C : pred K) (V V' : Type)
    (U : union_map C V) (U' : union_map C V') (f : U -> U') := {
  omf : K * V -> option V';  
  omfE : omap_fun_axiom f omf}.

HB.builders Context K C V V' U U' f of isOmapFun K C V V' U U' f.

Lemma omap_fun_is_pcm_morph : pcm_morph_axiom relT f.
Proof.
split=>[|x y W _]; first by rewrite omfE omap0.
by rewrite !omfE -omapUn // valid_omap.
Qed.

HB.instance Definition _ := 
  isPCM_morphism.Build U U' f omap_fun_is_pcm_morph.

Lemma omap_fun_is_tpcm_morph : tpcm_morph_axiom f.
Proof. by rewrite /tpcm_morph_axiom omfE omap_undef. Qed.

HB.instance Definition _ := 
  isTPCM_morphism.Build U U' f omap_fun_is_tpcm_morph.

Lemma omap_fun_is_full_morph : full_pcm_morph_axiom f.
Proof. by []. Qed.

HB.instance Definition _ := 
  isFull_PCM_morphism.Build U U' f omap_fun_is_full_morph.

Lemma omap_fun_is_norm_morph : norm_pcm_morph_axiom f.
Proof. by move=>x /=; rewrite omfE valid_omap. Qed.

HB.instance Definition _ := 
  isNorm_PCM_morphism.Build U U' f omap_fun_is_norm_morph.
HB.instance Definition _ := 
  isOmapFun_morph.Build K C V V' U U' f omfE.
HB.end.

(* notation to hide the structure when projecting omf *)
Section OmapFunNotation.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

Definition omfx (f : omap_fun U U') of phantom (U -> U') f :
  K * V -> option V' := omf_op f.

Notation omf f := (omfx (Phantom (_ -> _) f)).

Lemma omfE (f : omap_fun U U') : f =1 omap (omf f).
Proof. exact: omfE_op. Qed.
End OmapFunNotation.

Notation omf f := (omfx (Phantom (_ -> _) f)).

(* omap is omap_fun *)
Section OmapOmapFun.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

HB.instance Definition _ f := 
  isOmapFun.Build K C V V' U U' (omap f) (fun => erefl _). 

Lemma omf_omap f : omf (omap f) = f. Proof. by []. Qed.
End OmapOmapFun.


(* general omap_fun lemmas *)

Section OmapFunLemmas.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').
Implicit Types (f : omap_fun U U') (x : U).

(* different name for pfjoin on full morphisms *)
Lemma omfUn f x1 x2 : valid (x1 \+ x2) -> f (x1 \+ x2) = f x1 \+ f x2.
Proof. exact: pfjoinT. Qed.

Lemma omfPtE f k v :
        f (pts k v) =
        if C k then 
          if omf f (k, v) is Some w then pts k w else Unit
        else undef.
Proof. by rewrite omfE omapPt. Qed.

Lemma omfPt f k v :
        C k ->
        f (pts k v) = if omf f (k, v) is Some w then pts k w else Unit.
Proof. by rewrite omfPtE=>->. Qed.

Lemma omfPtUn f k v x :
        f (pts k v \+ x) =
        if valid (pts k v \+ x) then
          if omf f (k, v) is Some v' then pts k v' \+ f x else f x
        else undef.
Proof.
case: ifP=>X; last first.
- by move/invalidE: (negbT X)=>->; rewrite pfundef.
rewrite omfUn // omfPtE (validPtUn_cond X).
by case: (omf f _)=>//; rewrite unitL.
Qed.

Lemma omfUnPt f k v x :
        f (x \+ pts k v) =
        if valid (x \+ pts k v) then
          if omf f (k, v) is Some v' then f x \+ pts k v' else f x
        else undef.
Proof.
rewrite joinC omfPtUn; case: ifP=>// W. 
by case: (omf f _)=>// w; rewrite joinC.
Qed.

(* membership *)
Lemma In_omfX f k v x :
        (k, v) \In f x <->
        exists2 w, (k, w) \In x & omf f (k, w) = Some v.
Proof.
rewrite omfE; elim/um_indf: x k v=>[||k' v' x IH W P] k v.
- by rewrite pfundef; split=>[/In_undef|[w][]] //; rewrite valid_undef.
- by rewrite pfunit; split=>[/In0|[w] /In0].
split=>[H|[w] H E].
- move: (dom_valid (In_dom H)); rewrite omapPtUn W in H *.
  case E : (omf f _) H=>[z|] H W1; last first.
  - by case/IH: H=>w1; exists w1=>//; apply/InR.
  move: H; rewrite InPtUnE //.
  case=>[[->->]|]; first by exists v'.
  by case/IH=>w; exists w=>//; apply/InR.
have : valid (omap (U':=U') (omf f) (pts k' v' \+ x)) by rewrite pfV.
rewrite omapPtUn W; move/(InPtUnE _ W): H E; case.
- by case=>->->-> V1; apply/InPtUnE=>//; left.
case: (omf _ (k', v'))=>[b|] H E V1; last by apply/IH; exists w.
by rewrite InPtUnE //; right; apply/IH; exists w.
Qed.

(* one side of the In_omfX can destruct the existential *)
Lemma In_omf f k v w x : 
        (k, w) \In x -> omf f (k, w) = Some v -> (k, v) \In f x.
Proof. by move=>H1 H2; apply/In_omfX; exists w. Qed.

(* dom *)
Lemma omf_subdom f x : {subset dom (f x) <= dom x}.
Proof. rewrite omfE; apply: omap_subdom. Qed.

Arguments omf_subdom {f x}.

Lemma omf_cond f x k : k \in dom (f x) -> C k.
Proof. by move/omf_subdom/dom_cond. Qed.

Lemma omf_sorted f x : sorted ord (dom (f x)).
Proof. by apply: sorted_dom. Qed.

Lemma path_omf f x k : path ord k (dom x) -> path ord k (dom (f x)).
Proof.
apply: subseq_path; first by apply: trans.
apply: (sorted_subset_subseq (ltT := ord)); last by apply: omf_subdom.
- by apply: irr.
- by apply: trans.
- by apply: sorted_dom.
by apply: sorted_dom.
Qed.

Lemma In_dom_omfX f x k :
        reflect (exists v, (k, v) \In x /\ omf f (k, v))
                (k \in dom (f x)).
Proof.
case: In_domX=>H; constructor. 
- by case: H=>v /In_omfX [w H1 H2]; exists w; rewrite H2. 
case=>v [X]; case Y: (omf _ _)=>[w|] // _.
by elim: H; exists w; apply/In_omfX; exists v.
Qed.

Lemma dom_omfUn f x1 x2 :
        dom (f (x1 \+ x2)) =i
        [pred k | valid (x1 \+ x2) & (k \in dom (f x1)) || (k \in dom (f x2))].
Proof. 
move=>k; rewrite !(omfE f) inE.
case: (normalP (x1 \+ x2))=>[->|W]; first by rewrite pfundef dom_undef.
by rewrite pfjoinT //= domUn inE -pfjoinT //= pfV //= W.
Qed.

Lemma dom_omfPtUn f k v x :
        dom (f (pts k v \+ x)) =i
        [pred t | valid (pts k v \+ x) &
           (omf f (k, v) && (t == k)) || (t \in dom (f x))].
Proof.
move=>t; rewrite dom_omfUn !inE; case D : (valid _)=>//=.
rewrite omfPtE (validPtUn_cond D); case E: (omf _ _)=>[a|] /=.
- by rewrite domPt inE (validPtUn_cond D) eq_sym.
by rewrite dom0.
Qed.

(* validity *)

Lemma In_omfV f kw x : 
        kw \In f x -> 
        valid x.
Proof. by case/In_omfX=>v /In_valid. Qed.

(* stronger than morphism property as uses two different f's *)
Lemma valid_omfUn f1 f2 x1 x2 :
         valid (x1 \+ x2) -> 
         valid (f1 x1 \+ f2 x2).
Proof. 
move=>W; rewrite (omfE f1) (omfE f2) validUnAE !pfVE !(validE2 W) /=.
by apply/allP=>x /omf_subdom D2; apply/negP=>/omf_subdom/(dom_inNRX W D2).
Qed.

Lemma valid_omfPtUn f k v x :
        [&& C k, valid x & k \notin dom x] ->
        valid (pts k v \+ f x).
Proof.
case/and3P=>H1 H2 H3; rewrite validPtUn H1 pfVE H2 /=. 
by apply: contra (omf_subdom _) H3. 
Qed.

Lemma valid_omfUnPt f k v x :
        [&& C k, valid x & k \notin dom x] ->
        valid (f x \+ pts k v).
Proof. by move=>H; rewrite joinC; apply: valid_omfPtUn. Qed.

(* range *)

Lemma In_range_omapUn f x1 x2 v :
        v \In range (f (x1 \+ x2)) <->
        valid (x1 \+ x2) /\ (v \In range (f x1) \/ v \In range (f x2)).
Proof.
split=>[|[D]].
- case: (normalP (x1 \+ x2))=>[->|D]; last first.
  - by rewrite pfjoinT // => /In_rangeUn. 
  by rewrite pfundef range_undef. 
rewrite pfjoinT //; case.
- by apply/In_rangeL/pfV2I.  
by apply/In_rangeR/pfV2I.
Qed.

(* other interactions *)

Lemma find_omf f k x :
        find k (f x) =
        if find k x is Some v then omf f (k, v) else None.
Proof.
case E1 : (find k _)=>[b|].
- by move/In_find: E1=>/In_omfX [w] /In_find ->.
move/find_none/negP: E1=>E1.
case E2 : (find k x)=>[c|] //; move/In_find: E2=>E2.
case E3 : (omf f (k, c))=>[d|] //; elim: E1.
by apply/In_dom_omfX; exists c; rewrite E3. 
Qed.

Lemma omfF f k x : f (free x k) = free (f x) k.
Proof.
case: (normalP x)=>[->|D]; first by rewrite pfundef !free_undef pfundef.
apply: umem_eq.
- by rewrite pfVE validF.
- by rewrite validF pfVE.
case=>t v; split.
- case/In_omfX=>w /InF /= [_ N M E].
  apply/InF; rewrite validF pfVE D N; split=>//.
  by apply/In_omfX; exists w.
case/InF=>/= _ N /In_omfX [v'] M E.
by apply/In_omfX; exists v'=>//; apply/InF; rewrite validF.
Qed.

Lemma omfUE f k (v : V) (x : U) :
        f (upd k v x) =
        if C k then
          if omf f (k, v) is Some v' then upd k v' (f x)
          else free (f x) k
        else undef.
Proof.
case: ifP=>// D; last by rewrite (upd_condN v x (negbT D)) pfundef.
case: (normalP x)=>[->|H].
- by case: (omf _ _)=>[a|]; rewrite ?(upd_undef,free_undef,pfundef).
rewrite upd_eta omfPtUn validPtUn D validF H domF inE eq_refl /=.
case: (omf _ _)=>[xa|]; last by rewrite omfF.
by rewrite upd_eta omfF.
Qed.

Lemma omfU f k (v : V) (x : U) :
        C k ->
        f (upd k v x) =
        if omf f (k, v) is Some v' then upd k v' (f x) 
        else free (f x) k.
Proof. by move=>D; rewrite omfUE D. Qed.

(* when mapped functions are equal *)

Lemma eq_in_omf f1 f2 x :
        f1 x = f2 x <->
        (forall kv, kv \In x -> omf f1 kv = omf f2 kv).
Proof.
have L h : (forall kv, kv \In h -> omf f1 kv = omf f2 kv) ->
  f1 h = f2 h.
- elim/um_indf: h=>[||k v h IH W P H]; rewrite ?pfundef ?pfunit //.
  by rewrite !omfPtUn W (H _ (InPtUnL W)) -IH // => kv /(InR W)/H.
split; last by apply: L.
elim/um_indf: x=>[_ kv /In_undef|_ kv /In0|k v x IH W P H kv] //.
have E t : find t (f1 (pts k v \+ x)) = find t (f2 (pts k v \+ x)).
- by rewrite H.
case/(InPtUnE _ W)=>[->|].
- by move: (E k); rewrite !find_omf findPtUn.
apply: {kv} IH; apply: L; case=>k1 v1 X.
move: (E k1); rewrite !find_omf findPtUn2 //.
case: (k1 =P k) X =>[-> /In_dom|_ /In_find ->] //=.
by move/negbTE: (validPtUnD W)=>->.
Qed.

(* if mapped function is total, we have some stronger lemmas *)

Lemma dom_omf_some f x :
        (forall kv, kv \In x -> omf f kv) -> dom (f x) = dom x.
Proof. 
move=>H; apply/domE=>k; apply/idP/idP=>/In_domX [w].
- by case/In_omfX=>v /In_dom.
by move/[dup]/H=>E X; apply/In_dom_omfX; exists w. 
Qed.

Lemma domeq_omf_some f x :
        (forall kv, kv \In x -> omf f kv) -> dom_eq (f x) x.
Proof. by move/dom_omf_some=>E; rewrite /dom_eq E pfVE !eq_refl. Qed.

(* if mapped function is total on x1, x2 *)
(* we don't need validity condition for union *)
Lemma omfUn_some f x1 x2 :
        (forall k, k \In x1 -> omf f k) ->
        (forall k, k \In x2 -> omf f k) ->
        f (x1 \+ x2) = f x1 \+ f x2.
Proof.
move=>H1 H2; have Ev : valid (f x1 \+ f x2) = valid (x1 \+ x2).
- by rewrite !validUnAE !pfVE !dom_omf_some. 
case: (normalP (x1 \+ x2)) Ev=>[->|D _]; last by apply: pfjoinT.
by rewrite pfundef=>/negbT/invalidE.
Qed.

Lemma omf_predU f1 f2 x :
        (forall kv, omf f1 kv = None \/ omf f2 kv = None) ->
        f1 x \+ f2 x =
        omap (fun kv => if omf f1 kv is Some v 
                        then Some v else omf f2 kv) x.
Proof.
move=>E; rewrite (omfE f1) (omfE f2).
elim/um_indf: x=>[||k v x IH W /(order_path_min (@trans K)) P].
- by rewrite !pfundef undef_join.
- by rewrite !pfunit unitL.
rewrite !omapPtUn W -IH.
case E1 : (omf f1 (k, v))=>[b1|]; case E2 : (omf f2 (k, v))=>[b2|] //.
- by move: (E (k, v)); rewrite E1 E2; case.
- by rewrite joinA.
by rewrite joinCA.
Qed.

Lemma omf_unit f x :
        reflect (valid x /\ forall kv, kv \In x -> omf f kv = None) 
                (unitb (f x)).
Proof.
case: unitbP=>H; constructor; last first.
- case=>D; elim/um_indf: x D H=>[||k v x IH W P _];
  rewrite ?valid_undef ?pfunit ?omfPtUn //= W.
  case E : (omf f _)=>[a|]; first by move=>_ /(_ _ (InPtUnL W)); rewrite E. 
  by move=>H1 H2; apply: (IH (validR W) H1)=>kv H; apply: H2 (InR W H).
split; first by rewrite -(pfVE (f:=f)) /= H valid_unit.
elim/um_indf: x H=>[H kv /In_undef|H kv /In0|k v x IH W P /[swap] kv] //.
rewrite omfPtUn W; case E : (omf f _)=>[a|].
- by move/unitbP; rewrite um_unitbPtUn.
by move=>H /(InPtUnE _ W) [->//|]; apply: IH H _.
Qed.

Lemma omf_none f x :
        valid x ->
        (forall kv, kv \In x -> omf f kv = None) ->
        f x = Unit.
Proof. by move=>D H; apply/unitbP/omf_unit. Qed.

Lemma omf_noneR f x : 
        f x = Unit -> forall kv, kv \In x -> omf f kv = None.
Proof. by case/unitbP/omf_unit. Qed.

End OmapFunLemmas.

Arguments omf_subdom {K C V V' U U' f x}.
Arguments In_omf {K C V V' U U'} _ {k v w x}.

(* omap_fun's with different ranges *)

Section OmapFun2.
Variables (K : ordType) (C : pred K) (V V1 V2 : Type). 
Variables (U : union_map C V) (U1 : union_map C V1) (U2 : union_map C V2).
Variables (f1 : omap_fun U U1) (f2 : omap_fun U U2).

(* when one mapped function is included in other *)

Lemma omf_dom_subseq (x : U) :
        (forall kv, kv \In x -> omf f1 kv -> omf f2 kv) ->
        subseq (dom (f1 x)) (dom (f2 x)).
Proof.
elim/um_indf: x=>[||k v x IH W P] H; 
rewrite ?pfundef ?pfunit ?dom_undef ?dom0 //. 
move: (W); rewrite validPtUn=>W'; rewrite !omfPtUn W.
have T : transitive (@ord K) by apply: trans.
have B : (k, v) \In pts k v \+ x by apply: InPtUnL.
case E1 : (omf f1 (k, v))=>[x1|].
- have /(H _ B): (omf f1 (k, v)) by rewrite E1.
  case: (omf f2 (k, v))=>// x2 _.
  rewrite !domPtUnK //=; last first.
  - by apply/allP=>? /In_dom_omfX [?][] /In_dom Y _; apply: path_mem Y.
  - by rewrite valid_omfPtUn.
  - by apply/allP=>? /In_dom_omfX [?][] /In_dom Y _; apply: path_mem Y.
  - by rewrite valid_omfPtUn.
  by rewrite eq_refl; apply: IH=>kx X; apply: H (InR _ _).
case E2 : (omf f2 (k, v))=>[x2|]; last by apply: IH=>kx X; apply: H (InR _ _).
rewrite domPtUnK /=; last first.
- by apply/allP=>? /In_dom_omfX [?][] /In_dom Y _; apply: path_mem Y.
- by rewrite valid_omfPtUn.
case D : (dom (f1 x))=>[//|t ts].
case: eqP D=>[-> D|_ <-]; last by apply: IH=>kv X; apply: H (InR _ _).
have : k \in dom (f1 x) by rewrite D inE eq_refl.
case/In_dom_omfX=>w1 [] /In_dom /= D1.
by rewrite validPtUn D1 !andbF in W.
Qed.

End OmapFun2.

Section OmapFun2Eq.
Variables (K : ordType) (C : pred K) (V V1 V2 : Type).
Variables (U : union_map C V) (U1 : union_map C V1) (U2 : union_map C V2).
Variables (f1 : omap_fun U U1) (f2 : omap_fun U U2).

Lemma omf_dom_eq (x : U) : 
        (forall kv, kv \In x -> omf f1 kv <-> omf f2 kv) ->
        dom (f1 x) = dom (f2 x).
Proof.
move=>H; apply: subseq_anti.
by rewrite !omf_dom_subseq // => kv /H ->.
Qed.

End OmapFun2Eq.

Section OmapMembershipExtra.
Variables (K : ordType) (C : pred K) (V1 V2 : Type).
Variables (U1 : union_map C V1) (U2 : union_map C V2).
Variables f : omap_fun U1 U2.

Lemma omfL e (x y : U1) :  
        e.1 \in dom x -> 
        e \In f (x \+ y) -> 
        e \In f x.
Proof.
move=>D /[dup] /In_valid/fpV V; rewrite pfjoinT //.
by case/InUn=>// /In_dom/omf_subdom/(dom_inNLX V D).
Qed.

Lemma omfR e (x y : U1) :  
        e.1 \in dom y -> 
        e \In f (x \+ y) -> 
        e \In f y.
Proof.
move=>D /[dup] /In_valid/fpV V; rewrite pfjoinT //.
by case/InUn=>// /In_dom/omf_subdom/(dom_inNRX V D).
Qed.

Lemma omfDL k (x y : U1) : 
        k \in dom x ->
        k \in dom (f (x \+ y)) -> 
        k \in dom (f x).
Proof. by move=>D /In_domX [v] /omfL-/(_ D)/In_dom. Qed.

Lemma omfDR k (x y : U1) : 
        k \in dom y ->
        k \in dom (f (x \+ y)) -> 
        k \in dom (f y).
Proof. by move=>D /In_domX [v] /omfR-/(_ D)/In_dom. Qed.

Lemma InpfLTD k (x y : U1) :
        valid (x \+ y) -> 
        k \in dom (f x) -> 
        k \in dom (f (x \+ y)).
Proof. by move=>V /In_domX [v] /(InpfLT V)/In_dom. Qed.

Lemma InpfRTD k (x y : U1) :
        valid (x \+ y) -> 
        k \in dom (f y) -> 
        k \in dom (f (x \+ y)).
Proof. by move=>V /In_domX [v] /(InpfRT V)/In_dom. Qed.
End OmapMembershipExtra.

Section OmapMembershipExtra2.
Variables (K : ordType) (C : pred K) (V1 V2 : Type).
Variables (U1 : union_map C V1) (U2 : union_map C V2).
Variables f : omap_fun U1 U2.

Lemma omfDL00 k a (x y : U1) : 
        k \in a::dom x ->
        k \in a::dom (f (x \+ y)) -> 
        k \in a::dom (f x).
Proof. by rewrite !inE; case: (k =P a)=>//= _; apply: omfDL. Qed.

Lemma omfDL0 k a (x y : U1) : 
        k \in dom x ->
        k \in a::dom (f (x \+ y)) -> 
        k \in a::dom (f x).
Proof. by rewrite !inE; case: (k =P a)=>//= _; apply: omfDL. Qed.

Lemma omfDR00 k a (x y : U1) : 
        k \in a::dom y ->
        k \in a::dom (f (x \+ y)) -> 
        k \in a::dom (f y).
Proof. by rewrite !inE; case: (k =P a)=>//= _; apply: omfDR. Qed.

Lemma omfDR0 k a (x y : U1) : 
        k \in dom y ->
        k \in a::dom (f (x \+ y)) -> 
        k \in a::dom (f y).
Proof. by rewrite !inE; case: (k =P a)=>//= _; apply: omfDR. Qed.

Lemma InpfLTD0 k a (x y : U1) :
        valid (x \+ y) -> 
        k \in a::dom (f x) -> 
        k \in a::dom (f (x \+ y)).
Proof. by move=>V; rewrite !inE; case: (k =P a)=>//= _; apply: InpfLTD. Qed.

Lemma InpfRTD0 k a (x y : U1) :
        valid (x \+ y) -> 
        k \in a::dom (f y) -> 
        k \in a::dom (f (x \+ y)).
Proof. by move=>V; rewrite !inE; case: (k =P a)=>//= _; apply: InpfRTD. Qed.
End OmapMembershipExtra2.

(* categoricals *)

Section OmapFunId.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map C V).

Lemma omf_some (f : omap_fun U U) x :
        (forall kv, kv \In x -> omf f kv = Some kv.2) -> 
        f x = x.
Proof. 
elim/um_indf: x=>[||k v x IH W P] H; rewrite ?pfundef ?pfunit //.
by rewrite omfPtUn W H //= IH // => kv D; apply: H (InR _ D).
Qed.

Lemma id_is_omap_fun : omap_fun_axiom (@idfun U) (Some \o snd).
Proof. by move=>x; rewrite omf_some. Qed.

(* we already have that id is full/norm/tpcm morph *)
(* so we use the factory for that situation *)
HB.instance Definition _ := 
  isOmapFun_morph.Build K C V V U U idfun id_is_omap_fun.

Lemma omf_id : omf idfun = Some \o snd. Proof. by []. Qed.

Lemma valid_omfUnL (f : omap_fun U U) x1 x2 :
        valid (x1 \+ x2) -> valid (f x1 \+ x2).
Proof. by rewrite {2}(_ : x2 = @idfun U x2) //; apply: valid_omfUn. Qed.

Lemma valid_omfUnR (f : omap_fun U U) x1 x2 : 
        valid (x1 \+ x2) -> valid (x1 \+ f x2).
Proof. by rewrite !(joinC x1); apply: valid_omfUnL. Qed.

End OmapFunId.


Section OmapFunComp.
Variables (K : ordType) (C : pred K) (V1 V2 V3 : Type).
Variables (U1 : union_map C V1) (U2 : union_map C V2) (U3 : union_map C V3).
Variables (f1 : omap_fun U1 U2) (f2 : omap_fun U2 U3).

Lemma comp_is_omap_fun : 
        omap_fun_axiom (f2 \o f1)
          (fun x => obind (fun v => omf f2 (x.1, v)) (omf f1 x)).
Proof. 
elim/um_indf=>[||k v x /= IH W P]; rewrite ?pfundef ?pfunit //=.
rewrite !omapPtUn !omfPtUn W /=; case: (omf f1 (k, v))=>[w|//].
rewrite omfPtUn validPtUn (validPtUn_cond W) pfVE (validR W) /= IH.
by rewrite (contra _ (validPtUnD W)) //; apply: omf_subdom.
Qed.

HB.instance Definition _ := 
  isOmapFun_morph.Build K C V1 V3 U1 U3 (f2 \o f1) comp_is_omap_fun.

Lemma omf_comp : 
        omf (f2 \o f1) = 
        fun x => obind (fun v => omf f2 (x.1, v)) (omf f1 x).
Proof. by []. Qed.

End OmapFunComp.


(*********************)
(* omap specifically *)
(*********************)

(* special notation for some common variants of omap *)

(* when we don't supply the key *)
Notation omapv f := (omap (f \o snd)).
(* when the don't supply the key and the map is total *)
Notation mapv f := (omapv (Some \o f)).

Section OmapId.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).

Lemma omapv_id : omapv Some =1 @id U. 
Proof. by move=>x; apply: omf_some. Qed.

Lemma mapv_id : mapv id =1 @id U. 
Proof. by apply: omapv_id. Qed.

End OmapId.

Section OmapComp.
Variables (K : ordType) (C : pred K) (V1 V2 V3 : Type).
Variables (U1 : union_map C V1) (U2 : union_map C V2) (U3 : union_map C V3).

Lemma omap_omap f1 f2 (x : U1) :
        omap f2 (omap f1 x : U2) =
        omap (fun kv => obind (fun v => f2 (kv.1, v)) (f1 kv)) x :> U3.
Proof. by rewrite (compE (omap f2)) omfE. Qed.

Lemma omapv_omapv f1 f2 (x : U1) :
        omapv f2 (omapv f1 x : U2) = omapv (obind f2 \o f1) x :> U3.
Proof. by rewrite omap_omap. Qed.

Lemma omapv_mapv f1 f2 (x : U1) : 
        omapv f2 (mapv f1 x : U2) = omapv (f2 \o f1) x :> U3.
Proof. by rewrite omapv_omapv. Qed.

(* RHS is just filtering; will restate with um_filter below *)
Lemma mapv_omapvE f g (x : U1) : 
        ocancel f g ->
        mapv g (omapv f x : U2) = 
        omapv (fun v => if f v then Some v else None) x :> U1.
Proof.
move=>O; rewrite (compE (mapv g)) eq_in_omf omf_omap omf_comp !omf_omap /=.
by case=>k v H; case X: (f v)=>[a|] //=; rewrite -(O v) X. 
Qed.

End OmapComp.


Section OmapMembership.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

Lemma In_omapX f k v (x : U) :
        (k, v) \In (omap f x : U') <->
        exists2 w, (k, w) \In x & f (k, w) = Some v.
Proof. exact: In_omfX. Qed.

Lemma In_omap f k v w (x : U) : 
        (k, w) \In x -> f (k, w) = Some v -> (k, v) \In (omap f x : U').
Proof. by move=>H1 H2; apply: In_omf H1 _; apply: H2. Qed.

Lemma In_dom_omapX (f : K * V -> option V') k (x : U) : 
         reflect (exists w, (k, w) \In x /\ f (k, w))
                 (k \in dom (omap f x : U')).
Proof. by case: In_dom_omfX=>H; constructor; exact: H. Qed.

Lemma In_omapv f k v w (x : U) :
        (k, w) \In x -> f w = Some v -> (k, v) \In (omapv f x : U').
Proof. by move=>H1 H2; apply: In_omf H1 _; rewrite omf_omap. Qed.

Lemma In_mapv f k v (x : U) :
        injective f -> (k, f v) \In (mapv f x : U') <-> (k, v) \In x.
Proof. by move=>I; rewrite In_omfX; split; [case=>w H [] /I <-|exists v]. Qed.

End OmapMembership.

Arguments In_omapv {K C V V' U U' f k v w}.

Section OmapMembership2.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

Lemma In_omapV f g k v (x : U) :
        ocancel f g -> pcancel g f ->
        (k, v) \In (omapv f x : U') <-> (k, g v) \In x.
Proof.
move=>O P; rewrite -(In_mapv U _ _ _ (pcan_inj P)). 
rewrite mapv_omapvE // In_omapX /=.
split; first by case=>w H; case: (f w)=>[a|] //= [<-]. 
by exists (g v)=>//=; rewrite P.
Qed.

Lemma In_rangev f g v (x : U) :
        ocancel f g -> pcancel g f ->
        v \In range (omapv f x : U') <-> g v \In range x.
Proof.
move=>O P; rewrite !In_rangeX; split; case=>k H; exists k.
- by rewrite -(In_omapV _ _ _ O P).
by rewrite (In_omapV _ _ _ O P).
Qed.

End OmapMembership2.

Section OmapMembership3.
Variables (K : ordType) (C : pred K) (V V' : eqType).
Variables (U : union_map C V) (U' : union_map C V').

(* decidable variant of In_rangev *)
Lemma mem_rangev f g v (x : U) :
        ocancel f g -> pcancel g f ->
        v \in range (omapv f x : U') = (g v \in range x).
Proof.
by move=>O P; apply/idP/idP; move/mem_seqP/(In_rangev _ _ _ O P)/mem_seqP.
Qed.

End OmapMembership3.


(* freeing k representable as omap *)
Section OmapFree.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

Lemma omap_free k x :
        free x k = 
        omap (fun kv => if kv.1 == k then None else Some kv.2) x :> U.
Proof.
case: (normalP x)=>[->|D]; first by rewrite free_undef pfundef.
apply: umem_eq.
- by rewrite validF.
- by rewrite pfVE.
case=>t w; rewrite InF In_omapX /= validF D; split.
- by case=>_ /negbTE ->; exists w.
by case=>w' H; case: eqP=>// N [<-].
Qed.

End OmapFree.

(* eq_in_omap *)
Section EqInOmap.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

Lemma eq_in_omap a1 a2 (h : U) :
        (forall kv, kv \In h -> a1 kv = a2 kv) <->
        omap a1 h = omap a2 h :> U'.
Proof. by rewrite eq_in_omf. Qed.
End EqInOmap.


(*************)
(* um_filter *)
(*************)

(* filter that works over both domain and range at once *)

Section FilterDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (f : U) (p q : pred (K * V)).

Definition um_filter p f : U :=
  omap (fun kv => if p kv then Some kv.2 else None) f.

(* um_filter is omap_fun *)
HB.instance Definition _ p := OmapFun.copy (um_filter p) (um_filter p).

Lemma umfiltPtE p k v :
        um_filter p (pts k v) =
        if C k then
          if p (k, v) then pts k v else Unit
       else undef.
Proof. by rewrite omfPtE omf_omap; case: (ifP (p _)). Qed.

Lemma umfiltPt p k v :
        C k ->
        um_filter p (pts k v) = if p (k, v) then pts k v else Unit.
Proof. by move=>D; rewrite umfiltPtE D. Qed.

Lemma umfiltUn p f1 f2 :
        valid (f1 \+ f2) ->
        um_filter p (f1 \+ f2) = um_filter p f1 \+ um_filter p f2.
Proof. exact: pfjoinT. Qed.

Lemma umfiltPtUn p k v f :
        um_filter p (pts k v \+ f) =
        if valid (pts k v \+ f) then
          if p (k, v) then pts k v \+ um_filter p f else um_filter p f
        else undef.
Proof. by rewrite omfPtUn omf_omap; case: (ifP (p _)). Qed.

Lemma umfiltUnPt p k v f :
        um_filter p (f \+ pts k v) =
        if valid (f \+ pts k v) then
          if p (k, v) then um_filter p f \+ pts k v else um_filter p f
        else undef.
Proof. by rewrite omfUnPt omf_omap; case: (ifP (p _)). Qed.

Lemma In_umfiltX x p f : x \In um_filter p f <-> p x /\ x \In f.
Proof.
case: x => k v; rewrite In_omfX omf_omap; split=>[[w H]|[I H]] /=.
- by case E: (p (k, w))=>//=; case=><-.
by exists v=>//; rewrite I.
Qed.

(* In_umfilt is really only good in one direction. *)
(* For the other direction, we need the following one *)
Lemma In_umfilt p x f : x \In f -> p x -> x \In um_filter p f.
Proof. by move=>X1 X2; apply/In_umfiltX. Qed.

Lemma In_dom_umfilt p f k :
        reflect (exists2 v, p (k, v) & (k, v) \In f)
                (k \in dom (um_filter p f)).
Proof.
apply: (iffP (In_domX _ _)).
-  by case=>v /In_umfiltX []; exists v.
by case=>v Hp Hf; exists v; apply/In_umfilt.
Qed.

Lemma dom_omf_umfilt V' (U' : union_map C V') (f : omap_fun U U') x :
        dom (f x) = dom (um_filter (isSome \o omf f) x).
Proof.
apply/domE=>k; apply/idP/idP.
- case/In_dom_omfX=>//= v [H1 H2].
  by apply/In_dom_umfilt; exists v. 
case/In_dom_umfilt=>w /=.
case E: (omf f (k, w))=>[a|] // _ H.
by move/In_dom: (In_omf _ H E).
Qed.

Lemma dom_omap_umfilt V' (U' : union_map C V') a x :
        dom (omap a x : U') = dom (um_filter (isSome \o a) x).
Proof. exact: dom_omf_umfilt. Qed.

Lemma dom_umfiltE p f :
        dom (um_filter p f) =
        filter (fun k => if find k f is Some v then p (k, v) else false)
               (dom f).
Proof.
apply: ord_sorted_eq=>//=.
- by apply: sorted_filter; [apply: trans | apply: sorted_dom].
move=>k; rewrite mem_filter; apply/idP/idP.
- by case/In_dom_umfilt=>w H1 H2; move/In_find: H2 (H2) H1=>-> /In_dom ->->.
case X: (find k f)=>[v|] // /andP [H1 _]; move/In_find: X=>H2.
by apply/In_dom_umfilt; exists v.
Qed.

Lemma umfilt_pred0 f : valid f -> um_filter pred0 f = Unit.
Proof. by move=>W; apply: omf_none. Qed.

Lemma umfilt_predT f : um_filter predT f = f.
Proof. by apply: omf_some. Qed.

Lemma umfilt_predI p1 p2 f :
        um_filter (predI p1 p2) f = um_filter p1 (um_filter p2 f).
Proof.
rewrite [RHS]compE eq_in_omf omf_comp !omf_omap /=.
by case=>k v H /=; case: (ifP (p2 _))=>//=; rewrite ?andbT ?andbF.
Qed.

Lemma eq_in_umfilt p1 p2 f :
        (forall kv, kv \In f -> p1 kv = p2 kv) <->
        um_filter p1 f = um_filter p2 f.
Proof.
rewrite eq_in_omf !omf_omap /=.
split=>E [k v] H; first by rewrite E.
by case: (p1 _) (E _ H); case: (p2 _).
Qed.

Lemma eq_in_umfiltI p1 p2 f :
        (forall kv, kv \In f -> p1 kv = p2 kv) ->
        um_filter p1 f = um_filter p2 f.
Proof. by move/eq_in_umfilt. Qed.

(* common use omits the localization part *)
Lemma eq_in_umfiltE p1 p2 f :
        p1 =1 p2 -> um_filter p1 f = um_filter p2 f.
Proof. by move=>S; apply/eq_in_umfilt=>kv _; apply: S. Qed.

Lemma umfiltC p1 p2 f :
        um_filter p1 (um_filter p2 f) = um_filter p2 (um_filter p1 f).
Proof.
by rewrite -!umfilt_predI; apply: eq_in_umfiltE=>x /=; rewrite andbC.
Qed.

Lemma umfilt_predU p1 p2 f :
        um_filter (predU p1 p2) f =
        um_filter p1 f \+ um_filter (predD p2 p1) f.
Proof.
rewrite omf_predU=>[|kv].
- by rewrite eq_in_omf !omf_omap /= => kv; case: (p1 _).
by rewrite !omf_omap /=; case: (p1 _)=>/=; [right|left].
Qed.

(* we put localization back In for xor *)
(* DEVCOMMENT *)
(* TODO: this should be done for all umfilt_?pred? lemmas *)
(* /DEVCOMMENT *)
Lemma umfilt_predX f p q :
        (forall kv, kv \In f -> p kv (+) q kv) ->
        f = um_filter p f \+ um_filter q f.
Proof.
move=>D; rewrite -{1}[f]umfilt_predT.
have : forall kv, kv \In f -> predT kv = (predU p q) kv.
- by move=>kv /D /=; case: (p kv).
move/eq_in_umfilt=>->; rewrite umfilt_predU; congr (_ \+ _).
by apply/eq_in_umfilt=>kv /D /=; case: (p kv)=>// /negbTE ->.
Qed.

Lemma umfilt_predD p1 p2 f :
        subpred p1 p2 ->
        um_filter p2 f = um_filter p1 f \+ um_filter (predD p2 p1) f.
Proof.
move=>S; rewrite -umfilt_predU -eq_in_umfilt=>kv _ /=.
by case E: (p1 _)=>//; apply: S E.
Qed.

Lemma umfilt_dpredU f p q :
        subpred p (predC q) ->
        um_filter (predU p q) f = um_filter p f \+ um_filter q f.
Proof.
move=>D; rewrite umfilt_predU.
suff : forall kv, kv \In f -> predD q p kv = q kv by move/eq_in_umfilt=>->.
by move=>kv _ /=; case X: (p _)=>//=; move/D/negbTE: X.
Qed.

Corollary umfilt_predC f p : f = um_filter p f \+ um_filter (predC p) f.
Proof.
rewrite -umfilt_dpredU; last by move=>? /=; rewrite negbK.
rewrite -[LHS]umfilt_predT; apply: eq_in_umfiltE=>kv /=.
by rewrite orbN.
Qed.

Lemma umfiltUnK p f1 f2 :
        valid (f1 \+ f2) ->
        um_filter p (f1 \+ f2) = f1 ->
        um_filter p f1 = f1 /\ um_filter p f2 = Unit.
Proof.
move=>V'; rewrite (umfiltUn _ V') => E.
have W' : valid (um_filter p f1 \+ um_filter p f2).
- by rewrite E; move/validL: V'.
have F : dom (um_filter p f1) =i dom f1.
- move=>x; apply/idP/idP; first by apply: omf_subdom.
  move=>D; move: (D); rewrite -{1}E domUn inE W' /=.
  by case/orP=>// /omf_subdom; case: validUn V'=>// _ _ /(_ _ D) /negbTE ->.
rewrite -{2}[f1]unitR in E F; move/(dom_prec W' E): F=>X.
by rewrite X in E W' *; rewrite (joinxK W' E).
Qed.

Lemma umfiltUE p k v f :
        um_filter p (upd k v f) =
        if C k then
           if p (k, v) then upd k v (um_filter p f)
           else free (um_filter p f) k
        else undef.
Proof. by rewrite omfUE omf_omap; case: (p _). Qed.

Lemma umfiltU p k v f :
        C k ->
        um_filter p (upd k v f) =
        if p (k, v) then upd k v (um_filter p f)
        else free (um_filter p f) k.
Proof. by move=>H; rewrite umfiltUE H. Qed.

Lemma umfoldl_umfilt R (a : R -> K -> V -> R) (p : pred (K * V)) f z0 d:
        um_foldl a z0 d (um_filter p f) =
        um_foldl (fun r k v => if p (k, v) then a r k v else r) z0 d f.
Proof.
move: f z0; elim/um_indf=>[||k v f IH W P] z0 /=.
- by rewrite !pfundef !umfoldl_undef.
- by rewrite !pfunit !umfoldl0.
have V1 : all (ord k) (dom f) by apply/allP=>x; apply: path_mem (@trans K) P.
have V2 : all (ord k) (dom (um_filter p f)).
- apply/allP=>x /In_dom_umfilt [w _] /In_dom.
  by apply: path_mem (@trans K) P.
have : valid (um_filter p (pts k v \+ f)) by rewrite pfVE W.
by rewrite !umfiltPtUn W; case: ifP=>E V3; rewrite !umfoldlPtUn // E IH.
Qed.

Lemma umfilt_mem0 p f :
        um_filter p f = Unit -> forall k v, (k, v) \In f -> ~~ p (k, v).
Proof. by move/omf_noneR=>H k v /H; rewrite omf_omap /=; case: (p _). Qed.

Lemma umfilt_mem0X p f k v :
        (k, v) \In f -> um_filter p f = Unit -> ~ p (k, v).
Proof. by move=>H /umfilt_mem0/(_ _ _ H)/negP. Qed.

Lemma umfilt_mem0L p f :
        valid f -> (forall k v, (k, v) \In f -> ~~ p (k, v)) ->
        um_filter p f = Unit.
Proof. by move=>W H; rewrite omf_none // omf_omap; case=>k v /H/negbTE ->. Qed.

Lemma umfilt_idemp p f : um_filter p (um_filter p f) = um_filter p f.
Proof.
rewrite -umfilt_predI; apply/eq_in_umfilt.
by case=>k v H /=; rewrite andbb.
Qed.

Lemma assocs_umfilt p f : assocs (um_filter p f) = filter p (assocs f).
Proof.
elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite pfundef assocs_undef.
- by rewrite pfunit assocs0. 
rewrite umfiltPtUn W assocsPtUn //=.
case: ifP W=>// H W; rewrite assocsPtUn; first by rewrite IH.
- suff: valid (um_filter p (pts k v \+ f)) by rewrite umfiltPtUn W H.
  by rewrite pfVE.
by apply/allP=>x; move/allP: P=>P; move/omf_subdom/P.
Qed.

Lemma find_umfilt k p f :
        find k (um_filter p f) =
        if find k f is Some v then
          if p (k, v) then Some v else None
        else None.
Proof. by rewrite find_omf. Qed.

Lemma unitb_umfilt p f : unitb f -> unitb (um_filter p f).
Proof. by move/unitbP=>->; rewrite pfunit unitb0. Qed.

(* filter p x is lower bound for x *)
Lemma umfilt_pleqI x p : [pcm um_filter p x <= x].
Proof.
exists (um_filter (predD predT p) x); rewrite -umfilt_predU.
by rewrite -{1}[x]umfilt_predT; apply/eq_in_umfilt=>a; rewrite /= orbT.
Qed.

Hint Resolve umfilt_pleqI : core.

Lemma dom_umfilt2 p1 p2 f x :
        x \in dom (um_filter p1 (um_filter p2 f)) =
        (x \in dom (um_filter p1 f)) && (x \in dom (um_filter p2 f)).
Proof.
rewrite -umfilt_predI; apply/idP/idP.
- case/In_dom_umfilt=>v /andP [X1 X2] H.
  by apply/andP; split; apply/In_dom_umfilt; exists v.
case/andP=>/In_dom_umfilt [v1 X1 H1] /In_dom_umfilt [v2 X2 H2].
move: (In_fun H1 H2)=>E; rewrite -{v2}E in X2 H2 *.
by apply/In_dom_umfilt; exists v1=>//; apply/andP.
Qed.

End FilterDefLemmas.

#[export]
Hint Extern 0 [pcm um_filter _ ?X <= ?X] =>
  apply: umfilt_pleqI : core.

Notation um_filterk p f := (um_filter (p \o fst) f).
Notation um_filterv p f := (um_filter (p \o snd) f).

Arguments In_umfilt [K C V U] p x f _ _.

Section FilterKLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Type f : U.
Implicit Type p q : pred K.

Lemma dom_umfiltkE p f : dom (um_filterk p f) = filter p (dom f).
Proof.
apply: ord_sorted_eq=>//=.
- by apply: sorted_filter; [apply: trans | apply: sorted_dom].
move=>k; rewrite mem_filter; apply/idP/idP.
- by case/In_dom_umfilt=>v /= -> /In_dom.
by case/andP=>H1 /In_domX [v H2]; apply/In_dom_umfilt; exists v.
Qed.

Lemma valid_umfiltkUn p1 p2 f :
        valid f ->
        {in dom f, forall x, p1 x -> p2 x -> false} ->
        valid (um_filterk p1 f \+ um_filterk p2 f).
Proof.
move=>W H; rewrite validUnAE !pfVE W /=.
apply/allP=>x; case/In_dom_umfilt=>v1 /= H2 F1.
apply/negP; case/In_dom_umfilt=>v2 /= H1 F2.
by move: (H x (In_dom F1) H1 H2).
Qed.

Lemma dom_umfiltk p f : dom (um_filterk p f) =i predI p (mem (dom f)).
Proof. by move=>k; rewrite dom_umfiltkE mem_filter. Qed.

(* DEVCOMMENT *)
(* this also holds for invalid f1, as the corollary shows *)
(* /DEVCOMMENT *)
Lemma umfiltk_dom f1 f2 :
        valid (f1 \+ f2) -> 
        um_filterk (mem (dom f1)) (f1 \+ f2) = f1.
Proof.
move=>W; apply/umem_eq; first by rewrite pfVE.
- by rewrite (validL W).
case=>k v; rewrite In_umfiltX; split=>[|H].
- by case=>H /InUn [] // /In_dom; rewrite (negbTE (dom_inNL W H)).
by split; [apply: In_dom H | apply: InL].
Qed.

Corollary umfiltk_dom' f : um_filterk (mem (dom f)) f = f.
Proof.
case: (normalP f)=>[->|H]; first by rewrite pfundef.
by rewrite -{2}[f]unitR umfiltk_dom // unitR.
Qed.

Lemma eq_in_umfiltk p1 p2 f :
        {in dom f, p1 =1 p2} -> 
        um_filterk p1 f = um_filterk p2 f.
Proof. by move=>H; apply/eq_in_umfilt; case=>k v /In_dom; apply: H. Qed.

(* filter p x is lower bound for p *)
Lemma umfiltk_subdom p f : {subset dom (um_filterk p f) <= p}.
Proof. by move=>a; rewrite dom_umfiltk; case/andP. Qed.

Lemma umfiltk_subdomE p f : 
        {subset dom f <= p} <-> um_filterk p f = f.
Proof.
split; last by move=><- a; rewrite dom_umfiltk; case/andP.
by move/eq_in_umfiltk=>->; rewrite umfilt_predT.
Qed.

(* specific consequence of subdom_umfiltkE *)
Lemma umfiltk_memdomE f : um_filterk (mem (dom f)) f = f.
Proof. by apply/umfiltk_subdomE. Qed.

Lemma find_umfiltk k (p : pred K) f :
        find k (um_filterk p f) = if p k then find k f else None.
Proof. by rewrite find_umfilt /=; case: (find _ _)=>[a|]; case: ifP. Qed.

Lemma umfiltk_subdom0 p f :
        valid f -> 
        {subset dom f <= predC p} <-> um_filterk p f = Unit.
Proof.
move=>W; split=>[H|H k X].
- rewrite (eq_in_umfiltk (p2:=pred0)) ?umfilt_pred0 //.
  by move=>a /H /negbTE ->.
case: dom_find X H=>// v _ -> _; rewrite omfUE !inE omf_omap /=.
case: (ifP (p k))=>// _ /unitbP.
by rewrite fun_if um_unitbU unitb_undef if_same.
Qed.

Lemma umfiltkPt p k v :
        um_filterk p (pts k v : U) =
        if p k then pts k v else if C k then Unit else undef.
Proof.
rewrite ptsU umfiltUE pfunit free0 /=.
by case: ifP=>//; move/negbT=>N; rewrite upd_condN // if_same.
Qed.

Lemma umfiltkPtUn p k v f :
        um_filterk p (pts k v \+ f) =
        if valid (pts k v \+ f) then
          if p k then pts k v \+ um_filterk p f else um_filterk p f
        else undef.
Proof.
case: (normalP (pts k v \+ f))=>[->|W]; first by rewrite pfundef.
rewrite pfjoinT //= umfiltPtE (validPtUn_cond W) /=. 
by case: ifP=>//; rewrite unitL.
Qed.

Lemma umfiltk_preimUn (q : pred V) f1 f2 :
        valid (f1 \+ f2) ->
        um_filterk (um_preim q (f1 \+ f2)) f1 = um_filterk (um_preim q f1) f1.
Proof.
move=>v; apply: eq_in_umfiltk; move=>x xf1; rewrite umpreimUn // inE orbC.
have -> : um_preim q f2 x = false=>//.
by move: (dom_inNL v xf1); rewrite /um_preim; case: dom_find=>//->.
Qed.

(* filters commute with omap_fun *)

Lemma umfiltk_omf V' (U' : union_map C V') (f : omap_fun U U') p x :
        f (um_filterk p x) = um_filterk p (f x).
Proof.
rewrite (compE f) [RHS]compE eq_in_omf !omf_comp !omf_omap /=.
by rewrite /obind/oapp /=; case=>k v; case: ifP; case: (omf f _).
Qed.

Lemma umfiltk_dom_omf V' (U' : union_map C V') (f : omap_fun U U') x :
        um_filterk (mem (dom x)) (f x) = f x.
Proof. by rewrite -umfiltk_omf umfiltk_dom'. Qed.

Lemma umfiltkU p k v f :
        um_filterk p (upd k v f) =
        if p k then upd k v (um_filterk p f) else
          if C k then um_filterk p f else undef.
Proof.
rewrite umfiltUE /=; case: ifP; case: ifP=>//= Hp Hc.
- by rewrite dom_free // dom_umfiltk inE Hp.
by rewrite upd_condN ?Hc.
Qed.

Lemma umfiltkF p k f :
        um_filterk p (free f k) =
        if p k then free (um_filterk p f) k else um_filterk p f.
Proof.
rewrite omfF; case: ifP=>//= N.
by rewrite dom_free // dom_umfiltk inE N.
Qed.

Lemma In_umfiltk p x f : x \In f -> p x.1 -> x \In um_filterk p f.
Proof. by apply: In_umfilt. Qed.

End FilterKLemmas.

Arguments In_umfiltk {K C V U} p {x f} _ _.

Section FilterVLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Type f : U.
Implicit Type p q : pred V.

Lemma eq_in_umfiltv (q1 q2 : pred V) f :
        (forall v, v \In range f -> q1 v = q2 v) ->
        um_filterv q1 f = um_filterv q2 f.
Proof. by move=>H; apply/eq_in_umfilt; case=>k v /In_range; apply: H. Qed.

Lemma umfiltv_predD (q1 q2 : pred V) f :
        subpred q1 q2 ->
        um_filterv q2 f = um_filterv q1 f \+ um_filterv (predD q2 q1) f.
Proof. by move=>H; apply: umfilt_predD; case. Qed.

Lemma In_umfiltv p x f : x \In f -> p x.2 -> x \In um_filterv p f.
Proof. by apply: In_umfilt. Qed.

End FilterVLemmas.

Arguments In_umfiltv {K C V U} p {x f} _ _.

Section OmapMembershipLemmas.
Variables (K : ordType) (C : pred K) (V V' : Type).
Variables (U : union_map C V) (U' : union_map C V').

Lemma mapv_omapv f g (x : U) :
        ocancel f g ->
        mapv g (omapv f x : U') = um_filterv (isSome \o f) x.
Proof. exact: mapv_omapvE. Qed.

End OmapMembershipLemmas.


(************************)
(* PCM-induced ordering *)
(************************)

(* Union maps and PCM ordering. *)

Section UmpleqLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (x y a b : U) (p : pred K).

(* PCM-induced preorder is order in the case of union maps *)

Lemma umpleq_asym x y : [pcm x <= y] -> [pcm y <= x] -> x = y.
Proof.
case=>a -> [b]; case W : (valid x); last first.
- by move/invalidE: (negbT W)=>->; rewrite undef_join.
rewrite -{1 2}[x]unitR -joinA in W *.
by case/(joinxK W)/esym/umap0E=>->; rewrite unitR.
Qed.

(* lemmas on the PCM ordering and um_filter(k) *)

Lemma umfilt_pleq_mono x y (p : pred (K * V)) :
        [pcm x <= y] -> [pcm um_filter p x <= um_filter p y].
Proof.
move=>H; case: (normalP y)=>[->|].
- by rewrite pfundef; apply: pleq_undef.
by case: H=>z -> D; rewrite pfjoinT.
Qed.

(* filter p f is largest lower bound for f and p *)
Lemma umpleq_filtk_meet a p f :
        {subset dom a <= p} -> 
        [pcm a <= f] -> 
        [pcm a <= um_filterk p f].
Proof. 
move=>D /(umfilt_pleq_mono (p \o fst)).
by rewrite (eq_in_umfiltk D) umfilt_predT.
Qed.

(* in valid case, we can define the order by means of filter *)
Lemma umpleqk_pleqE a x :
        valid x -> [pcm a <= x] <->
                   um_filterk (mem (dom a)) x = a.
Proof. by move=>W; split=>[|<-] // H; case: H W=>b ->; apply: umfiltk_dom. Qed.

(* join is the least upper bound *)
Lemma umpleq_join a b f :
        valid (a \+ b) -> 
        [pcm a <= f] -> 
        [pcm b <= f] -> 
        [pcm a \+ b <= f].
Proof.
case: (normalP f)=>[->???|Df Dab]; first by apply: pleq_undef.
move/(umpleqk_pleqE _ Df)=> <- /(umpleqk_pleqE _ Df) <-.
by rewrite -umfilt_dpredU //; case=>/= k _; apply: dom_inNL Dab.
Qed.

(* x <= y and subdom *)
Lemma umpleq_subdom x y : valid y -> [pcm x <= y] -> {subset dom x <= dom y}.
Proof. by move=>W H; case: H W=>a -> W b D; rewrite domUn inE W D. Qed.

Lemma subdom_umpleq a (x y : U) :
        valid (x \+ y) -> [pcm a <= x \+ y] ->
        {subset dom a <= dom x} -> [pcm a <= x].
Proof.
move=>W H Sx; move: (umpleq_filtk_meet Sx H); rewrite umfiltUn //.
rewrite umfiltk_memdomE; move/subsetR: (valid_subdom W).
by move/(umfiltk_subdom0 _ (validR W))=>->; rewrite unitR.
Qed.

(* meet is the greatest lower bound *)
Lemma umpleq_meet a (x y1 y2 : U) :
        valid (x \+ y1 \+ y2) ->
        [pcm a <= x \+ y1] -> [pcm a <= x \+ y2] -> [pcm a <= x].
Proof.
rewrite um_valid3=> /and3P[V1 V12 V2] H1 H2.
apply: subdom_umpleq (V1) (H1) _ => k D.
move: {D} (umpleq_subdom V1 H1 D) (umpleq_subdom V2 H2 D).
rewrite !domUn !inE V1 V2 /=; case : (k \in dom x)=>//=.
by move/(dom_inNLX V12)=>X /X.
Qed.

(* some/none lemmas *)

Lemma umpleq_some x1 x2 t s :
        valid x2 -> [pcm x1 <= x2] -> find t x1 = Some s -> find t x2 = Some s.
Proof. by move=>W H; case: H W=>a -> W H; rewrite findUnL // (find_some H). Qed.

Lemma umpleq_none x1 x2 t :
        valid x2 -> [pcm x1 <= x2] -> find t x2 = None -> find t x1 = None.
Proof. by case E: (find t x1)=>[a|] // W H <-; rewrite (umpleq_some W H E). Qed.

End UmpleqLemmas.


(********************)
(* Precision lemmas *)
(********************)

(* DEVCOMMENT *)
(* naturally belongs to dom section, but proofs use lemmas *)
(* that haven't been proved before the dom section *)
(* /DEVCOMMENT *)
Section Precision.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (x y : U).

Lemma prec_flip x1 x2 y1 y2 :
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        valid (y2 \+ x2) /\ y2 \+ x2 = y1 \+ x1.
Proof. by move=>X /esym E; rewrite joinC E X joinC. Qed.

Lemma prec_domV x1 x2 y1 y2 :
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        reflect {subset dom x1 <= dom x2} (valid (x1 \+ y2)).
Proof.
move=>V1 E; case V12 : (valid (x1 \+ y2)); constructor.
- move=>n Hs; have : n \in dom (x1 \+ y1) by rewrite domUn inE V1 Hs.
  by rewrite E domUn inE -E V1 /= (negbTE (dom_inNL V12 Hs)) orbF.
move=>Hs; case: validUn V12=>//.
- by rewrite (validE2 V1).
- by rewrite E in V1; rewrite (validE2 V1).
by rewrite E in V1; move=>k /Hs /(dom_inNL V1)/negbTE ->.
Qed.

Lemma prec_filtV x1 x2 y1 y2 :
        valid (x1 \+ y1) -> x1 \+ y1 = x2 \+ y2 ->
        reflect (x1 = um_filterk (mem (dom x1)) x2) (valid (x1 \+ y2)).
Proof.
move=>V1 E; case X : (valid (x1 \+ y2)); constructor; last first.
- case: (prec_domV V1 E) X=>// St _ H; apply: St.
  by move=>n; rewrite H dom_umfiltk inE; case/andP.
move: (umfiltk_dom V1); rewrite E umfiltUn -?E //.
rewrite (eq_in_umfiltk (f:=y2) (p2:=pred0)).
- by rewrite umfilt_pred0 ?unitR //; rewrite E in V1; rewrite (validE2 V1).
by move=>n; case: validUn X=>// _ _ L _ /(contraL (L _)) /negbTE.
Qed.

End Precision.


(****************)
(* Ordered eval *)
(****************)

(* version of eval where the user provides new order of evaluation *)
(* as list of timestamps which are then read in-order. *)

Section OrdEvalDefLemmas.
Variables (K : ordType) (C : pred K) (V R : Type) (U : union_map C V).
Implicit Type f : U.
Implicit Type a : R -> K -> V -> R.
Implicit Type p q : pred (K * V).
Implicit Type ks : seq K.

Fixpoint oeval a ks f z0 :=
  if ks is k :: ks' then
    oeval a ks' f (if find k f is Some v then a z0 k v else z0)
  else z0.

Lemma oev_undef a ks z0 : oeval a ks undef z0 = z0.
Proof. by elim: ks=>[|k ks IH] //=; rewrite find_undef. Qed.

Lemma oev0 a ks z0 : oeval a ks Unit z0 = z0.
Proof. by elim: ks=>[|k ks IH] //=; rewrite find0E. Qed.

Lemma oev_dom0 a ks f z0 : dom f =i [::] -> oeval a ks f z0 = z0.
Proof.
case: (normalP f)=>[-> _|D]; first by apply: oev_undef.
by move/(dom0E D)=>->; apply: oev0.
Qed.

(* interaction with constructors that build the ordering mask *)

Lemma oev_nil a f z0 : oeval a [::] f z0 = z0.
Proof. by []. Qed.

Lemma oev_consP a k v ks f z0 :
        (k, v) \In f -> oeval a (k :: ks) f z0 = oeval a ks f (a z0 k v).
Proof. by move/In_find=>/= ->. Qed.

Lemma oev_consN a k ks f z0 :
        k \notin dom f -> oeval a (k :: ks) f z0 = oeval a ks f z0.
Proof. by case: dom_find=>//= ->. Qed.

Lemma oev_rconsE a ks k f z0 :
        oeval a (rcons ks k) f z0 =
        if find k f is Some v then a (oeval a ks f z0) k v
        else oeval a ks f z0.
Proof. by elim: ks z0=>[|k' ks IH] z0 /=. Qed.

Lemma oev_rconsP a k v ks f z0 :
        (k, v) \In f ->
        oeval a (rcons ks k) f z0 = a (oeval a ks f z0) k v.
Proof. by rewrite oev_rconsE=>/In_find ->. Qed.

Lemma oev_rconsN a k ks f z0 :
        k \notin dom f -> oeval a (rcons ks k) f z0 = oeval a ks f z0.
Proof. by rewrite oev_rconsE=>/find_none ->. Qed.

Lemma oev_cat a ks1 ks2 f z0 :
        oeval a (ks1 ++ ks2) f z0 = oeval a ks2 f (oeval a ks1 f z0).
Proof. by elim: ks1 z0=>/=. Qed.

(* equalities of oeval wrt. each component *)

Lemma eq_in_oevA a1 a2 ks f z0 :
        (forall r k v, a1 r k v = a2 r k v) ->
        oeval a1 ks f z0 = oeval a2 ks f z0.
Proof.
move=>H; elim: ks z0=>[|k ks IH] z0 //=.
by case E : (find k f)=>[b|] //; rewrite IH H.
Qed.

Lemma eq_in_oevK a ks1 ks2 f z0 :
        [seq k <- ks1 | k \in dom f] = [seq k <- ks2 | k \in dom f] ->
        oeval a ks1 f z0 = oeval a ks2 f z0.
Proof.
suff oevFK ks : oeval a ks f z0 =
  oeval a [seq k <- ks | k \in dom f] f z0.
- by move=>E; rewrite oevFK E -oevFK.
elim: ks z0=>[|k' ks IH] z0 //=.
by case: dom_find=>[_|v /= -> _]; rewrite IH.
Qed.

Lemma eq_in_oevF a ks f1 f2 z0 :
        (forall k v, k \in ks -> (k, v) \In f1 <-> (k, v) \In f2) ->
        oeval a ks f1 z0 = oeval a ks f2 z0.
Proof.
elim: ks z0=>[|k ks IH] z0 //= H.
case E1: (find k f1)=>[v1|].
- move/In_find: E1; rewrite H ?(inE,eq_refl) // => /In_find ->.
  by apply: IH=>k' v' D; apply: H; rewrite inE D orbT.
case E2: (find k f2)=>[v2|].
- by move/In_find: E2; rewrite -H ?(inE,eq_refl) // => /In_find; rewrite E1.
by apply: IH=>k' v' D; apply: H; rewrite inE D orbT.
Qed.

(* restrictions that a, ks, f impose on each other *)

Lemma oevFK a ks f z0 :
        oeval a ks f z0 = oeval a [seq k <- ks | k \in dom f] f z0.
Proof.
by elim: ks z0=>[|k' ks IH] z0 //=; case: dom_find=>[_|v /= -> _]; rewrite IH.
Qed.

Lemma oevFA a ks f z0 :
        oeval a ks f z0 =
        oeval (fun r k v => if k \in dom f then a r k v else r) ks f z0.
Proof.
elim: ks a z0=>[|k ks IH] a z0 //=.
by case E: (find k f)=>[b|] //; rewrite (find_some E).
Qed.

Lemma oevKF a ks f z0 :
        oeval a ks f z0 =
        oeval a ks (um_filter (fun x => x.1 \in ks) f) z0.
Proof.
elim: ks f z0=>[|k ks IH] f z0 //=.
rewrite find_umfilt /= inE eq_refl [in LHS]IH [in RHS]IH /=.
congr oeval; last by case: (find k f).
by rewrite -umfilt_predI; apply/eq_in_umfilt=>kv /= D; rewrite orKb.
Qed.

Lemma oevKA a ks f z0 :
        oeval a ks f z0 =
        oeval (fun r k v => if k \in ks then a r k v else r) ks f z0.
Proof.
elim: ks a z0=>[|k ks IH] a z0 //=; rewrite inE eq_refl [in LHS]IH [in RHS]IH.
by apply: eq_in_oevA=>r k' v; case: ifP=>// D; rewrite inE D orbT.
Qed.

(* interaction with map constructions *)

Lemma oev_umfilt a ks p f z0 :
        oeval a ks (um_filter p f) z0 =
        oeval a [seq k <- ks | if find k f is Some v
                               then p (k, v) else false] f z0.
Proof.
elim: ks z0=>[|k ks IH] z0 //=; rewrite IH find_umfilt.
by case E: (find k f)=>[b|] //; case: ifP=>//= P; rewrite E.
Qed.

Lemma oev_filter a ks (p : pred K) f z0 :
        oeval a (filter p ks) f z0 =
        oeval a ks (um_filterk p f) z0.
Proof.
rewrite oev_umfilt oevFK -filter_predI; congr oeval.
by apply: eq_in_filter=>k D /=; case: dom_find.
Qed.

Lemma oev_umfiltA a ks p f z0 :
        oeval a ks (um_filter p f) z0 =
        oeval (fun r k v => if p (k, v) then a r k v else r) ks f z0.
Proof.
elim: ks z0=>[|k ks IH] z0 //=; rewrite IH find_umfilt.
by case E : (find k f)=>[b|] //; case: ifP=>//.
Qed.

(* convenient derived lemma *)
Lemma oev_dom_umfilt a p f z0 :
        oeval a (dom (um_filter p f)) f z0 =
        oeval a (dom f) (um_filter p f) z0.
Proof.
rewrite dom_umfiltE oev_filter; apply: eq_in_oevF=>k v _.
by rewrite !In_umfiltX /=; split; case=>H Y; move/In_find: Y (Y) H=>->.
Qed.

Lemma oevF a ks f z0 k :
        k \notin ks -> oeval a ks f z0 = oeval a ks (free f k) z0.
Proof.
move=>H; apply: eq_in_oevF=>k' v' D; rewrite InF /= validF.
by case: eqP H D=>[-> /negbTE -> //|???]; split; [move=>H; case: (H) | case].
Qed.

Lemma oevUE a k ks v1 v2 f (z0 : R) :
        (forall r, a r k v1 = a r k v2) ->
        oeval a ks (upd k v1 f) z0 = oeval a ks (upd k v2 f) z0.
Proof.
move=>H; elim: ks z0=>[|k' ks IH] z0 //=.
rewrite !findU; case: eqP=>// ->; rewrite IH.
by congr oeval; case: ifP.
Qed.

Lemma oevU a k ks v1 v2 f z0 :
        (k, v2) \In f ->
        (forall r, a r k v1 = a r k v2) ->
        oeval a ks (upd k v1 f) z0 = oeval a ks f z0.
Proof.
move=>X H.
have [C' W] : C k /\ valid f by move/In_dom/dom_cond: (X); case: (X).
rewrite [in RHS](_ : f = upd k v2 f); first by apply: oevUE.
apply: umem_eq=>//; first by rewrite validU C' W.
case=>k' v'; rewrite InU validU C' W /=.
case: ifP=>[/eqP ->|_]; last by split=>//; case.
by split=>[/(In_fun X)|[_] ->].
Qed.

Lemma oevPtUn a k ks v z0 f :
        valid (pts k v \+ f) -> k \notin ks ->
        oeval a ks (pts k v \+ f) z0 = oeval a ks f z0.
Proof.
move=>W S; apply: eq_in_oevF=>k0 v0 H.
rewrite InPtUnE //; split; last by right.
by case=>// [][??]; subst k0; rewrite H in S.
Qed.

(* a somewhat different version; makes side conditions easier to discharge *)
Lemma oevPtUn_sub a k ks v z0 f :
        valid (pts k v \+ f) -> {subset ks <= dom f} ->
        oeval a ks (pts k v \+ f) z0 =
        oeval a ks f z0.
Proof.
move=>W F; apply: oevPtUn=>//; apply/negP=>/F.
by rewrite (negbTE (validPtUnD W)).
Qed.

Lemma oevPtUnE a k ks v1 v2 f z0 :
        (forall r, a r k v1 = a r k v2) ->
        oeval a ks (pts k v1 \+ f) z0 = oeval a ks (pts k v2 \+ f) z0.
Proof.
move=>H; case W1 : (valid (pts k v1 \+ f)); last first.
- have W2 : valid (pts k v2 \+ f) = false by rewrite !validPtUn in W1 *.
  move/invalidE: (negbT W1)=>->; move/invalidE: (negbT W2)=>->.
  by rewrite oev_undef.
elim: ks z0=>[|k' ks IH] z0 //=.
have W2 : valid (pts k v2 \+ f) by rewrite !validPtUn in W1 *.
by rewrite !findPtUn2 //; case: eqP=>// ->; rewrite H; apply: IH.
Qed.

Lemma oev_sub_filter a ks (p : pred K) (h : U) z0 :
        {subset dom h <= p} ->
        oeval a (filter p ks) h z0 = oeval a ks h z0.
Proof.
move=>S; rewrite oev_filter (eq_in_umfiltI (p2:=predT)) ?umfilt_predT //=.
by case=>k v /In_dom /S.
Qed.

Lemma oev_ind {P : R -> Prop} f ks a z0 :
        P z0 ->
        (forall k v z0, (k, v) \In f -> k \in ks -> P z0 -> P (a z0 k v)) ->
        P (oeval a ks f z0).
Proof.
elim: ks z0=>[|k ks IH] z0 //= Z H; apply: IH; last first.
- by move=>k' v' z' X D; apply: H=>//; rewrite inE D orbT.
case E: (find k f)=>[b|] //; move/In_find: E=>E.
by apply: H=>//; rewrite inE eq_refl.
Qed.

(* a somewhat stronger lemma making clear that z0' isn't *)
(* arbitrary but always obtained by evaluation starting from z0 *)
Lemma oev_indX {P : R -> Prop} f ks a z0 :
        P z0 ->
        (forall k ks1 ks2 v z0', (k, v) \In f -> ks = ks1 ++ k :: ks2 ->
           z0' = oeval a ks1 f z0 -> P z0' -> P (a z0' k v)) ->
        P (oeval a ks f z0).
Proof.
elim: ks z0=>[|k ks IH] z0 //= Z H; apply: IH; last first.
- move=>k' ks1 ks2 v' z' X D E.
  by apply: (H k' (k::ks1) ks2 v' z' X _ _)=>//; rewrite D.
case E: (find k f)=>[b|] //; move/In_find: E=>E.
by apply: (H k [::] _ b z0).
Qed.

End OrdEvalDefLemmas.

Arguments oev_sub_filter {K C V R U a ks p}.
Notation oevalv a ks f z0 := (oeval (fun r _ => a r) ks f z0).

Section OrdEvalRelationalInduction1.
Variables (K : ordType) (C : pred K) (V R1 R2 : Type) (U : union_map C V).

Lemma oev_ind2 {P : R1 -> R2 -> Prop} (f : U) ks a1 a2 z1 z2 :
        P z1 z2 ->
        (forall k v z1 z2, (k, v) \In f -> k \in ks ->
           P z1 z2 -> P (a1 z1 k v) (a2 z2 k v)) ->
        P (oeval a1 ks f z1) (oeval a2 ks f z2).
Proof.
elim: ks a1 a2 z1 z2=>[|k ks IH] a1 a2 z1 z2 Z H //=.
apply: IH; last first.
- by move=>k' v' z1' z2' H' K'; apply: H=>//; rewrite inE K' orbT.
case H' : (find k f)=>[b|] //; move/In_find: H'=>H'.
by apply: H=>//; rewrite inE eq_refl.
Qed.

End OrdEvalRelationalInduction1.

Section OrdEvalPCM.
Variables (K : ordType) (C : pred K) (V : Type) (R : pcm) (U : union_map C V).
Implicit Type f : U.
Variable (a : R -> K -> V -> R).
Implicit Type p q : pred (K * V).
Implicit Type ks : seq K.
Hypothesis frame : forall x y k v, a (x \+ y) k v = a x k v \+ y.

Lemma oev1 ks f z0 : oeval a ks f z0 = oeval a ks f Unit \+ z0.
Proof.
apply: (oev_ind2 (P:=fun r1 r2 => r1 = r2 \+ z0)); first by rewrite unitL.
by move=>k v z1 z2 H1 H2 ->; apply: frame.
Qed.

Lemma oevUn ks (f1 f2 : U) (z0 : R) :
        valid (f1 \+ f2) ->
        oeval a ks (f1 \+ f2) z0 = oeval a ks f1 (oeval a ks f2 z0).
Proof.
move=>W; elim: ks z0=>[|k ks IH] z0 //=; rewrite findUnL //.
case: dom_find=>[E|v E _]; rewrite IH //.
move/In_find/In_dom/(dom_inNL W)/find_none: E=>->; congr oeval; apply/esym.
by rewrite oev1 joinC frame joinC -oev1.
Qed.

End OrdEvalPCM.


(********)
(* eval *)
(********)

(* A special case of oeval with the initial value used *)
(* as default for undefined maps. *)

Section EvalDefLemmas.
Variables (K : ordType) (C : pred K) (V R : Type) (U : union_map C V).
Implicit Type f : U.
Implicit Type a : R -> K -> V -> R.
Implicit Type p q : pred (K * V).

Definition eval a p f z0 :=
  oeval a (dom (um_filter p f)) f z0.

Lemma eval_oevUmfilt a p f z0 :
        eval a p f z0 =
        oeval a (dom (um_filter p f)) (um_filter p f) z0.
Proof.
apply: eq_in_oevF =>k v H; rewrite In_umfiltX.
split=>[|[]//]; split=>//; case/In_dom_umfilt: H=>v' H H1.
by rewrite (In_fun H1 H0) in H.
Qed.

Lemma eval_undef a p z0 : eval a p undef z0 = z0.
Proof. by rewrite /eval oev_undef. Qed.

Lemma eval0 a p z0 : eval a p Unit z0 = z0.
Proof. by rewrite /eval oev0. Qed.

Lemma eval_dom0 a p f z0 : dom f =i [::] -> eval a p f z0 = z0.
Proof. by move=> H; rewrite /eval oev_dom0. Qed.

Lemma evalPt a p (z0 : R) k v :
        eval a p (pts k v) z0 = if C k && p (k, v) then a z0 k v else z0.
Proof.
rewrite /eval umfiltPtE.
case E1: (C k); last by rewrite dom_undef oev_nil.
case: (p (k, v)); last by rewrite dom0 oev_nil.
by rewrite domPtK E1 /= findPt E1.
Qed.

Lemma evalPtUn a p k v z0 f :
        valid (pts k v \+ f) -> all (ord k) (dom f) ->
        eval a p (pts k v \+ f) z0 =
        eval a p f (if p (k, v) then a z0 k v else z0).
Proof.
move=>W /allP H; have: valid (um_filter p (pts k v \+ f)) by rewrite pfV.
rewrite /eval umfiltPtUn W.
case: (p (k, v))=>W'; last first.
- rewrite oevPtUn //; apply/negP=>/omf_subdom.
  by rewrite (negbTE (validPtUnD W)).
rewrite domPtUnK //=; last by apply/allP=>x /omf_subdom /H.
by rewrite findPtUn // oevPtUn // (validPtUnD W').
Qed.

Lemma evalUnPt a p k v z0 f :
        valid (f \+ pts k v) -> all (ord^~ k) (dom f) ->
        eval a p (f \+ pts k v) z0 =
        if p (k, v) then a (eval a p f z0) k v else eval a p f z0.
Proof.
move=>W /allP H; have: valid (um_filter p (f \+ pts k v)) by rewrite pfV.
rewrite /eval umfiltUnPt W.
case: (p (k, v))=>W'; last first.
- rewrite joinC oevPtUn //; first by rewrite joinC.
  by apply/negP=>/omf_subdom; rewrite (negbTE (validUnPtD W)).
rewrite domUnPtK //=; last by apply/allP=>x /omf_subdom /H.
rewrite (oev_rconsP _ (v:=v)) // joinC oevPtUn //; first by rewrite joinC.
by apply/negP=>/omf_subdom; rewrite (negbTE (validUnPtD W)).
Qed.

Lemma evalUn a p z0 f1 f2 :
        valid (f1 \+ f2) -> {in dom f1 & dom f2, forall x y, ord x y} ->
        eval a p (f1 \+ f2) z0 = eval a p f2 (eval a p f1 z0).
Proof.
elim/um_indb: f2=>[||k v f2 IH W' P W H].
- by rewrite join_undef valid_undef.
- by rewrite dom0 !unitR eval0.
rewrite -(joinC f2) joinA in W *; rewrite evalUnPt //; last first.
- apply/allP=>x; rewrite domUn inE (validL W).
  case/orP=>[/H|]; last by apply: P.
  by apply; rewrite domPtUn inE joinC W' eq_refl.
rewrite evalUnPt //; last by apply/allP.
rewrite (IH (validL W)) // => k1 k2 D1 D2; apply: H D1 _.
by rewrite domPtUn inE joinC W' D2 orbT.
Qed.

Lemma evalPtUnE v2 v1 a p k (z0 : R) f :
        (forall r, (if p (k, v1) then a r k v1 else r) =
                   (if p (k, v2) then a r k v2 else r)) ->
        eval a p (pts k v1 \+ f) z0 = eval a p (pts k v2 \+ f) z0.
Proof.
move=>H; rewrite /eval !oev_dom_umfilt !oev_umfiltA.
by rewrite (domPtUnE2 k v1 v2); apply: oevPtUnE.
Qed.

Lemma evalUEU v2 v1 a p k (z0 : R) f :
        (forall r, (if p (k, v1) then a r k v1 else r) =
                   (if p (k, v2) then a r k v2 else r)) ->
        eval a p (upd k v1 f) z0 = eval a p (upd k v2 f) z0.
Proof.
move=>H; rewrite /eval !oev_dom_umfilt !oev_umfiltA.
rewrite (oevUE _ _ _ H); apply: eq_in_oevK; congr filter.
by apply/domE=>x; rewrite !domU.
Qed.

Lemma evalUE v2 v1 a p k (z0 : R) f :
        (k, v2) \In f ->
        (forall r, (if p (k, v1) then a r k v1 else r) =
                   (if p (k, v2) then a r k v2 else r)) ->
        eval a p (upd k v1 f) z0 = eval a p f z0.
Proof.
move=>X H; rewrite (evalUEU _ _ H) (_ : upd k v2 f = f) //.
have [C' W] : C k /\ valid f by move/In_dom/dom_cond: (X); case: (X).
apply: umem_eq=>//; first by rewrite validU C' W.
case=>k' v'; rewrite InU validU C' W /=.
by case: ifP=>[/eqP ->|_]; [split=>[[_] ->|/(In_fun X)] | split=>[[]|]].
Qed.

Lemma eval_ifP a p z0 f :
        eval a p f z0 =
        eval (fun r k v => if p (k, v) then a r k v else r) predT f z0.
Proof. by rewrite /eval umfilt_predT oev_dom_umfilt oev_umfiltA. Qed.

Lemma eq_filt_eval a p1 p2 z0 f1 f2 :
        um_filter p1 f1 = um_filter p2 f2 ->
        eval a p1 f1 z0 = eval a p2 f2 z0.
Proof. by rewrite !eval_oevUmfilt=>->. Qed.

Lemma eval_pred0 a z0 f : eval a xpred0 f z0 = z0.
Proof.
case: (normalP f)=>[->|D]; first by rewrite eval_undef.
by rewrite /eval umfilt_pred0 // dom0.
Qed.

Lemma eval_predI a p q z0 f :
        eval a p (um_filter q f) z0 = eval a (predI p q) f z0.
Proof. by rewrite !eval_oevUmfilt -!umfilt_predI. Qed.

Lemma eval_umfilt p z0 f a :
        eval a p f z0 = eval a xpredT (um_filter p f) z0.
Proof. by rewrite eval_predI; apply: eq_filt_eval; apply/eq_in_umfilt. Qed.

Lemma eq_in_eval p q z0 f a :
        (forall kv, kv \In f -> p kv = q kv) ->
        eval a p f z0 = eval a q f z0.
Proof.
by rewrite (eval_umfilt p) (eval_umfilt q); move/eq_in_umfilt=>->.
Qed.

Lemma eval_ind {P : R -> Prop} f p a z0 :
        P z0 ->
        (forall k v z0, (k, v) \In f -> p (k, v) -> P z0 -> P (a z0 k v)) ->
        P (eval a p f z0).
Proof.
move=>Z H; elim/um_indf: f z0 Z H=>[||k v h IH W T] z0 Z H;
rewrite ?eval_undef ?eval0 // evalPtUn // ?(order_path_min (@trans K) T) //.
by apply: IH=>[|k0 v0 z1 /(InR W)]; [case: ifP=>Pk //=; apply: H | apply: H].
Qed.

End EvalDefLemmas.


Section EvalOmapLemmas.
Variables (K : ordType) (C : pred K) (V V' R : Type).
Variables (U : union_map C V) (U' : union_map C V').

Lemma eval_omap (b : R -> K -> V' -> R) p a (f : U) z0 :
        eval b p (omap a f : U') z0 =
        eval (fun r k v =>
               if a (k, v) is Some v' then b r k v' else r)
             (fun kv =>
               if a kv is Some v' then p (kv.1, v') else false)
             f z0.
Proof.
elim/um_indf: f z0=>[||k v f IH W /(order_path_min (@trans K)) P] z0.
- by rewrite pfundef !eval_undef.
- by rewrite pfunit !eval0.
rewrite omapPtUn W evalPtUn //=; case D : (a (k, v))=>[w|]; last by apply: IH.
rewrite evalPtUn //; last by move/allP: P=>H; apply/allP=>x /omf_subdom /H.
rewrite (_ : pts k w \+ omap a f = omap a (pts k v \+ f)) ?valid_omap //.
by rewrite omapPtUn W D.
Qed.

End EvalOmapLemmas.


Section EvalRelationalInduction1.
Variables (K : ordType) (C : pred K) (V R1 R2 : Type) (U : union_map C V).

Lemma eval_ind2 {P : R1 -> R2 -> Prop} (f : U) p0 p1 a0 a1 z0 z1 :
        P z0 z1 ->
        (forall k v z0 z1, (k, v) \In f -> P z0 z1 ->
           P (if p0 (k, v) then a0 z0 k v else z0)
             (if p1 (k, v) then a1 z1 k v else z1)) ->
        P (eval a0 p0 f z0) (eval a1 p1 f z1).
Proof.
move=>Z H; elim/um_indf: f z0 z1 Z H=>[||k v h IH W T] z0 z1 Z H;
rewrite ?eval_undef ?eval0 // !evalPtUn // ?(order_path_min (@trans K) T) //=.
apply: IH; first by case: ifPn (H k v z0 z1 (InPtUnL W) Z).
by move=>k0 v0 w1 w2 X; apply: H (InR W X).
Qed.

End EvalRelationalInduction1.


Section EvalRelationalInduction2.
Variables (K1 K2 : ordType) (C1 : pred K1) (C2 : pred K2).
Variables (V1 V2 R1 R2 : Type).
Variables (U1 : union_map C1 V1) (U2 : union_map C2 V2).
Variables (U : union_map C1 K2) (P : R1 -> R2 -> Prop).

(* generalization of eval_ind2 to different maps, but related by a bijection *)

(* f1 and f2 evaluate the same if there exists a monotone bijection *)
(* phi between their timestamps, so that the filtering and *)
(* stepping functions are invariant under the bijection *)

Lemma eval_ind3 (phi : U)
        (f1 : U1) (p1 : pred (K1*V1)) (a1 : R1 -> K1 -> V1 -> R1) (z1 : R1)
        (f2 : U2) (p2 : pred (K2*V2)) (a2 : R2 -> K2 -> V2 -> R2) (z2 : R2) :
        um_mono phi -> dom phi = dom f1 -> range phi = dom f2 ->
        P z1 z2 ->
        (forall k1 v1 k2 v2 z1 z2,
           (k1, k2) \In phi -> (k1, v1) \In f1 -> (k2, v2) \In f2 ->
           P z1 z2 ->
           P (if p1 (k1, v1) then a1 z1 k1 v1 else z1)
             (if p2 (k2, v2) then a2 z2 k2 v2 else z2)) ->
        P (eval a1 p1 f1 z1) (eval a2 p2 f2 z2).
Proof.
elim/um_indf: f1 f2 phi z1 z2 =>[||k1 v1 f1 IH W Po]
  f2 phi1 z1 z2 /ummonoP M1 D1 R Hz H.
- rewrite eval_undef eval_dom0 // -R; move/domE: D1; rewrite dom_undef.
  case W1 : (valid phi1); first by move/(dom0E W1)=>->; rewrite range0.
  by move/negbT/invalidE: W1=>->; rewrite dom_undef range_undef.
- rewrite eval0 eval_dom0 // -R; move/domE: D1; rewrite dom0.
  case W1 : (valid phi1); first by move/(dom0E W1)=>->; rewrite range0.
  by move/negbT/invalidE: W1=>->; rewrite dom_undef range_undef.
have A1 : all (ord k1) (dom f1) by apply: order_path_min Po; apply: trans.
case W1 : (valid phi1); last first.
- by move/negbT/invalidE: W1 D1 R=>->; rewrite dom_undef domPtUnK.
rewrite domPtUnK // in D1 *; rewrite evalPtUn //.
have [k2 I1] : exists k2, (k1, k2) \In phi1.
- by apply/In_domX; rewrite D1 inE eq_refl.
have I2 : (k1, v1) \In pts k1 v1 \+ f1 by apply/InPtUnE=>//; left.
have [v2 I3] : exists v2, (k2, v2) \In f2.
- by apply/In_domX; rewrite -R; apply/mem_seqP/(In_range I1).
move: (H _ _ _ _ _ _ I1 I2 I3 Hz)=>Hp.
set phi2 := free phi1 k1.
have W2 : valid f2 by move/In_dom/dom_valid: I3.
have E2 : f2 = pts k2 v2 \+ free f2 k2 by apply/In_eta: I3.
have A2 : all (ord k2) (dom (free f2 k2)).
- apply/allP=>x; rewrite domF inE E2 domPtUn inE -E2 W2 /= domF inE.
  case: eqP=>//= N; rewrite -R =>R'; move/mem_seqP/In_rangeX: (R').
  case=>k' H1; apply: M1 (I1) (H1) _; move/allP: A1; apply.
  move/In_dom: H1 (H1); rewrite D1 inE; case/orP=>//= /eqP ->.
  by move/(In_fun I1)/N.
rewrite E2 evalPtUn -?E2 //.
have M2 : um_mono phi2.
- by apply/ummonoP=>???? /InF [_ _ /M1] X /InF [_ _]; apply: X.
have D2 : dom phi2 = dom f1.
- apply/domE=>x; rewrite domF inE D1 inE eq_sym.
  by case: eqP=>// ->{x}; rewrite (negbTE (validPtUnD W)).
have R2' : range phi2 = dom (free f2 k2).
  move/In_eta: (I1) (R)=>E1; rewrite E1 rangePtUnK.
  - by rewrite {1}E2 domPtUnK //; [case | rewrite -E2].
  - by rewrite -E1.
  apply/allP=>x; rewrite domF inE D1 inE eq_sym.
  by case: eqP=>//= _; apply/allP/A1.
have {}H x1 w1 x2 w2 t1 t2 : (x1, x2) \In phi2 -> (x1, w1) \In f1 ->
  (x2, w2) \In free f2 k2 -> P t1 t2 ->
  P (if p1 (x1, w1) then a1 t1 x1 w1 else t1)
    (if p2 (x2, w2) then a2 t2 x2 w2 else t2).
- case/InF=>_ _ F1 F2 /InF [_ _ F3].
  by apply: H F1 _ F3; apply/(InPtUnE _ W); right.
by case: ifP Hp=>L1; case: ifP=>L2 Hp; apply: IH M2 D2 R2' Hp H.
Qed.

End EvalRelationalInduction2.


(* Evaluating frameable functions *)
Section EvalFrame.
Variables (K : ordType) (C : pred K) (V : Type) (R : pcm) (U : union_map C V).
Variables (a : R -> K -> V -> R) (p : pred (K * V)).
Hypothesis frame : (forall x y k v, a (x \+ y) k v = a x k v \+ y).

Implicit Type f : U.

(* a lemma on eval update only makes sense if the function a is frameable, *)
(* so that the result is independent of the order of k *)
Lemma evalFPtUn k v z0 f :
        valid (pts k v \+ f) ->
        eval a p (pts k v \+ f) z0 =
        if p (k, v) then a Unit k v \+ eval a p f z0 else eval a p f z0.
Proof.
move=>W; rewrite /eval umfiltPtUn W.
have D : k \notin dom f by apply: (validPtUnD W).
have Ck : C k by apply: (validPtUn_cond W).
case: ifP=>_; last by apply: oevPtUn_sub=>//; apply: omf_subdom.
rewrite oevUn // -(oev_sub_filter (p:=mem [:: k])) ?(domPtK,Ck) //.
rewrite -dom_umfiltkE umfiltPtUn /= valid_omfUnR // inE eq_refl.
rewrite umfilt_mem0L ?(inE,pfV,validR W) //=; first last.
- by move=>?? /In_umfiltX [] _ /In_dom Df; rewrite inE; case: eqP Df D=>// ->->.
rewrite unitR domPtK Ck /= findPt Ck -frame unitL.
rewrite -(oev_sub_filter (p:=mem (dom f))) //.
rewrite -dom_umfiltkE umfiltPtUn /= valid_omfUnR // (negbTE D).
congr (a (oeval a (dom _) f z0) k v).
by rewrite -umfiltk_subdomE; apply: omf_subdom.
Qed.

Lemma evalFU k v z0 f :
        valid (upd k v f) ->
        eval a p (upd k v f) z0 =
        if p (k, v) then a Unit k v \+ eval a p (free f k) z0
        else eval a p (free f k) z0.
Proof.
move=>W; move: (W); rewrite validU =>/andP [C1 _].
have /um_eta2 E : find k (upd k v f) = Some v.
- by rewrite findU eq_refl -(validU k v) W.
by rewrite E evalFPtUn -?E // freeU eq_refl C1.
Qed.

End EvalFrame.

Notation evalv a p f z0 := (eval (fun r _ => a r) p f z0).


(************)
(* um_count *)
(************)

Section CountDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Type f : U.
Implicit Type p : pred (K * V).

Definition um_count p f := size (dom (um_filter p f)).

Lemma umcnt0 p : um_count p Unit = 0.
Proof. by rewrite /um_count pfunit dom0. Qed.

Lemma umcnt_undef p : um_count p undef = 0.
Proof. by rewrite /um_count pfundef dom_undef. Qed.

Lemma umcntPt p k v :
        um_count p (pts k v) = if C k && p (k, v) then 1 else 0.
Proof.
rewrite /um_count umfiltPtE; case C': (C k); last by rewrite dom_undef.
by case: ifP; [rewrite domPtK C' | rewrite dom0].
Qed.

Lemma umcntUn p f1 f2 :
        valid (f1 \+ f2) ->
        um_count p (f1 \+ f2) = um_count p f1 + um_count p f2.
Proof.
by move=>W; rewrite /um_count umfiltUn // size_domUn // -umfiltUn // pfV.
Qed.

Lemma umcntPtUn p k v f :
        valid (pts k v \+ f) ->
        um_count p (pts k v \+ f) = (if p (k, v) then 1 else 0) + um_count p f.
Proof. by move=>W; rewrite umcntUn // umcntPt (validPtUn_cond W). Qed.

Lemma umcntUnPt p k v f :
        valid (f \+ pts k v) ->
        um_count p (f \+ pts k v) = um_count p f + if p (k, v) then 1 else 0.
Proof. by rewrite joinC=>W; rewrite umcntPtUn // addnC. Qed.

Lemma umcntF p k v f :
        (k, v) \In f ->
        um_count p (free f k) =
        if p (k, v) then (um_count p f).-1 else um_count p f.
Proof.
move=>H; move/In_dom: (H)=>/= D; rewrite /um_count.
case E: (k \in dom (um_filter p f)).
- case/In_dom_umfilt: E=>w H1 H2.
  rewrite -{w H2}(In_fun H H2) in H1 *.
  rewrite H1 omfF size_domF ?subn1 //=.
  by apply/In_dom_umfilt; exists v.
rewrite omfF; case: ifP=>P; last by rewrite dom_free // E.
by move/negP: E; elim; apply/In_dom_umfilt; exists v.
Qed.

Lemma umcntU p k v w f :
        (k, w) \In f ->
        um_count p (upd k v f) =
        if p (k, v) then
          if p (k, w) then um_count p f else (um_count p f).+1
        else
          if p (k, w) then (um_count p f).-1 else um_count p f.
Proof.
move=>H; have E : f = pts k w \+ free f k.
- by apply: um_eta2; apply/In_find.
have W1 : valid f by move/In_dom/dom_valid: H.
have W2 : valid (pts k v \+ free f k).
- by rewrite {1}E !validPtUn in W1 *.
have W3 : valid (pts k w \+ free f k).
- by rewrite {1}E !validPtUn in W1 *.
rewrite {1}E updPtUn umcntPtUn // (umcntF p H).
case: ifP=>H1; case: ifP=>H2; rewrite ?add0n ?add1n //.
have: um_count p f > 0; first by rewrite E umcntPtUn // H2.
by case X: (um_count p f).
Qed.

Lemma eq_in_umcnt p1 p2 f :
        (forall kv, kv \In f -> p1 kv = p2 kv) ->
        um_count p1 f = um_count p2 f.
Proof. by rewrite /um_count=>/eq_in_umfilt ->. Qed.

(* common case *)
Lemma eq_in_umcnt2 p1 p2 f :
        p1 =1 p2 -> um_count p1 f = um_count p2 f.
Proof. by move=>S; apply: eq_in_umcnt=>kv _; apply: S. Qed.

Lemma umcnt_leq p1 p2 f :
        subpred p1 p2 -> um_count p1 f <= um_count p2 f.
Proof.
move=>S; case: (normalP f)=>[->|W]; first by rewrite !umcnt_undef.
rewrite /um_count (umfilt_predD _ S) size_domUn ?leq_addr //.
by rewrite -umfilt_predD // pfV.
Qed.

Lemma umcnt_count q f : count q (dom f) = um_count (q \o fst) f.
Proof.
rewrite assocs_dom /um_count -size_assocs.
by rewrite assocs_umfilt /= size_filter count_map.
Qed.

Lemma umcnt_umfilt p q f :
        um_count p (um_filter q f) = um_count (predI p q) f.
Proof. by rewrite /um_count umfilt_predI. Qed.

Lemma umcnt_umfiltC p q f :
        um_count p (um_filter q f) = um_count q (um_filter p f).
Proof. by rewrite !umcnt_umfilt; apply: eq_in_umcnt=>x; rewrite /= andbC. Qed.

Lemma umcnt_pred0 f : um_count pred0 f = 0.
Proof.
case: (normalP f)=>[->|D]; first by rewrite umcnt_undef. 
by rewrite /um_count umfilt_pred0 // dom0.
Qed.

Lemma umcnt_predT f : um_count predT f = size (dom f).
Proof. by rewrite /um_count umfilt_predT. Qed.

Lemma umcnt_predU p1 p2 f :
        um_count (predU p1 p2) f =
        um_count p1 f + um_count (predD p2 p1) f.
Proof.
case: (normalP f)=>[->|W]; first by rewrite !umcnt_undef.
rewrite /um_count umfilt_predU size_domUn //.
case: validUn=>//; rewrite ?(pfV,W) //.
move=>k /In_dom_umfilt [v1 P1 H1] /In_dom_umfilt [v2 /= P2 H2].
by rewrite -(In_fun H1 H2) P1 in P2.
Qed.

Lemma umcnt_predD p1 p2 f :
        subpred p1 p2 ->
        um_count p2 f = um_count p1 f + um_count (predD p2 p1) f.
Proof.
move=>S; rewrite -umcnt_predU //; apply: eq_in_umcnt=>kv /= _.
by case E: (p1 kv)=>//; apply: S.
Qed.

Lemma umcnt_predDE p1 p2 f :
        um_count (predD p2 p1) f =
        um_count p2 f - um_count (predI p1 p2) f.
Proof.
have S1 : p2 =1 predU (predD p2 p1) (predI p1 p2).
- by move=>x /=; case: (p1 x)=>//; rewrite orbF.
have S2: predD (predI p1 p2) (predD p2 p1) =1 predI p1 p2.
- by move=>x /=; case: (p1 x)=>//; rewrite andbF.
rewrite {1}(eq_in_umcnt2 _ S1) umcnt_predU // (eq_in_umcnt2 _ S2).
by rewrite -addnBA // subnn addn0.
Qed.

Lemma umcnt_umfiltU p f q1 q2 :
        um_count p (um_filter (predU q1 q2) f) =
        um_count p (um_filter q1 f) + um_count p (um_filter (predD q2 q1) f).
Proof. by rewrite umcnt_umfiltC umcnt_predU !(umcnt_umfiltC p). Qed.

Lemma umcnt_umfilt0 f :
        valid f -> forall p, um_count p f = 0 <-> um_filter p f = Unit.
Proof.
move=>W; split; last by rewrite /um_count=>->; rewrite dom0.
by move/size0nil=>D; apply: dom0E; rewrite ?pfV ?D.
Qed.

Lemma umcnt_eval0 R a p f (z0 : R) : um_count p f = 0 -> eval a p f z0 = z0.
Proof.
case: (normalP f)=>[->|W]; first by rewrite eval_undef.
by move/(umcnt_umfilt0 W)=>E; rewrite eval_umfilt E eval0.
Qed.

Lemma umcnt_mem0 p f :
        um_count p f = 0 <-> (forall k v, (k, v) \In f -> ~~ p (k, v)).
Proof.
case: (normalP f)=>[->|W].
- by rewrite umcnt_undef; split=>// _ k v /In_undef.
split; first by move/(umcnt_umfilt0 W)/umfilt_mem0.
by move=>H; apply/(umcnt_umfilt0 W); apply/umfilt_mem0L.
Qed.

Lemma umcnt_size p f : um_count p f <= size (dom f).
Proof. by rewrite -umcnt_predT; apply: umcnt_leq. Qed.

Lemma umcnt_memT p f :
        um_count p f = size (dom f) <->
        forall k v, (k, v) \In f -> p (k, v).
Proof.
elim/um_indf: f=>[||k v f IH W P].
- by rewrite umcnt_undef dom_undef; split=>// _ k v /In_undef.
- by rewrite umcnt0 dom0; split=>// _ k v /In0.
rewrite umcntPtUn // size_domPtUn //.
case: ifP=>H; split.
- move/eqP; rewrite !add1n eqSS=>/eqP/IH=>H1 k1 v1.
  by case/InPtUnE=>//; [case=>->-> | apply: H1].
- move=>H1; apply/eqP; rewrite !add1n eqSS; apply/eqP.
  by apply/IH=>k1 v1 H2; apply: H1; apply/InR.
- by rewrite add0n=>X; move: (umcnt_size p f); rewrite X add1n ltnn.
by move/(_ k v)/(_ (InPtUnL W)); rewrite H.
Qed.

Lemma umcnt_filt_eq p f : um_count p f = size (dom f) <-> f = um_filter p f.
Proof.
rewrite umcnt_memT -{2}[f]umfilt_predT -eq_in_umfilt.
by split=>H; [case=>k v /H | move=>k v /H].
Qed.

Lemma umcnt_eval p f : um_count p f = eval (fun n _ _ => n.+1) p f 0.
Proof.
elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite umcnt_undef eval_undef.
- by rewrite umcnt0 eval0.
rewrite umcntPtUn // evalPtUn //=; case: ifP=>// H.
by rewrite /eval oev1 // IH addnC; congr (_ + _).
Qed.

End CountDefLemmas.


(*************************************)
(* Filtering maps of tagged elements *)
(*************************************)

Section SideFilter.
Variables (T : eqType) (Us : T -> Type).

(* could also be defined as *)
(* Definition side_m t : sigT Us -> option (Us t) := *)
(*   fun '(Tag tx ux) => *)
(*     if t =P tx is ReflectT pf then Some (cast Us pf ux) *)
(*    else None. *)
(* but that doesn't reduce to then/else clause *)
(* if t == tx and t != tx, respectively *)
(* The following definition gets that reduction *)

Definition side_m t : sigT Us -> option (Us t) :=
  fun '(Tag tx ux) => 
    if decP (t =P tx) is left pf then Some (cast Us pf ux) 
    else None.
 
Lemma side_ocancel t : ocancel (side_m t) (Tag t).
Proof. by case=>tx vx /=; case: eqP=>//= pf; subst tx; rewrite eqc. Qed.

End SideFilter.

#[export]
Hint Extern 0 (ocancel (side_m _) (Tag _)) =>
 (apply: side_ocancel) : core.

(* select all tags in h that equal t *)
(* differs from tags t in that it drops t *)
(* from the result map *)
(* whereas tags keeps the entries in result map unmodified *)

Section Side.
Variables (K : ordType) (C : pred K) (T : eqType) (Us : T -> Type).
Variables (U : union_map C (sigT Us)).
Variables (Ut : forall t, union_map C (Us t)).
Variables t : T.

Definition side_map : U -> Ut t := locked (omapv (side_m t)).
Lemma side_unlock : side_map = omapv (side_m t).
Proof. by rewrite /side_map -lock. Qed.
Lemma sidemap_is_omf : omap_fun_axiom side_map (side_m t \o snd).
Proof. by rewrite side_unlock; apply: omfE. Qed.
HB.instance Definition _ := 
  isOmapFun.Build K C (sigT Us) (Us t) U (Ut t) side_map sidemap_is_omf.

(* explicit name for validity of side *)
Lemma valid_side (h : U) : valid (side_map h) = valid h.
Proof. exact: pfVE. Qed.

Lemma In_side x (v : Us t) (h : U) :
        (x, v) \In side_map h <-> (x, Tag t v) \In h.
Proof.
rewrite side_unlock In_omapX; split=>[|H]; last first.
- by exists (Tag t v)=>//=; case: eqP=>//= ?; rewrite eqc.
case; case=>t' v' /= H; case: eqP=>//= ?; subst t'.
by rewrite eqc; case=><-.
Qed.

Lemma side_umfilt p q (h : U) : 
        (forall k v, 
           (k, Tag t v) \In h -> p (k, Tag t v) = q (k, v)) ->
        side_map (um_filter p h) = um_filter q (side_map h).
Proof.
move=>H; rewrite side_unlock /um_filter !omap_omap eq_in_omf !omf_omap /=. 
rewrite /side_m/obind/oapp/=; case=>k; case=>t' v X /=. 
by case P : (p _); case: eqP=>//= ?; subst t'; rewrite eqc -H // P.
Qed.

(* if p can only inspect keys *)
Lemma side_umfiltk (p : pred K) h : 
        side_map (um_filterk p h) = um_filterk p (side_map h).
Proof. by apply: side_umfilt. Qed.

Lemma In_side_umfiltX x (v : Us t) p (h : U) :
        (x, v) \In side_map (um_filter p h) <->
        p (x, Tag t v) /\ (x, Tag t v) \In h.
Proof. by rewrite In_side In_umfiltX. Qed.

Lemma In_side_umfilt x (v : Us t) (p : pred (K * sigT Us)) (h : U) :
        p (x, Tag t v) -> (x, Tag t v) \In h ->
        (x, v) \In side_map (um_filter p h).
Proof. by move=>H1 H2; apply/In_side_umfiltX. Qed.

Lemma In_dom_sideX x (h : U) :
        reflect (exists a, (x, Tag t a) \In h) 
                (x \in dom (side_map h)).
Proof.
case: In_dom_omfX=>/= H; constructor.
- case: H=>[[t' v']][H]; rewrite /omfx/=.  
  by case: eqP=>// ?; subst t'; exists v'.
case=>v H'; elim: H.
exists (Tag t v); split=>//; rewrite /omfx/=. 
by case: eqP=>// ?; rewrite eqc.
Qed.

Lemma In_dom_side x a (h : U) :
        (x, Tag t a) \In h -> x \in dom (side_map h).
Proof. by move/In_side/In_dom. Qed.

Lemma sidePtE x e :
        side_map (pts x e) = 
        if C x then
          if decP (t =P tag e) is left pf then 
            pts x (cast Us pf (tagged e)) else Unit
        else undef.
Proof. by case: e=>k v; rewrite omfPtE /omfx/=; case: eqP. Qed.

Lemma dom_sidePt x e : 
        dom (side_map (pts x e)) =
        if C x && (t == tag e) then [:: x] else [::].
Proof.
rewrite sidePtE; case H : (C x)=>//=; last by rewrite dom_undef.
case: eqP=>[pf|] /=; last by rewrite dom0.
by rewrite domPtK H.
Qed.

Lemma dom_sidePtUn k e h :
        dom (side_map (pts k e \+ h)) =i
        [pred x | valid (pts k e \+ h) &
          (x == k) && (t == tag e) || (x \in dom (side_map h))].
Proof.
move=>x; rewrite dom_omfPtUn !inE /omfx/= (andbC (x == k)). 
by case: e=>t' v /=; case: eqP.
Qed.

End Side.

Arguments side_map {K C T Us U}.
Arguments In_side {K C T Us U} Ut {t x v h}.
Arguments In_dom_sideX {K C T Us U} Ut {t x h}.
Arguments In_dom_side {K C T Us U} Ut {t x a h}.


(* lemmas about two different sides *)

Section Side2.
Variables (K : ordType) (C : pred K) (T : eqType) (Us : T -> Type).
Variables (U : union_map C (sigT Us)).
Variables (Ut : forall t, union_map C (Us t)).
Variables t1 t2 : T.

Lemma sideN_all_predC (h : U) :
        t1 <> t2 -> 
        all [predC dom (side_map Ut t1 h)] 
            (dom (side_map Ut t2 h)).
Proof.
move=>N; apply/allP=>x /In_domX [v1] /In_side H /=.
apply/negP=>/In_domX [v2] /In_side /(In_fun H).
by case=>X; rewrite X in N.
Qed.

Lemma In_side_fun k (v1 : Us t1) (v2 : Us t2) (h : U) :
        (k, v1) \In side_map Ut t1 h ->
        (k, v2) \In side_map Ut t2 h ->
        t1 = t2 /\ jmeq Us v1 v2.
Proof.
move/In_side=>H /In_side/(In_fun H) [?]; subst t2.
by move/inj_pair2=>->.
Qed.

Lemma dom_sideE k (h : U) :
        k \in dom (side_map Ut t1 h) -> 
        k \in dom (side_map Ut t2 h) -> 
        t1 = t2.
Proof. by case/In_domX=>v1 H1 /In_domX [v2] /(In_side_fun H1) []. Qed.

Lemma dom_sideEX k (h : U) :
        k \in dom (side_map Ut t1 h) -> 
        k \in dom (side_map Ut t2 h) = (t1 == t2).
Proof.
case/In_dom_sideX=>v H; case: (t1 =P t2)=>[?|N].
- by subst t2; apply/In_dom_sideX; exists v. 
by apply/In_dom_sideX; case=>w /(In_fun H) [] /N.
Qed.

Lemma dom_sideN k1 k2 (h : U) :
        k1 \in dom (side_map Ut t1 h) -> 
        k2 \in dom (side_map Ut t2 h) ->
        t1 != t2 -> k1 != k2.
Proof. by move=>D1 D2; apply: contra=>E; rewrite -(dom_sideEX D1) (eqP E). Qed.

End Side2.

(* iterated tagging = when sigT Ts is used as tag *)

Definition sliceT T (Ts : T -> Type) Us t := 
  {x : Ts t & Us (Tag t x)}.
Arguments sliceT {T Ts}.

Section IterTag.
Variables (T : Type) (Ts : T -> Type) (Us : sigT Ts -> Type).

(* tag re-association *)

(* split (i.e., slice) tag in two *)
Definition slice_m : sigT Us -> sigT (sliceT Us) := 
  fun '(Tag (Tag t k) v) => Tag t (Tag k v).
(* conjoin (i.e. gather) first and second tag *)
Definition gather_m : sigT (sliceT Us) -> sigT Us :=
  fun '(Tag t (Tag k v)) => Tag (Tag t k) v.

Variables (K : ordType) (C : pred K).
Variables (U : union_map C (sigT Us)).
Variables (S : union_map C (sigT (sliceT Us))).

Definition slice : U -> S := mapv slice_m.
HB.instance Definition _ := OmapFun.copy slice slice.
Definition gather : S -> U := mapv gather_m.
HB.instance Definition _ := OmapFun.copy gather gather.

Lemma In_slice x t (k : Ts t) (v : Us (Tag t k)) h :
        (x, Tag t (Tag k v)) \In slice h <->
        (x, Tag (Tag t k) v) \In h.
Proof. 
rewrite In_omfX; split=>[|H]; last first.
- by exists (Tag (Tag t k) v).
case; case; case=>t' k' v' H /=.  
case=>?; subst t'=>/inj_pair2 ?; subst k'.
by move/inj_pair2/inj_pair2=><-. 
Qed.

Lemma In_gather x t (k : Ts t) (v : Us (Tag t k)) h :
        (x, Tag (Tag t k) v) \In gather h <->
        (x, Tag t (Tag k v)) \In h.
Proof. 
rewrite In_omfX; split=>[|H]; last first.
- by exists (Tag t (Tag k v)).
case; case=>t' [k' v'] H /=.
case=>?; subst t'=>/inj_pair2 ?; subst k'.
by move/inj_pair2=><-.
Qed.

Lemma gather_slice h : gather (slice h) = h.
Proof.
case: (normalP h)=>[->|V]; first by rewrite !pfundef.
apply: umem_eq=>//; first by rewrite !pfV.
by case=>x [[t k v]]; rewrite In_gather In_slice.
Qed.

Lemma slice_gather h : slice (gather h) = h.
Proof.
case: (normalP h)=>[->|V]; first by rewrite !pfundef.
apply: umem_eq=>//; first by rewrite !pfV.
by case=>x [t][k v]; rewrite In_slice In_gather.
Qed.

End IterTag.

Arguments slice {T Ts Us K C U}.
Arguments gather {T Ts Us K C U}.


(* grafting *)
(* clear side t from h and replace it with ht *)
(* side+graft are for union_maps what sel+splice are for finfuns *)

Section GraftDef.
Variables (K : ordType) (C : pred K) (T : eqType) (Us : T -> Type).
Variables (U : union_map C (sigT Us)).
Variables (Ut : forall t, union_map C (Us t)).
Variables (h : U) (t : T).

Definition graft (ht : Ut t) : U := 
  um_filterv (fun v => t != tag v) h \+ mapv (Tag t) ht.
End GraftDef.

Arguments graft {K C T Us U Ut}.

Section GraftLemmas.
Variables (K : ordType) (C : pred K) (T : eqType) (Us : T -> Type).
Variables (U : union_map C (sigT Us)) (Ut : forall t, union_map C (Us t)).
Implicit Type h : U.

(* ht has disjoint domain with other sides of h *)
Definition disjoint_graft h t (ht : Ut t) := 
  forall tx x, 
    x \in dom (side_map Ut tx h) -> 
    x \in dom ht -> 
    tx = t.

Lemma valid_graft h (t : T) (ht : Ut t) :
        [/\ valid h, valid ht & disjoint_graft h ht] ->
        valid (graft h t ht).
Proof.
case=>Vh V D.
rewrite validUnAE !pfV //=; apply/allP=>x /In_dom_omapX [].
move=>t1 [/In_dom /= H _]; apply/In_dom_umfilt.
case; case=>tx vx /= /eqP /= N.
by move/(In_side Ut)/In_dom/D/(_ H)/esym/N.
Qed.

Lemma valid_graftUn h1 h2 (t : T) (ht : Ut t) : 
        [/\ valid (h1 \+ h2), valid ht,
            disjoint_graft h1 ht & 
            forall x, x \in dom h2 -> x \in dom ht -> false] ->
        valid (graft h1 t ht \+ h2).
Proof.
case=>Vh V D1 D2.
rewrite validUnAE valid_graft ?(validL Vh, validR Vh) //=.
apply/allP=>x D; apply/In_domX; case; case=>tx vx.
case/InUn; first by case/In_umfiltX=>_ /In_dom /(dom_inNLX Vh).
case/In_omapX=>w /In_dom /= H [?]; subst tx=>/inj_pair2 ?; subst w.
by move: (D2 _ D H).
Qed.

(* if ht has disjoint domain with other sides of h *)
(* then side t (graft h t ht) = ht *)
Lemma side_graftE h t (ht : Ut t) :
        valid h -> 
        disjoint_graft h ht ->
        side_map Ut t (graft h t ht) = ht.
Proof.
move=>Vh D; case: (normalP ht)=>[->|V].
- by rewrite /graft pfundef join_undef pfundef.
have W : valid (graft h t ht) by apply: valid_graft.
rewrite /graft pfjoin //=; apply/umem_eq=>//=; first by rewrite pfV2.
case=>k v; split=>[|H].
- case/InUn; first by case/In_side/In_umfiltX; rewrite /= eqxx.
  by case/In_side/In_omapX=>w H [] /inj_pair2 <-.
apply: InR; first by rewrite pfV2.
by apply/In_side/(In_omap _ H). 
Qed.

Lemma side_graftN h (t1 t2 : T) (ht2 : Ut t2) :
        valid ht2 ->
        disjoint_graft h ht2 ->
        t1 != t2 -> 
        side_map Ut t1 (graft h t2 ht2) = side_map Ut t1 h.
Proof.
move=>V D N; case: (normalP h)=>[->|Vh].
- by rewrite /graft pfundef undef_join.
have W : valid (graft h t2 ht2) by apply: valid_graft.
rewrite /graft pfjoin //=; apply/umem_eq=>/=.
- by rewrite pfV2.
- by rewrite pfV.
case=>k v; split.
- case/InUn; first by case/In_side/In_umfiltX=>_ /(In_side Ut).
  case/In_side/In_omapX=>w /In_dom /= H [?]; subst t2.
  by rewrite eqxx in N.
move/In_side=>H; apply/InL; first by rewrite pfV2.
by apply/In_side/In_umfiltX; rewrite /= eq_sym N.
Qed.

End GraftLemmas.


(***********)
(* dom_map *)
(***********)

(* Viewing domain as finite set instead of sequence. *)
(* Because sequences don't have PCM structure, *)
(* dom_maps facilitate proving disjointness of sequences *)
(* by enabling the pcm lemmas. *)

Section DomMap.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map C V) (U' : union_map C unit).

Definition dom_map (x : U) : U' := omap (fun => Some tt) x.

HB.instance Definition _ := OmapFun.copy dom_map dom_map.

Lemma dom_mapE x : dom (dom_map x) = dom x.
Proof. by apply: dom_omf_some. Qed.

(* like pfjoinT but without validity condition *)
Lemma dom_mapUn (x y : U) : 
        dom_map (x \+ y) = dom_map x \+ dom_map y. 
Proof.
case W : (valid (x \+ y)); first exact: pfjoinT.
move/invalidE: (negbT W)=>->; rewrite pfundef.
case: validUn W=>//.
- by move/invalidE=>->; rewrite pfundef undef_join.
- by move/invalidE=>->; rewrite pfundef join_undef.
move=>k D1 D2 _; suff : ~~ valid (dom_map x \+ dom_map y) by move/invalidE=>->.
by case: validUn=>// _ _ /(_ k); rewrite !dom_mapE=>/(_ D1); rewrite D2.
Qed.

Lemma domeq_dom_mapL x : dom_eq (dom_map x) x.
Proof. by rewrite /dom_eq pfVE dom_mapE !eq_refl. Qed.

Lemma domeq_dom_mapR x : dom_eq x (dom_map x).
Proof. by apply: domeq_sym; apply: domeq_dom_mapL. Qed.

End DomMap.

Arguments dom_map [K C V U U'] _.

(* composing dom_map *)

Section DomMapIdempotent.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Variables (U' : union_map C unit) (U'' : union_map C unit).

Lemma dom_map_idemp (x : U) : dom_map (dom_map x : U') = dom_map x :> U''.
Proof. by rewrite /dom_map omap_omap. Qed.

End DomMapIdempotent.


(*****************)
(* Map inversion *)
(*****************)

Section MapInvert.
Variables (K V : ordType) (C : pred K) (C' : pred V).
Variables (U : union_map C V) (U' : union_map C' K).

(* inverting f = flipping each pts k v in f into pts v k *)
Definition invert (f : U) : U' :=
  um_foldl (fun r k v => r \+ pts v k) Unit undef f.

(* invert isn't morphism as pfV doesn't hold *)
(* but invert has several morphism properties *)

Lemma invert_undef : invert undef = undef.
Proof. by rewrite /invert umfoldl_undef. Qed.

Lemma invert0 : invert Unit = Unit.
Proof. by rewrite /invert umfoldl0. Qed.

Lemma invertUn f1 f2 :
        valid (f1 \+ f2) -> 
        invert (f1 \+ f2) = invert f1 \+ invert f2.
Proof.
move=>W; rewrite /invert umfoldlUn_frame ?unitR //.
by move=>*; rewrite joinAC.
Qed.

Lemma invertPt k v : C k -> invert (pts k v) = pts v k.
Proof. by move=>H; rewrite /invert umfoldlPt unitL H. Qed.

Lemma invertPtUn k v f :
        valid (pts k v \+ f) ->
        invert (pts k v \+ f) = pts v k \+ invert f.
Proof. by move=>W; rewrite invertUn // invertPt // (validPtUn_cond W). Qed.

Lemma dom_invert f : valid (invert f) -> dom (invert f) =i range f.
Proof.
rewrite /invert/um_foldl/range; case: ifP=>_; last by rewrite valid_undef.
elim: (assocs f)=>[|x g IH] /= W k; first by rewrite dom0.
rewrite foldl_init in W *; last by move=>*; rewrite joinAC.
by rewrite domUnPt !inE W /= eq_sym IH // (validL W).
Qed.

Lemma valid_invert f :
        valid (invert f) =
        [&& valid f, uniq (range f) & all C' (range f)].
Proof.
elim/um_indf: f=>[||k v f IH W /(order_path_min (@trans K)) P].
- by rewrite invert_undef !valid_undef.
- by rewrite invert0 !valid_unit range0.
rewrite invertPtUn W //= rangePtUnK // validPtUn /=.
rewrite IH (validR W) /=; bool_congr; rewrite andbC -!andbA.
rewrite andbC [in X in _ = X]andbC.
case X1 : (uniq (range f)) IH=>//=.
case X2 : (all C' (range f))=>//=.
by rewrite (validR W)=>/dom_invert ->.
Qed.

(* The next few lemmas that depend on valid (invert f) *)
(* can be strenghtened to require just uniq (range f) and *)
(* all C' (range f). *)
(* However, the formulation with the hypothesis valid (invert f) *)
(* is packaged somewhat better, and is what's encountered in practice. *)

Lemma range_invert f :
         valid (invert f : U') -> 
         range (invert f) =i dom f.
Proof.
elim/um_indf: f=>[||k v f IH W P].
- by rewrite invert_undef valid_undef.
- by rewrite invert0 range0 dom0.
rewrite invertPtUn // => W' x.
rewrite rangePtUn inE W' domPtUn inE W /=.
by case: eqP=>//= _; rewrite IH // (validR W').
Qed.

Lemma In_invert k v f :
        valid (invert f) -> 
        (k, v) \In f <-> (v, k) \In invert f.
Proof.
elim/um_indf: f k v=>[||x w f IH W /(order_path_min (@trans K)) P] k v.
- by rewrite invert_undef valid_undef.
- by rewrite invert0; split=>/In0.
move=>W'; rewrite invertPtUn // !InPtUnE //; last by rewrite -invertPtUn.
rewrite IH; first by split; case=>[[->->]|]; auto.
rewrite !valid_invert rangePtUnK // (validR W) in W' *.
by case/and3P: W'=>_ /= /andP [_ ->] /andP [_ ->].
Qed.

Lemma uniq_range_invert f : uniq (range (invert f)).
Proof.
case: (normalP (invert f))=>[->|W]; first by rewrite range_undef.
rewrite /range map_inj_in_uniq.
- by apply: (@map_uniq _ _ fst); rewrite -assocs_dom; apply: uniq_dom.
case=>x1 x2 [y1 y] /= H1 H2 E; rewrite {x2}E in H1 *.
move/mem_seqP/In_assocs/(In_invert _ _ W): H1=>H1.
move/mem_seqP/In_assocs/(In_invert _ _ W): H2=>H2.
by rewrite (In_fun H1 H2).
Qed.

Lemma all_range_invert f : all C (range (invert f)).
Proof.
apply: (@sub_all _ (fun k => k \in dom f)); first by move=>x /dom_cond.
by apply/allP=>x H; rewrite -range_invert //; apply: range_valid H.
Qed.

Lemma sorted_range_invert f :
        valid (invert f) ->
        sorted ord (range f) -> 
        sorted ord (range (invert f)).
Proof.
move=>W /ummonoP X; apply/ummonoP=>v v' k k'.
move/(In_invert _ _ W)=>H1 /(In_invert _ _ W) H2.
apply: contraTT; case: ordP=>//= E _; first by case: ordP (X _ _ _ _ H2 H1 E).
by move/eqP: E H2=>-> /(In_fun H1) ->; rewrite irr.
Qed.

End MapInvert.

Arguments invert {K V C C' U U'}.


Section InvertLaws.
Variables (K V : ordType) (C : pred K) (C' : pred V).
Variables (U : union_map C V) (U' : union_map C' K).

Lemma valid_invert_idemp (f : U) :
        valid (invert (invert f : U') : U) = valid (invert f : U').
Proof. by rewrite valid_invert uniq_range_invert all_range_invert !andbT. Qed.

Lemma invert_idemp (f : U) : 
        valid (invert f : U') -> 
        invert (invert f : U') = f.
Proof.
move=>W; apply/umem_eq.
- by rewrite valid_invert_idemp.
- by move: W; rewrite valid_invert; case/and3P.
move=>x; split=>H.
- by apply/(In_invert _ _ W); apply/(@In_invert _ _ _ _ _ U) =>//; case: H.
case: x H=>k v /(In_invert _ _ W)/In_invert; apply.
by rewrite valid_invert_idemp.
Qed.

End InvertLaws.

Arguments In_invert {K V C C' U U' k v f}.


(***************************)
(* Composition of two maps *)
(***************************)

(* composing maps as functions, rather than PCMs *)

Section MapComposition.
Variables (K1 K2 : ordType) (C1 : pred K1) (C2 : pred K2) (V : Type).
Variables (Uf : union_map C1 K2) (Ug : union_map C2 V) (U : union_map C1 V).
Implicit Types (f : Uf) (g : Ug).

Definition um_comp g f : U :=
  um_foldl (fun r k v => if find v g is Some w
                         then pts k w \+ r else r) Unit undef f.

Lemma umcomp_undeff f : valid f -> um_comp undef f = Unit.
Proof.
move=>W; apply: (umfoldl_ind (P:=fun r => r = Unit))=>//.
by move=>*; rewrite find_undef.
Qed.
Lemma umcomp_fundef g : um_comp g undef = undef.
Proof. by rewrite /um_comp umfoldl_undef. Qed.

Lemma umcomp0f f : valid f -> um_comp Unit f = Unit.
Proof.
move=>W; apply: (umfoldl_ind (P:=fun r => r = Unit))=>//.
by move=>*; rewrite find0E.
Qed.

Lemma umcompf0 g : um_comp g Unit = Unit.
Proof. by rewrite /um_comp umfoldl0. Qed.

Lemma umcomp_subdom g f : {subset dom (um_comp g f) <= dom f}.
Proof.
rewrite /um_comp; elim/um_indf: f=>[||k v f IH W P] x.
- by rewrite umfoldl_undef dom_undef.
- by rewrite umfoldl0 dom0.
rewrite umfoldlUn_frame //;
last by move=>*; case: (find _ _)=>// a; rewrite joinA.
rewrite unitR umfoldlPt (validPtUn_cond W).
case E : (find v g)=>[b|]; last first.
- by rewrite unitL=>/IH; rewrite domPtUn inE W =>->; rewrite orbT.
rewrite unitR domPtUn inE; case/andP=>_ /orP [/eqP <-|/IH].
- by rewrite domPtUn inE W eq_refl.
by rewrite domPtUn inE W=>->; rewrite orbT.
Qed.

Lemma valid_umcomp g f : valid (um_comp g f) = valid f.
Proof.
rewrite /um_comp; elim/um_indf: f=>[||k v f IH W P].
- by rewrite umfoldl_undef !valid_undef.
- by rewrite umfoldl0 !valid_unit.
rewrite umfoldlUn_frame //;
  last by move=>*; case: (find _ _)=>// a; rewrite joinA.
rewrite unitR W umfoldlPt (validPtUn_cond W).
case: (find v g)=>[a|]; last by rewrite unitL IH (validR W).
rewrite unitR validPtUn (validPtUn_cond W) IH (validR W).
by apply: contra (notin_path P); apply: umcomp_subdom.
Qed.

Lemma umcompUnf g1 g2 f :
        valid (g1 \+ g2) -> 
        um_comp (g1 \+ g2) f = um_comp g1 f \+ um_comp g2 f.
Proof.
rewrite /um_comp=>Wg; elim/um_indf: f=>[||k v f IH P W].
- by rewrite !umfoldl_undef undef_join.
- by rewrite !umfoldl0 unitL.
rewrite !umfoldlUn_frame //;
try by move=>*; case: (find _ _)=>// a; rewrite joinA.
rewrite !unitR !umfoldlPt; case: ifP=>C; last by rewrite !undef_join.
rewrite {}IH joinAC [in X in _ = X]joinA [in X in _ = X]joinAC;
rewrite -[in X in _ = X]joinA; congr (_ \+ _).
case: validUn (Wg)=>// W1 W2 X _; rewrite findUnL //.
by case: ifP=>[/X|]; case: dom_find=>//; rewrite ?unitL ?unitR.
Qed.

Lemma umcompfUn g f1 f2 :
        valid (f1 \+ f2) -> 
        um_comp g (f1 \+ f2) = um_comp g f1 \+ um_comp g f2.
Proof.
rewrite /um_comp=>W; rewrite umfoldlUn_frame ?unitR //.
by move=>*; case: (find _ _)=>// a; rewrite joinA.
Qed.

Lemma umcompfPtE g k v :
        um_comp g (pts k v) =
        if C1 k then
          if find v g is Some w then pts k w else Unit
        else undef.
Proof.
rewrite /um_comp umfoldlPt; case: ifP=>C //.
by case: (find _ _)=>// a; rewrite unitR.
Qed.

Lemma umcompfPt g k v :
        C1 k ->
        um_comp g (pts k v) =
        if find v g is Some w then pts k w else Unit.
Proof. by move=>H; rewrite umcompfPtE H. Qed.

Lemma umcompfPtUn g f k v :
        valid (pts k v \+ f) ->
        um_comp g (pts k v \+ f) =
        if find v g is Some w then pts k w \+ um_comp g f
        else um_comp g f.
Proof.
move=>W; rewrite umcompfUn // umcompfPtE (validPtUn_cond W).
by case: (find _ _)=>[a|] //; rewrite unitL.
Qed.

Lemma umcompPtf f k v :
        um_comp (pts k v) f =
        if C2 k then
          omap (fun x => if x.2 == k then Some v else None) f
        else if valid f then Unit else undef.
Proof.
elim/um_indf: f=>[||x w f IH W P].
- rewrite umcomp_fundef omap_undef.
  by case: ifP=>//; rewrite valid_undef.
- rewrite umcompf0 pfunit.
  by case: ifP=>//; rewrite valid_unit.
rewrite umcompfUn // umcompfPtE (validPtUn_cond W) omapPtUn.
rewrite W findPt2 andbC.
case C: (C2 k) IH=>/= IH; last by rewrite IH (validR W) unitL.
by case: eqP=>_; rewrite IH // unitL.
Qed.

Lemma umcompPtUnf g f k v :
        valid (pts k v \+ g) ->
        um_comp (pts k v \+ g) f =
        omap (fun x => if x.2 == k then Some v else None) f \+ um_comp g f.
Proof.
by move=>W; rewrite umcompUnf // umcompPtf (validPtUn_cond W).
Qed.

Lemma In_umcomp g f k v :
        (k, v) \In um_comp g f <->
        valid (um_comp g f) /\ exists k', (k, k') \In f /\ (k', v) \In g.
Proof.
split=>[H|[W][k'][]].
- split; first by case: H.
  elim/um_indf: f H=>[||x w f IH P W].
  - by rewrite umcomp_fundef=>/In_undef.
  - by rewrite umcompf0=>/In0.
  rewrite /um_comp umfoldlUn_frame //;
  last by move=>*; case: (find _ _)=>// a; rewrite joinA.
  rewrite unitR !umfoldlPt; case: ifP=>C; last first.
  - by rewrite undef_join=>/In_undef.
  case/InUn; last by case/IH=>k' [H1 H2]; exists k'; split=>//; apply/InR.
  case E: (find _ _)=>[b|]; last by move/In0.
  rewrite unitR=>/InPt; case; case=>?? _; subst x b.
  by exists w; split=>//; apply/In_find.
elim/um_indf: f W k'=>[||x w f IH P W] W' k'.
- by move/In_undef.
- by move/In0.
rewrite umcompfPtUn // in W'; rewrite InPtUnE //.
case=>[[??] G|H1 H2].
- subst x w; rewrite umcompfPtUn //.
  by move/In_find: (G)=>E; rewrite E in W' *; apply/InPtUnL.
rewrite umcompfPtUn //.
case E: (find _ _) W'=>[b|] W'; last by apply: IH H1 H2.
by apply/InR=>//; apply:IH H1 H2; rewrite (validR W').
Qed.

End MapComposition.


(**********)
(* um_all *)
(**********)

Section AllDefLemmas.
Variables (K : ordType) (C : pred K) (V : Type).
Variables (U : union_map C V) (P : K -> V -> Prop).
Implicit Types (k : K) (v : V) (f : U).

Definition um_all f := forall k v, (k, v) \In f -> P k v.

Lemma umall_undef : um_all undef.
Proof. by move=>k v /In_undef. Qed.

Lemma umall0 : um_all Unit.
Proof. by move=>k v /In0. Qed.

Hint Resolve umall_undef umall0 : core.

Lemma umallUn f1 f2 : 
        um_all f1 -> 
        um_all f2 -> 
        um_all (f1 \+ f2).
Proof. by move=>X Y k v /InUn [/X|/Y]. Qed.

Lemma umallUnL f1 f2 : 
        valid (f1 \+ f2) -> 
        um_all (f1 \+ f2) -> 
        um_all f1.
Proof. by move=>W H k v F; apply: H; apply/InL. Qed.

Lemma umallUnR f1 f2 : 
        valid (f1 \+ f2) -> 
        um_all (f1 \+ f2) -> 
        um_all f2.
Proof. by rewrite joinC; apply: umallUnL. Qed.

Lemma umallPt k v : P k v -> um_all (pts k v).
Proof. by move=>X k1 v1 /InPt [[->->]]. Qed.

Lemma umallPtUn k v f : P k v -> um_all f -> um_all (pts k v \+ f).
Proof. by move/(umallPt (k:=k)); apply: umallUn. Qed.

Lemma umallUnPt k v f : P k v -> um_all f -> um_all (f \+ pts k v).
Proof. by rewrite joinC; apply: umallPtUn. Qed.

Lemma umallPtE k v : C k -> um_all (pts k v) -> P k v.
Proof. by move/(In_condPt v)=>C'; apply. Qed.

Lemma umallPtUnE k v f :
        valid (pts k v \+ f) -> 
        um_all (pts k v \+ f) -> 
        P k v /\ um_all f.
Proof.
move=>W H; move: (umallUnL W H) (umallUnR W H)=>{H} H1 H2.
by split=>//; apply: umallPtE H1; apply: validPtUn_cond W.
Qed.

End AllDefLemmas.

#[export]
Hint Resolve umall_undef umall0 : core.


(***********)
(* um_allb *)
(***********)

(* decidable um_all *)

Section MapAllDecidable.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Implicit Types (f : U) (p : pred (K*V)). 

Definition um_allb p f := um_count p f == size (dom f).

Lemma umallbP p f : reflect (forall x, x \In f -> p x) (um_allb p f). 
Proof.
apply/(equivP idP); split=>[/eqP | H].
- by rewrite umcnt_memT=>H [k v]; apply: H.
by apply/eqP; rewrite umcnt_memT=>k v; apply: H.
Qed.

Lemma umallb_is_pcm_morph p : pcm_morph_axiom relT (um_allb p).
Proof.
rewrite /um_allb; split=>[|x y W _]; first by rewrite umcnt0 dom0.
split=>//; apply/idP/idP.
- by move/umallbP=>H; apply/andP; split; apply/umallbP=>k X;
  apply: H; [apply: InL | apply: InR].
case/andP=>/umallbP X1 /umallbP X2; apply/umallbP=>k.
by case/InUn; [apply: X1 | apply: X2].
Qed.

HB.instance Definition _ p := 
  isPCM_morphism.Build U bool (um_allb p) (umallb_is_pcm_morph p).
HB.instance Definition _ p := 
  isFull_PCM_morphism.Build U bool (um_allb p) (fun x y => erefl).

Lemma umallb0 p : um_allb p Unit.
Proof. exact: pfunit. Qed.

Lemma umallbUn p f1 f2 :
        valid (f1 \+ f2) -> 
        um_allb p (f1 \+ f2) = um_allb p f1 && um_allb p f2.
Proof. exact: pfjoinT. Qed.

(* bool isn't tpcm, so we can't declare umallb tpcm morphism *)
(* however, we can prove some properties about under *)

Lemma umallb_undef p : um_allb p undef.
Proof. by rewrite /um_allb umcnt_undef dom_undef. Qed.

Lemma umallbPt p k v : C k -> um_allb p (pts k v) = p (k, v).
Proof. by move=>C'; rewrite /um_allb umcntPt domPtK C' /=; case: (p (k, v)). Qed.

Lemma umallbPtUn p k v f :
        valid (pts k v \+ f) ->
        um_allb p (pts k v \+ f) = p (k, v) && um_allb p f.
Proof. by move=>W; rewrite umallbUn // umallbPt // (validPtUn_cond W). Qed.

Lemma umallbU p k v f :
        valid (upd k v f) ->
        um_allb p (upd k v f) = p (k, v) && um_allb p (free f k).
Proof.
rewrite validU=>/andP [W1 W2]; rewrite upd_eta // umallbPtUn //.
by rewrite validPtUn W1 validF W2 domF inE eq_refl.
Qed.

Lemma umallbF p k f : um_allb p f -> um_allb p (free f k).
Proof. by move/umallbP=>H; apply/umallbP=>kv /InF [_ _ /H]. Qed.

End MapAllDecidable.


(************************************)
(* Zipping a relation over two maps *)
(************************************)

(* Binary version of um_all, where comparison is done over *)
(* values of equal keys in both maps. *)

Section BinaryMapAll.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map C V).
Variables (P : V -> V -> Prop).
Implicit Types (k : K) (v : V) (f : U).

Definition um_all2 (f1 f2 : U) := 
  forall k, optionR P (find k f1) (find k f2).

Lemma umall2_refl f : Reflexive P -> um_all2 f f.
Proof. by move=>R k; apply: Reflexive_optionR. Qed.

Lemma umall2_sym : Symmetric P -> Symmetric um_all2.
Proof. by move=>S x y; split=>H k; apply/Symmetric_optionR. Qed.

Lemma umall2_trans : Transitive P -> Transitive um_all2.
Proof. by move=>T x y z H1 H2 k; apply: Transitive_optionR (H1 k) (H2 k). Qed.

Lemma umall2_eq : Equivalence_rel P -> Equivalence_rel um_all2.
Proof.
case/Equivalence_relS=>R S T; apply/Equivalence_relS; split.
- by move=>f; apply: umall2_refl.
- by apply: umall2_sym.
by apply: umall2_trans.
Qed.

Lemma umall20 : um_all2 Unit Unit.
Proof. by move=>k; rewrite /optionR /= find0E. Qed.

Lemma umall2_undef : um_all2 undef undef.
Proof. by move=>k; rewrite /optionR /= find_undef. Qed.

Lemma umall2_dom f1 f2 : um_all2 f1 f2 -> dom f1 = dom f2.
Proof.
move=>H; apply/domE=>k; apply/idP/idP;
move: (H k); rewrite /optionR /=;
by case: dom_find =>// v _; case: dom_find=>//.
Qed.

Lemma umall2_umfilt f1 f2 p :
        (forall k v1 v2,
           (k, v1) \In f1 -> (k, v2) \In f2 -> P v1 v2 ->
           p (k, v1) = p (k, v2)) ->
        um_all2 f1 f2 -> um_all2 (um_filter p f1) (um_filter p f2).
Proof.
move=>E H k; move: (H k); rewrite /optionR /= !find_umfilt.
case E1: (find k f1)=>[v1|]; case E2: (find k f2)=>[v2|] // X.
move/In_find: E1=>E1; move/In_find: E2=>E2.
by rewrite -(E k v1 v2 E1 E2) //; case: ifP.
Qed.

Lemma umall2_umfilt_inv f1 f2 p :
        um_all2 (um_filter p f1) (um_filter p f2) ->
        forall k, 
          match find k f1 , find k f2 with
            Some v1 , Some v2 => p (k, v1) && p (k, v2) -> P v1 v2
          | Some v1 , None => ~~ p (k, v1)
          | None , Some v2 => ~~ p (k, v2)
          | None , None => True
         end.
Proof.
move=>H k; move: (H k); rewrite !find_umfilt.
case: (find k f1)=>[a1|]; case: (find k f2)=>[a2|] //.
- by case: ifP; case: ifP.
- by case: ifP.
by case: ifP.
Qed.

Lemma umall2_umfilt_ord f1 f2 t :
        um_all2 (um_filter (fun kv => ord kv.1 t) f1)
                (um_filter (fun kv => ord kv.1 t) f2) <->
        forall k, ord k t -> optionR P (find k f1) (find k f2).
Proof.
split=>[H k X|H k]; last first.
- move: (H k); rewrite !find_umfilt.
  case: (find k f1)=>[a1|]; case: (find k f2)=>[a2|] //=;
  by case: ifP=>// X; apply.
move/umall2_umfilt_inv/(_ k): H=>/=.
case: (find k f1)=>[v1|]; case: (find k f2)=>[v2|] //=.
- by rewrite X; apply.
- by rewrite X.
by rewrite X.
Qed.

Lemma umall2_umfilt_oleq f1 f2 t :
        um_all2 (um_filter (fun kv => oleq kv.1 t) f1)
                (um_filter (fun kv => oleq kv.1 t) f2) <->
        forall k, oleq k t -> optionR P (find k f1) (find k f2).
Proof.
split=>[H k X|H k]; last first.
- move: (H k); rewrite !find_umfilt.
  case: (find k f1)=>[a1|]; case: (find k f2)=>[a2|] //=;
  by case: ifP=>// X; apply.
move/umall2_umfilt_inv/(_ k): H=>/=.
case: (find k f1)=>[v1|]; case: (find k f2)=>[v2|] //=.
- by rewrite X; apply.
- by rewrite X.
by rewrite X.
Qed.

Lemma umall2_umcnt f1 f2 p :
        (forall k v1 v2,
           (k, v1) \In f1 -> (k, v2) \In f2 -> P v1 v2 ->
           p (k, v1) = p (k, v2)) ->
        um_all2 f1 f2 -> um_count p f1 = um_count p f2.
Proof. by move=>*; congr size; apply: umall2_dom; apply: umall2_umfilt. Qed.

Lemma umall2_find X f1 f2 (f : option V -> X) t :
        (forall k v1 v2,
           (k, v1) \In f1 -> (k, v2) \In f2 -> P v1 v2 ->
           f (Some v1) = f (Some v2)) ->
        um_all2 f1 f2 -> f (find t f1) = f (find t f2).
Proof.
move=>E /(_ t).
case E1: (find t f1)=>[v1|]; case E2: (find t f2)=>[v2|] //=.
by move/In_find: E1=>E1; move/In_find: E2=>E2; apply: E E1 E2.
Qed.

Lemma umall2fUn f f1 f2 :
        Reflexive P ->
        valid f1 = valid f2 -> um_all2 f1 f2 -> um_all2 (f \+ f1) (f \+ f2).
Proof.
move=>R Ev X; have De : dom_eq f1 f2.
- by apply/domeqP; rewrite (umall2_dom X) Ev.
move=>k; case V1 : (valid (f \+ f1)) (domeqVUnE (domeq_refl f) De)=>/esym V2;
last first.
- by move/negbT/invalidE: V1 V2=>-> /negbT/invalidE ->; rewrite find_undef.
rewrite /optionR /= !findUnL //; case: ifP=>D; last by apply: X.
by case/In_domX: D=>v /In_find ->; apply: R.
Qed.

Lemma umall2Unf f f1 f2 :
        Reflexive P ->
        valid f1 = valid f2 -> um_all2 f1 f2 -> um_all2 (f1 \+ f) (f2 \+ f).
Proof. by rewrite -!(joinC f); apply: umall2fUn. Qed.

Lemma umall2Un f1 f2 g1 g2 :
        Reflexive P -> Transitive P ->
        valid f1 = valid f2 -> valid g1 = valid g2 ->
        um_all2 f1 f2 -> um_all2 g1 g2 ->
        um_all2 (f1 \+ g1) (f2 \+ g2).
Proof.
move=>R T Ef Eg Uf Ug; apply: (@umall2_trans T (f2 \+ g1));
by [apply: umall2Unf | apply: umall2fUn].
Qed.

Lemma umall2Pt2 k1 k2 v1 v2 :
        um_all2 (pts k1 v1) (pts k2 v2) <->
        if k1 == k2 then C k1 -> P v1 v2
        else ~~ C k1 && ~~ C k2.
Proof.
split; last first.
- case: eqP=>[-> H|N /andP [C1 C2]] k.
  - by rewrite /optionR /= !findPt2; case: ifP=>// /andP [].
  by rewrite /optionR /= !findPt2 (negbTE C1) (negbTE C2) !andbF.
move=>X; move: (X k1) (X k2).
rewrite /optionR !findPt !findPt2 (eq_sym k2 k1) /=.
case: (k1 =P k2)=>[<-|N] /=; first by case: ifP.
by do 2![case: ifP].
Qed.

Lemma umall2Pt k v1 v2 :
        C k ->
        um_all2 (pts k v1) (pts k v2) <-> P v1 v2.
Proof. by move=>C'; rewrite umall2Pt2 eq_refl; split=>//; apply. Qed.

Lemma umall2cancel k v1 v2 f1 f2 :
        valid (pts k v1 \+ f1) -> valid (pts k v2 \+ f2) ->
        um_all2 (pts k v1 \+ f1) (pts k v2 \+ f2) ->
        P v1 v2 /\ um_all2 f1 f2.
Proof.
move=>V1 V2 X; split=>[|x]; first by move: (X k); rewrite !findPtUn.
move: (X x); rewrite !findPtUn2 //; case: ifP=>// /eqP -> _.
by case: dom_find (validPtUnD V1)=>//; case: dom_find (validPtUnD V2).
Qed.

Lemma umall2PtUn k v1 v2 f1 f2 :
        Reflexive P -> Transitive P ->
        valid f1 = valid f2 -> um_all2 f1 f2 ->
        P v1 v2 ->
        um_all2 (pts k v1 \+ f1) (pts k v2 \+ f2).
Proof.
move=>R T; case W : (valid (pts k v1 \+ f1)).
- move=>H1 H2 H3; apply: umall2Un=>//.
  - by rewrite !validPt (validPtUn_cond W).
  by apply/(@umall2Pt _ _ _ (validPtUn_cond W)).
case: validUn W=>//.
- rewrite validPt=>H _ _ _ _.
  have L v : pts k v = undef :> U by apply/pts_undef.
  by rewrite !L !undef_join; apply: umall2_undef.
- move=>W _; rewrite (negbTE W)=>/esym.
  move/invalidE: W=>-> /negbT/invalidE -> _ _; rewrite !join_undef.
  by apply: umall2_undef.
move=>x; rewrite domPt inE=>/andP [X /eqP <- D1] _ W /umall2_dom E _.
suff : ~~ valid (pts k v1 \+ f1) /\ ~~ valid (pts k v2 \+ f2).
- by case=>/invalidE -> /invalidE ->; apply: umall2_undef.
by rewrite !validPtUn X -W -E D1 (dom_valid D1).
Qed.

Lemma umall2fK f f1 f2 :
        valid (f \+ f1) -> valid (f \+ f2) ->
        um_all2 (f \+ f1) (f \+ f2) -> um_all2 f1 f2.
Proof.
move=>V1 V2 X k; move: (X k); rewrite !findUnL //; case: ifP=>// D _.
by case: dom_find (dom_inNL V1 D)=>//; case: dom_find (dom_inNL V2 D)=>//.
Qed.

Lemma umall2KL f1 f2 g1 g2 :
        Equivalence_rel P ->
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        um_all2 (f1 \+ g1) (f2 \+ g2) ->
        um_all2 f1 f2 -> um_all2 g1 g2.
Proof.
move=>E; case/Equivalence_relS: E=>R S T.
move=>V1 V2 H1 Ha; have /(umall2_sym S) H2: um_all2 (f1 \+ g1) (f2 \+ g1).
- by apply: umall2Unf Ha=>//; rewrite (validL V1) (validL V2).
apply: umall2fK (V2) _; last first.
- by apply: umall2_trans H2 H1.
apply: domeqVUn (V1)=>//; apply/domeqP.
by rewrite (validL V1) (validL V2) (umall2_dom Ha).
Qed.

Lemma umall2KR f1 f2 g1 g2 :
        Equivalence_rel P ->
        valid (f1 \+ g1) -> valid (f2 \+ g2) ->
        um_all2 (f1 \+ g1) (f2 \+ g2) ->
        um_all2 g1 g2 -> um_all2 f1 f2.
Proof. by rewrite (joinC f1) (joinC f2); apply: umall2KL. Qed.

End BinaryMapAll.

(* big join and union maps *)

Section BigOpsUM.
Variables (K : ordType) (C : pred K) (T : Type).
Variables (U : union_map C T).
Variables (I : Type) (f : I -> U).

Lemma big_domUn (xs : seq I) :
        dom (\big[join/Unit]_(i <- xs) f i) =i
        [pred x | valid (\big[join/Unit]_(i <- xs) f i) &
                  has (fun i => x \in dom (f i)) xs].
Proof.
elim: xs=>[|x xs IH] i; first by rewrite big_nil inE /= dom0 valid_unit.
rewrite big_cons /= inE domUn inE IH inE /=.
by case V : (valid _)=>//=; rewrite (validR V) /=.
Qed.

Lemma big_domUnE (xs : seq I) a :
        valid (\big[join/Unit]_(i <- xs) f i) ->
        a \in dom (\big[join/Unit]_(i <- xs) f i) =
        has (fun i => a \in dom (f i)) xs.
Proof. by move=>V; rewrite big_domUn inE V. Qed.

(* we can construct a big validity, if we know that *)
(* the list contains unique elements *)
Lemma big_validV2I (xs : seq I) :
        Uniq xs ->
        (forall i, i \In xs -> valid (f i)) ->
        (forall i j, i \In xs -> j \In xs -> i <> j -> valid (f i \+ f j)) ->
        valid (\big[join/Unit]_(i <- xs) f i).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite big_nil valid_unit.
case=>X Uq H1 H2; rewrite big_cons validUnAE.
rewrite H1 /=; last by rewrite InE; left.
rewrite IH //=; last first.
- by move=>i j Xi Xj; apply: H2; rewrite InE; right.
- by move=>i Xi; apply: H1; rewrite InE; right.
apply/allP=>a /=; apply: contraL=>Dx; apply/negP.
rewrite big_domUn inE=>/andP [V] /hasPIn [y Y Dy].
have : x <> y by move=>N; rewrite N in X; move/X: Y.
move/(H2 x y (or_introl erefl) (or_intror Y)).
by case: validUn=>// _ _ /(_ a Dx); rewrite Dy.
Qed.

Lemma big_size_dom (xs : seq I) :
       valid (\big[join/Unit]_(i <- xs) f i) ->
       size (dom (\big[join/Unit]_(i <- xs) f i)) =
         \sum_(i <- xs) (size (dom (f i))).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite !big_nil dom0.
rewrite !big_cons=>V; rewrite size_domUn //; congr (size _ + _).
by apply/IH/(validR V).
Qed.

Lemma big_find_some (xs : seq I) a i v :
        valid (\big[join/Unit]_(i <- xs) f i) ->
        i \In xs ->
        find a (f i) = some v ->
        find a (\big[join/Unit]_(i <- xs) f i) = some v.
Proof.
elim: xs=>[|x xs IH /[swap]] //; rewrite big_cons InE.
case=>[<-{x}|Xi] V E; first by rewrite findUnL // (find_some E).
rewrite findUnR // big_domUnE ?(validR V) //=.
rewrite ifT; first by apply: IH (validR V) Xi E.
by apply/hasPIn; exists i=>//; apply: find_some E.
Qed.

Lemma big_find_someD (xs : seq I) a i v :
        i \In xs ->
        a \in dom (f i) ->
        find a (\big[join/Unit]_(x <- xs) f x) = Some v ->
        find a (f i) = Some v.
Proof.
elim: xs v=>[|y xs IH] v //=; rewrite big_cons InE.
case=>[->|Xi] Da /[dup]/In_find/In_valid V; first by rewrite findUnL // Da.
rewrite findUnR // big_domUnE ?(validR V) //=.
by rewrite ifT; [apply: IH | apply/hasPIn; exists i].
Qed.

Lemma big_find_someX (xs : seq I) a v :
        find a (\big[join/Unit]_(i <- xs) f i) = Some v ->
        exists2 i, i \In xs & find a (f i) = Some v.
Proof.
elim: xs=>[|x xs IH]; first by rewrite big_nil find0E.
move/[dup]=>E1; rewrite big_cons=>/[dup] E /find_some.
rewrite domUn inE=>/andP [V] /orP [] D; last first.
- move: E; rewrite findUnR // D=>/IH [j Dj Xj].
  by exists j=>//; rewrite InE; right.
case/In_domX: D=>w /In_find /[dup] X.
move/(big_find_some (dom_valid (find_some E1)) (or_introl erefl)).
by rewrite E1; case=>->; exists x=>//; rewrite InE; left.
Qed.

Lemma big_find_someXP (xs : seq I) P a v :
        find a (\big[join/Unit]_(i <- xs | P i) f i) = Some v ->
        exists i, [/\ i \In xs, P i & find a (f i) = Some v].
Proof.
by rewrite -big_filter=>/big_find_someX [i] /Mem_filter [H1 H2 H3]; exists i.
Qed.

Lemma bigIn (xs : seq I) a i v :
        valid (\big[join/Unit]_(i <- xs) f i) ->
        i \In xs ->
        (a, v) \In f i ->
        (a, v) \In \big[join/Unit]_(i <- xs) f i.
Proof. by move=>V H /In_find/(big_find_some V H)/In_find. Qed.

Lemma bigInD (xs : seq I) a x v :
        x \In xs ->
        a \in dom (f x) ->
        (a, v) \In \big[join/Unit]_(i <- xs) f i ->
        (a, v) \In f x.
Proof. by move=>X D /In_find/(big_find_someD X D)/In_find. Qed.

Lemma bigInX (xs : seq I) a v :
        (a, v) \In \big[join/Unit]_(i <- xs) f i ->
        exists2 i, i \In xs & (a, v) \In f i.
Proof. by case/In_find/big_find_someX=>x X /In_find; exists x. Qed.

Lemma bigInXP (xs : seq I) P a v :
        (a, v) \In \big[join/Unit]_(i <- xs | P i) f i ->
        exists i, [/\ i \In xs, P i & (a, v) \In f i].
Proof. by case/In_find/big_find_someXP=>x [X1 X2 /In_find]; exists x. Qed.

End BigOpsUM.

Prenex Implicits big_find_some big_find_someD.
Prenex Implicits big_find_someX big_find_someXP bigIn bigInD bigInX bigInXP.

(* if the index type is eqtype, we can have a somewhat better *)
(* big validity lemma *)

Section BigOpsUMEq.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Variables (I : eqType) (f : I -> U).

Lemma big_validP (xs : seq I) :
        reflect
        [/\ forall i, i \in xs -> valid (f i),
            forall i k, i \in xs -> k \in dom (f i) -> count_mem i xs = 1 &
            forall i j, i \in xs -> j \in xs -> i <> j -> valid (f i \+ f j)]
        (valid (\big[join/Unit]_(i <- xs) f i)).
Proof.
elim: xs=>[|x xs IH] /=; first by rewrite big_nil valid_unit; constructor.
rewrite big_cons validUnAE.
case H1 : (valid (f x))=>/=; last first.
- by constructor; case=>/(_ x); rewrite inE eqxx H1=>/(_ erefl).
rewrite andbC; case: allP=>/= H2; last first.
- constructor; case=>H3 H4 H5; apply: H2=>k; rewrite big_domUn inE.
  case/andP=>V /hasP [y]; case : (x =P y)=>[<- /[swap]|N X D].
  - by move/(H4 x); rewrite inE eqxx add1n=>/(_ erefl) []/count_memPn/negbTE ->.
  by apply: dom_inNR (H5 _ _ _ _ N) D; rewrite inE ?eqxx ?X ?orbT.
case: {2 3}(valid _) / IH (erefl (valid (\big[join/Unit]_(j <- xs) f j)))
=> H V; constructor; last first.
- case=>H3 H4 H5; apply: H; split; last 1 first.
  - by move=>i k X1 X2; apply: H5; rewrite inE ?X1 ?X2 orbT.
  - by move=>i X; apply: H3; rewrite inE X orbT.
  move=>i k X1 X2; move: (H4 i k); rewrite inE X1 orbT=>/(_ erefl X2).
  case: (x =P i) X1 X2=>[<-{i} X1 X2|]; last by rewrite add0n.
  by rewrite add1n; case=>/count_memPn; rewrite X1.
case: H=>H3 H4 H5; split; first by move=>i; rewrite inE=>/orP [/eqP ->|/H3].
- move=>i k; rewrite inE eq_sym; case: (x =P i)=>[<- _|X] /= D; last first.
  - by rewrite add0n; apply: H4 D.
  rewrite add1n; congr (_.+1); apply/count_memPn.
  apply: contraL (D)=>X; apply: H2; rewrite big_domUn V inE.
  by apply/hasP; exists x.
move=>i j; rewrite !inE=>/orP [/eqP ->{i}| Xi] /orP [/eqP ->{j}|Xj] // N.
- rewrite validUnAE H1 H3 //=; apply/allP=>k D; apply: H2.
  by rewrite big_domUn V inE; apply/hasP; exists j.
- rewrite validUnAE H3 ?H1 //=; apply/allP=>k; apply: contraL=>D; apply: H2.
  by rewrite big_domUn V inE; apply/hasP; exists i.
by apply: H5 Xi Xj N.
Qed.

End BigOpsUMEq.

Section BigCatSeqUM.
Variables (K : ordType) (C : pred K) (T : Type) (U : union_map C T).
Variables (I : eqType) (g : I -> U).

Lemma big_valid_dom_seq (xs : seq I) :
        (valid (\big[join/Unit]_(i <- xs) g i) =
         all (fun i => valid (g i)) xs &&
         uniq (\big[cat/[::]]_(i <- xs) dom (g i))) *
        (dom (\big[join/Unit]_(i <- xs) g i) =i
         if valid (\big[join/Unit]_(i <- xs) g i) then
           \big[cat/[::]]_(i <- xs) dom (g i)
         else [::]).
Proof.
elim: xs=>[|x xs [IH1 IH2]]; first by rewrite !big_nil valid_unit /= dom0.
rewrite !big_cons cat_uniq /=; split=>[|z]; last first.
- rewrite domUn inE; case V : (valid _)=>//=.
  by rewrite mem_cat IH2 (validR V).
rewrite validUnAE IH1 -all_predC -!andbA uniq_dom /=.
case V : (valid (g x))=>//=; case A : (all _)=>//=.
rewrite [RHS]andbC; case Uq : (uniq _)=>//=.
by apply: eq_all_r=>i; rewrite IH2 IH1 A Uq.
Qed.

Lemma big_valid_seq (xs : seq I) :
        valid (\big[join/Unit]_(i <- xs) g i) =
        all (fun i => valid (g i)) xs &&
        uniq (\big[cat/[::]]_(i <- xs) dom (g i)).
Proof. by rewrite big_valid_dom_seq. Qed.

Lemma big_dom_seq (xs : seq I) :
        dom (\big[join/Unit]_(i <- xs) g i) =i
        if valid (\big[join/Unit]_(i <- xs) g i) then
          \big[cat/[::]]_(i <- xs) dom (g i)
        else [::].
Proof. by move=>x; rewrite big_valid_dom_seq. Qed.

End BigCatSeqUM.

Section OMapBig.
Variables (K : ordType) (C : pred K) (T T' : Type).
Variables (U : union_map C T) (U' : union_map C T').
Variables (I : Type) (f : I -> U).

Lemma big_omapVUn (a : K * T -> option T') ts :
        omap a (\big[join/Unit]_(x <- ts) f x) =
        if valid (\big[join/Unit]_(x <- ts) f x)
        then \big[join/Unit]_(x <- ts) omap a (f x)
        else undef : U'.
Proof.
elim: ts=>[|t ts IH]; first by rewrite !big_nil omap0 valid_unit.
by rewrite !big_cons omapVUn IH; case: ifP=>// /validR ->.
Qed.

End OMapBig.


(* DEVCOMMENT: *)
(*   remove "tests" for release *)
Lemma xx (f : umap nat nat) : 3 \in dom (free f 2).
rewrite domF -domF.
Abort.
(* /DEVCOMMENT *)
