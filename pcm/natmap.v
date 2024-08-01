(*
Copyright 2015 IMDEA Software Institute
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
(* This file contains an implementation of maps over non-zero natural         *)
(* numbers, pcm instance for natmap, gapless natmaps, natmaps with binary     *)
(* range, several sorts of continuous natmaps.                                *)
(* Histories are a special case of natmaps.                                   *)
(******************************************************************************)

From HB Require Import structures.
From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval.
From pcm Require Import axioms options prelude pred finmap rtc seqext.
From pcm Require Export useqord uslice uconsec pcm morphism unionmap.
Import order.Order.NatOrder. (* listed last to avoid notation clash *)

(************************)
(* Maps over non-0 nats *)
(************************)

Definition null := 0.
Notation nat_pred := (fun x => x != 0). 

(* natmap is union map of non-0 nat keys *)
HB.mixin Record isNatMap V U of UMC nat (fun x => x != 0) V U.
#[short(type="natmap")]
HB.structure Definition NatMap V := {
  U of UMC nat (fun x => x != 0) V U & isNatMap V U}.

(* pred structure (to write x \In h) is copied from union_map *)
Canonical natmap_PredType A (U : natmap A) : PredType (nat * A) := 
  Mem_UmMap_PredType U.
Coercion Pred_of_natmap A (U : natmap A) (x : U) : Pred_Class := 
  [eta Mem_UmMap x].

(* canonical natmap is histories *)

Record history A := Hist {hist_base : @UM.base nat nat_pred A}.

Section HistoryUMC.
Variables A : Type.
Implicit Type f : history A.
Local Coercion hist_base : history >-> UM.base.
Let ht_valid f := @UM.valid nat nat_pred A f.
Let ht_empty := Hist (@UM.empty nat nat_pred A).
Let ht_undef := Hist (@UM.Undef nat nat_pred A).
Let ht_upd k v f := Hist (@UM.upd nat nat_pred A k v f).
Let ht_dom f := @UM.dom nat nat_pred A f. 
Let ht_assocs f := @UM.assocs nat nat_pred A f. 
Let ht_free f k := Hist (@UM.free nat nat_pred A f k).
Let ht_find k f := @UM.find nat nat_pred A k f. 
Let ht_union f1 f2 := Hist (@UM.union nat nat_pred A f1 f2).
Let ht_empb f := @UM.empb nat nat_pred A f. 
Let ht_undefb f := @UM.undefb nat nat_pred A f.
Let ht_from (f : history A) : UM.base _ _ := f. 
Let ht_to (b : @UM.base nat nat_pred A) : history A := Hist b.
Let ht_pts k v := Hist (@UM.pts nat nat_pred A k v).

Lemma history_is_umc : 
        union_map_axiom ht_valid ht_empty ht_undef ht_upd ht_dom 
                        ht_assocs ht_free ht_find ht_union ht_empb 
                        ht_undefb ht_pts ht_from ht_to. 
Proof. by split=>//; split=>[|[]]. Qed.

HB.instance Definition _ := 
  isUnion_map.Build nat nat_pred A (history A) history_is_umc. 
End HistoryUMC.

HB.instance Definition _ A := isNatMap.Build A (history A).
HB.instance Definition _ (A : eqType) := 
  hasDecEq.Build (history A) (@union_map_eqP nat _ A (history A)).
Canonical history_PredType A : PredType (nat * A) := 
  Mem_UmMap_PredType (history A).
Coercion Pred_of_history A (x : history A) : Pred_Class := 
  [eta Mem_UmMap x].

Notation "x \-> v" := (ptsT (history _) x v) (at level 30).

(* DEVCOMMENT *)
(* tests *)
Lemma xx : 1 \-> true = null \-> false.   
Abort.

Lemma xx : ((1 \-> true) \+ (2 \-> false)) == (1 \-> false). 
rewrite joinC. 
Abort.

Lemma xx (x : history nat) : x \+ x == x \+ x.
Abort.

Lemma xx : 1 \-> (1 \-> 3) = 2 \-> (7 \-> 3). 
Abort.

Lemma xx : (1, 3) \In (1 \-> 3).
Abort.
(* /DEVCOMMENT *)

(*************)
(* Main defs *)
(*************)

Definition last_key {A} {U : natmap A} (h : U) := last 0 (dom h).
Definition fresh {A} {U : natmap A} (h : U) := (last_key h).+1.
Definition last_val {A} {U : natmap A} (h : U) := find (last_key h) h.

(**********************)
(* generic properties *)
(**********************)

(* alternative to In_cond *)
Lemma In_neq A (U : natmap A) (h : U) k : 
        k \In h -> 
        k.1 > 0.
Proof. by move/In_cond; rewrite lt0n. Qed. 

Lemma mem_dom0 A (U : natmap A) {h : U} : 0 \in dom h = false.
Proof. by rewrite cond_dom. Qed.

Lemma uniq_dom0 A (U : natmap A) {h : U} : uniq (0 :: dom h).
Proof. by rewrite /= uniq_dom cond_dom. Qed.

Lemma all_leq0 A (U : natmap A) {h : U} : all (leq 0) (dom h).
Proof. by apply/allP=>x /dom_cond; case: ltngtP. Qed.

Lemma all_ltn0 A (U : natmap A) {h : U} : all (ltn 0) (dom h).
Proof. by apply/allP=>x /dom_cond; case: ltngtP. Qed.

#[export] Hint Resolve uniq_dom0 all_leq0 all_ltn0 : core.

Lemma In_dom0 {A} {U : natmap A} (h : U) k e : 
        (k, e) \In h -> k \in 0 :: dom h.
Proof. by move=>H; rewrite inE (In_dom H) orbT. Qed.

Lemma sorted_leq_dom A {U : natmap A} {h : U} : sorted leq (dom h).
Proof. by rewrite -(eq_sorted nat_oleq) sorted_dom_oleq. Qed.

Lemma sorted_ltn_dom A {U : natmap A} {h : U} : sorted ltn (dom h).
Proof. by rewrite sorted_dom. Qed.

Lemma path_leq_dom A {U : natmap A} {h : U} : path leq 0 (dom h).
Proof. by rewrite path_min_sorted // sorted_leq_dom. Qed.

Lemma path_ltn_dom A {U : natmap A} {h : U} : path ltn 0 (dom h).
Proof. by rewrite path_min_sorted. Qed.

#[export] Hint Resolve sorted_leq_dom sorted_ltn_dom 
  path_leq_dom path_ltn_dom : core.

(* form of totality of key order *)
Lemma umfiltT A (U : natmap A) k1 k2 (h : U) :
        k1 \in dom h -> k1 \notin dom (um_filterk (ltn^~ k2) h) ->
        k2 \in dom h -> k2 \notin dom (um_filterk (ltn^~ k1) h) ->
        k1 = k2.
Proof.
case/In_domX=>v1 D1 S1 /In_domX [v2 D2] S2.
case: (ltngtP k1 k2)=>// N.
- by move/(In_umfiltk (ltn^~ k2))/(_ N)/In_dom: D1; rewrite (negbTE S1).
by move/(In_umfiltk (ltn^~ k1))/(_ N)/In_dom: D2; rewrite (negbTE S2).
Qed.

Lemma umfiltT0 A (U : natmap A) k1 k2 (h : U) :
        k1 \in dom h -> um_filterk (ltn^~ k1) h = Unit ->
        k2 \in dom h -> um_filterk (ltn^~ k2) h = Unit ->
        k1 = k2.
Proof. 
by move=>D1 U1 D2 U2; apply: umfiltT D1 _ D2 _; rewrite ?U1 ?U2 dom0. 
Qed.

Lemma omf_subdom0 {A1 A2} {U1 : natmap A1} {U2 : natmap A2} 
                          {f : omap_fun U1 U2} {h : U1} :
        {subset 0::dom (f h) <= 0::dom h}.
Proof.
move=>x; rewrite !inE; case/orP=>[|/omf_subdom] -> //.
by rewrite orbT.
Qed.

(**************)
(* Base cases *)
(**************)

Lemma lastkey_undef A (U : natmap A) : last_key (undef : U) = 0.
Proof. by rewrite /last_key dom_undef. Qed.

Lemma lastkey0 A (U : natmap A) : last_key (Unit : U) = 0.
Proof. by rewrite /last_key dom0. Qed.

Lemma lastkeyPt A (U : natmap A) (x : nat) (v : A) : 
        last_key (pts x v : U) = x. 
Proof. by rewrite /last_key domPtK; case: (x =P 0). Qed.

Lemma lastval0 A (U : natmap A) : last_val (Unit : U) = None.
Proof. by rewrite /last_val lastkey0 find0E. Qed.

Lemma lastval_undef A (U : natmap A) : last_val (undef : U) = None.
Proof. by rewrite /last_val lastkey_undef find_undef. Qed.

Lemma lastvalPt A (U : natmap A) x v : 
        last_val (pts x v : U) = if x != 0 then Some v else None.
Proof. by rewrite /last_val lastkeyPt findPt. Qed.

(* basic transfer lemma *)
Lemma In_last A (U : natmap A) (h : U) v : 
        (last_key h, v) \In h <-> last_val h = Some v.
Proof. exact: In_find. Qed.

(* for inlined rewriting *)
Lemma In_lastE A (U : natmap A) (h : U) v : 
        (last_key h, v) \In h -> last_val h = Some v.
Proof. exact: In_findE. Qed.

(* fresh and 0 *)

Lemma fresh_undef A (U : natmap A) : fresh (undef : U) = 1.
Proof. by rewrite /fresh lastkey_undef. Qed.

Lemma fresh0 A (U : natmap A) : fresh (Unit : U) = 1.
Proof. by rewrite /fresh lastkey0. Qed.

Lemma fresh_lt0 A (U : natmap A) (h : U) x : fresh h <= x -> 0 < x.
Proof. by case: x. Qed.

Lemma freshN0 A (U : natmap A) (h : U) x : fresh h <= x -> x != 0.
Proof. by case: x. Qed.

(*************)
(* Main view *)
(*************)

(* captures that following properties are equivalent: *)
(* (undefb && unitb) = (last_key != 0) = (last_key > 0) = ... *)
(* ... = (last_key \in dom) = (dom <> [::]) = lastval = Some *)

Variant lastkey_dom_spec A (U : natmap A) (h : U) : 
  bool -> bool -> bool -> nat -> seq nat -> 
  bool -> bool -> bool -> option A -> Type := 
| lastkey_dom_undef of h = undef : 
    lastkey_dom_spec h false true false 0 [::] true false false None
| lastkey_dom_unit of h = Unit : 
    lastkey_dom_spec h true false true 0 [::] true false false None
| lastkey_dom_valid v of (last_key h, v) \In h :
    lastkey_dom_spec h true false false (last_key h) 
                     (dom h) false true true (Some v).

Lemma lastkeyP A (U : natmap A) (h : U) :
        lastkey_dom_spec h (valid h) (undefb h) (unitb h)
                           (last_key h) (dom h) (last_key h == 0) 
                           (last_key h > 0) (last_key h \in dom h) 
                           (last_val h).
Proof.
have L (x : U) : valid x -> last_key x \notin dom x -> x = Unit.
- rewrite /last_key !umEX /UM.valid/UM.dom/UM.empty -{4}[x]tfE. 
  case: (UMC_from x)=>//=; case=>s H H1 _ /seq_last_in. 
  by rewrite eqE UM.umapE /supp fmapE /= {H H1}; elim: s. 
case: (normalP0 h)=>[->|->|].
- by rewrite lastkey_undef dom_undef lastval_undef; apply: lastkey_dom_undef.
- by rewrite lastkey0 dom0 lastval0; apply: lastkey_dom_unit.
move=>V H.
have H1 : last_key h \in dom h by apply: contraT=>/(L _ V)/H.
have H2 : last_key h != 0 by apply: dom_cond H1.
have [v H4] : {v | last_val h = Some v}.
- by rewrite /last_val; case: dom_find H1=>// v; exists v.
by rewrite H1 lt0n (negbTE H2) H4; apply/lastkey_dom_valid/In_last.
Qed.

(* main membership invariant of last_key *)
Lemma lastkey_mem0 A (U : natmap A) (h : U) : last_key h \in 0 :: dom h.
Proof. by rewrite inE; case: lastkeyP. Qed.

(* DEVCOMMENT: *)
(*    Weird variation. Worth preserving? *)
(* /DEVCOMMENT *)
Lemma lastkey_memk A (U : natmap A) (h : U) k :
        (k < last_key h -> last_key h \notin dom h) -> 
        last_key h <= k.
Proof. by case: lastkeyP=>//= v _; case: ltngtP=>// _; apply. Qed.

(************)
(* last_key *)
(************)

Section LastkeyLemmas.
Variables (A : Type) (U : natmap A).
Implicit Type h : U.

(* last_key is upper bound *)
Lemma dom_lastkey h k : k \in dom h -> k <= last_key h.
Proof.
rewrite /last_key !umEX /UM.dom; case: (UMC_from h)=>//; case=>s H _ /=.
rewrite /supp/ord /= (leq_eqVlt k) orbC. 
by apply: sorted_last_key_maxR otrans (sorted_oleq H).
Qed.

(* useful variants with 0 :: dom and contrapositives *)
Lemma dom0_lastkey h k : k \in 0 :: dom h -> k <= last_key h.
Proof. by rewrite inE; case/orP=>[/eqP -> //|]; apply: dom_lastkey. Qed.
Lemma lastkey_dom h k : last_key h < k -> k \notin dom h.
Proof. by apply: contraL; rewrite -leqNgt; apply: dom_lastkey. Qed.
Lemma lastkey_dom0 h k : last_key h < k -> k \notin 0 :: dom h.
Proof. by apply: contraL; rewrite -leqNgt; apply: dom0_lastkey. Qed.

(* DEVCOMMENT: *)
(*   Weird variation. Worth preserving? *)
(* /DEVCOMMENT *)
Lemma dom_lastkey_eq h k :
        k \in dom h -> 
        (k < last_key h -> last_key h \notin dom h) ->
        k = last_key h.
Proof.
move/dom_lastkey=>D /lastkey_memk H.
by rewrite (@anti_leq (last_key _) k) // H D.
Qed.

(* last_key is least upper bound *)
Lemma lastkey_lub h k : {in dom h, forall x, x <= k} -> last_key h <= k.
Proof. by case lastkeyP=>// v /In_dom H; apply. Qed.

(* useful variant with equality *)
Lemma lub_lastkey h k : 
        k \in dom h -> 
        (forall x, k < x -> x \notin dom h) -> 
        k = last_key h.
Proof.
case: lastkeyP=>// v H /dom_lastkey Dx X.
rewrite (@anti_leq (last_key _) k) // Dx andbT.
apply: lastkey_lub=>x; apply: contraTT.
by rewrite -ltnNge; apply: X.
Qed.

(* equivalences *)

Lemma lastkey_leq h k : (last_key h <= k) = all (fun x => x <= k) (dom h).
Proof. 
apply/idP/allP=>[H x /dom_lastkey D|]; 
by [apply: leq_trans D H | apply: lastkey_lub].
Qed.

Lemma leq_lastkey h k : (k <= last_key h) = has (fun x => k <= x) (0 :: dom h).
Proof. 
apply/idP/hasP=>[|[x] D H]; last by apply: leq_trans H (dom0_lastkey D).
by exists (last_key h)=>//; apply: lastkey_mem0.
Qed.

Lemma ltn_lastkey h k : (k < last_key h) = has (fun x => k < x) (dom h).
Proof. 
apply/idP/hasP=>[|[x] D H]; last by apply: leq_trans H (dom_lastkey D).
by exists (last_key h)=>//; case: lastkeyP H.
Qed.

Lemma lastkey_ltn h k : (last_key h < k) = all (fun x => x < k) (0 :: dom h).
Proof. 
apply/idP/allP=>[H x D|]; last by apply; apply: lastkey_mem0.
by apply: leq_ltn_trans (dom0_lastkey D) H. 
Qed.

(* unfolding equivalences into implications (forward) *)
Lemma lastkey_leq_dom h x k : last_key h <= k -> x \in dom h -> x <= k.
Proof. by rewrite lastkey_leq=>/allP; apply. Qed.
Lemma lastkey_leq_dom0 h x k : last_key h <= k -> x \in 0 :: dom h -> x <= k.
Proof. by move=>H; case/orP=>[/eqP ->//|]; apply: lastkey_leq_dom H. Qed.
Lemma lastkey_ltn_dom0 h x k : last_key h < k -> x \in 0 :: dom h -> x < k.
Proof. by rewrite lastkey_ltn=>/allP; apply. Qed.
Lemma lastkey_ltn_dom h x k : last_key h < k -> x \in dom h -> x < k.
Proof. by move=>H D; apply: lastkey_ltn_dom0 H _; rewrite inE D orbT. Qed.

(* unfolding equivalences into implications (backward) *)
Lemma dom0_leq_lastkey h x k : x \in 0 :: dom h -> k <= x -> k <= last_key h.
Proof. by move=>D H; rewrite leq_lastkey; apply/hasP; exists x. Qed.
Lemma dom_leq_lastkey h x k : x \in dom h -> k <= x -> k <= last_key h.
Proof. by move=>D; apply: dom0_leq_lastkey; rewrite inE D orbT. Qed.
Lemma dom_ltn_lastkey h x k : x \in dom h -> k < x -> k < last_key h.
Proof. by move=>D H; rewrite ltn_lastkey; apply/hasP; exists x. Qed.
Lemma dom0_ltn_lastkey h x k : x \in 0 :: dom h -> k < x -> k < last_key h.
Proof. by case/orP=>[/eqP ->//|]; apply: dom_ltn_lastkey. Qed.
End LastkeyLemmas.

(* interaction of two lastkeys *)

Lemma lastkey_mono A1 A2 (U1 : natmap A1) (U2 : natmap A2) (h1 : U1) (h2 : U2) :
        {subset dom h1 <= dom h2} -> 
        last_key h1 <= last_key h2.
Proof.
rewrite leq_eqVlt orbC; apply: (seq_last_monoR orefl otrans); 
by rewrite (eq_path nat_oleq).
Qed.

Lemma lastkey_subdom A1 A2 (U1 : natmap A1) (U2 : natmap A2) (h1 : U1) (h2 : U2) :
        {subset dom h1 <= dom h2} ->
        last_key h2 \in dom h1 -> 
        last_key h1 = last_key h2.
Proof.
by move=>S D; apply/eqP; rewrite eqn_leq (dom_lastkey D) (lastkey_mono S). 
Qed.

Lemma lastkeyUnL A (U : natmap A) (h1 h2 : U) :
        valid (h1 \+ h2) -> 
        last_key h1 <= last_key (h1 \+ h2).
Proof. by move=>V; apply: lastkey_mono=>x; rewrite domUn inE V => ->. Qed.

Lemma lastkeyUnLT A (U : natmap A) (h1 h2 : U) k :
        valid (h1 \+ h2) -> 
        last_key (h1 \+ h2) < k ->
        last_key h1 < k.
Proof. by move=>V; apply/leq_ltn_trans/lastkeyUnL/V. Qed.

Lemma lastkeyUnR A (U : natmap A) (h1 h2 : U) :
        valid (h1 \+ h2) -> 
        last_key h2 <= last_key (h1 \+ h2).
Proof. by rewrite joinC; apply: lastkeyUnL. Qed.

Lemma lastkeyUnRT A (U : natmap A) (h1 h2 : U) k :
        valid (h1 \+ h2) -> 
        last_key (h1 \+ h2) < k ->
        last_key h2 < k. 
Proof. by rewrite joinC; apply: lastkeyUnLT. Qed.

(* disjoint maps with equal last keys are both empty *)
Lemma lastkeyUn0T A1 A2 (U1 : natmap A1) (U2 : natmap A2) (h1 : U1) (h2 : U2) :
        valid h1 -> valid h2 ->
        (forall x, x \in dom h1 -> x \in dom h2 -> false) ->
        last_key h1 = last_key h2 -> 
        (h1 = Unit) * (h2 = Unit).
Proof.
case: (lastkeyP h1)=>[//|-> _ V _ /esym/eqP|]; first by case: (lastkeyP h2) V.
move=>v1 H1 _ V2 /(_ _ (In_dom H1)) /[swap]/eqP /=.
case: (lastkeyP h2) V2=>//; first by rewrite (negbTE (In_cond H1)).
by move=>v2 H2 _ /eqP -> /(_ (In_dom H2)).
Qed.

(* specialization to equally-typed maps *)
Lemma lastkeyUn0 A (U : natmap A) (h1 h2 : U) :
        valid (h1 \+ h2) ->
        last_key h1 = last_key h2 -> 
        (h1 = Unit) * (h2 = Unit).
Proof. by case: validUn=>// ?? D _; apply: lastkeyUn0T=>// x /D/negbTE ->. Qed.

(* variation to avoid validity *)
Lemma lastkey00 A1 A2 (U1 : natmap A1) (U2 : natmap A2) (h1 : U1) (h2 : U2) :
        (forall x, x \in dom h1 -> x \in dom h2 -> false) ->
        last_key h1 = last_key h2 -> 
        (last_key h1 = 0) * (last_key h2 = 0).
Proof.
case: (normalP h1)=>[->|V1] D; first by rewrite lastkey_undef.
case: (normalP h2) D=>[->|V2] D; first by rewrite lastkey_undef.
by move=>H; rewrite !(lastkeyUn0T V1 V2 D H) !lastkey0.
Qed.

(* variation with subdoms *)
Lemma lastkey_subdom00 A1 A2 (U1 : natmap A1) (U2 : natmap A2) 
           (h1 : U1) (h2 : U2) (s1 s2 : pred nat) : 
        (forall x, x \in s1 -> x \in s2 -> false) ->
        {subset dom h1 <= s1} ->
        {subset dom h2 <= s2} ->
        last_key h1 = last_key h2 -> 
        (last_key h1 = 0) * (last_key h2 = 0).
Proof. by move=>D S1 S2; apply: lastkey00=>x /S1 H /S2; apply: D H. Qed.

(* interaction with constructors *)

Section LastkeyConstructors.
Variables (A : Type) (U : natmap A).
Implicit Type h : U.

Lemma lastkey_find h k : last_key h < k -> find k h = None.
Proof. by move/lastkey_dom; case: dom_find. Qed.

(* monotonicity gives <=; removing last_key gives strict < *)
Lemma lastkeyF h : 
        last_key h != 0 -> 
        last_key (free h (last_key h)) < last_key h.
Proof.
move=>D; have {}D : last_key h \in dom h by case: lastkeyP D.
case: (um_eta D)=>v [Ef Eh].
have N : last_key h \notin dom (free h (last_key h)).
- by rewrite domF inE eqxx.
have: last_key (free h (last_key h)) <= last_key h.
- by apply: lastkey_mono=>x; rewrite domF inE; case: ifP.
rewrite leq_eqVlt; case/orP=>// /eqP E; rewrite -{1}E in N.
have : last_key h > 0 by move/dom_cond: D; case: (last_key h).
by case: lastkeyP N.
Qed.

(* lastkey of union is max of lastkeys *)
Lemma lastkeyUn h1 h2 :
        last_key (h1 \+ h2) =
        if valid (h1 \+ h2) then maxn (last_key h1) (last_key h2) else 0.
Proof.
have H (k1 k2 : U) : valid (k1 \+ k2) ->
  last_key k1 < last_key k2 -> last_key (k1 \+ k2) = last_key k2.
- move=>V H; apply/eqP; rewrite eqn_leq lastkeyUnR // andbT lastkey_leq.
  apply/allP=>/= x; rewrite domUn inE V /=.
  by case/orP=>/dom_lastkey // T; apply: leq_trans T (ltnW H). 
case: (normalP (h1 \+ h2))=>[->|V]; first by rewrite lastkey_undef.
case: (ltngtP (last_key h2) (last_key h1)).
- by rewrite joinC in V *; apply: H.
- by apply: H.
by move/esym/(lastkeyUn0 V)=>E; rewrite !E unitL.
Qed.

Lemma lastkeyPtUnV h k v : last_key h < k -> valid (pts k v \+ h) = valid h.
Proof.
move=>N; rewrite validPtUn -lt0n (leq_ltn_trans _ N) //= andbC.
by case D: (k \in dom h)=>//; move/dom_lastkey: D; case: leqP N.
Qed.

Lemma lastkey_domPtUn h k v :
        valid h -> last_key h < k -> dom (pts k v \+ h) = rcons (dom h) k.
Proof.
move=>V N; rewrite joinC domUnPtK //.
- by rewrite joinC lastkeyPtUnV.
by apply/allP=>x /dom_lastkey D; apply: leq_ltn_trans D N.
Qed.

Lemma lastkey_rangePtUn h k v :
        valid h -> last_key h < k -> range (pts k v \+ h) = rcons (range h) v.
Proof.
move=>V K; rewrite joinC rangeUnPtK //; last first.
- by apply/allP=>x /dom_lastkey H; apply: leq_ltn_trans H K.
by rewrite joinC lastkeyPtUnV.
Qed.

Lemma lastkeyPtUnE h k v :
        last_key (pts k v \+ h) =
        if valid (pts k v \+ h) then maxn k (last_key h) else 0.
Proof. by rewrite lastkeyUn lastkeyPt. Qed.

Lemma lastkeyPtUn h k v :
        valid h -> last_key h < k -> last_key (pts k v \+ h) = k.
Proof.
move=>V N; rewrite lastkeyPtUnE (lastkeyPtUnV _ N) V. 
by apply: maxn_idPl (ltnW N).
Qed.

Lemma lastkeyPtUnEX v2 v1 h k :
        last_key (pts k v1 \+ h) = last_key (pts k v2 \+ h).
Proof. by rewrite !lastkeyPtUnE !validPtUn. Qed.

Lemma lastkeyUnPtEX v2 v1 h k :
        last_key (h \+ pts k v1) = last_key (h \+ pts k v2).
Proof. by rewrite !(joinC h) (lastkeyPtUnEX v2). Qed.

Lemma lastkeyU h k v : k \in dom h -> last_key (upd k v h) = last_key h.
Proof. by case/um_eta=>u [_ ->]; rewrite updPtUn (lastkeyPtUnEX u). Qed.

Lemma lastkeyUE h k v :
        last_key (upd k v h) =
        if k \in dom h then last_key h else
        if valid (upd k v h) then maxn k (last_key h) else 0.
Proof.
case: ifP=>[|H]; first by apply: lastkeyU.
rewrite validU; case: eqVneq=>[->|N] /=. 
- by rewrite upd_condN // lastkey_undef.
case: (normalP h)=>[->|V]; first by rewrite upd_undef lastkey_undef.
by rewrite upd_eta2 ?H // lastkeyUn -upd_eta2 ?H // validU N V lastkeyPt. 
Qed.

(* backward induction on valid natmaps *)
Lemma valid_indb (P : U -> Prop) :
        P Unit ->
        (forall v, P (pts 1 v)) ->
        (forall k v h, 
           P h -> last_key h < k ->
           valid (pts k v \+ h) -> P (pts k v \+ h)) ->
        forall h, valid h -> P h.
Proof.
move=>H1 H2 H3; elim/um_indb=>[||k v f H V K _]; rewrite ?valid_undef //. 
rewrite joinC in V; move: (validR V)=>Vf; case E: (unitb f); last first.
- by apply: H3 (H Vf) (K _ _) V; case: lastkeyP Vf E.
move/unitbP: {K H} E V (H3 k v Unit H1)=>->.
by rewrite unitR validPt lastkey0 lt0n=>V; apply.
Qed.

(* forward induction on valid natmaps *)
Lemma valid_indf (P : U -> Prop) :
        P Unit ->
        (forall k v h, P h ->
           {in dom h, forall x, k < x} ->
           valid (pts k v \+ h) -> P (pts k v \+ h)) ->
        forall h, valid h -> P h.
Proof.
move=>H1 H2; elim/um_indf=>[||k v f H V K _]; rewrite ?valid_undef //.
by apply: H2 (H (validR V)) _ V; apply/allP/(order_path_min _ K). 
Qed.

(* membership *)

Lemma In_lastkey h k v : (k, v) \In h -> k <= last_key h.
Proof. by move/In_dom/dom_lastkey. Qed.

Lemma In_lastkeyPtUn h x k v w :
         last_key h < k -> (x, w) \In h -> (x, w) \In pts k v \+ h.
Proof. by move=>N H; apply: InR=>//; rewrite lastkeyPtUnV ?(In_valid H). Qed.

Lemma In_lastkeyPtUn_inv h x k v w :
         x <= last_key h -> last_key h < k ->
         (x, w) \In pts k v \+ h -> (x, w) \In h.
Proof. 
move=>N1 N2 H; case/(InPtUnE _ (In_valid H)): H N2=>//.
by case=><- _; case: ltngtP N1.
Qed.

End LastkeyConstructors.

(* last_key and omap_fun -- compositions with omf_subdom/omf_subdom0 *)

Section LastKeyOmapFun.
Variables (A1 A2 : Type) (U1 : natmap A1) (U2 : natmap A2).
Implicit Type f : omap_fun U1 U2.

(* upper bound lemmas *)
Lemma odom_lastkey f h k : k \in dom (f h) -> k <= last_key h.
Proof. by move/omf_subdom/dom_lastkey. Qed.
Lemma odom0_lastkey f h k : k \in 0 :: dom (f h) -> k <= last_key h.
Proof. by move/omf_subdom0/dom0_lastkey. Qed.
Lemma lastkey_odom f h k : last_key h < k -> k \notin dom (f h).
Proof. by move/lastkey_dom; apply/(subsetC omf_subdom). Qed.
Lemma lastkey_odom0 f h k : last_key h < k -> k \notin 0 :: dom (f h).
Proof. move/lastkey_dom0; apply/(subsetC omf_subdom0). Qed.

(* DEVCOMMENT: *)
(*   Weird variation. Worth preserving? *)
(*   composes dom_lastkey_eq with In_dom_omfX *)
(* /DEVCOMMENT *)
Lemma odom_lastkey_eq f h k v :
        (k, v) \In h -> omf f (k, v) ->
        (forall w, k < last_key (f h) -> 
           (last_key (f h), w) \In h -> 
           omf f (last_key (f h), w) -> False) ->
        k = last_key (f h).
Proof.
move=>D1 D2 H; apply: dom_lastkey_eq=>[|X].
- by apply/In_dom_omfX; exists v.
by apply/In_dom_omfX; case=>w []; apply: H X.
Qed.

(* lub lemmas: combine lastkey_lub/lub_lastkey with In_dom_omfX *)
Lemma lastkey_olub f h k : 
        (forall x v, (x, v) \In h -> omf f (x, v) -> x <= k) ->
        last_key (f h) <= k.
Proof.
move=>H; apply: lastkey_lub=>x /In_dom_omfX [v][X E].
by apply: H X _; rewrite E.
Qed.

Lemma olub_lastkey f h k : 
        k \in dom (f h) ->
        (forall x v, k < x -> (x, v) \In h -> omf f (x, v) -> False) ->
        k = last_key (f h).
Proof.
move=>D H; apply: lub_lastkey=>// x K; apply/In_dom_omfX; case=>y [X E].
by apply: H K X _; rewrite E.
Qed.

(* equivalence lemmas (forward) *)
Lemma lastkey_leq_odom f h x k : last_key h <= k -> x \in dom (f h) -> x <= k.
Proof. by move/lastkey_leq_dom=>H /omf_subdom /H. Qed.
Lemma lastkey_leq_odom0 f h x k : last_key h <= k -> x \in 0 :: dom (f h) -> x <= k.
Proof. by move/lastkey_leq_dom0=>H /omf_subdom0 /H. Qed.
Lemma lastkey_ltn_odom0 f h x k : last_key h < k -> x \in 0 :: dom (f h) -> x < k.
Proof. by move/lastkey_ltn_dom0=>H /omf_subdom0 /H. Qed.
Lemma lastkey_ltn_odom f h x k : last_key h < k -> x \in dom (f h) -> x < k.
Proof. by move/lastkey_ltn_dom=>H /omf_subdom /H. Qed.

(* equivalence lemms (backward) *)
Lemma odom0_leq_lastkey f h x k : x \in 0 :: dom (f h) -> k <= x -> k <= last_key h.
Proof. by move/omf_subdom0; apply/dom0_leq_lastkey. Qed.
Lemma odom_leq_lastkey f h x k : x \in dom (f h) -> k <= x -> k <= last_key h.
Proof. by move/omf_subdom; apply/dom_leq_lastkey. Qed.
Lemma odom_ltn_lastkey f h x k : x \in dom (f h) -> k < x -> k < last_key h.
Proof. by move/omf_subdom; apply: dom_ltn_lastkey. Qed.
Lemma odom0_ltn_lastkey f h x k : x \in 0 :: dom (f h) -> k < x -> k < last_key h.
Proof. by move/omf_subdom0; apply: dom0_ltn_lastkey. Qed.

(* other lemmas *)

Lemma lastkey_omf f h : last_key (f h) <= last_key h.
Proof. by apply: lastkey_mono; apply: omf_subdom. Qed.

Lemma lastkey_omfT f h k : last_key h <= k -> last_key (f h) <= k.
Proof. by apply/leq_trans/lastkey_omf. Qed.

Lemma lastkey_omfT' f h k : last_key h < k -> last_key (f h) < k.
Proof. by apply/leq_ltn_trans/lastkey_omf. Qed.

Lemma lastkey_omfUn f h1 h2 :
        valid (h1 \+ h2) -> last_key (f h1 \+ f h2) <= last_key (h1 \+ h2).
Proof. by move=>V; rewrite -omfUn // lastkey_omf. Qed.

Lemma lastkey_omf_some f h :
        (forall x, x \In h -> oapp predT false (omf f x)) -> 
        last_key (f h) = last_key h.
Proof. by rewrite /last_key=>/dom_omf_some ->. Qed.

Lemma lastkey_omfE f h : last_key h \in dom (f h) -> last_key (f h) = last_key h.
Proof. by apply: lastkey_subdom omf_subdom. Qed.

Lemma lastkey_omfPtUn f k v h :
        last_key h < k ->
        f (pts k v \+ h) =
        if omf f (k, v) is Some w then pts k w \+ f h else f h.
Proof. 
case: (normalP h)=>[->|V N]; last by rewrite omfPtUn lastkeyPtUnV // V.
by case: (omf _ _)=>[a|]; rewrite pfundef !join_undef pfundef.
Qed.

Lemma omf_sublastkey f k v h : 
        last_key h < k ->
        {subset dom (f h) <= dom (f (pts k v \+ h))}.
Proof.
move=>N x H; rewrite lastkey_omfPtUn //; case: (omf _ _)=>[a|//].
by rewrite domPtUn inE H orbT lastkeyPtUnV ?(dom_valid H,lastkey_omfT').
Qed.

End LastKeyOmapFun.

(* last_key and filter *)

Lemma lastkey_umfilt_le A (U : natmap A) (h : U) k :
        last_key h <= k -> um_filterk [pred x | x <= k] h = h.
Proof.
move=>N; rewrite -[RHS]umfilt_predT -eq_in_umfilt.
by case=>x v /In_dom/dom_lastkey/leq_trans/(_ N).
Qed.

Lemma lastkey_umfilt_lt A (U : natmap A) (h : U) k :
        last_key h < k -> um_filterk [pred x | x < k] h = h.
Proof.
move=>N; rewrite -[RHS]umfilt_predT -eq_in_umfilt.
by case=>x v /In_dom/dom_lastkey/leq_ltn_trans/(_ N).
Qed.

Lemma lastkey_umfiltPtUn A (U : natmap A) (p : pred (nat * A)) (h : U) k v :
        last_key h < k ->
        um_filter p (pts k v \+ h) =
        if p (k, v) then pts k v \+ um_filter p h else um_filter p h.
Proof. by move=>V; rewrite lastkey_omfPtUn ?omf_omap //=; case: ifP. Qed.

(* last_key and side *)

Lemma lastkey_sidePtUn (T : eqType) (Us : T -> Type) 
          (U : natmap (sigT Us)) (Ut : forall t, natmap (Us t)) 
          (h : U) t k v :
        fresh h <= k ->
        side_map Ut t (pts k v \+ h) =
        if decP (t =P tag v) is left pf then 
          pts k (cast Us pf (tagged v)) \+ side_map Ut t h
        else side_map Ut t h.
Proof. by case: v=>tx vx N; rewrite lastkey_omfPtUn //= /omfx/=; case: eqP. Qed.

Lemma lastkey_dom_sidePtUn (T : eqType) (Us : T -> Type) 
          (U : natmap (sigT Us)) (Ut : forall t, natmap (Us t))
          (h : U) t k v :
        last_key h < k ->
        dom (side_map Ut t (pts k v \+ h)) =
        if valid h then
          if t == tag v then rcons (dom (side_map Ut t h)) k 
          else dom (side_map Ut t h)
        else [::].
Proof. 
case: (normalP h)=>[->|V N]; first by rewrite join_undef pfundef dom_undef.
rewrite lastkey_sidePtUn //; case: eqP=>//= ?; subst t. 
by rewrite eqc lastkey_domPtUn ?(pfV (side_map Ut _)) ?lastkey_omfT'.
Qed.

(* last_key and non-omap morphisms *)
Lemma plastkey (A : Type) (U1 : pcm) (U2 : natmap A) 
               (f : pcm_morph U1 U2) k (x y : U1) : 
        valid (x \+ y) -> 
        sep f x y ->
        last_key (f (x \+ y)) < k -> 
        last_key (f x) < k.
Proof.
move=>V D; apply: leq_ltn_trans.
by rewrite pfjoin // lastkeyUnL // pfV2.
Qed.

Lemma plastkeyT A (U1 : pcm) (U2 : natmap A) 
                (f : full_pcm_morph U1 U2) k (x y : U1) : 
        valid (x \+ y) -> 
        last_key (f (x \+ y)) < k -> 
        last_key (f x) < k.
Proof. by move=>V; apply/(plastkey V)/pfT. Qed.

(* monotonicity for natmap nat *)
Lemma lastkey_monoPtUn (U : natmap nat) k w (h : U) :
        last_key h < k ->
        (forall k v, (k, v) \In h -> v < w) ->
        um_mono (pts k w \+ h) = um_mono h.
Proof.
move=>N H; case: (normalP h)=>[->|V]; first by rewrite join_undef.
apply: ummonoPtUn; first by rewrite lastkeyPtUnV.
move=>x v X; split; last by apply: H X.
by apply: leq_ltn_trans (dom_lastkey (In_dom X)) N.  
Qed.

(* last_key and pcm ordering *)
Lemma lastkey_fun A (U1 : pcm) (U2 : natmap A) 
           (f : full_pcm_morph U1 U2) (x y : U1) :
        [pcm y <= x] ->
        valid x -> 
        last_key (f y) <= last_key (f x).
Proof. by case=>z -> V; rewrite pfjoinT // lastkeyUnL // pfV2I. Qed.

(* special case of lastkey_fun when f = id *)
Lemma lastkey_umpleq A (U : natmap A) (h1 h2 : U) : 
        [pcm h1 <= h2] ->
        valid h2 -> 
        last_key h1 <= last_key h2.
Proof. by apply: (lastkey_fun idfun). Qed.

Lemma lastkeyL A (U1 : pcm) (U2 : natmap A)
          (f : full_pcm_morph U1 U2) (x y : U1) :
        valid (x \+ y) -> 
        last_key (f x) <= last_key (f (x \+ y)).
Proof. by apply: lastkey_fun. Qed.

Lemma lastkeyR A (U1 : pcm) (U2 : natmap A) 
          (f : full_pcm_morph U1 U2) (x y : U1) :
        valid (x \+ y) -> 
        last_key (f y) <= last_key (f (x \+ y)).
Proof. by apply: lastkey_fun. Qed.

(*********)
(* fresh *)
(*********)

(* mostly new names for lastkey lemmas *)
(* but there are several new lemmas also *)
(* to be systematic, we list all *)

Section FreshLemmas.
Variables (A : Type) (U : natmap A).
Implicit Type h : U.

(* fresh is strict upper bound *)
Lemma dom_fresh h k : k \in dom h -> k < fresh h. 
Proof. exact: dom_lastkey. Qed.

(* variants with 0 :: dom and contrapositives *) 
Lemma dom0_fresh h k : k \in 0 :: dom h -> k < fresh h. 
Proof. exact: dom0_lastkey. Qed.
Lemma fresh_dom h k : fresh h <= k -> k \notin dom h.
Proof. exact: lastkey_dom. Qed.
Lemma fresh_dom0 h k : fresh h <= k -> k \notin 0 :: dom h.
Proof. exact: lastkey_dom0. Qed.

(* equivalences (similar to lastkey, but with x.+1) *)
Lemma fresh_leq h k : (fresh h <= k) = all (fun x => x.+1 <= k) (0 :: dom h).
Proof. exact: lastkey_ltn. Qed.

Lemma leq_fresh h k : (k <= fresh h) = has (fun x => k <= x.+1) (0 :: dom h).
Proof. 
apply/idP/hasP=>[|[x] D H]; last by apply: leq_trans H (dom0_fresh D). 
by exists (last_key h)=>//; apply: lastkey_mem0.
Qed.

Lemma ltn_fresh h k : (k < fresh h) = has (fun x => k < x.+1) (0 :: dom h).
Proof. by rewrite ltnS leq_lastkey. Qed.

Lemma fresh_ltn h k : (fresh h < k) = all (fun x => x.+1 < k) (0 :: dom h).
Proof. 
apply/idP/allP=>[H x D|]; last by apply; apply: lastkey_mem0.
by apply: leq_ltn_trans (dom0_fresh D) H.
Qed.

(* unfolding equivalences into implications (forward) *)
Lemma fresh_leq_dom0 h x k : fresh h <= k -> x \in 0 :: dom h -> x < k.
Proof. exact: lastkey_ltn_dom0. Qed.
Lemma fresh_leq_dom h x k : fresh h <= k -> x \in dom h -> x < k.
Proof. exact: lastkey_ltn_dom. Qed.
Lemma fresh_ltn_dom0 h x k : fresh h < k -> x \in 0 :: dom h -> x.+1 < k.
Proof. by rewrite fresh_ltn=>/allP; apply. Qed.
Lemma fresh_ltn_dom h x k : fresh h < k -> x \in dom h -> x.+1 < k.
Proof. by move=>H D; apply: fresh_ltn_dom0 H _; rewrite inE D orbT. Qed.

(* unfolding equivalences into implications (backward) *)
Lemma dom0_leq_fresh h x k : x \in 0 :: dom h -> k <= x.+1 -> k <= fresh h.
Proof. by move=>D H; rewrite leq_fresh; apply/hasP; exists x. Qed.
Lemma dom_leq_fresh h x k : x \in dom h -> k <= x.+1 -> k <= fresh h.
Proof. by move=>D; apply: dom0_leq_fresh; rewrite inE D orbT. Qed.
Lemma dom0_ltn_fresh h x k : x \in 0 :: dom h -> k <= x -> k < fresh h.
Proof. exact: dom0_leq_lastkey. Qed.
Lemma dom_ltn_fresh h x k : x \in dom h -> k <= x -> k < fresh h.
Proof. exact: dom_leq_lastkey. Qed.
End FreshLemmas.

(* interaction of two fresh's *)

Lemma fresh_mono A1 A2 (U1 : natmap A1) (U2 : natmap A2) 
          (h1 : U1) (h2 : U2) :
        {subset dom h1 <= dom h2} -> 
        fresh h1 <= fresh h2.
Proof. exact: lastkey_mono. Qed.

Lemma fresh_subdom A1 A2 (U1 : natmap A1) (U2 : natmap A2) 
          (h1 : U1) (h2 : U2) :
        {subset dom h1 <= dom h2} -> 
        fresh h2 \notin dom h1.
Proof. by move/fresh_mono/fresh_dom. Qed.

Lemma fresh_subdom_lt A1 A2 (U1 : natmap A1) (U2 : natmap A2) 
          (h1 : U1) (h2 : U2) x :
        {subset dom h1 <= dom h2} -> 
        x \in dom h1 -> 
        x < fresh h2.
Proof. by move=>H /H /dom_fresh. Qed.

Lemma fresh_subdomN A1 A2 (U1 : natmap A1) (U2 : natmap A2) 
          (h1 : U1) (h2 : U2) x :
        {subset dom h1 <= dom h2} -> 
        x \in dom h1 -> 
        x != fresh h2.
Proof. by move=>S /(fresh_subdom_lt S); case: ltngtP. Qed.

Lemma freshUnL A (U : natmap A) (h1 h2 : U) :
        valid (h1 \+ h2) -> 
        fresh h1 <= fresh (h1 \+ h2).
Proof. exact: lastkeyUnL. Qed.

Lemma freshUnLT A (U : natmap A) (h1 h2 : U) k :
        valid (h1 \+ h2) -> 
        fresh (h1 \+ h2) <= k ->
        fresh h1 <= k.
Proof. exact: lastkeyUnLT. Qed.

Lemma freshUnR A (U : natmap A) (h1 h2 : U) :
        valid (h1 \+ h2) -> 
        fresh h2 <= fresh (h1 \+ h2).
Proof. exact: lastkeyUnR. Qed.

Lemma freshUnRT A (U : natmap A) (h1 h2 : U) k :
        valid (h1 \+ h2) -> 
        fresh (h1 \+ h2) <= k ->
        fresh h2 <= k.
Proof. exact: lastkeyUnRT. Qed.

(* interaction with constructors *)

Section FreshConstructors.
Variables (A : Type) (U : natmap A).
Implicit Type h : U.

Lemma fresh_find h k : 
        fresh h <= k -> find k h = None.
Proof. exact: lastkey_find. Qed.

Lemma freshF h : 
        last_key h != 0 -> 
        fresh (free h (last_key h)) < fresh h.
Proof. exact: lastkeyF. Qed.

Lemma freshUn h1 h2 :
        fresh (h1 \+ h2) = 
        if valid (h1 \+ h2) then maxn (fresh h1) (fresh h2) else 1.
Proof. by rewrite /fresh lastkeyUn maxnSS; case: ifP. Qed.

Lemma freshPtUnV h k v : 
        fresh h <= k -> 
        valid (pts k v \+ h) = valid h.
Proof. exact: lastkeyPtUnV. Qed.

(* easier name to remember *)
Definition valid_fresh := freshPtUnV.

Lemma fresh_domPtUn h k v :
        valid h -> 
        fresh h <= k -> 
        dom (pts k v \+ h) = rcons (dom h) k.
Proof. exact: lastkey_domPtUn. Qed.

Lemma fresh_rangePtUn h k v :
        valid h -> 
        fresh h <= k -> 
        range (pts k v \+ h) = rcons (range h) v.
Proof. exact: lastkey_rangePtUn. Qed.

Lemma freshPtUnE h k v :
        fresh (pts k v \+ h) =
        if valid (pts k v \+ h) then maxn k.+1 (fresh h) else 1.
Proof. by rewrite /fresh lastkeyPtUnE maxnSS; case: ifP. Qed.

Lemma freshPtUn h k v :
        valid h -> fresh h <= k -> fresh (pts k v \+ h) = k.+1.
Proof. by move=>V N; rewrite /fresh lastkeyPtUn. Qed.

Lemma freshPtUnEX v2 v1 h k : fresh (pts k v1 \+ h) = fresh (pts k v2 \+ h).
Proof. by congr (_.+1); apply: lastkeyPtUnEX. Qed.

Lemma freshUnPtEX v2 v1 h k : fresh (h \+ pts k v1) = fresh (h \+ pts k v2).
Proof. by rewrite !(joinC h) (freshPtUnEX v2). Qed.

Lemma freshU h k v : k \in dom h -> fresh (upd k v h) = fresh h.
Proof. by move=>D; congr _.+1; apply: lastkeyU D. Qed.

Lemma freshUE h k v :
        fresh (upd k v h) =
        if k \in dom h then fresh h else
        if valid (upd k v h) then maxn k.+1 (fresh h) else 1.
Proof. by rewrite /fresh lastkeyUE maxnSS; case: ifP=>//; case: ifP. Qed.

(* membership *)

Lemma In_fresh h k v : (k, v) \In h -> k < fresh h.
Proof. exact: In_lastkey. Qed.

Lemma In_freshPtUn h x k v w :
         fresh h <= k -> (x, w) \In h -> (x, w) \In pts k v \+ h.
Proof. exact: In_lastkeyPtUn. Qed.

Lemma In_freshPtUn_inv h x k v w :
         x < fresh h -> fresh h <= k ->
         (x, w) \In pts k v \+ h -> (x, w) \In h.
Proof. exact: In_lastkeyPtUn_inv. Qed.

End FreshConstructors.

(* fresh and omap_fun -- compositions with omf_subdom/omf_subdom0 *)
Section FreshOmapFun.
Variables (A1 A2 : Type) (U1 : natmap A1) (U2 : natmap A2).
Implicit Types (f : omap_fun U1 U2) (h : U1).

(* strict upper bound lemmas *)
Lemma odom_fresh f h k : k \in dom (f h) -> k < fresh h.  
Proof. exact: odom_lastkey. Qed.
Lemma odom0_fresh f h k : k \in 0 :: dom (f h) -> k < fresh h. 
Proof. exact: odom0_lastkey. Qed.
Lemma fresh_odom f h k : fresh h <= k -> k \notin dom (f h).
Proof. exact: lastkey_odom. Qed.
Lemma fresh_odom0 f h k : fresh h <= k -> k \notin 0 :: dom (f h).
Proof. exact: lastkey_odom0. Qed.

(* equivalence lemmas (forward) *)
Lemma fresh_leq_odom0 f h x k : fresh h <= k -> x \in 0 :: dom (f h) -> x < k.
Proof. exact: lastkey_ltn_odom0. Qed.
Lemma fresh_leq_odom f h x k : fresh h <= k -> x \in dom (f h) -> x < k.
Proof. exact: lastkey_ltn_odom. Qed.
Lemma fresh_ltn_odom0 f h x k : fresh h < k -> x \in 0 :: dom (f h) -> x.+1 < k.
Proof. by move/fresh_ltn_dom0=>H /omf_subdom0 /H. Qed.
Lemma fresh_ltn_odom f h x k : fresh h < k -> x \in dom (f h) -> x.+1 < k.
Proof. by move/fresh_ltn_dom=>H /omf_subdom /H. Qed.

(* equivalence lemmas (backward) *)
Lemma odom0_leq_fresh f h x k : x \in 0 :: dom (f h) -> k <= x.+1 -> k <= fresh h.
Proof. by move/omf_subdom0; apply/dom0_leq_fresh. Qed.
Lemma odom_leq_fresh f h x k : x \in dom (f h) -> k <= x.+1 -> k <= fresh h.
Proof. by move/omf_subdom; apply/dom_leq_fresh. Qed.
Lemma odom0_ltn_fresh f h x k : x \in 0 :: dom (f h) -> k <= x -> k < fresh h.
Proof. exact: odom0_leq_lastkey. Qed.
Lemma odom_ltn_fresh f h x k : x \in dom (f h) -> k <= x -> k < fresh h.
Proof. exact: odom_leq_lastkey. Qed.

(* other lemmas *)

Lemma fresh_omf f h : fresh (f h) <= fresh h.
Proof. exact: lastkey_omf. Qed.

Lemma fresh_omfT f k h : 
        fresh h <= k -> 
        fresh (f h) <= k.
Proof. exact: lastkey_omfT'. Qed.

Lemma fresh_omfUn f h1 h2 :
        valid (h1 \+ h2) -> 
        fresh (f h1 \+ f h2) <= fresh (h1 \+ h2).
Proof. exact: lastkey_omfUn. Qed.

Lemma fresh_omf_some f h :
        (forall x, x \In h -> oapp predT false (omf f x)) ->
        fresh (f h) = fresh h.
Proof. by move=>H; congr _.+1; apply: lastkey_omf_some H. Qed.

Lemma fresh_omfE f h : 
        last_key h \in dom (f h) -> 
        fresh (f h) = fresh h.
Proof. by move=>H; congr _.+1; apply: lastkey_omfE. Qed.

Lemma fresh_omfPtUn f k v h :
        fresh h <= k ->
        f (pts k v \+ h) =
        if omf f (k, v) is Some w then pts k w \+ f h else f h.
Proof. exact: lastkey_omfPtUn. Qed.

Lemma omf_subfresh f k v h : 
        fresh h <= k ->
        {subset dom (f h) <= dom (f (pts k v \+ h))}.
Proof. exact: omf_sublastkey. Qed.

End FreshOmapFun.

(* fresh and filter *)

Lemma fresh_umfilt_lt A (U : natmap A) (h : U) k :
        fresh h <= k -> 
        um_filterk [pred x | x < k] h = h.
Proof. exact: lastkey_umfilt_lt. Qed.

Lemma fresh_umfiltPtUn A (U : natmap A) (p : pred (nat * A)) (h : U) k v :
        fresh h <= k ->
        um_filter p (pts k v \+ h) =
        if p (k, v) then pts k v \+ um_filter p h else um_filter p h.
Proof. exact: lastkey_umfiltPtUn. Qed.

(* fresh and side *)

Lemma fresh_sidePtUn (T : eqType) (Us : T -> Type) 
          (U : natmap (sigT Us)) (Ut : forall t, natmap (Us t)) 
          (h : U) t k v :
        fresh h <= k ->
        side_map Ut t (pts k v \+ h) =
        if decP (t =P tag v) is left pf then 
          pts k (cast Us pf (tagged v)) \+ side_map Ut t h
        else side_map Ut t h.
Proof. exact: lastkey_sidePtUn. Qed.

Lemma fresh_dom_sidePtUn (T : eqType) (Us : T -> Type) 
          (U : natmap (sigT Us)) (Ut : forall t, natmap (Us t))
          (h : U) t k v :
        fresh h <= k ->
        dom (side_map Ut t (pts k v \+ h)) =
        if valid h then
          if t == tag v then rcons (dom (side_map Ut t h)) k 
          else dom (side_map Ut t h)
        else [::].
Proof. exact: lastkey_dom_sidePtUn. Qed.

(* fresh and non-omap morphisms *)
Lemma pfresh (A : Type) (U1 : pcm) (U2 : natmap A) 
             (f : pcm_morph U1 U2) k (x y : U1) : 
        valid (x \+ y) -> 
        sep f x y ->
        fresh (f (x \+ y)) <= k -> 
        fresh (f x) <= k.
Proof. exact: plastkey. Qed.

Lemma pfreshT (A : Type) (U1 : pcm) (U2 : natmap A) 
              (f : full_pcm_morph U1 U2) k (x y : U1) : 
        valid (x \+ y) -> 
        fresh (f (x \+ y)) <= k -> 
        fresh (f x) <= k.
Proof. exact: plastkeyT. Qed.

(* monotonicity for natmap nat *)
Lemma fresh_monoPtUn (U : natmap nat) k w (h : U) :
        fresh h <= k ->
        (forall k v, (k, v) \In h -> v < w) ->
        um_mono (pts k w \+ h) = um_mono h.
Proof. exact: lastkey_monoPtUn. Qed.

(* fresh and pcm ordering *)
Lemma fresh_fun A (U1 : pcm) (U2 : natmap A) 
           (f : full_pcm_morph U1 U2) (x y : U1) :
        [pcm y <= x] ->
        valid x -> 
        fresh (f y) <= fresh (f x).
Proof. exact: lastkey_fun. Qed.

(* special case of fresh_fun when f = id *)
Lemma fresh_umpleq A (U : natmap A) (h1 h2 : U) : 
        [pcm h1 <= h2] ->
        valid h2 -> 
        fresh h1 <= fresh h2.
Proof. exact: lastkey_umpleq. Qed.

Lemma freshL A (U1 : pcm) (U2 : natmap A)
          (f : full_pcm_morph U1 U2) (x y : U1) :
        valid (x \+ y) -> 
        fresh (f x) <= fresh (f (x \+ y)).
Proof. exact: lastkeyL. Qed.

Lemma freshR A (U1 : pcm) (U2 : natmap A) 
          (f : full_pcm_morph U1 U2) (x y : U1) :
        valid (x \+ y) -> 
        fresh (f y) <= fresh (f (x \+ y)).
Proof. by apply: lastkeyR. Qed.

(***********************************************)
(***********************************************)
(* Executing up to (and including/excluding) t *)
(***********************************************)
(***********************************************)

Definition oexec_le V (U : natmap V) R (a : R -> V -> R) ks t (h : U) z0 :=
  oevalv a (&=ks `]-oo, t]) h z0.
Definition oexec_lt V (U : natmap V) R (a : R -> V -> R) ks t (h : U) z0 :=
  oevalv a (&=ks `]-oo, t[) h z0.

(* explicit rewrites to facilitate folding *)
Lemma oexleP V U R a ks t h z0 : 
        oevalv a (&=ks `]-oo, t]) h z0 = @oexec_le V U R a ks t h z0.
Proof. by []. Qed.
Lemma oexltP V U R a ks t h z0 : 
        oevalv a (&=ks `]-oo, t[) h z0 = @oexec_lt V U R a ks t h z0.
Proof. by []. Qed.

(* Main transfer lemmas *)

Lemma oexleE V (U : natmap V) R a t v (h : U) ks (z0 : R) :
        t \in ks -> (t, v) \In h ->
        oexec_le a ks t h z0 = a (oexec_lt a ks t h z0) v.
Proof.
by move=>K H; rewrite /oexec_le/oexec_lt eqsl_uxR K (oev_rconsP _ _ _ H).
Qed.

Arguments oexleE [V U R a t v h ks z0].

Lemma oexleNE V (U : natmap V) R a t (h : U) ks (z0 : R) :
        (t \notin ks) || (t \notin dom h) ->
        oexec_le a ks t h z0 = oexec_lt a ks t h z0.
Proof.
rewrite /oexec_le/oexec_lt; case K: (t \in ks)=>/= H; last first.
- rewrite (eqsl_uoxx (t1:=t) (t2:=t)); last by exact: sle_refl.
  by rewrite eqsl_kk1 /= K cats0.
rewrite [LHS]oevFK [RHS]oevFK; congr oeval.
by rewrite eqsl_uxR K filter_rcons (negbTE H).
Qed.

Arguments oexleNE [V U R a t h ks z0].

(**********************************************************)
(* Interaction of oexec_lt and oexec_le with constructors *)
(**********************************************************)

(* DEVCOMMENT *)
(*
Lemma oexlt0 V (U : natmap V) R a ks (h : U) (z0 : R) : oexec_lt a ks 0 h z0 = z0.
Proof. by rewrite /oexec_lt squo0. Qed.

Lemma oexle0 V R a ks (h : natmap V) (z0 : R) : oexec_le a ks 0 h z0 = z0.
Proof.
rewrite /oexec_le squx0; case: ifP=>//= _.
set xs := filter _ _; rewrite oevFK; set ys := filter _ _.
rewrite (_ : ys = [::]) //.
rewrite -[RHS](filter_pred0 xs); apply: eq_in_filter.
by move=>x; rewrite mem_filter=>/andP [/eqP ->]; rewrite cond_dom.
Qed.
*)
(* /DEVCOMMENT *)

Lemma oexlt_notin V (U : natmap V) R a ks t (h : U) (z0 : R) :
        t \notin ks ->
        oexec_lt a ks t h z0 = oevalv a ks h z0.
Proof. by move=>K; rewrite /oexec_lt eqsl_uL_notinE. Qed.

Arguments oexlt_notin [V U R a ks t h z0].

Lemma oexle_notin V (U : natmap V) R a ks t (h : U) (z0 : R) :
        t \notin ks ->
        oexec_le a ks t h z0 = oevalv a ks h z0.
Proof. by move=>K; rewrite /oexec_le eqsl_uL_notinE. Qed.

Arguments oexle_notin [V U R a ks t h z0].

Lemma oexlt_cat V (U : natmap V) R a ks1 ks2 t (h : U) (z0 : R) :
        t \notin ks1 ->
        oexec_lt a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_lt a ks1 t h z0
        else oexec_lt a ks2 t h (oexec_lt a ks1 t h z0).
Proof.
move=>T; rewrite /oexec_lt eqsl_uL_catE (negbTE T).
by rewrite oev_cat (eqsl_uL_notinE (s:=ks1)).
Qed.

Arguments oexlt_cat [V U R a ks1 ks2 t h z0].

Lemma oexle_cat V (U : natmap V) R a ks1 ks2 t (h : U) (z0 : R) :
        t \notin ks1 ->
        oexec_le a (ks1 ++ ks2) t h z0 =
        if t \in ks1 then oexec_le a ks1 t h z0
        else oexec_le a ks2 t h (oexec_le a ks1 t h z0).
Proof.
move=>T; rewrite /oexec_le eqsl_uL_catE (negbTE T).
by rewrite oev_cat (eqsl_uL_notinE (s:=ks1)).
Qed.

Arguments oexle_cat [V U R a ks1 ks2 t h z0].

Lemma oexlt_cons V (U : natmap V) R a ks k t v (h : U) (z0 : R) :
        (k, v) \In h -> t != k ->
        oexec_lt a (k :: ks) t h z0 = oexec_lt a ks t h (a z0 v).
Proof.
move=>H Ntk; rewrite /oexec_lt eqsl_uL_consE (negbTE Ntk) /=.
by move/In_find: H=>->.
Qed.

Arguments oexlt_cons [V U R a ks k t v h z0].

Lemma oexle_cons V (U : natmap V) R a ks k t v (h : U) (z0 : R) :
        (k, v) \In h ->
        oexec_le a (k :: ks) t h z0 =
        if t == k then a z0 v else oexec_le a ks t h (a z0 v).
Proof.
move=>H; rewrite /oexec_le eqsl_uL_consE.
by case: eqP=>/=; move/In_find: H=>->.
Qed.

Arguments oexle_cons [V U R a ks k t v h z0].

(* for oexlt, we need to cover the case when k == t *)
Lemma oexlt_cons_same V (U : natmap V) R a ks k (h : U) (z0 : R) :
        oexec_lt a (k :: ks) k h z0 = z0.
Proof. by rewrite /oexec_lt eqsl_uL_consL. Qed.

Arguments oexlt_cons_same {V U R a ks k h z0}.

Lemma oexlt_cons_notin V (U : natmap V) R a ks k t (h : U) (z0 : R) :
        k \notin dom h -> t != k ->
        oexec_lt a (k :: ks) t h z0 = oexec_lt a ks t h z0.
Proof.
move=>H Ntk; rewrite /oexec_lt eqsl_uL_consE (negbTE Ntk) /=.
by case: dom_find H=>//= -> _.
Qed.

Arguments oexlt_cons_notin [V U R a ks k t h z0].

(* for oexle, we have two "notin" lemmas *)
Lemma oexle_cons_same_notin V (U : natmap V) R a ks k (h : U) (z0 : R) :
        k \notin dom h -> oexec_le a (k :: ks) k h z0 = z0.
Proof.
move=>H.
by rewrite /oexec_le [in LHS]oevFK eqsl_uL_consL /= (negbTE H).
Qed.

Arguments oexle_cons_same_notin [V U R a ks k h z0].

Lemma oexle_cons_notin V (U : natmap V) R a ks k t (h : U) (z0 : R) :
        k \notin dom h -> t != k ->
        oexec_le a (k :: ks) t h z0 = oexec_le a ks t h z0.
Proof.
move=>H Ntk; rewrite /oexec_le [in LHS]oevFK [in RHS]oevFK.
by rewrite eqsl_uL_consE (negbTE Ntk) /= (negbTE H).
Qed.

Arguments oexle_cons_notin [V U R a ks k t h z0].

Lemma oexlt_rcons V (U : natmap V) R a ks k t (h : U) (z0 : R) :
        t \in ks ->
        oexec_lt a (rcons ks k) t h z0 = oexec_lt a ks t h z0.
Proof. by move=>T; rewrite /oexec_lt eqsl_uL_rconsE T. Qed.

Arguments oexlt_rcons [V U R a ks k t h z0].

Lemma oexle_rcons V (U : natmap V) R a ks k t (h : U) (z0 : R) :
        t \in ks ->
        oexec_le a (rcons ks k) t h z0 = oexec_le a ks t h z0.
Proof. by move=>T; rewrite /oexec_le eqsl_uL_rconsE T. Qed.

Arguments oexle_rcons [V U R a ks k t h z0].

Lemma oexlt_rcons_notin V (U : natmap V) R a ks k t v (h : U) (z0 : R) :
        (k, v) \In h -> t \notin ks -> t != k ->
        oexec_lt a (rcons ks k) t h z0 =
        a (oexec_lt a ks t h z0) v.
Proof.
move=>H T Ntk; rewrite /oexec_lt eqsl_uL_rconsE /= (negbTE T) Ntk.
by rewrite oev_rconsE eqsl_uL_notinE //; move/In_find: H=>->.
Qed.

Arguments oexlt_rcons_notin [V U R a ks k t v h z0].

Lemma oexle_rcons_notin V (U : natmap V) R a ks k t (h : U) (z0 : R) :
        t \notin ks ->
        oexec_le a (rcons ks k) t h z0 = oevalv a (rcons ks k) h z0.
Proof. by move=>T; rewrite /oexec_le eqsl_uL_rconsE (negbTE T). Qed.

Arguments oexle_rcons_notin [V U R a ks k t h z0].

(* in case of oexlt we must cover the case when t == k *)
Lemma oexlt_rcons_same V (U : natmap V) R a ks k (h : U) (z0 : R) :
        k \notin ks ->
        oexec_lt a (rcons ks k) k h z0 = oevalv a ks h z0.
Proof. by move=>N; rewrite /oexec_lt eqsl_uL_rconsE eqxx /= (negbTE N). Qed.

Arguments oexlt_rcons_same [V U R a ks k h z0].

(* in case of oexle, case t == k can be optimized *)
(* DEVCOMMENT *)
(* TODO doesn't simplify anything now, remove? *)
(* /DEVCOMMENT *)
Lemma oexle_rcons_same V (U : natmap V) R a ks k (h : U) (z0 : R) :
        k \notin ks ->
        oexec_le a (rcons ks k) k h z0 = oevalv a (rcons ks k) h z0.
Proof. exact: oexle_rcons_notin. Qed.

Arguments oexle_rcons_same [V U R a ks k h z0].

(* in case of oexle, when we know the value at k *)
(* we can further expand the right-hand side *)
Lemma oexle_rcons_notin_in V (U : natmap V) R a ks k t v (h : U) (z0 : R) :
        (k, v) \In h -> t \notin ks ->
        oexec_le a (rcons ks k) t h z0 = a (oexec_le a ks t h z0) v.
Proof.
move=>H T; rewrite oexle_rcons_notin // oev_rconsE.
by move/In_find: (H)=>->; rewrite oexleNE ?T // /oexec_lt eqsl_uL_notinE.
Qed.

Arguments oexle_rcons_notin_in [V U R a ks k t v h z0].

(* oexlt/oexle filter lemmas *)

Lemma oexlt_umfilt V (U : natmap V) R a ks p t (h : U) (z0 : R) :
        oexec_lt a ks t (um_filterk p h) z0 =
        oevalv a (filter p (&=ks `]-oo, t[)) h z0.
Proof. by rewrite /oexec_lt oev_filter. Qed.

Arguments oexlt_umfilt {V U R a ks p t h z0}.

Lemma oexle_umfilt V (U : natmap V) R a ks p t (h : U) (z0 : R) :
        oexec_le a ks t (um_filterk p h) z0 =
        oevalv a (filter p (&=ks `]-oo, t])) h z0.
Proof. by rewrite /oexec_le oev_filter. Qed.

Arguments oexle_umfilt {V U R a ks p t h z0}.

(* two somewhat simpler rewrites under a condition *)
Lemma oexlt_umfiltN V (U : natmap V) R a ks p t (h : U) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_lt a ks t (um_filterk p h) z0 =
        oexec_lt a (filter p ks) t h z0.
Proof.
move=>H; rewrite /oexec_lt oev_umfilt eqsl_filterL //=.
apply: eq_in_oevK; rewrite -!filter_predI; apply: eq_in_filter=>k Ks /=.
by case D : (k \in dom h)=>//=; case/In_domX: D=>v /In_find ->.
Qed.

Arguments oexlt_umfiltN [V U R a ks p t h z0].

Lemma oexle_umfiltN V (U : natmap V) R a ks p t (h : U) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_le a ks t (um_filterk p h) z0 =
        oexec_le a (filter p ks) t h z0.
Proof.
move=>H; rewrite /oexec_le oev_umfilt eqsl_filterL //=.
apply: eq_in_oevK; rewrite -!filter_predI; apply: eq_in_filter=>k Ks /=.
by case D : (k \in dom h)=>//=; case/In_domX: D=>v /In_find ->.
Qed.

Arguments oexle_umfiltN [V U R a ks p t h z0].

(* restating the last two lemmas for the other direction *)
(* DEVCOMMENT *)
(* TODO why not just state them like this initially? *)
(* /DEVCOMMENT *)
Lemma oexlt_filter V (U : natmap V) R a ks p t (h : U) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_lt a (filter p ks) t h z0 =
        oexec_lt a ks t (um_filterk p h) z0.
Proof. by move=>H; rewrite (oexlt_umfiltN H). Qed.

Lemma oexle_filter V (U : natmap V) R a ks p t (h : U) (z0 : R) :
        (t \notin ks) || (p t) ->
        oexec_le a (filter p ks) t h z0 =
        oexec_le a ks t (um_filterk p h) z0.
Proof. by move=>H; rewrite (oexle_umfiltN H). Qed.

(* interaction with the map *)

Lemma oexlt_filter_dom V (U : natmap V) R a ks t (h : U) (z0 : R) :
        (t \notin ks) || (t \in dom h) ->
        oexec_lt a ks t h z0 =
        oexec_lt a (filter (mem (dom h)) ks) t h z0.
Proof. by move=>H; rewrite oexlt_filter // umfiltk_dom'. Qed.

Lemma oexle_filter_dom V (U : natmap V) R a ks t (h : U) (z0 : R) :
        (t \notin ks) || (t \in dom h) ->
        oexec_le a ks t h z0 =
        oexec_le a (filter (mem (dom h)) ks) t h z0.
Proof. by move=>H; rewrite oexle_filter // umfiltk_dom'. Qed.

(* interaction of oexlt, oexle and last *)

Lemma oexlt_oexle_last V (U : natmap V) R a k ks t (h : U) (z0 : R) :
        uniq (k::ks) -> t != k ->
        oexec_lt a (k::ks) t h z0 =
        oexec_le a (k::ks) (last k (&=ks `]-oo, t[)) h z0.
Proof.
move=>Uq Ntk; rewrite /oexec_lt/oexec_le [LHS]oevFK [RHS]oevFK.
by rewrite eqsl_uox_last.
Qed.

Lemma oev_oexle_last V (U : natmap V) R a k ks (h : U) (z0 : R) :
        uniq (k::ks) ->
        oevalv a (k::ks) h z0 =
        oexec_le a (k::ks) (last k ks) h z0.
Proof.
case/andP=>U1 U2; rewrite /oexec_le eqsl_uL_consE.
case: eqP=>/= [/last_nochange|/eqP/last_change H].
- by rewrite (negbTE U1)=>/eqP->.
by congr oeval; apply/eqsl_lastR_uniq.
Qed.

(*******************************************************)
(* oexlt/oexle on endpoints of intervals of invariance *)
(*******************************************************)

(* these can be called "induction" lemmas over the interval *)

Definition oex_inv V (U : natmap V) R (P : R -> Prop) a ks (h : U) (z0 : R) :=
  forall k v, (k, v) \In h ->
    let z := oexec_lt a ks k h z0 in P z -> P (a z v).

(* The naming schema in these lemmas is based on backward reasoning *)
(* E.g., the suffix ox means we're proving an lt_fact (o) from le_fact (x) *)

(* two-sided intervals *)

Lemma oex_ox V (U : natmap V) R (P : R -> Prop) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <[ks] t2 ->
        {in &=ks `]t1, t2[, oex_inv P a ks h z0} ->
        P (oexec_le a ks t1 h z0) -> P (oexec_lt a ks t2 h z0).
Proof.
move=>Uq T IH P0; rewrite /oexec_lt (eqsl_uxoo T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `]t1, t2[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]t1, t2[): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_oo: (K)=>// [_ T1K T2K].
suff {IH Uq K}-> : ks1 = &=ks `]t1, k[ by rewrite -eqsl_uxoo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first.
- rewrite !lteBSide /= leEnat -seqlt_unlockE -seqle_unlock.
  by rewrite T1K (sltW T2K).
rewrite eqsl_xoL T2K /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

(* one can try to derive the next lemma from the previous *)
(* but we need to reason about successor of t1 in ks *)
(* which we don't have yet. Hence, we prove the lemma directly *)
(* using the same approach as in the previous lemma. *)

Lemma oex_oo V (U : natmap V) R (P : R -> Prop) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2[, oex_inv P a ks h z0} ->
        P (oexec_lt a ks t1 h z0) -> P (oexec_lt a ks t2 h z0).
Proof.
move=>Uq T IH P0; rewrite /oexec_lt (eqsl_uoxo T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `[t1, t2[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `[t1, t2[): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_xo: (K)=>// [_ T1K T2K].
suff {IH Uq K}-> : ks1 = &=ks `[t1, k[ by rewrite -eqsl_uoxo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first.
- by rewrite !lteBSide /= !leEnat -!seqle_unlock T1K (sltW T2K).
rewrite (eqsl_xoL k) T2K /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_xo V (U : natmap V) R (P : R -> Prop) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2], oex_inv P a ks h z0} ->
        P (oexec_lt a ks t1 h z0) -> P (oexec_le a ks t2 h z0).
Proof.
move=>Uq T IH P0; rewrite /oexec_le (eqsl_uoxx T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `[t1, t2] by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `[t1, t2]): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_xx: (K)=>// [Ks T1K T2K].
suff {IH Uq K}-> : ks1 = &=ks `[t1, k[ by rewrite -eqsl_uoxo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first.
- by rewrite /order.Order.le/=/order.Order.le/= -!seqle_unlock T1K T2K.
rewrite eqsl_xxL T2K Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_xx V (U : natmap V) R (P : R -> Prop) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `]t1, t2], oex_inv P a ks h z0} ->
        P (oexec_le a ks t1 h z0) -> P (oexec_le a ks t2 h z0).
Proof.
move=>Uq T IH P0; rewrite /oexec_le (eqsl_uxox T) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `]t1, t2] by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]t1, t2]): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_ox: (K)=>// [Ks T1K T2K].
suff {IH Uq K}-> : ks1 = &=ks `]t1, k[ by rewrite -eqsl_uxoo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first. 
- rewrite /order.Order.le/=/order.Order.le/=/order.Order.lt /=.
  by rewrite -seqlt_unlock -seqle_unlock T1K T2K.
rewrite eqsl_xxL T2K Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Arguments oex_ox [V U R] P [a ks h t1 t2 z0].
Arguments oex_oo [V U R] P [a ks h t1 t2 z0].
Arguments oex_xo [V U R] P [a ks h t1 t2 z0].
Arguments oex_xx [V U R] P [a ks h t1 t2 z0].

(* one-sided intervals *)

Lemma oex_ux V (U : natmap V) R (P : R -> Prop) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `]t,+oo[, oex_inv P a ks h z0} ->
        P (oexec_le a ks t h z0) -> P (oevalv a ks h z0).
Proof.
move=>Uq IH P0; rewrite (eqsl_uxou ks t) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `]t, +oo[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]t, +oo[): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_ou: (K)=>// [Ks TK].
suff {IH Uq K}-> : ks1 = &=ks `]t, k[ by rewrite -eqsl_uxoo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first. 
- by rewrite /order.Order.le/=/order.Order.lt/= -seqlt_unlock TK.
rewrite eqsl_xuL Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_uo V (U : natmap V) R (P : R -> Prop) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `[t,+oo[, oex_inv P a ks h z0} ->
        P (oexec_lt a ks t h z0) -> P (oevalv a ks h z0).
Proof.
move=>Uq IH P0; rewrite (eqsl_uoxu ks t) oev_cat.
apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->; rewrite -oev_cat.
have K : k \in &=ks `[t, +oo[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `[t, +oo[): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_xu: (K)=>// [Ks TK].
suff {IH Uq K}-> : ks1 = &=ks `[t, k[ by rewrite -eqsl_uoxo //; apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first. 
- by rewrite /order.Order.le/=/order.Order.le/= -seqle_unlock TK.
rewrite eqsl_xuL Ks => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_xu V (U : natmap V) R (P : R -> Prop) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t], oex_inv P a ks h z0} ->
        P z0 -> P (oexec_le a ks t h z0).
Proof.
move=>Uq IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have K : k \in &=ks `]-oo, t] by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]-oo, t]): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_ux: (K)=>// [Ks TK].
suff {IH Uq K}-> : ks1 = &=ks `]-oo, k[ by apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) //=; last first.
- by rewrite /order.Order.le/=/order.Order.le/= -seqle_unlock.
rewrite eqsl_xxL TK Ks /= => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Lemma oex_ou V (U : natmap V) R (P : R -> Prop) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t[, oex_inv P a ks h z0} ->
        P z0 -> P (oexec_lt a ks t h z0).
Proof.
move=>Uq IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have K : k \in &=ks `]-oo, t[ by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move/(eqslice_uniq `]-oo, t[): Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
case/mem_uo: (K)=>// [Ks TK].
suff {IH Uq K}-> : ks1 = &=ks `]-oo, k[ by apply: IH.
move: Eh; rewrite (eqslice_split (b:=true) (x:=k)) /=; last first.
- by rewrite lteBSide /= leEnat -seqle_unlock (sltW TK).
rewrite eqsl_xoL TK => Eh; rewrite (cat_cancel _ _ Eh) //.
by apply: eqsliceRO_notin.
Qed.

Arguments oex_ux [V U R] P [a ks h t z0].
Arguments oex_uo [V U R] P [a ks h t z0].
Arguments oex_xu [V U R] P [a ks h t z0].
Arguments oex_ou [V U R] P [a ks h t z0].

(* whole list *)

Lemma oex_uu V (U : natmap V) R (P : R -> Prop) a ks (h : U) (z0 : R) :
        uniq ks ->
        {in ks, oex_inv P a ks h z0} ->
        P z0 -> P (oevalv a ks h z0).
Proof.
move=>Uq IH P0; apply: oev_indX=>// k ks1 ks2 v _ Kh Eh ->.
have K : k \in ks by rewrite Eh mem_cat inE eqxx orbT.
have Nk : k \notin ks1.
- move: Uq.
  by rewrite Eh cat_uniq /= negb_or -andbA; case/and5P.
suff -> : ks1 = &=ks `]-oo, k[ by apply: IH.
move: Eh; rewrite {1}(eqsl_uxou ks k) eqsl_uxR K -cats1 -catA /= => Eh.
by rewrite (cat_cancel _ _ Eh) //=; apply: eqsliceRO_notin.
Qed.

Arguments oex_uu [V U R] P [a ks h z0].

(**********************************************)
(* functional versions of the interval lemmas *)
(**********************************************)

Definition oexF_inv V (U : natmap V) R X (f : R -> X) a ks (h : U) (z0 : R) :=
  forall k v, (k, v) \In h ->
    let z := oexec_lt a ks k h z0 in f (a z v) = f z.

(* two-sided intervals *)

Lemma oexF_ox V (U : natmap V) R X (f : R -> X) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <[ks] t2 ->
        {in &=ks `]t1, t2[, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t2 h z0) = f (oexec_le a ks t1 h z0).
Proof.
move=>Uq T H; pose P := fun x => f x = f (oexec_le a ks t1 h z0).
by apply: (oex_ox P) T _ _=>// x S v K E ; rewrite /P -E; apply: H.
Qed.

Lemma oexF_oo V (U : natmap V) R X (f : R -> X) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2[, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t2 h z0) = f (oexec_lt a ks t1 h z0).
Proof.
move=>Uq T H; pose P := fun x => f x = f (oexec_lt a ks t1 h z0).
by apply: (oex_oo P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xo V (U : natmap V) R X (f : R -> X) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `[t1, t2], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t2 h z0) = f (oexec_lt a ks t1 h z0).
Proof.
move=>Uq T H; pose P := fun x => f x = f (oexec_lt a ks t1 h z0).
by apply: (oex_xo P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xx V (U : natmap V) R X (f : R -> X) a ks (h : U) t1 t2 (z0 : R) :
        uniq ks -> t1 <=[ks] t2 ->
        {in &=ks `]t1, t2], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t2 h z0) = f (oexec_le a ks t1 h z0).
Proof.
move=>Uq T H; pose P := fun x => f x = f (oexec_le a ks t1 h z0).
by apply: (oex_xx P) T _ _=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Arguments oexF_ox [V U R X] f [a ks h t1 t2 z0].
Arguments oexF_oo [V U R X] f [a ks h t1 t2 z0].
Arguments oexF_xo [V U R X] f [a ks h t1 t2 z0].
Arguments oexF_xx [V U R X] f [a ks h t1 t2 z0].

(* one-sided intervals *)

Lemma oexF_ux V (U : natmap V) R X (f : R -> X) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `]t, +oo[, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f (oexec_le a ks t h z0).
Proof.
move=>Uq H; pose P := fun x => f x = f (oexec_le a ks t h z0).
by apply: (oex_ux P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_uo V (U : natmap V) R X (f : R -> X) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `[t, +oo[, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f (oexec_lt a ks t h z0).
Proof.
move=>Uq H; pose P := fun x => f x = f (oexec_lt a ks t h z0).
by apply: (oex_uo P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_xu V (U : natmap V) R X (f : R -> X) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t], oexF_inv f a ks h z0} ->
        f (oexec_le a ks t h z0) = f z0.
Proof.
move=>Uq H; pose P := fun x => f x = f z0.
by apply: (oex_xu P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Lemma oexF_ou V (U : natmap V) R X (f : R -> X) a ks (h : U) t (z0 : R) :
        uniq ks ->
        {in &=ks `]-oo, t[, oexF_inv f a ks h z0} ->
        f (oexec_lt a ks t h z0) = f z0.
Proof.
move=>Uq H; pose P := fun x => f x = f z0.
by apply: (oex_ou P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Arguments oexF_ux [V U R X] f [a ks h t z0].
Arguments oexF_uo [V U R X] f [a ks h t z0].
Arguments oexF_xu [V U R X] f [a ks h t z0].
Arguments oexF_ou [V U R X] f [a ks h t z0].

(* whole list *)

Lemma oexF_uu V (U : natmap V) R X (f : R -> X) a ks (h : U) (z0 : R) :
        uniq ks ->
        {in ks, oexF_inv f a ks h z0} ->
        f (oevalv a ks h z0) = f z0.
Proof.
move=>Uq H; pose P := fun x => f x = f z0.
by apply: (oex_uu P)=>// x S v K E; rewrite /P -E; apply: H.
Qed.

Arguments oexF_uu [V U R X] f [a ks h z0].

(* we can now combine the split lemmas with *)
(* cons properties of oeval, to obtain a point-split *)
(* when the middle point is in the map *)

Lemma oev2_split V (U : natmap V) R a t1 v (h : U) ks (z0 : R) :
        t1 \in ks -> (t1, v) \In h ->
        oevalv a ks h z0 =
        oevalv a (&=ks `]t1, +oo[) h (a (oexec_lt a ks t1 h z0) v).
Proof.
move=>D H; rewrite {1}(eqsl_uoxu ks t1) oev_cat.
by rewrite eqsl_xuL D /=; move/In_find: H=>->.
Qed.

Arguments oev2_split [V U R a t1 v h ks z0] _ _.

Lemma oex2_split V (U : natmap V) R a t1 t2 v (h : U) ks (z0 : R) :
        t1 <[ks] t2 -> (t1, v) \In h ->
        oexec_lt a ks t2 h z0 =
        oevalv a (&=ks `]t1, t2[) h (a (oexec_lt a ks t1 h z0) v).
Proof.
move=>T H; rewrite /oexec_lt.
rewrite (eqsl_uoxo (sltW T)) oev_cat eqsl_xoL T /=.
by move/In_find: H=>->.
Qed.

Arguments oex2_split [V U R a t1 t2 v h ks z0] _ _.

(* we frequently iterate oex2_split, so the following saves verbiage *)
Lemma oex3_split V (U : natmap V) R a t1 t2 t3 v1 v2 (h : U) ks (z0 : R) :
        t1 <[ks] t2 -> (t1, v1) \In h ->
        t2 <[ks] t3 -> (t2, v2) \In h ->
        oexec_lt a ks t3 h z0 =
        oevalv a (&=ks `]t2, t3[) h
                 (a (oevalv a (&=ks `]t1, t2[) h
                    (a (oexec_lt a ks t1 h z0) v1))
                 v2).
Proof.
move=>T1 H1 T2 H2.
by rewrite (oex2_split T2 H2) (oex2_split T1 H1).
Qed.

Arguments oex3_split [V U R a t1 t2 t3 v1 v2 h ks z0] _ _ _ _.

(******************************************)
(* Interaction of consec with oexlt/oexle *)
(******************************************)

Lemma oexlt_consec V (U : natmap V) R a ks t1 t2 (h : U) (z0 : R) :
        uniq ks ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 = oexec_le a ks t1 h z0.
Proof.
move=>Uq C; apply: (oexF_ox id)=>//; first by apply: consec_slt.
by move=>x; rewrite consec_oo.
Qed.

Arguments oexlt_consec [V U R a ks t1 t2 h z0].

(* the following is direct *)
Lemma oexlt_split V (U : natmap V) R a x1 t1 t2 x2 (h : U) (z0 : R) :
        uniq (x1++t1::t2::x2) ->
        oexec_lt a (x1++t1::t2::x2) t2 h z0 =
        oexec_le a (x1++t1::t2::x2) t1 h z0.
Proof.
move=>Uq; apply: oexlt_consec=>//; apply/consecP_split=>//.
- by rewrite mem_cat !inE eqxx !orbT.
by exists x1, x2.
Qed.

Lemma oexlt_consec_in V (U : natmap V) R a t1 t2 v (h : U) ks (z0 : R) :
        uniq ks ->
        (t1, v) \In h ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 = a (oexec_lt a ks t1 h z0) v.
Proof.
move=>Uq H C; move/slt_memE: (consec_slt C)=>T.
by rewrite (oexlt_consec Uq C) (oexleE T H).
Qed.

Lemma oexlt_consec_fst V (U : natmap V) R a t (h : U) k ks (z0 : R) :
        uniq (k::ks) -> k \notin dom h -> t \in k::ks ->
        consec (k::ks) k t ->
        oexec_lt a (k::ks) t h z0 = z0.
Proof.
move=>Uq K T C; case/(consecP_split _ Uq T): C=>xs1 [xs2] X.
case: xs1 X Uq {T}=>[|x xs1]; last first.
- by case=>->-> /=; rewrite mem_cat inE eqxx !orbT.
case=>->{ks}; rewrite /= inE negb_or -andbA; case/and4P=>U1 U2 U3 U4.
rewrite oexlt_cons_notin ?inE 1?negb_or ?(eq_sym t) ?U1 ?U2 //.
by rewrite oexlt_cons_same.
Qed.

Lemma oexlt_consec_find V (U : natmap V) R a t1 t2 (h : U) ks (z0 : R) :
        uniq ks ->
        consec ks t1 t2 ->
        oexec_lt a ks t2 h z0 =
        if find t1 h is Some e
          then a (oexec_lt a ks t1 h z0) e
          else oexec_lt a ks t1 h z0.
Proof.
move=>Uq C; rewrite (oexlt_consec Uq C).
case E : (find t1 h)=>[e|]; first by move/In_find: E=>/(oexleE (consec_mem C)) ->.
by rewrite oexleNE // orbC; move/In_findN: E=>->.
Qed.

Arguments oexlt_consec_find [V U R a t1 t2 h ks z0].

Lemma oexlt_last V (U : natmap V) R a t2 (h : U) ks (z0 : R) :
        uniq ks ->
        t2 \notin ks ->
        oexec_lt a ks t2 h z0 = 
        if ks is k :: ks' then 
          if last k ks' \in dom h then 
            oexec_le a ks (last k ks') h z0
          else oexec_lt a ks (last k ks') h z0
        else z0.
Proof.
case: ks=>[|k ks] Uq //= T2.
have C : consec (k :: ks) (last k ks) t2.
- by rewrite (consecP_lastE k) // mem_last /=.
rewrite (oexlt_consec_find Uq C).
case: dom_find=>// v /In_find E _.
by rewrite -oexleE // mem_last.
Qed.

Lemma oexlt_last0 V (U : natmap V) R a t2 (h : U) ks (z0 : R) :
        uniq (0::ks) ->
        t2 \notin 0::ks ->
        oexec_lt a ks t2 h z0 = 
        if last 0 ks \in dom h then 
          oexec_le a ks (last 0 ks) h z0
        else oexec_lt a ks (last 0 ks) h z0.
Proof.
move=>Uq T2.
have D : 0 \notin dom h by rewrite cond_dom. 
have N : t2 != 0 by case: eqP T2=>// ->. 
rewrite -(oexlt_cons_notin D N) oexlt_last //.
case: ifP=>L.
- by rewrite oexle_cons_notin // (dom_cond L).
case: ks Uq {N T2 D L}=>[|k ks] //= Uq.
rewrite oexlt_cons_notin ?cond_dom //.
apply/negP=>/eqP N.
by rewrite -N (mem_last k ks) in Uq.
Qed.

(* The lemmas past this point are currently used for some examples, *)
(* but will be deprecated and removed in future releases *)

(*******************)
(*******************)
(* Gapless natmaps *)
(*******************)
(*******************)

Section Gapless.
Variables (A : Type) (U : natmap A).
Implicit Type h : U.

Definition gapless h := forall k, 0 < k <= last_key h -> k \in dom h.

Definition gaplessb h := all (fun t => t \in dom h) (iota 1 (last_key h)).

Lemma gaplessP h : reflect (gapless h) (gaplessb h).
Proof.
case V: (gaplessb h);constructor; last first.
- move=>H;apply/(elimF idP V)/allP=>?.
  by rewrite mem_iota add1n ltnS=>?; apply/H.
by move/allP:V=>H t;move: (H t);rewrite mem_iota add1n ltnS.
Qed.

Lemma gp_undef : gapless undef.
Proof. by move=>k; rewrite lastkey_undef; case: k. Qed.

Lemma gp0 : gapless Unit.
Proof. by move=>k; rewrite lastkey0; case: k. Qed.

Lemma gp_fresh h u : gapless (pts (fresh h) u \+ h) <-> gapless h.
Proof.
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undef.
split=>H k; move: (V); rewrite -(freshPtUnV u (leqnn _))=>V'; last first.
- rewrite lastkeyPtUn // domPtUn inE V' /= (leq_eqVlt k) eq_sym.
  by move: (H k); rewrite -(ltnS k); case: (ltngtP k (last_key h).+1).
rewrite -(ltnS k) -/(fresh h); case/andP=>Z N.
move: (H k); rewrite lastkeyPtUn // domPtUn inE V' Z /= leq_eqVlt eq_sym.
by case: ltngtP N=>//= _ _; apply.
Qed.

Lemma gpPtUn h k u :
        valid (pts k u \+ h) ->
        gapless (pts k u \+ h) -> last_key h < k -> k = fresh h.
Proof.
move=>V C N; apply/eqP/contraT=>X.
have Y : fresh h < k by rewrite leq_eqVlt eq_sym (negbTE X) in N.
suff Z : last_key (pts k u \+ h) = k.
- move: (C (fresh h)); rewrite Z (leq_eqVlt _ k) Y orbT andbT; move/(_ (erefl _)).
  by rewrite domPtUn inE (negbTE X) /=; case/andP=>_ /dom_fresh; rewrite ltnn. 
by rewrite lastkeyPtUn // (validR V). 
Qed.

Lemma gaplessPtUnE u2 u1 h k :
        gapless (pts k u1 \+ h) <-> gapless (pts k u2 \+ h).
Proof.
rewrite /gapless (lastkeyPtUnEX u2); split=>H t /H;
by rewrite !domPtUn !inE !validPtUn.
Qed.

Lemma gapless_pleq h1 h2 :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] ->
        exists h, h2 = h1 \+ h /\ forall k, k \in dom h -> last_key h1 < k.
Proof.
move=>G V H; case: H V=>h ->{h2} V; exists h; split=>// k D.
apply: contraR (dom_inNR V D)=>H; apply: G; move/dom_cond: D=>/= D.
by rewrite lt0n D leqNgt.
Qed.

End Gapless.

Arguments gp_fresh [A U][h] u.

(*****************************)
(*****************************)
(* Natmaps with binary range *)
(*****************************)
(*****************************)

Section AtVal.
Variables (A : Type) (U : natmap (A * A)).
Implicit Type h : U.

Definition atval v t h := oapp snd v (find t h).

Lemma atvalUn v t h1 h2 :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        (forall k : nat, k \in dom h2 -> last_key h1 < k) ->
        atval v t (h1 \+ h2) = atval v t h1.
Proof.
move=>V K H; rewrite /atval findUnR //.
by case: ifP=>// /H; rewrite ltnNge K.
Qed.

Lemma umpleq_atval v t h1 h2 :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        atval v t h2 = atval v t h1.
Proof.
move=>G V H K; case/(gapless_pleq G V): {V} H (V)=>h [->{h2} H] V.
by apply: atvalUn.
Qed.

Definition last_atval v h := atval v (last_key h) h.

Lemma lastatval0 v : last_atval v Unit = v.
Proof. by rewrite /last_atval /atval lastkey0 find0E. Qed.

Lemma lastatval_undef v : last_atval v undef = v.
Proof. by rewrite /last_atval /atval lastkey_undef find_undef. Qed.

Lemma lastatvalPt v p x : p != 0 -> last_atval v (pts p x) = x.2.
Proof.
by move=>V; rewrite /last_atval /atval lastkeyPt // findPt /= V.
Qed.

Lemma lastatval_fresh v x h :
        valid h -> last_atval v (pts (fresh h) x \+ h) = x.2.
Proof.
by move=>V; rewrite /last_atval /atval lastkeyPtUn // findPtUn // freshPtUnV.
Qed.

Lemma lastatvalUn v h1 h2 :
        last_atval v (h1 \+ h2) =
        if valid (h1 \+ h2) then
          if last_key h1 < last_key h2 then last_atval v h2 else last_atval v h1
        else v.
Proof.
rewrite /last_atval /atval lastkeyUn maxnC /maxn.
case: ifP; last by move/negbT/invalidE=>->; rewrite find_undef.
case: (ltngtP (last_key h1) (last_key h2)) => N V.
- by rewrite findUnR //; case: lastkeyP N.
- by rewrite findUnL //; case: lastkeyP N.
by rewrite !(lastkeyUn0 V N) unitL lastkey0 find0E.
Qed.

Lemma lastatval_freshUn v x h1 h2 :
        valid h1 -> [pcm h2 <= h1] ->
        last_atval v (pts (fresh h1) x \+ h2) = x.2.
Proof.
move=>V H; move: (pleqV H V)=>V2; move: (fresh_mono (umpleq_subdom V H))=>N.
by rewrite /last_atval /atval lastkeyPtUn // findPtUn // freshPtUnV.
Qed.

Lemma lastatval_indom v h :
        last_atval v h <> v -> last_key h \in dom h.
Proof. by rewrite /last_atval /atval; case: dom_find=>// ->. Qed.

End AtVal.

(* in case A = bool *)
Lemma lastatval_indomb (U : natmap (bool*bool)) (h : U) :
        last_atval false h -> last_key h \in dom h.
Proof. by move=>H; apply: (lastatval_indom (v:=false)); rewrite H. Qed.

(* Continuous maps with binary range *)

Section Continuous.
Variables (A : Type) (U : natmap (A * A)).
Implicit Type h : U.

Definition continuous v h :=
  forall k x, find k.+1 h = Some x -> oapp snd v (find k h) = x.1.

Lemma cn_undef v : continuous v undef.
Proof. by move=>x w; rewrite find_undef. Qed.

Lemma cn0 v : continuous v Unit.
Proof. by move=>x w; rewrite find0E. Qed.

Lemma cn_fresh v h x :
        valid h ->
        continuous v (pts (fresh h) x \+ h) <->
        continuous v h /\ last_atval v h = x.1.
Proof.
rewrite -(freshPtUnV x (leqnn _))=>V; split; last first.
- case=>C H k y; rewrite !findPtUn2 // eqSS; case: ltngtP=>N.
  - by rewrite ltn_eqF; [apply: C | apply: (ltn_trans N _)].
  - by move/find_some/dom_fresh/(ltn_trans N); rewrite ltnn.
  by case=><-; rewrite N ltn_eqF.
move=>C; split; last first.
- move: (C (last_key h) x).
  by rewrite !findPtUn2 // eqxx ltn_eqF //; apply.
move=>k w; case: (ltnP k (last_key h))=>N; last first.
- by move/find_some/dom_fresh/(leq_ltn_trans N); rewrite ltnn.
by move: (C k w); rewrite !findPtUn2 // eqSS !ltn_eqF // (ltn_trans N _).
Qed.

Lemma cn_sub v h x y k :
        valid (pts k.+1 (x, y) \+ h) -> continuous v (pts k.+1 (x, y) \+ h) ->
        oapp snd v (find k h) = x.
Proof.
by move=>V /(_ k (x, y)); rewrite !findPtUn2 // eqxx ltn_eqF //; apply.
Qed.

End Continuous.

Arguments cn_fresh [A U][v][h][x] _.

(* Complete natmaps with binary range *)

Section Complete.
Variables (A : Type) (U : natmap (A * A)).
Implicit Type h : U.

Definition complete v0 h vn :=
  [/\ valid h, gapless h, continuous v0 h & last_atval v0 h = vn].

Lemma cm_valid v0 h vn : complete v0 h vn -> valid h.
Proof. by case. Qed.

Lemma cm0 v : complete v Unit v.
Proof. by split=>//; [apply: gp0|apply: cn0|rewrite lastatval0]. Qed.

Lemma cm_fresh v0 vn h x :
        complete v0 (pts (fresh h) x \+ h) vn <-> vn = x.2 /\ complete v0 h x.1.
Proof.
split.
- by case=>/validR V /gp_fresh G /(cn_fresh V) []; rewrite lastatval_fresh.
case=>-> [V] /(gp_fresh x) G C E; split=>//;
by [rewrite freshPtUnV|apply/(cn_fresh V)| rewrite lastatval_fresh].
Qed.

Lemma cmPtUn v0 vn h k x :
        complete v0 (pts k x \+ h) vn -> last_key h < k -> k = fresh h.
Proof. by case=>V /(gpPtUn V). Qed.

Lemma cmPt v0 vn k x : complete v0 (pts k x) vn -> k = 1 /\ x = (v0, vn).
Proof.
case; rewrite validPt; case: k=>//= k _ /(_ 1).
rewrite lastkeyPt //= domPt inE /= => /(_ (erefl _))/eqP ->.
move/(_ 0 x); rewrite findPt findPt2 /= => -> //.
by rewrite /last_atval lastkeyPt // /atval findPt /= => <-; case: x.
Qed.

Lemma cmCons v0 vn k x h :
        complete v0 (pts k x \+ h) vn -> last_key h < k ->
         [/\ k = fresh h, vn = x.2 & complete v0 h x.1].
Proof. by move=>C H; move: {C} (cmPtUn C H) (C)=>-> /cm_fresh []. Qed.

End Complete.

Prenex Implicits cm_valid cmPt.

(************************)
(************************)
(************************)
(* Surgery on histories *)
(* using leq filtering  *)
(************************)
(************************)
(************************)

Notation le t := (fun '(k, _) => k <= t).
Notation lt t := (fun '(k, _) => k < t).

Lemma pts_sub V t1 t2 : t1 <= t2 -> subpred (T:=nat*V) (le t1) (le t2).
Proof. by move=>T [k v] /leq_trans; apply. Qed.

Lemma pts_sub_lt V t1 t2 : t1 < t2 -> subpred (T:=nat*V) (le t1) (lt t2).
Proof. by move=>T [k v] /leq_ltn_trans; apply. Qed.

Lemma ptsD V t1 t2 :
        t1 <= t2 -> predD (le t2) (le t1) =1 
                    (fun kv : (nat * V) =>
                       let '(k, v) := kv in t1 < k <= t2).  
Proof. by move=>T [k v] /=; rewrite -ltnNge. Qed.

Lemma ptsD_lt V t1 t2 :
        t1 < t2 -> predD (lt t2) (le t1) =1 
                   (fun kv : nat * V => 
                     let '(k, v) := kv in t1 < k < t2).
Proof. by move=>T [k v] /=; rewrite -ltnNge. Qed.

Lemma lastkey_umfilt_leq A (U : natmap A) (h : U) t : 
        last_key (um_filterk (leq^~ t) h) <= t.
Proof.
case V : (valid h); last first.
- by move/negbT/invalidE: V=>->; rewrite pfundef lastkey_undef.
set j := um_filterk _ _.
have V' : valid j by rewrite pfV.
case E : (unitb j); first by move/unitbP: E=>->; rewrite lastkey0.
have : last_key j \in dom j by case: lastkeyP V' E.
by case/In_dom_umfilt=>v [].
Qed.

Lemma lastkey_umfilt_dom A (U : natmap A) (h : U) t :
        last_key (um_filterk (leq^~ t) h) <= last_key h.
Proof. by apply: lastkey_mono; apply: omf_subdom. Qed.

Lemma umfilt_le_last A (U : natmap A) (h : U) t :
        last_key h <= t -> um_filter (le t) h = h.
Proof.
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite pfundef.
move=>N; rewrite -{2}[h]umfilt_predT; apply/eq_in_umfilt.
by case=>k v /In_dom/dom_lastkey/leq_trans; apply.
Qed.

Lemma umfilt_last A (U : natmap A) (h : U) : 
        um_filter (le (last_key h)) h = h.
Proof. by apply: umfilt_le_last. Qed.

Lemma umfilt_le_fresh A (U : natmap A) (h : U) : 
        um_filter (le (fresh h)) h = h.
Proof. by apply: umfilt_le_last; apply: ltnW. Qed.

Lemma umfilt_le0 A (U : natmap A) (h : U) t :
        valid h -> {in dom h, forall k, t < k} -> um_filter (le t) h = Unit.
Proof.
move=>V D; rewrite -(umfilt_pred0 V).
apply/eq_in_umfilt; case=>k v [/= _][z E]; subst h.
rewrite leqNgt; apply: contraTF (D k _)=>//.
by rewrite domPtUn inE V eqxx.
Qed.

Lemma umfilt_le_split A (U : natmap A) (h : U) t1 t2 :
        t1 <= t2 ->
        um_filter (le t2) h =
        um_filter (le t1) h \+ um_filter (fun '(k, _) => t1 < k <= t2) h.
Proof.
move=>T; rewrite -umfilt_dpredU; last first.
- by case=>x y /= N; rewrite negb_and -leqNgt N.
apply/eq_in_umfilt; case=>k v _ => /=.
by case: (leqP k t1)=>//= /leq_trans; apply.
Qed.

Lemma umfilt_lt_split A (U : natmap A) (h : U) t1 t2 k :
        t1 <= k <= t2 ->
        um_filter (fun '(x, _)=>t1 < x <= t2) h =
        um_filter (fun '(x, _)=>t1 < x <= k) h \+
        um_filter (fun '(x, _)=>k < x <= t2) h.
Proof.
move=>/andP [T1 T2]; rewrite -umfilt_dpredU; last first.
- by case=>x y /andP [N1 N2]; rewrite /= negb_and -leqNgt N2.
apply/eq_in_umfilt; case=>k1 v1 _ /=.
case: (leqP k1 k)=>//=; last by move/(leq_ltn_trans T1)=>->.
by move/leq_trans=>-> //; rewrite orbF.
Qed.

Lemma umfilt_pt_split A (U : natmap A) (h : U) k v :
        (k, v) \In h -> 
        um_filter (fun '(x, _)=>k.-1 < x <= k) h = pts k v.
Proof.
move=>H; have W : valid h by case: H.
have N: 0 < k by move/In_dom/dom_cond: H; case: k.
have subX : forall m n, 0 < n -> (m < n) = (m <= n.-1) by move=>? [].
rewrite (In_eta H) umfiltPtUn -(In_eta H) /= subX // W !leqnn /=.
rewrite umfilt_mem0L ?unitR ?validF //.
move=>k1 v1 /InF [_ /=]; rewrite andbC; case: (ltngtP k k1) =>//=.
by rewrite subX //; case: (ltngtP k1 k.-1).
Qed.

Lemma umfilt_leUn A (U : natmap A) (h1 h2 : U) t :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        {in dom h2, forall k, k > last_key h1} ->
        um_filter (le t) (h1 \+ h2) = um_filter (le t) h1.
Proof.
move=>V K D; rewrite umfiltUn // (umfilt_le0 (validR V)) ?unitR //.
by move=>k /D /(leq_ltn_trans K).
Qed.

Lemma umfilt_le_gapless A (U : natmap A) (h1 h2 : U) t :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        um_filter (le t) h2 = um_filter (le t) h1.
Proof.
move=>G V H K; case: (gapless_pleq G V H)=>h [? D].
by subst h2; rewrite umfilt_leUn.
Qed.

Lemma dom_umfilt_le_eq A (U : natmap A) (h : U) t1 t2 :
        t1 \in 0::dom h -> t2 \in 0::dom h ->
        um_filter (le t1) h = um_filter (le t2) h ->
        t1 = t2.
Proof.
rewrite !inE; case/orP=>[/eqP ->|/In_domX [v1 T1]].
- case/orP=>[/eqP ->|/In_domX [v2 T2]] //.
  move/eq_in_umfilt=>/(_ (t2, v2) T2) /=.
  by rewrite leqnn leqn0 eq_sym=>/eqP.
case/orP=>[/eqP ->|/In_domX [v2 T2] L].
- move/eq_in_umfilt=>/(_ (t1, v1) T1) /=.
  by rewrite leqnn leqn0=>/esym/eqP.
move/eq_in_umfilt: (L)=>/(_ (t1, v1) T1).
move/eq_in_umfilt: (L)=>/(_ (t2, v2) T2) /=.
by rewrite !leqnn; case: ltngtP.
Qed.

Lemma eval_leUn A (U : natmap A) R a (h1 h2 : U) t (z0 : R) :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        {in dom h2, forall k, k > last_key h1} ->
        eval a (le t) (h1 \+ h2) z0 = eval a (le t) h1 z0.
Proof. by move=>V K D; apply: eq_filt_eval; apply: umfilt_leUn. Qed.

Lemma eval_le_gapless A (U : natmap A) R a (h1 h2 : U) t (z0 : R) :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        eval a (le t) h2 z0 = eval a (le t) h1 z0.
Proof. by move=>G V H K; apply: eq_filt_eval; apply: umfilt_le_gapless. Qed.

Lemma eval_le0 A (U : natmap A) R a (h : U) (z0 : R) : eval a (le 0) h z0 = z0.
Proof.
case W : (valid h); last first.
- by move/negbT/invalidE: W=>->; rewrite eval_undef.
rewrite eval_umfilt umfilt_mem0L ?eval0 //.
by move=>k v /In_dom/dom_cond; rewrite /=; case: ltngtP.
Qed.

Lemma eval_le_split A (U : natmap A) R a (h : U) t1 t2 (z0 : R) :
        t1 <= t2 ->
        eval a (le t2) h z0 =
        eval a (fun '(k, _)=>t1 < k <= t2) h (eval a (le t1) h z0).
Proof.
move=>T; case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite !eval_undef.
rewrite eval_umfilt (umfilt_predD h (pts_sub T)) evalUn; last first.
- move=>x y /In_dom_umfilt [vx][X _] /In_dom_umfilt [wy][/= /andP][].
  by rewrite /= -ltnNge; move/(leq_ltn_trans X).
- by rewrite -(umfilt_predD h (pts_sub T)) pfV.
by rewrite -!eval_umfilt; apply: eq_in_eval; case=>k v _; apply: ptsD.
Qed.

Lemma eval_lt_split A (U : natmap A) R a (h : U) t1 t2 (z0 : R) :
        t1 < t2 ->
        eval a (lt t2) h z0 =
        eval a (fun '(k, _)=>t1 < k < t2) h (eval a (le t1) h z0).
Proof.
move=>T; case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite !eval_undef.
rewrite eval_umfilt (umfilt_predD h (pts_sub_lt T)) evalUn; last first.
- move=>x y /In_dom_umfilt [vx][X _] /In_dom_umfilt [wy][/= /andP][].
  by rewrite /= -ltnNge; move/(leq_ltn_trans X).
- by rewrite -(umfilt_predD h (pts_sub_lt T)) pfV.
by rewrite -!eval_umfilt; apply: eq_in_eval; case=>k v _; apply: ptsD_lt.
Qed.

Lemma eval_le_lt_split A (U : natmap A) R a (h : U) t (z0 : R) :
        eval a (le t) h z0 =
        eval a (fun '(k, _)=>k == t) h (eval a (lt t) h z0).
Proof.
case V : (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite !eval_undef.
have D : subpred (T:=nat*A) (lt t) (le t) by case=>k v /ltnW.
rewrite eval_umfilt (umfilt_predD h D) evalUn; last first.
- move=>x y /In_dom_umfilt [vx][X _] /In_dom_umfilt [wy][/= /andP][].
  by rewrite /= -ltnNge; move/(leq_ltn_trans X).
- by rewrite -(umfilt_predD h D) pfV.
rewrite -!eval_umfilt; apply: eq_in_eval; case=>k v _ /=.
by case: ltngtP.
Qed.

Lemma eval_eq A (U : natmap A) R a (h : U) t v (z0 : R) :
        (t, v) \In h -> eval a (fun '(k, _)=>k == t) h z0 = a z0 t v.
Proof.
move=>H; rewrite eval_umfilt; have N : t != 0 by move/In_dom/dom_cond: H.
suff -> : um_filter (fun '(k, _)=>k == t) h = pts t v by rewrite evalPt /= N.
apply/umem_eq=>[||[k w]]; first by rewrite pfV; case: H.
- by rewrite validPt.
rewrite In_umfiltX; split; last by move/InPt =>[[->->]].
by move=>[/eqP -> H1]; rewrite (In_fun H H1); apply: In_condPt.
Qed.

Lemma eval_le_last A (U : natmap A) R a (h : U) t (z0 : R) :
        last_key h <= t -> eval a (le t) h z0 = eval a xpredT h z0.
Proof.
by move=>H; apply: eq_in_eval; case=>k v /In_dom/dom_lastkey/leq_trans; apply.
Qed.

Lemma eval_fresh_le A (U : natmap A) R a (h : U) t v (z0 : R) :
        eval a (le t) (pts (fresh h) v \+ h) z0 =
        if t <= last_key h then eval a (le t) h z0 else
          if valid h then a (eval a predT h z0) (fresh h) v else z0.
Proof.
case V: (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undef !eval_undef; case: ifP.
case: ifP=>H.
- by rewrite eval_umfilt umfiltPtUn freshPtUnV // V ltnNge H -eval_umfilt.
rewrite joinC evalUnPt; last first.
- by apply/allP=>x; apply: dom_lastkey.
- by rewrite joinC freshPtUnV.
rewrite ltnNge H; congr a; apply: eq_in_eval.
case=>k w /In_dom/dom_lastkey /=.
by case: ltngtP H=>// /ltnW H _ /leq_trans; apply.
Qed.

Lemma eval_fresh_lt A (U : natmap A) R a (h : U) t v (z0 : R) :
        eval a (lt t) (pts (fresh h) v \+ h) z0 =
        if t <= fresh h then eval a (lt t) h z0 else
          if valid h then a (eval a predT h z0) (fresh h) v else z0.
Proof.
case V: (valid h); last first.
- by move/invalidE: (negbT V)=>->; rewrite join_undef !eval_undef; case: ifP.
case: ifPn=>H.
- by rewrite eval_umfilt umfiltPtUn valid_fresh // V ltnNge H -eval_umfilt.
rewrite joinC evalUnPt; last first.
- by apply/allP=>x; apply: dom_lastkey.
- by rewrite joinC valid_fresh.
rewrite ltnNge H; congr a; apply: eq_in_eval.
case=>k w /In_dom/dom_lastkey /=; rewrite /fresh -ltnNge in H.
by case: ltngtP H=>// /ltnW H _ /leq_ltn_trans; apply.
Qed.

Lemma eval_le_fresh A (U : natmap A) R a (h : U) t v (z0 : R) :
        t <= last_key h ->
        eval a (le t) (pts (fresh h) v \+ h) z0 = eval a (le t) h z0.
Proof. by move=>H; rewrite eval_fresh_le H. Qed.

Lemma eval_lt_fresh A (U : natmap A) R a (h : U) t v (z0 : R) :
        t <= fresh h ->
        eval a (lt t) (pts (fresh h) v \+ h) z0 = eval a (lt t) h z0.
Proof. by move=>H; rewrite eval_fresh_lt H. Qed.

Lemma eval_le_ind A (U : natmap A) R a (P : R -> Prop) (h : U) t1 t2 (z0 : R) :
         t1 <= t2 ->
         P (eval a (le t1) h z0) ->
         (forall k v z0, (k, v) \In h -> t1 < k <= t2 -> P z0 -> P (a z0 k v)) ->
         P (eval a (le t2) h z0).
Proof.
by move=>T P0 H; rewrite (eval_le_split a h z0 T); apply: eval_ind.
Qed.

Lemma eval_lt_ind A (U : natmap A) R a (P : R -> Prop) (h : U) t1 t2 (z0 : R) :
         t1 < t2 ->
         P (eval a (le t1) h z0) ->
         (forall k v z0, (k, v) \In h -> t1 < k < t2 -> P z0 -> P (a z0 k v)) ->
         P (eval a (lt t2) h z0).
Proof.
by move=>T P0 H; rewrite (eval_lt_split a h z0 T); apply: eval_ind.
Qed.

(* common case: functional version of the above le_lemma *)
Lemma eval_leF A (U : natmap A) R X a (f : R -> X) (h : U) t1 t2 (z0 : R) :
         t1 <= t2 ->
         (forall k v z0, (k, v) \In h -> t1 < k <= t2 -> f (a z0 k v) = f z0) ->
         f (eval a (le t1) h z0) = f (eval a (le t2) h z0).
Proof.
move=>T H.
apply: (eval_le_ind (P := fun x => f (eval a (le t1) h z0) = f x)) T _ _=>//.
by move=>k v z1 H1 /H ->.
Qed.

(* common case: functional version of the above lt_lemma *)
Lemma eval_ltF A (U : natmap A) R X a (f : R -> X) (h : U) t1 t2 (z0 : R) :
         t1 < t2 ->
         (forall k v z0, (k, v) \In h -> t1 < k < t2 -> f (a z0 k v) = f z0) ->
         f (eval a (le t1) h z0) = f (eval a (lt t2) h z0).
Proof.
move=>T H.
apply: (eval_lt_ind (P := fun x => f (eval a (le t1) h z0) = f x)) T _ _=>//.
by move=>k v z1 H1 /H ->.
Qed.

Lemma umcnt_le_split A (U : natmap A) p (h : U) t1 t2 :
        t1 <= t2 ->
        um_count (predI p (le t2)) h =
        um_count (predI p (le t1)) h +
        um_count (predI p (fun '(k, _)=>t1 < k <= t2)) h.
Proof.
move=>T; rewrite -!umcnt_umfilt !(umcnt_umfiltC p).
by rewrite (umcnt_predD _ (pts_sub T)) (eq_in_umcnt2 _ (ptsD T)).
Qed.

Lemma umcnt_le0 A (U : natmap A) p (h : U) t :
        valid h -> {in dom h, forall k, t < k} ->
        um_count (predI p (le t)) h = 0.
Proof. by rewrite -umcnt_umfilt=>V /(umfilt_le0 V) ->; rewrite umcnt0. Qed.

Lemma umcnt_leUn A (U : natmap A) p (h1 h2 : U) t :
        valid (h1 \+ h2) -> t <= last_key h1 ->
        {in dom h2, forall k, k > last_key h1} ->
        um_count (predI p (le t)) (h1 \+ h2) =
        um_count (predI p (le t)) h1.
Proof. by move=>V K D; rewrite -!umcnt_umfilt umfilt_leUn. Qed.

Lemma umcnt_le_gapless A (U : natmap A) p (h1 h2 : U) t :
        gapless h1 -> valid h2 -> [pcm h1 <= h2] -> t <= last_key h1 ->
        um_count (predI p (le t)) h2 = um_count (predI p (le t)) h1.
Proof. by move=>G V K D; rewrite -!umcnt_umfilt (umfilt_le_gapless G). Qed.

Lemma umcnt_le_last A (U : natmap A) p (h : U) t :
        last_key h <= t -> um_count (predI p (le t)) h = um_count p h.
Proof. by move=>K; rewrite -!umcnt_umfilt umfilt_le_last. Qed.

Lemma umcnt_fresh_le A (U : natmap A) p (h : U) t v :
        um_count (predI p (le t)) (pts (fresh h) v \+ h) =
        if t <= last_key h then um_count (predI p (le t)) h else
        if p (fresh h, v) && valid h then 1 + um_count p h else um_count p h.
Proof.
case V: (valid h); last first.
- move/invalidE: (negbT V)=>->; rewrite join_undef !umcnt_undef.
  by rewrite lastkey_undef andbF; case: ifP.
case: ifP=>H.
- by rewrite -!umcnt_umfilt umfiltPtUn valid_fresh // V ltnNge H.
rewrite umcntPtUn ?valid_fresh //= ltnNge H /=.
by rewrite umcnt_le_last; [case: ifP | case: ltngtP H].
Qed.

Lemma umcnt_le_fresh A (U : natmap A) p (h : U) t v :
        t <= last_key h ->
        um_count (predI p (le t)) (pts (fresh h) v \+ h) =
        um_count (predI p (le t)) h.
Proof. by move=>H; rewrite umcnt_fresh_le H. Qed.

Definition fresh_le := (umcnt_fresh_le, eval_fresh_le).
Definition le_last := (umcnt_le_last, eval_le_last).
Definition le_fresh := (umcnt_le_fresh, eval_le_fresh).
Definition lt_fresh := (eval_lt_fresh).

(*********************************)
(* Some notational abbreviations *)
(*********************************)

(* exec is evaluating a history up to a timestamp *)
(* run is evaluating a history up to the end *)

(* In exec and run, the timestamp shouldn't influence *)
(* the val of the operation. So we need a coercion to *)
(* account for the timestamp, which is then ignored *)
Notation exec a t h z0 := (evalv a (le t) h z0).
Notation run a h z0 := (evalv a xpredT h z0).

Section Exec.
Variables (V R : Type) (U : natmap V).

Lemma exec0 a (h : U) (z0 : R) : exec a 0 h z0 = z0.
Proof.
have /(eq_in_eval _) -> : forall kv, kv \In h -> le 0 kv = pred0 kv.
- by case=>k v /In_cond; case: k.
by rewrite eval_pred0.
Qed.

End Exec.

Section Growing.
Variables (V R : Type) (U : natmap V) (X : ordType) (a : R -> V -> R) (f : R -> X).
Implicit Types p : pred (nat*V).

Definition growing (h : U) :=
  forall k v z0, (k, v) \In h -> oleq (f z0) (f (a z0 v)).

Lemma growL h1 h2 : valid (h1 \+ h2) -> growing (h1 \+ h2) -> growing h1.
Proof. by move=>W G k v z0 H; apply: (G k); apply/InL. Qed.

Lemma growR h1 h2 : valid (h1 \+ h2) -> growing (h1 \+ h2) -> growing h2.
Proof. by rewrite joinC; apply: growL. Qed.

Lemma helper0 p h z0 : growing h -> oleq (f z0) (f (evalv a p h z0)).
Proof.
elim/um_indf: h z0=>[||k v h IH W /(order_path_min (@trans _)) T] z0 G;
rewrite ?eval_undef ?eval0 // evalPtUn //.
have K: (k, v) \In pts k v \+ h by apply/InPtUnE=>//; left.
have Gh: growing h.
- by move=>k1 v1 z1 X1; apply: (G k1); apply/InPtUnE=>//; right.
case: ifP=>// P; last by apply: IH.
by apply: otrans (IH _ Gh); apply: (G k).
Qed.

Lemma helper1 p h z0 k v :
        growing (pts k v \+ h) ->
        valid (pts k v \+ h) ->
        all (ord k) (dom h) ->
        p (k, v) ->
        f (evalv a p (pts k v \+ h) z0) = f z0 ->
        f (a z0 v) = f z0.
Proof.
move=>G W D P; move: (growR W G)=>Gh.
have K: (k, v) \In pts k v \+ h by apply/InPtUnE=>//; left.
rewrite evalPtUn // P => E; apply/eqP; case: ordP=>//.
- by move/(G k v z0): K; rewrite /oleq eq_sym; case: ordP.
by move: (helper0 p (a z0 v) Gh); rewrite -E /oleq eq_sym; case: ordP.
Qed.

Lemma helper2 p h1 h2 z0 k v :
        growing (h1 \+ (pts k v \+ h2)) ->
        valid (h1 \+ (pts k v \+ h2)) ->
        {in dom h1, forall x, x < k} ->
        all (ord k) (dom h2) ->
        p (k, v) ->
        f (evalv a p (h1 \+ (pts k v \+ h2)) z0) = f z0 ->
        f (a (evalv a p h1 z0) v) = f (evalv a p h1 z0).
Proof.
move=>G W D1 D2 P E1; rewrite evalUn ?W // in E1; last first.
- move=>x y /D1 X1; rewrite domPtUn inE (validR W).
  by case/orP=>[/eqP <-|/(allP D2)] //; apply: ltn_trans.
suff E2 : f (evalv a p h1 z0) = f z0.
- by apply: helper1 (growR W G) (validR W) D2 P _; rewrite E1 E2.
apply/eqP; case: ordP=>//.
- by move: (helper0 p z0 (growL W G)); rewrite /oleq eq_sym; case: ordP.
move: (helper0 p (evalv a p h1 z0) (growR W G)).
by rewrite -E1 /oleq eq_sym; case: ordP.
Qed.

(* "introducing" growth *)
Lemma growI h t1 t2 z0 :
        growing h -> t1 <= t2 ->
        oleq (f (exec a t1 h z0)) (f (exec a t2 h z0)).
Proof.
move=>G N; case W: (valid h); last first.
- by move/negbT/invalidE: W=>->; rewrite !eval_undef.
rewrite eval_umfilt [in X in oleq _ X]eval_umfilt (umfilt_le_split h N).
rewrite evalUn; first by apply: helper0=>x y z /In_umfiltX [_ /G].
- by rewrite -(umfilt_le_split h N) pfV.
by move=>??/In_dom_umfilt[?][/leq_ltn_trans Y _]/In_dom_umfilt[?][/andP[/Y]].
Qed.

(* "eliminating" growth *)
Lemma growE h t1 t2 z0 k v :
        growing h -> (k, v) \In h -> t1 < k <= t2 ->
        f (exec a t2 h z0) = f (exec a t1 h z0) ->
        f (a (exec a k.-1 h z0) v) = f (exec a k.-1 h z0).
Proof.
move=>G H /andP [N1 N2] E; have W : valid h by case: H.
pose h0 : U := um_filter (le t1) h.
pose h1 : U := um_filter (fun '(x, _)=>t1 < x <= k.-1) h.
pose h2 : U := um_filter (fun '(x, _)=>k < x <= t2) h.
have subX : forall k m n, k < n -> (m < n) = (m <= n.-1) by move=>?? [].
have K1 : k.-1 <= k by rewrite ltnW // (subX t1).
have K2 : t1 <= k.-1 by rewrite -(subX t1).
have K3 : k.-1 <= k <= t2 by rewrite K1 N2.
have K4 : t1 <= k.-1 <= t2 by rewrite K2 (leq_trans K1 N2).
have Eh: um_filter (le t2) h = h0 \+ (h1 \+ (pts k v \+ h2)).
- rewrite (umfilt_le_split h N2) (umfilt_le_split h K1).
  by rewrite (umfilt_le_split h K2) (umfilt_pt_split H) -!joinA.
have W1 : valid (h0 \+ (h1 \+ (pts k v \+ h2))) by rewrite -Eh pfV.
rewrite eval_umfilt (umfilt_le_split h K2) evalUn ?(validAL W1) //; last first.
- by move=>??/In_dom_umfilt[?][/leq_ltn_trans Y] _ /In_dom_umfilt[?][] /andP [/Y].
rewrite -(eval_umfilt (le t1)); apply: helper2 (validR W1) _ _ _ _ =>//.
- by apply: growR W1 _; rewrite -Eh=>k1 v1 z1 /In_umfiltX [] _ /G.
- by move=>x /In_dom_umfilt; rewrite (subX t1 x) //; case=>v0 [] /andP [].
- by apply/allP=>x /In_dom_umfilt; case=>v0 [] /andP [].
rewrite eval_umfilt Eh evalUn ?(validX W1) -?eval_umfilt // in E.
move=>x y /In_dom_umfilt; case=>v1 [/leq_ltn_trans Y _].
rewrite -(umfilt_pt_split H) -(umfilt_lt_split h K3).
by rewrite -(umfilt_lt_split h K4) =>/In_dom_umfilt; case=>v0 [/andP][/Y].
Qed.

End Growing.

(* The common case of growI and growE is when X = nat. *)

Section GrowingNat.
Variables (V R : Type) (U : natmap V) (X : ordType) (a : R -> V -> R) (f : R -> nat).
Implicit Types p : pred (nat*V).

Lemma growIn (h : U) t1 t2 z0 :
        growing a f h -> t1 <= t2 ->
        f (exec a t1 h z0) <= f (exec a t2 h z0).
Proof.
by move=>G N; move: (growI z0 G N); rewrite leq_eqVlt /oleq/ord orbC.
Qed.

Lemma growEn (h : U) t1 t2 z0 k v :
        growing a f h -> (k, v) \In h -> t1 < k <= t2 ->
        f (exec a t2 h z0) = f (exec a t1 h z0) ->
        f (a (exec a k.-1 h z0) v) = f (exec a k.-1 h z0).
Proof. by apply: growE. Qed.

End GrowingNat.
