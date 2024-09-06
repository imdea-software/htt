(*
Copyright 2022 IMDEA Software Institute
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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path interval order.
From pcm Require Import options prelude ordtype seqext.
Local Open Scope order_scope.
Import Order.Theory.

(* We assume the sequences are unique and use the first index, however most *)
(* lemmas don't require this condition explicitly. The ones that do are     *)
(* grouped in a separate section.                                           *)

(***********************************)
(***********************************)
(* Sequence-induced ordering       *)
(* definition and basic properties *)
(***********************************)
(***********************************)

(* x <[ks] y if first x appears to the left of last y in the sequence ks *)

(* It turns out it's useful to have 0 <[ks] x, for every x. *)
(* Basically, we use these orderings for reasoning about *)
(* timestamps in histories, and we always keep the null timestamp *)
(* to stand for the initialization step *)
(* That said, the null timestamp is never in any history as *)
(* the initialization step is implicit *)

Module Type SeqOrdTp.
Parameter seq_le : forall (A : eqType) (ks : seq A), A -> A -> bool.
Parameter seq_lt : forall (A : eqType) (ks : seq A), A -> A -> bool.
Notation "t1 '<=[' ks ] t2" := (seq_le ks t1 t2)
  (at level 10, format "t1  '<=[' ks ]  t2").
Notation "t1 '<[' ks ] t2" := (seq_lt ks t1 t2)
  (at level 10, format "t1  '<[' ks ]  t2").
Parameter seqle_unlock : forall (A : eqType) ks (t1 t2 : A),
  t1 <=[ks] t2 = (index t1 ks <= index t2 ks)%N.
Parameter seqlt_unlock : forall (A : eqType) ks (t1 t2 : A),
  t1 <[ks] t2 = (index t1 ks < index t2 ks)%N.
End SeqOrdTp.

Module SeqOrd : SeqOrdTp.
Section SeqOrd.
Variables (A : eqType) (ks : seq A) (t1 t2 : A).
Definition seq_le := (index t1 ks <= index t2 ks)%N.
Definition seq_lt := (index t1 ks < index t2 ks)%N.
Definition seqle_unlock := erefl seq_le.
Definition seqlt_unlock := erefl seq_lt.
End SeqOrd.
End SeqOrd.
Export SeqOrd.

(* alternative rewrites *)
Lemma seqle_unlockE (A : eqType) ks (t1 t2 : A) : 
        t1 <=[ks] t2 = (index t1 ks <= index t2 ks).
Proof. exact: seqle_unlock. Qed.

Lemma seqlt_unlockE (A : eqType) ks (t1 t2 : A) : 
        t1 <[ks] t2 = (index t1 ks < index t2 ks).
Proof. exact: seqlt_unlock. Qed.

Section SeqLeBase.
Variable (A : eqType).
Implicit Type (ks : seq A).

(****************** transitivity ****************)

Lemma sle_trans ks : transitive (seq_le ks).
Proof. by move=>y x z; rewrite !seqle_unlock; apply: leq_trans. Qed.

Lemma slt_trans ks : transitive (seq_lt ks).
Proof. by move=>y x z; rewrite !seqlt_unlock; apply: ltn_trans. Qed.

Lemma sle_slt_trans ks t1 t2 t3 :
        t1 <=[ks] t2 -> t2 <[ks] t3 -> t1 <[ks] t3.
Proof. by rewrite !seqlt_unlock !seqle_unlock; apply: leq_ltn_trans. Qed.

Lemma slt_sle_trans ks t1 t2 t3 :
        t1 <[ks] t2 -> t2 <=[ks] t3 -> t1 <[ks] t3.
Proof. by rewrite !seqlt_unlock !seqle_unlock; apply: leq_trans. Qed.


(****************** reflexivity ****************)

Lemma sle_refl ks : reflexive (seq_le ks).
Proof. by move=>x; rewrite seqle_unlock. Qed.

(****************** irreflexivity ***************)

Lemma slt_irr x ks : x <[ks] x = false.
Proof. by rewrite seqlt_unlock; apply: ltnn. Qed.

(* non-equational variant *)
Lemma sltnn x ks : ~ x <[ks] x.
Proof. by rewrite slt_irr. Qed.

(****************** antisymmetry ****************)

Lemma sle_antisym ks : {in ks, antisymmetric (seq_le ks)}.
Proof.
move=>x Hx y; rewrite !seqle_unlock.
by rewrite -eqn_leq =>/eqP /index_inj; apply.
Qed.

(****************** asymmetry ***************)

Lemma slt_asym x y ks : x <[ks] y -> ~~ y <[ks] x.
Proof. by rewrite !seqlt_unlock; case: ltngtP. Qed.

(***************** totality ********************)

Lemma sle_total ks x y : x <=[ks] y || y <=[ks] x.
Proof. by rewrite !seqle_unlock; case: ltngtP. Qed.

Lemma slt_total ks x y : 
        x \in ks -> 
        [|| x == y, x <[ks] y | y <[ks] x].
Proof.
rewrite !seqlt_unlock=>H; case: ltngtP; rewrite ?orbT ?orbF //.
by move/index_inj=>->.
Qed.

(* transfer properties of sequence ordering *)

(****************** sle_eqVlt ***************)

Lemma sle_eqVlt ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <=[ks] t2 = (t1 == t2) || (t1 <[ks] t2).
Proof.
move=>H; rewrite seqlt_unlock seqle_unlock leq_eqVlt /=.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

(****************** slt_neqAle ***************)

Lemma slt_neqAle ks t1 t2 :
        (t1 \in ks) || (t2 \in ks) ->
        t1 <[ks] t2 = (t1 != t2) && (t1 <=[ks] t2).
Proof.
move=>H.
rewrite seqlt_unlock seqle_unlock ltn_neqAle.
case: (t1 =P t2)=>[->|N] /=; first by rewrite eq_refl.
case: eqP=>//=; case/orP: H=>H; first by move/(index_inj H)/N.
by move/esym/(index_inj H)/esym/N.
Qed.

(****************** sltNge ***************)

Lemma sltNge ks t1 t2 : t1 <[ks] t2 = ~~ t2 <=[ks] t1.
Proof. by rewrite seqlt_unlock seqle_unlock ltnNge. Qed.

(****************** sleNgt ***************)

Lemma sleNgt ks t1 t2 : t1 <=[ks] t2 = ~~ t2 <[ks] t1.
Proof. by rewrite sltNge negbK. Qed.

(* order properties of the sequence orderings *)

(****************** slt_neq ***************)

Corollary slt_neq x y ks : x <[ks] y -> x != y.
Proof. by apply/contraL=>/eqP->; rewrite slt_irr. Qed.

End SeqLeBase.

#[export] Hint Resolve sle_refl : core.

Section SeqLeProp.
Variable (A : eqType).
Implicit Type (ks : seq A).

Lemma sltW ks t1 t2 : t1 <[ks] t2 -> t1 <=[ks] t2.
Proof. by rewrite seqlt_unlock seqle_unlock; apply: ltnW. Qed.


(* membership properties of the sequence orderings *)

Lemma slt_memI x y ks : x \in ks -> y \notin ks -> x <[ks] y.
Proof. by move=>X /index_memN E; rewrite seqlt_unlock E index_mem. Qed.

Lemma sle_memI x y ks : y \notin ks -> x <=[ks] y.
Proof. by move/index_memN=>E; rewrite seqle_unlock E index_size. Qed.

Lemma slt_memE x y ks : x <[ks] y -> x \in ks.
Proof. 
rewrite seqlt_unlock -index_mem=>/leq_trans.
by apply; rewrite index_size. 
Qed.

Lemma sle_memE x y ks : x <=[ks] y -> y \in ks -> x \in ks.
Proof. by rewrite seqle_unlock -!index_mem; apply: leq_ltn_trans. Qed.

(* sequence orderings and constructors *)

Lemma slt_nil x y : x <[Nil A] y = false. 
Proof. by rewrite seqlt_unlock. Qed.
Lemma sle_nil x y : x <=[Nil A] y. 
Proof. by rewrite seqle_unlock. Qed.

(* cons *)

Lemma slt_cons x y k ks :
        x <[k :: ks] y = (y != k) && ((x == k) || (x <[ks] y)).
Proof. by rewrite !seqlt_unlock /= !(eq_sym k); case: eqP; case: eqP. Qed.

Lemma sle_cons x y k ks :
        x <=[k :: ks] y = (x == k) || (y != k) && x <=[ks] y.
Proof. by rewrite sleNgt slt_cons negb_and negbK negb_or -sleNgt. Qed.

Lemma sltL x y ks : x <[x :: ks] y = (y != x).
Proof. by rewrite slt_cons eq_refl andbT. Qed.

Lemma sleL x y ks : x <=[x :: ks] y.
Proof. by rewrite sle_cons eq_refl. Qed.

Lemma sltR x y ks : x <[y :: ks] y = false.
Proof. by rewrite sltNge sleL. Qed.

Lemma sleR x y ks : x <=[y :: ks] y = (y == x).
Proof. by rewrite sleNgt sltL negbK. Qed.

(* sequence ordering and head *)

Lemma sle_head x ks y : (head x ks) <=[ks] y.
Proof. 
case: ks=>[|k ks] /=; first by rewrite sle_nil.
by rewrite sleL. 
Qed.

(* sequence orderings and rcons *)

Lemma slt_rcons x y k ks :
        x <[rcons ks k] y = if y \in ks then x <[ks] y
                            else (x \in ks) || (k != y) && (k == x).
Proof.
rewrite !seqlt_unlock !index_rcons.
case X: (x \in ks); case Y: (y \in ks)=>//=.
- by case: eqP; [rewrite index_mem | rewrite ltnS index_size].
- move/negbT/index_memN: X=>X; rewrite [LHS]ltnNge [RHS]ltnNge.
  rewrite X index_size /=.
  case: eqP=>//; first by rewrite index_size.
  by rewrite ltnW // ltnS index_size.
rewrite !(eq_sym k).
case: eqP=>_; case: eqP=>_ /=.
- by rewrite ltnn.
- by rewrite ltnS leqnn.
- by rewrite ltnNge leqnSn.
by rewrite ltnn.
Qed.

Lemma sle_rcons x y k ks :
        x <=[rcons ks k] y = if x \in ks then x <=[ks] y
                             else (y \notin ks) && ((k == x) || (k != y)).
Proof.
by rewrite !sleNgt slt_rcons; case: ifP=>//; rewrite negb_or negb_and negbK.
Qed.

(* some shortcuts for slt/sle_rcons *)

Lemma slt_rconsI x y k ks : x <[ks] y -> x <[rcons ks k] y.
Proof. by move=>H; rewrite slt_rcons H (slt_memE H) if_same. Qed.

Lemma sle_rconsI x y k ks : k != y -> x <=[ks] y -> x <=[rcons ks k] y.
Proof.
move=>N H; rewrite sle_rcons H N orbT andbT.
case: ifP=>// K; apply: contraFT K.
by rewrite negbK; apply: sle_memE H.
Qed.

Lemma slt_rcons_in x y k ks :
        x \in ks -> x <[rcons ks k] y = x <[ks] y.
Proof.
move=>H; rewrite slt_rcons H /=; case: ifP=>// K.
by apply/esym; apply: slt_memI=>//; rewrite K.
Qed.

Lemma sle_rcons_in x y k ks :
        x \in ks -> x <=[rcons ks k] y = x <=[ks] y.
Proof. by move=>X; rewrite sle_rcons X. Qed.

Lemma slt_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <[rcons ks k1] y = x <[rcons ks k2] y.
Proof. by rewrite !slt_rcons=>/orP [] ->. Qed.

Lemma sle_rcons_inE ks x y k1 k2 :
        (x \in ks) || (y \in ks) ->
        x <=[rcons ks k1] y = x <=[rcons ks k2] y.
Proof. by rewrite !sle_rcons=>/orP [] ->. Qed.

Lemma slt_rconsR ks x k : x <[rcons ks k] k -> x \in ks.
Proof. by rewrite slt_rcons eq_refl orbF; case: ifP=>[_ /slt_memE|]. Qed.

Lemma sle_rconsR ks x k : x <=[rcons ks k] k -> x \in rcons ks k.
Proof.
rewrite sle_rcons eq_refl orbF mem_rcons inE.
case X: (x \in ks); first by rewrite orbT.
by rewrite orbF eq_sym; case/andP.
Qed.

(* sequence orderings and concatenation *)
Lemma sle_cat ks1 ks2 x y :
        x <=[ks1++ks2] y = if x \in ks1 then x <=[ks1] y
                           else (y \notin ks1) && x <=[ks2] y.
Proof.
rewrite !seqle_unlock !index_cat.
case X: (x \in ks1); case Y: (y \in ks1)=>//=.
- move/negbT/index_memN: Y=>Y.
  by rewrite Y index_size ltnW // ltn_addr // index_mem.
- rewrite -index_mem in Y.
  apply/negP=>H; move/(leq_ltn_trans H): Y.
  by rewrite ltnNge leq_addr.
by rewrite leq_add2l.
Qed.

Lemma slt_cat ks1 ks2 x y :
        x <[ks1++ks2] y = if y \in ks1 then x <[ks1] y
                          else (x \in ks1) || x <[ks2] y.
Proof. by rewrite !sltNge sle_cat; case: ifP=>//; rewrite negb_and negbK. Qed.

(* shortcuts *)

Lemma slt_catL ks1 ks2 x y : x <[ks1] y -> x <[ks1++ks2] y.
Proof. by move=>H; rewrite slt_cat H (slt_memE H) if_same. Qed.

Lemma slt_splitR x y ks1 ks2 : y != x -> y \notin ks1 -> x <[ks1++x::ks2] y.
Proof.
by move=>N Y; rewrite slt_cat slt_cons eq_refl andbT (negbTE Y) N orbT.
Qed.

Lemma sle_splitR x y ks1 ks2 : y \notin ks1 -> x <=[ks1++x::ks2] y.
Proof.
move=>Y; rewrite sle_eqVlt; last first.
- by apply/orP; left; rewrite mem_cat inE eq_refl orbT.
by case: eqP=>[|/eqP N] //=; rewrite (slt_splitR _ _ Y) // eq_sym.
Qed.

(* the other direction of slt_splitR, further strenghtened *)
(* with an additional fact that x \notin ks1 *)
(* by picking a split with the first occurrence of x *)
(* in fact, we can have both directions here, so we prove a reflect lemma *)
(* but it should really only be used in the direction x <[ks] y -> .. *)
(* because in the other direction slt_splitR is already stronger. *)
Lemma slt_splitL ks x y :
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2, x != y,
                                     x \notin ks1 & y \notin ks1])
                (x <[ks] y).
Proof.
case H : (x <[ks] y); constructor; last first.
- apply/contraFnot: H; case=>ks1 [ks2][-> N _].
  by apply: slt_splitR; rewrite eq_sym.
rewrite seqlt_unlock in H.
have : x \in ks by rewrite -index_mem (leq_trans H _) // index_size.
case/in_split=>ks1 [ks2][E X]; exists ks1, ks2.
rewrite /seq_lt {ks}E !index_cat /= eq_refl in H *.
case: eqP H=>[->|/eqP N] /=; first by rewrite ltnn.
rewrite (negbTE X) addn0; case: ifP=>//= _.
by rewrite ltnNge index_size.
Qed.

(* ditto for ole_split *)
Lemma sle_splitL ks x y :
        x \in ks ->
        reflect (exists ks1 ks2, [/\ ks = ks1++x::ks2,
                                     x \notin ks1 & y \notin ks1])
                (x <=[ks] y).
Proof.
move=>X; case H : (x <=[ks] y); constructor; last first.
- apply/contraFnot: H; case=>ks1 [ks2][-> _ N].
  by apply: sle_splitR.
case/in_split: X=>ks1 [ks2][E X]; exists ks1, ks2; split=>//.
rewrite seqle_unlock {ks}E !index_cat /= eq_refl (negbTE X) addn0 in H.
by case: ifP H=>//; rewrite -index_mem; case: ltngtP.
Qed.

(* sequence orderings and filter *)

Lemma slt_filterL (p : pred A) ks x y :
         (x \notin ks) || p x ->
         x <[ks] y -> x <[filter p ks] y.
Proof. by rewrite !seqlt_unlock; apply: index_filter_ltL. Qed.

Lemma sle_filterL (p : pred A) ks x y :
        (x \notin ks) || p x ->
        x <=[ks] y -> x <=[filter p ks] y.
Proof. by rewrite !seqle_unlock; apply: index_filter_leL. Qed.

Lemma slt_filterR (p : pred A) ks x y :
        (y \notin ks) || p y ->
        x <[filter p ks] y -> x <[ks] y.
Proof. by rewrite !seqlt_unlock; apply: index_filter_ltR. Qed.

Lemma sle_filterR (p : pred A) ks x y :
        (y \notin ks) || p y ->
        x <=[filter p ks] y -> x <=[ks] y.
Proof. by rewrite !seqle_unlock; apply: index_filter_leR. Qed.

Lemma slt_filter (p : pred A) ks x y :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <[filter p ks] y = x <[ks] y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: slt_filterR | apply: slt_filterL].
Qed.

Lemma sle_filter (p : pred A) ks x y :
        (x \notin ks) || p x -> (y \notin ks) || p y ->
        x <=[filter p ks] y = x <=[ks] y.
Proof.
by move=>H1 H2; apply/idP/idP; [apply: sle_filterR | apply: sle_filterL].
Qed.

(* sequence orderings and sortedness *)

(* slt/sle under general sorted relations *)
Lemma slt_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <[ks] y -> ltT x y.
Proof. by rewrite seqlt_unlock; apply: sorted_index_ord. Qed.

Lemma sle_sorted_lt ltT ks x y :
        transitive ltT ->
        sorted ltT ks ->
        y \in ks -> x <=[ks] y -> (x == y) || ltT x y.
Proof.
move=>T S Y; rewrite sle_eqVlt; last by rewrite Y orbT.
by case/orP=>[->//|/(slt_sorted_lt T S Y) ->]; rewrite orbT.
Qed.

(* we can get the other direction as well *)
(* if we add antisymmetry *)
(* and the condition that x \in ks *)
Lemma slt_sorted_leE leT ks x y :
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        x \in ks -> y \in ks ->
        x <[ks] y = (x != y) && leT x y.
Proof.
move=>As T S X Y; apply/idP/idP.
- by case: eqP=>[->|/eqP N] /=; [apply: contraLR; rewrite slt_irr | apply: slt_sorted_lt].
by rewrite seqlt_unlock; case/andP=>H K; apply: sorted_ord_index_leq K H.
Qed.

(* if we add antisymmetry and t1 \in ks *)
Lemma sle_sorted_leE leT ks x y :
        antisymmetric leT ->
        transitive leT ->
        sorted leT ks ->
        x \in ks -> y \in ks ->
        x <=[ks] y = (x == y) || leT x y.
Proof.
move=>As T S X Y; rewrite sle_eqVlt; last by rewrite X.
by rewrite (slt_sorted_leE As T S X Y); case: eqP.
Qed.

End SeqLeProp.

#[export] Hint Resolve slt_nil sle_nil : core.


Section SeqLeUniq.
Variable (A : eqType).
Implicit Type (ks : seq A).

Lemma slt_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <[ks1] t = k <[ks2] t.
Proof. 
rewrite !seqlt_unlock=>S U T K.
by apply/idP/idP=>/(index_subseq S U T K). 
Qed.

Lemma sle_subseq ks1 ks2 k t :
        subseq ks1 ks2 -> uniq ks2 -> k \in ks1 -> t \in ks1 ->
        k <=[ks1] t = k <=[ks2] t.
Proof. by move=>S U T K; rewrite !sleNgt (slt_subseq S U K T). Qed.

(* sequence orderings and last *)

Lemma sle_last x k ks :
        uniq ks -> x \in ks -> x <=[ks] (last k ks).
Proof. by rewrite seqle_unlock; apply: index_last_mono. Qed.

Lemma sle_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks -> x <=[k::ks] (last k ks).
Proof.
move=>/= /andP [U1 U2].
rewrite inE sle_cons; case: eqP=>//= /eqP Nxk K.
by rewrite (last_notin K) //=; apply: sle_last.
Qed.

Lemma slt_last x k ks :
        uniq ks -> x \in ks -> last k ks != x -> x <[ks] (last k ks).
Proof.
move=>U X N; move: (sle_last k U X); rewrite sle_eqVlt; last by rewrite X.
by rewrite eq_sym (negbTE N).
Qed.

Lemma slt_last_cons x k ks :
        uniq (k :: ks) -> x \in k::ks ->
        last k ks != x -> x <[k::ks] (last k ks).
Proof.
move=>U X N; rewrite slt_neqAle; last by rewrite X.
by rewrite eq_sym N sle_last_cons.
Qed.

(* every list is sorted by its slt relation, assuming uniqueness *)
Lemma sorted_slt ks : uniq ks -> sorted (seq_lt ks) ks.
Proof.
case: ks=>//= k ks; elim: ks k=>[|k1 ks IH] k2 //=.
rewrite inE negb_or -andbA=>/and4P [N1 N2 N3 N4].
rewrite sltL eq_sym N1 /=.
have : path (seq_lt [:: k1 & ks]) k1 ks by apply: IH; rewrite N3 N4.
apply: (@sub_in_path _ (mem (k1::ks))); last by apply/allP.
move=>x y /=; rewrite !inE !slt_cons.
case/orP=>[/eqP ->{x}|X].
- rewrite (eq_sym k1 k2) (negbTE N1) /= eq_refl andbT.
  case/orP=>[/eqP ->|Y ->]; first by rewrite eq_refl.
  by case: eqP Y N2=>// ->->.
case/orP=>[/eqP ->|Y]; first by rewrite eq_refl.
case: eqP Y N3=>[->|/eqP N Y N3] //=.
case: eqP X N3=>[->->|/eqP M X K1] //= H.
by rewrite H orbT andbT; case: eqP Y N2=>// ->->.
Qed.

Lemma sorted_sle ks : uniq ks -> sorted (seq_le ks) ks.
Proof.
move=>U; apply: sub_sorted (sorted_slt U).
by move=>x y /sltW.
Qed.

End SeqLeUniq.

Section SeqLeOrd.
Variable (A : ordType).
Implicit Type (ks : seq A).

(* olt/ole and sortedness under ordering on A *)

Lemma slt_sorted ks x y :
        sorted ord ks -> y \in ks -> x <[ks] y -> ord x y.
Proof. by apply/slt_sorted_lt/trans. Qed.

Lemma sle_sorted ks x y :
        sorted ord ks -> y \in ks -> x <=[ks] y -> oleq x y.
Proof. by rewrite oleq_eqVord; apply/sle_sorted_lt/trans. Qed.

Lemma slt_sortedE ks x y :
        sorted ord ks ->
        x \in ks -> y \in ks ->
        x <[ks] y = ord x y.
Proof.
move=>S X Y; apply/idP/idP; first by apply: slt_sorted S Y.
by rewrite seqlt_unlock; apply: (sorted_ord_index (@irr _) (@trans _)) S X.
Qed.

Lemma sle_sortedE ks x y :
        sorted ord ks ->
        x \in ks -> y \in ks ->
        x <=[ks] y = oleq x y.
Proof. by move=>S X Y; rewrite oleqNord sleNgt (slt_sortedE S Y X). Qed.

End SeqLeOrd.
