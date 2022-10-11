From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
(* temp*)
From mathcomp Require Import bigop.
From fcsl Require Import options axioms pred prelude seqperm.

From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import interlude model heapauto.

Section FindLast.

Variables (T : Type).
Implicit Types (x : T) (p : pred T) (s : seq T).

Definition find_last p s :=
  let i := seq.find p (rev s) in
  if i == size s then size s else (size s - i).-1.

Lemma find_last_size p s : find_last p s <= size s.
Proof.
rewrite /find_last; case: ifP=>// _.
by rewrite -subnS; apply: leq_subr.
Qed.

Lemma has_find_last p s : has p s = (find_last p s < size s).
Proof.
rewrite /find_last -has_rev has_find -(size_rev s); case: ltngtP=>/=.
- move=>H; case/posnP: (size (rev s))=>[/eqP/nilP|] E.
  - by rewrite E /= in H.
  by rewrite -subnS ltn_subrL E.
- by rewrite ltnNge find_size.
by rewrite ltnn.
Qed.

Lemma nth_find_last x0 p s : has p s -> p (nth x0 s (find_last p s)).
Proof.
rewrite /find_last -has_rev -(size_rev s) => /[dup] E.
rewrite has_find ltn_neqAle; case/andP=>/negbTE H _; rewrite H.
move/(@nth_find _ x0): E; rewrite nth_rev; first by rewrite subnS size_rev.
by move: (find_size p (rev s)); rewrite leq_eqVlt H -(size_rev s).
Qed.

Lemma has_drop p s i : has p s -> has p (drop i.+1 s) = (i < find_last p s).
Proof.
rewrite /find_last -has_rev -(size_rev s) => /[dup] E.
rewrite has_find =>/[dup] H.
rewrite ltn_neqAle; case/andP=>/negbTE -> _.
move/(has_take (size s - i).-1): E.
rewrite take_rev has_rev -subnS.
case/boolP: (i < size s)=>[Hi|].
- rewrite subKn // =>->; rewrite size_rev in H *.
  by rewrite ltn_subCr -[RHS]ltnS prednK // subn_gt0.
rewrite -ltnNge ltnS => Hi _.
rewrite drop_oversize /=; last by apply: (leq_trans Hi).
symmetry; apply/negbTE; rewrite size_rev -ltnNge ltnS.
by apply/leq_trans/Hi; rewrite -subnS; exact: leq_subr.
Qed.

Variant split_find_last_nth_spec p : seq T -> seq T -> seq T -> T -> Type :=
  FindLastNth x s1 s2 of p x & ~~ has p s2 :
    split_find_last_nth_spec p (rcons s1 x ++ s2) s1 s2 x.

Lemma split_find_last_nth x0 p s (i := find_last p s) :
  has p s -> split_find_last_nth_spec p s (take i s) (drop i.+1 s) (nth x0 s i).
Proof.
move=> p_s; rewrite -[X in split_find_last_nth_spec _ X](cat_take_drop i s).
rewrite (drop_nth x0 _); last by rewrite -has_find_last.
rewrite -cat_rcons; constructor; first by apply: nth_find_last.
by rewrite has_drop // ltnn.
Qed.

Variant split_find_last_spec p : seq T -> seq T -> seq T -> Type :=
  FindLastSplit x s1 s2 of p x & ~~ has p s2 :
    split_find_last_spec p (rcons s1 x ++ s2) s1 s2.

Lemma split_find_last p s (i := find_last p s) :
  has p s -> split_find_last_spec p s (take i s) (drop i.+1 s).
Proof.
by case: s => // x ? in i * => ?; case: split_find_last_nth => //; constructor.
Qed.

End FindLast.

Section FindLastEq.

Variables (T : eqType).
Implicit Type p : seq T.

Definition index_last (x : T) := find_last (pred1 x).

Variant splitLast x : seq T -> seq T -> seq T -> Type :=
  SplitLast p1 p2 of x \notin p2 : splitLast x (rcons p1 x ++ p2) p1 p2.

Lemma splitLastP s x (i := index_last x s) :
  x \in s -> splitLast x s (take i s) (drop i.+1 s).
Proof.
case: s => // y s in i * => H.
case: split_find_last_nth=>//; first by rewrite has_pred1.
move=>_ s1 s2 /= /eqP->; rewrite has_pred1 => H2.
by constructor.
Qed.

End FindLastEq.

Section UM.
Variables (K : ordType) (C : pred K) (V : Type) (U : union_map_class C V).

Lemma umpreim_cond (p : pred V) f k : um_preim (C:=C) (U:=U) p f k -> C k.
Proof.
rewrite /um_preim; case E: (find k f)=>[v|] //= _.
by move/find_some/dom_cond: E.
Qed.

Lemma umpreimPt (p : pred V) k v : C k -> um_preim (C:=C) (U:=U) p (pts k v) =1 [pred x | (x == k) && p v].
Proof.
move=>Hk x; rewrite /um_preim /= findPt2.
by case: eqP=>//= _; rewrite Hk.
Qed.

End UM.

Section Sep.
Variable U : pcm.
(*
Definition wand (p2 p : Pred U) : Pred U :=
  [Pred h1 | forall h2 h, h = h1 \+ h2 -> h2 \In p2 -> h \In p].
*)
Lemma sepit_perm {A} s1 s2 (f : A -> Pred U) :
        perm s1 s2 -> IterStar.sepit s1 f =p IterStar.sepit s2 f.
Proof.
elim: s1 s2 =>[|x s1 IH] s2 /=; first by move/pperm_nil=>->.
move=>H.
have Hx: x \In s2 by apply/(pperm_in H)/In_cons; left.
case: (In_split Hx)=>s21[s22] E; rewrite {s2 Hx}E in H *.
move/pperm_cons_cat_cons: H=>H.
rewrite IterStar.sepit_cons IterStar.sepit_cat /= =>h0; split.
- case=>h1[h2][{h0}-> H1]; rewrite (IH _ H) IterStar.sepit_cat.
  case=>_[_][{h2}-> [hs3][E3 -> H3] [hs4][E4 -> H4]]; rewrite joinCA.
  exists (IterStar.bigjoin hs3), (h1 \+ IterStar.bigjoin hs4); split=>//; first by exists hs3.
  by rewrite IterStar.sepit_cons; exists h1, (IterStar.bigjoin hs4); split=>//; exists hs4.
case=>_[h2][{h0}-> [hs1][Hs1 -> H1]]; rewrite IterStar.sepit_cons.
case=>h3[_][{h2}-> H3 [hs2][Hs2 -> H2]]; rewrite joinCA.
exists h3, (IterStar.bigjoin hs1 \+ IterStar.bigjoin hs2); split=>//.
rewrite (IH _ H); exists (hs1 ++ hs2); split.
- by rewrite !size_cat Hs1 Hs2.
- by rewrite /IterStar.bigjoin big_cat.
by rewrite /IterStar.bigand zip_cat //; apply/IterStar.bigand_cat.
Qed.

End Sep.
(*
Notation "p2 '--#' p" := (wand p2 p)
  (at level 58, right associativity) : rel_scope.
*)
Variant bin_node A := BN of ptr & A & ptr.

Definition bn_get {A} : bin_node A -> ptr * A * ptr :=
  fun '(BN l a r) => (l, a, r).

Definition bn_val {A} : bin_node A -> A :=
  fun '(BN _ a _) => a.

Definition bn_sub {A} : ptr * A * ptr -> bin_node A :=
  fun '(l, a, r) => BN l a r.

Lemma bn_ccl {A : Type} : ssrfun.cancel bn_get (@bn_sub A).
Proof. by case; case. Qed.

Definition binnode_eqMixin {A : eqType} := CanEqMixin (@bn_ccl A).
Canonical binnode_eqType A := Eval hnf in EqType _ (@binnode_eqMixin A).

Notation ptr_pred := (fun x : ptr => x != null).

Module Type PGSig.

Parameter tp : Type -> Type.

Section Params.
Variable A : Type.
Notation tp := (tp A).

Parameter pg_undef : tp.
Parameter defined : tp -> bool.
Parameter empty : tp.
Parameter upd : ptr -> bin_node A -> tp -> tp.
Parameter dom : tp -> seq ptr.
Parameter dom_eq : tp -> tp -> bool.
Parameter assocs : tp -> seq (ptr * bin_node A).
Parameter free : tp -> ptr -> tp.
Parameter find : ptr -> tp -> option (bin_node A).
Parameter union : tp -> tp -> tp.
Parameter empb : tp -> bool.
Parameter undefb : tp -> bool.
Parameter pts : ptr -> bin_node A -> tp.

Parameter from : tp -> @UM.base ptr_ordType ptr_pred (bin_node A).
Parameter to : @UM.base ptr_ordType ptr_pred (bin_node A) -> tp.

Axiom ftE : forall b, from (to b) = b.
Axiom tfE : forall f, to (from f) = f.
Axiom undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred (bin_node A)).
Axiom defE : forall f, defined f = UM.valid (from f).
Axiom emptyE : empty = to (@UM.empty ptr_ordType ptr_pred (bin_node A)).
Axiom updE : forall k v f, upd k v f = to (UM.upd k v (from f)).
Axiom domE : forall f, dom f = UM.dom (from f).
Axiom dom_eqE : forall f1 f2, dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Axiom assocsE : forall f, assocs f = UM.assocs (from f).
Axiom freeE : forall f k, free f k = to (UM.free (from f) k).
Axiom findE : forall k f, find k f = UM.find k (from f).
Axiom unionE : forall f1 f2, union f1 f2 = to (UM.union (from f1) (from f2)).
Axiom empbE : forall f, empb f = UM.empb (from f).
Axiom undefbE : forall f, undefb f = UM.undefb (from f).
Axiom ptsE : forall k v, pts k v = to (@UM.pts ptr_ordType ptr_pred (bin_node A) k v).

End Params.
End PGSig.

Module PGDef : PGSig.
Section PGDef.
Variable A : Type.

Definition tp : Type := @UM.base ptr_ordType ptr_pred (bin_node A).

Definition pg_undef := @UM.Undef ptr_ordType ptr_pred (bin_node A).
Definition defined f := @UM.valid ptr_ordType ptr_pred (bin_node A) f.
Definition empty := @UM.empty ptr_ordType ptr_pred (bin_node A).
Definition upd k v f := @UM.upd ptr_ordType ptr_pred (bin_node A) k v f.
Definition dom f := @UM.dom ptr_ordType ptr_pred (bin_node A) f.
Definition dom_eq f1 f2 := @UM.dom_eq ptr_ordType ptr_pred (bin_node A) f1 f2.
Definition assocs f := @UM.assocs ptr_ordType ptr_pred (bin_node A) f.
Definition free f k := @UM.free ptr_ordType ptr_pred (bin_node A) f k.
Definition find k f := @UM.find ptr_ordType ptr_pred (bin_node A) k f.
Definition union f1 f2 := @UM.union ptr_ordType ptr_pred (bin_node A) f1 f2.
Definition empb f := @UM.empb ptr_ordType ptr_pred (bin_node A) f.
Definition undefb f := @UM.undefb ptr_ordType ptr_pred (bin_node A) f.
Definition pts k v := @UM.pts ptr_ordType ptr_pred (bin_node A) k v.

Definition from (f : tp) : @UM.base ptr_ordType ptr_pred (bin_node A) := f.
Definition to (b : @UM.base ptr_ordType ptr_pred (bin_node A)) : tp := b.

Lemma ftE b : from (to b) = b. Proof. by []. Qed.
Lemma tfE f : to (from f) = f. Proof. by []. Qed.
Lemma undefE : pg_undef = to (@UM.Undef ptr_ordType ptr_pred (bin_node A)). Proof. by []. Qed.
Lemma defE f : defined f = UM.valid (from f). Proof. by []. Qed.
Lemma emptyE : empty = to (@UM.empty ptr_ordType ptr_pred (bin_node A)). Proof. by []. Qed.
Lemma updE k v f : upd k v f = to (UM.upd k v (from f)). Proof. by []. Qed.
Lemma domE f : dom f = UM.dom (from f). Proof. by []. Qed.
Lemma dom_eqE f1 f2 : dom_eq f1 f2 = UM.dom_eq (from f1) (from f2).
Proof. by []. Qed.
Lemma assocsE f : assocs f = UM.assocs (from f). Proof. by []. Qed.
Lemma freeE f k : free f k = to (UM.free (from f) k). Proof. by []. Qed.
Lemma findE k f : find k f = UM.find k (from f). Proof. by []. Qed.
Lemma unionE f1 f2 : union f1 f2 = to (UM.union (from f1) (from f2)).
Proof. by []. Qed.
Lemma empbE f : empb f = UM.empb (from f). Proof. by []. Qed.
Lemma undefbE f : undefb f = UM.undefb (from f). Proof. by []. Qed.
Lemma ptsE k v : pts k v = to (@UM.pts ptr_ordType ptr_pred (bin_node A) k v).
Proof. by []. Qed.

End PGDef.
End PGDef.

Notation pregraph := PGDef.tp.

Definition pregraphMixin A :=
  UMCMixin (@PGDef.ftE A) (@PGDef.tfE A) (@PGDef.defE A)
           (@PGDef.undefE A) (@PGDef.emptyE A) (@PGDef.updE A)
           (@PGDef.domE A) (@PGDef.dom_eqE A) (@PGDef.assocsE A)
           (@PGDef.freeE A) (@PGDef.findE A) (@PGDef.unionE A)
           (@PGDef.empbE A) (@PGDef.undefbE A) (@PGDef.ptsE A).

Canonical pregraphUMC A :=
  Eval hnf in UMC (pregraph A) (@pregraphMixin A).

(* we add the canonical projections matching against naked type *)
(* thus, there are two ways to get a PCM for a union map: *)
(* generic one going through union_map_classPCM, and another by going *)
(* through union_mapPCM. Luckily, they produce equal results *)
(* and this is just a matter of convenience *)
(* Ditto for the equality type *)

Definition pregraphPCMMix A := union_map_classPCMMix (pregraphUMC A).
Canonical pregraphPCM A := Eval hnf in PCM (pregraph A) (@pregraphPCMMix A).

Definition pregraphCPCMMix A := union_map_classCPCMMix (pregraphUMC A).
Canonical pregraphCPCM A := Eval hnf in CPCM (pregraph A) (@pregraphCPCMMix A).

Definition pregraphTPCMMix A := union_map_classTPCMMix (pregraphUMC A).
Canonical pregraphTPCM A := Eval hnf in TPCM (pregraph A) (@pregraphTPCMMix A).

Definition pregraph_eqMix (A : eqType) :=
  @union_map_class_eqMix ptr_ordType ptr_pred (binnode_eqType A) _ (@pregraphMixin A).
Canonical pregraph_eqType (A : eqType) :=
  Eval hnf in EqType (pregraph A) (@pregraph_eqMix A).

(* installing the Pred structure for writing x \In h *)
Canonical Structure pregraph_PredType A : PredType (ptr * bin_node A) :=
  Mem_UmMap_PredType (pregraphUMC A).
Coercion Pred_of_pregraph A (f : pregraph A) : Pred_Class := [eta Mem_UmMap f].

Definition pg_pts A (k : ptr) (v : bin_node A) :=
  @UMC.pts ptr_ordType ptr_pred (bin_node A) (@pregraphUMC A) k v.

(* baking ptr_pred into the notation *)
Notation "x &-> v" := (@pg_pts _ x v) (at level 30).

Fact no_null A (g : pregraph A) :
  null \notin dom g.
Proof.
by apply/negP=>/dom_cond.
Qed.

Section Bingraph.
Variable A : Type.

Definition node_shape p (n : bin_node A) :=
  let: BN l a r := n in
  [Pred h | h = p :-> l \+ (p .+ 1 :-> a \+ p .+ 2 :-> r)].

Lemma node_shapeK h1 h2 p n :
  h1 \In node_shape p n -> h2 \In node_shape p n -> h1 = h2.
Proof. by case: n=>/= l a r ->->. Qed.

Definition shape (gr : pregraph A) :=
  IterStar.sepit (assocs gr) (fun '(p,n) => node_shape p n).

Lemma shapeK h1 h2 gr :
  h1 \In shape gr -> h2 \In shape gr -> h1 = h2.
Proof.
rewrite /shape; elim/um_indf: gr h1 h2=>[||p n gr IH V P] h1 h2 /=.
- by rewrite assocs_undef; move/IterStar.sepit0=>->/IterStar.sepit0->.
- by rewrite assocs0; move/IterStar.sepit0=>->/IterStar.sepit0->.
rewrite assocsPtUn //; last by apply: path_all.
case/IterStar.sepit_cons=>h11[h12][{h1}-> H11 H12].
case/IterStar.sepit_cons=>h21[h22][{h2}-> H21 H22].
by rewrite (node_shapeK H11 H21) (IH _ _ H12 H22).
Qed.

Lemma shapeUn g1 g2 :
  valid (g1 \+ g2) ->
  shape (g1 \+ g2) =p shape g1 # shape g2.
Proof.
move=>V h; rewrite /shape.
move: (assocs_perm V)=>H.
by rewrite (sepit_perm _ H) IterStar.sepit_cat.
Qed.

Lemma shapePtUn g p n :
  valid (p &-> n \+ g) ->
  shape (pts p n \+ g) =p node_shape p n # shape g.
Proof.
move=>V h; apply: iff_trans; first by apply: shapeUn.
rewrite /shape assocsPt.
move: (validL V); rewrite validPt=>->/=; split.
- case=>h1[h2][->]; rewrite IterStar.sepit_cons.
  case=>h11[h12][-> H11]; rewrite IterStar.sepit0=>-> H2; rewrite unitR.
  by exists h11, h2.
case=>h1[h2][-> H1 H2].
exists h1, h2; split=>//.
rewrite IterStar.sepit_cons.
exists h1, Unit; split=>//; first by rewrite unitR.
by rewrite IterStar.sepit0.
Qed.

(*
(* focusing on a node *)
Lemma in_shape g p :
  p \in dom g ->
  forall h, valid h ->
  h \In shape g <-> exists n, h \In node_shape p n # (node_shape p n --# shape g).
Proof.
elim/um_indf: g.
- by rewrite dom_undef.
- by rewrite dom0.
move=>q nq g IH V P; rewrite domPtUn -topredE /= => /andP [_] /orP E h Vh.
rewrite /shape assocsPtUn //; last by apply: path_all.
case: E.
- move/eqP=>E; rewrite {q}E in V P *.
  rewrite IterStar.sepit_cons; split.
  - case=>h1[h2][E H1 H2]; exists nq, h1, h2; split=>// h22 _ -> H22.
    by apply/IterStar.sepit_cons; exists h22, h2; split=>//; rewrite joinC.
  case=>n [h1][h2][E H1 H2]; exists h1, h2; split=>//; rewrite {h}E in Vh.
  move: (H2 h1 (h2 \+ h1) erefl H1)=>/IterStar.sepit_cons [h3][h4][E2 H3 H4].
  move: (node_shapeK H3 H1)=>E3; rewrite {h3 H3}E3 joinC in E2.
  by move: (joinxK Vh E2)=>->.
- move/eqP=>->.

  case=>[{q}<-{nq}<-] h Vh; rewrite /shape IterStar.sepit_cons; split.
  - case=>h1[h2][E H1 H2]; exists h1, h2; split=>// h22 _ -> H22.
    by apply/IterStar.sepit_cons; exists h22, h2; split=>//; rewrite joinC.
  case=>h1[h2][E H1 H2]; exists h1, h2; split=>//; rewrite {h}E in Vh.
  move: (H2 h1 (h2 \+ h1) erefl H1)=>/IterStar.sepit_cons [h3][h4][E2 H3 H4].
  move: (node_shapeK H3 H1)=>E3; rewrite {h3 H3}E3 joinC in E2.
  by move: (joinxK Vh E2)=>->.
move/IH=>{}IH h Vh; rewrite /shape IterStar.sepit_cons; split.
- case=>h1[h2][E H1 /[dup] H2]; rewrite E in Vh.
  case/(IH h2 (validR Vh))=>h3[h4][E2 H3 H4].
  exists h3, (h1 \+ h4); rewrite E E2 joinCA; split=>// h5 _ -> H5.
  move: (node_shapeK H5 H3)=>{h5 H5}->; rewrite IterStar.sepit_cons.
  by exists h1, h2; split=>//; rewrite E2 joinA joinAC.
case=>h1[h2][E H1 H2].
move: (H2 h1 h); rewrite joinC => /(_ E H1).
by rewrite IterStar.sepit_cons; case=>h3[h4][E2 H3 H4]; exists h3, h4.
Qed.


case: n=>p l r V + Hg; case/(in_shape Hg V)=>h1[h2][E H1 _].
by rewrite E H1 in V.
Qed.
*)

Definition forget : bin_node A -> bin_node unit :=
  fun '(BN l _ r) => BN l tt r.

Definition structure : pregraph A -> pregraph unit :=
  mapv forget.

Lemma dom_structure g : dom (structure g) = dom g.
Proof. by apply: dom_omap_some. Qed.

Lemma structure_dom_eq g1 g2 : structure g1 = structure g2 -> dom g1 =i dom g2.
Proof. by move=>Hs; rewrite -dom_structure Hs dom_structure. Qed.

Lemma valid_structure g : valid (structure g) = valid g.
Proof. by rewrite valid_omap. Qed.

Lemma structurePt p n :
  structure (p &-> n) = p &-> forget n.
Proof.
rewrite /structure omapPt; case: ifP=>// /negbT/negbNE/eqP {p}->.
by symmetry; apply/invalidE; rewrite validPt.
Qed.

Lemma structurePtUn p n g :
  structure (p &-> n \+ g) = p &-> forget n \+ structure g.
Proof.
rewrite {1}/structure omapPtUn /=.
case: ifP=>// /negbT V; symmetry; apply/invalidE.
rewrite !validPtUn in V *.
by rewrite valid_structure dom_structure.
Qed.

Corollary structureUnPt p n g :
  structure (g \+ p &-> n) = structure g \+ p &-> forget n.
Proof. by rewrite joinC structurePtUn joinC. Qed.

Lemma find_structure x g :
  find x (structure g) = ssrfun.omap forget (find x g).
Proof. by rewrite /structure find_omap. Qed.

(*
Definition struct_eq (g1 g2 : pregraph A) : Prop :=
  um_all2 (fun '(BN l1 _ r1) '(BN l2 _ r2) => (l1 == l2) && (r1 == r2)) g1 g2.

Lemma struct_eq_refl g : struct_eq g g.
Proof.
by apply: umall2_refl; case=>l _ r; rewrite !eq_refl.
Qed.
*)
Definition good_ptr (g : pregraph A) p : bool := (p == null) || (p \in dom g).

Lemma good_dom (g1 g2 : pregraph A) : dom g1 =i dom g2 -> good_ptr g1 =1 good_ptr g2.
Proof.
by move=>H p; rewrite /good_ptr; case: eqP=>/=.
Qed.
(*
Lemma good_dom (g1 g2 : pregraph A) p : dom_eq g1 g2 -> good_ptr g1 <-> good_ptr g2.
Proof.
move=>H; rewrite /good_ptr; case: eqP=>//= Hp.
move/domeqP: H =>[_ H].
by rewrite (H p).
Qed.
*)
(*
Definition good_graph (g : pregraph A) : Prop :=
  forall p l a r, find p g = Some (BN l a r) -> good_ptr l g && good_ptr r g.
*)

Definition good_graph_b (g : pregraph A) : bool :=
  valid g &&
  all (fun '(BN l _ r) => good_ptr g l && good_ptr g r) (range (structure g)).

Lemma good_eq g1 g2 :
  valid g1 = valid g2 -> structure g1 = structure g2 ->
  good_graph_b g1 = good_graph_b g2.
Proof.
rewrite /good_graph_b =>->/[dup] Hs ->; case: (valid g2)=>//=.
apply: eq_all; case=>l _ r; rewrite /good_ptr.
by rewrite -!dom_structure Hs.
Qed.

Definition plink (p : pred A) (g : pregraph A) (x : ptr) : bool * seq ptr :=
  match find x g with
  | Some (BN l a r) => (p a, filter (fun x => x \in dom g) [::l;r])
  | None => (false, [::])
  end.

Definition prel (p : pred A) (g : pregraph A) :=
  [rel x y | (plink p g x).1 && (y \in (plink p g x).2)].

Fixpoint dfs (p : pred A) (g : pregraph A) n (v : seq ptr) x :=
  if (x \in v) || ~~ (plink p g x).1 then v else
  if n is n'.+1 then foldl (dfs p g n') (x :: v) (plink p g x).2 else v.

Lemma plinkF p g x : x \notin dom g -> plink p g x = (false, [::]).
Proof.
by rewrite /plink; move/find_none=>->.
Qed.

Lemma plinkT p g x xs : plink p g x = (true, xs) ->
                        (x \in dom g) * (all (fun z => z \in dom g) xs).
Proof.
rewrite /plink.
case Hf: (find x g)=>[[l a r]|]; last by case.
case=>? <-; split; first by move/find_some: Hf.
rewrite -/(filter (fun x => x \in dom g) [::l;r]) all_filter.
by apply/sub_all/all_predT=>z _ /=; apply: implybb.
Qed.

Lemma subset_dfs p g n v a : {subset v <= foldl (dfs p g n) v a}.
Proof.
elim: n a v => [|n IHn].
- elim=>/=[|h t IH] v; first by move=>?.
  by rewrite if_same.
elim=>/=[|h t IHa v]; first by move=>?.
move=>x Hx; apply: IHa; case: ifP=>//= _.
by apply: IHn; rewrite inE Hx orbT.
Qed.

(* hacky *)
Lemma subset_foldl_dfs_dom p g n v x :
  {subset v <= dom g} ->
  {subset foldl (dfs p g n) v x <= dom g}.
Proof.
elim: n x v=>/=[|n IH].
- by elim=>//= h t IH v; rewrite if_same; apply: IH.
elim=>//=h t IHx v Hv; case: ifP=>/=; first by move=>_; apply: IHx.
move/negbT; rewrite negb_or; case/andP=>_ /negbNE.
case Ep: (plink p g h)=>[px ls] /= Hpx; rewrite {px}Hpx in Ep.
case: (plinkT Ep)=>Hh _.
apply/IHx/IH=>z; rewrite inE; case/orP; last by apply/Hv.
by move/eqP=>{z}->.
Qed.

Corollary subset_dfs_dom p g n v x :
  {subset v <= dom g} ->
  {subset dfs p g n v x <= dom g}.
Proof.
case: n=>/= [|n] H; first by rewrite if_same.
move=>z; case: ifP; first by move=>_ /H.
move/negbT; rewrite negb_or; case/andP=>Hx /negbNE.
case Ep: (plink p g x)=>[px ls] /= Hpx; rewrite {px}Hpx in Ep.
apply: subset_foldl_dfs_dom=>{}z; rewrite inE; case/orP; last by apply/H.
by move/eqP=>{z}->; case: (plinkT Ep).
Qed.

Lemma uniq_dfs_foldl p g n v x : uniq v -> uniq (foldl (dfs p g n) v x).
Proof.
elim: n x v=>/=[|n IH].
- by elim=>//= h t IH v; rewrite if_same; apply: IH.
elim=>//=h t IHx v Hv; case: ifP=>/=; first by move=>_; apply: IHx.
move/negbT; rewrite negb_or; case/andP=>Hx _.
by apply/IHx/IH=>/=; rewrite Hx.
Qed.

Corollary uniq_dfs p g n v x :
  uniq v ->
  uniq (dfs p g n v x).
Proof.
case: n=>/= [|n] H; first by rewrite if_same.
case: ifP=>//.
move/negbT; rewrite negb_or; case/andP=>Hx _.
by apply: uniq_dfs_foldl=>/=; rewrite Hx.
Qed.

Definition p_val (p : pred A) (g : pregraph A) : applicative_pred ptr :=
  [pred x | um_preim (p \o bn_val) g x].

(* TODO umpreim_neg ? *)
Lemma pvalNeg p g x :
  x \in dom g ->
  p_val p g x = ~~ p_val (negb \o p) g x.
Proof.
case: dom_find=>// n.
rewrite /p_val /= /um_preim=>-> _ _ /=.
by case: negPn=>// /negP/negbTE.
Qed.

Lemma pvalPtUn p x n g y :
  valid (x &-> n \+ g) ->
  p_val p (x &-> n \+ g) y = ((x == y) && p (bn_val n)) || p_val p g y.
Proof.
move=>V; rewrite /p_val /= umpreimUn //= umpreimPt /=; first by rewrite eq_sym.
by move: V; rewrite validPtUn; case/and3P.
Qed.

Lemma plink_val p g x : p_val p g x = (plink p g x).1.
Proof.
by rewrite /plink /p_val /= /um_preim; case: (find x g)=>//=; case.
Qed.

Corollary pval_dom p g x : p_val p g x -> x \in dom g.
Proof.
apply/contraLR=>/(plinkF p).
by rewrite (surjective_pairing (plink _ _ _)); case; rewrite -plink_val =>/negbT.
Qed.

Lemma plink_conn (p : pred A) g x l r :
  find x (structure g) = Some (BN l tt r) ->
  (plink p g x).2 = filter (fun x => x \in dom g) [::l;r].
Proof.
rewrite find_structure /plink.
by case: (find x g)=>//=; case=>_ a _ [->->].
Qed.

Lemma plink_struct p g1 g2 x :
  x \in dom g1 ->
  structure g1 = structure g2 ->
  (plink p g1 x).2 =i (plink p g2 x).2.
Proof.
move=>Hx Hs y.
have: find x (structure g1) = find x (structure g2) by rewrite Hs.
case E2: (find x (structure g2))=>[[l2 [] r2]|].
- move/(plink_conn p)=>->.
  by rewrite (plink_conn p E2) !mem_filter -!dom_structure Hs.
by move/find_none; rewrite dom_structure Hx.
Qed.

Variant dfs_path (p : pred A) g (v : seq ptr) x y : Prop :=
  DfsPath xs of
    path (prel p g) x xs &
    y = last x xs &
    p_val p g y &
    all (fun z => z \notin v) (x::xs).

Lemma dfs_path_id p g v x :
  p_val p g x -> x \notin v -> dfs_path p g v x x.
Proof.
move=>Hx Hv; apply (DfsPath (xs:=[::]))=>//=.
by rewrite andbT.
Qed.

Lemma full_path_dom p g x y xs :
  path (prel p g) x xs ->
  y = last x xs ->
  p_val p g y ->
  all (fun z => z \in dom g) (x::xs).
Proof.
move=>+ + Hy; elim: xs x=>/=[|a xs IH] x.
- by move=>_ E; move: Hy; rewrite E andbT =>/pval_dom.
case/andP; case/andP; rewrite -plink_val=>/pval_dom-> _ H1 H2 /=.
by apply: IH.
Qed.

Lemma dfs_pathP p g n x y v :
  size (dom g) <= size v + n ->
  uniq v ->
  {subset v <= dom g} ->
  y \notin v ->
  reflect (dfs_path p g v x y) (y \in dfs p g n v x).
Proof.
case/boolP: (y \in dom g); last first.
- move=>Hy Hv Uv Sv Ny.
  move/contra: (@subset_dfs_dom p _ n _ x Sv y) =>/(_ Hy)/negbTE->.
  by apply: ReflectF; case=>xs _ _; rewrite plink_val (plinkF _ Hy).
elim: n => [|n IHn] /= in x y v * => Hy Hv Uv Sv Ny.
- rewrite addn0 in Hv.
  by case: (uniq_min_size Uv Sv Hv) Ny=>_ /(_ y); rewrite Hy=>->.
case Epl: (plink p g x)=>[px ls] /=.
have [Vx|] := ifPn.
- move/negbTE: (Ny)=>->; apply: ReflectF; case=>/= xs.
  case/orP: Vx; first by move=>->.
  move/negbTE=>Epx; rewrite {px}Epx in Epl.
  case: xs=>/=; last by rewrite Epl.
  by move=>_ ->; rewrite plink_val Epl.
rewrite negb_or; case/andP=>Nx /negbNE Px; rewrite {px}Px in Epl.
set v1 := x :: v; have [-> | Nyx] := eqVneq y x.
- rewrite subset_dfs; last by rewrite inE eq_refl.
  apply: ReflectT; apply: dfs_path_id=>//.
  by rewrite plink_val Epl.
apply: (@equivP (exists2 x1, x1 \in ls & dfs_path p g v1 x1 y)); last first.
- split=> {IHn} [[x1 Hx1 [p1 P1 Ey Py]] | [p1 /shortenP []]] /=.
  - case/andP; rewrite inE negb_or; case/andP =>Ex1 Nx1 Ha1; apply: (DfsPath (xs:=x1::p1))=>//=.
    - by rewrite Epl /= Hx1.
    by rewrite Nx Nx1 /=; apply/sub_all/Ha1=>z; rewrite inE negb_or; case/andP.
  case=>[_ _ _ /= Eyx | x1 xs /=]; first by case/eqP: Nyx.
  rewrite Epl /=. case/andP=>Hx1 Hp1 /and3P [H11 H12 H13] H2 H3 H4 /andP [H5 H6].
  exists x1=>//; apply: (DfsPath (xs:=xs))=>//.
  apply/allP=>z /[dup] Hz /H2; move/allP: H6=>/(_ z) /[apply].
  rewrite !inE negb_or=>->; rewrite andbT; apply/negP=>/eqP Ez.
  by rewrite -Ez Hz in H11.
have{Nyx Ny}: y \notin v1 by apply/norP.
have{Nx Uv}: uniq v1 by rewrite /= Nx.
have{Sv}: {subset v1 <= dom g}.
- move=>z; rewrite inE; case/orP; last by move/Sv.
  by move/eqP=>{z}->; case: (plinkT Epl).
have{Hv}: size (dom g) <= size v1 + n by rewrite addSnnS.
case/plinkT: Epl=>_ Hl.
elim: {x v}ls Hl v1 => /= [_|x a IHa /andP [Ha Hl]] v /= Hv Sv Uv Nv.
- by rewrite (negPf Nv); apply: ReflectF; case.
set v2 := dfs p g n v x; have v2v: {subset v <= v2} := @subset_dfs p g n v [:: x].
have [Hy2 | Ny2] := boolP (y \in v2).
- rewrite subset_dfs //; apply: ReflectT; exists x; first by rewrite inE eq_refl.
  by apply/IHn.
apply: {IHa}(equivP (IHa Hl _ _ _ _ Ny2)).
- by apply: (leq_trans Hv); rewrite leq_add2r; apply: uniq_leq_size.
- by apply: subset_dfs_dom.
- by apply: uniq_dfs.
split=> [] [x1 Hx1 [p1 P1 Ey Py Nay]].
  exists x1; first by rewrite inE Hx1 orbT.
  by apply: (DfsPath (xs:=p1))=>//; apply/sub_all/Nay=>z; apply/contra/v2v.
suff Nv2: all (fun z => z \notin v2) (x1 :: p1).
- move: Hx1; rewrite inE; case/orP=>[/eqP Ex1|Hx1]; last first.
  - by exists x1=>//; apply: (DfsPath (xs:=p1)).
  rewrite {x1}Ex1 in P1 Ey Nay Nv2.
  exfalso; move: Nv2=>/=; case/andP=>+ _; move/negbTE/negP; apply.
  suff Nx: x \notin v.
  - apply/IHn=>//; apply: dfs_path_id=>//.
    case: {Nay}p1 P1 Ey=>/=[_|??]; first by move=><-.
    by case/andP; case/andP; rewrite plink_val.
  by case/andP: Nay.
apply: contraR Ny2; case/allPn => x2 Hx2 /negbNE Hx2v.
case/splitPl: Hx2 Ey P1 Nay => p0 p2 p0x2.
rewrite last_cat cat_path -cat_cons lastI cat_rcons {}p0x2 => p2y /andP[_ g_p2].
rewrite all_cat /= => /and3P[{p0}_ not_vx2 not_p2v].
have H2d : x2 \in dom g.
- case: {not_p2v}p2 p2y g_p2=>/=[<-|??] // _.
  case Epl: (plink p g x2)=>[uu vv] /=; case/andP; case/andP=>H0.
  by rewrite H0 in Epl; case: (plinkT Epl).
have{not_vx2 Hx2v} [p3 g_p1 p1_x2 V2 not_p1v] := (IHn _ _ v H2d Hv Uv Sv not_vx2 Hx2v).
apply/IHn=>//; exists (p3 ++ p2)=>//.
- by rewrite cat_path g_p1 -p1_x2.
- by rewrite last_cat -p1_x2.
by rewrite -cat_cons all_cat not_p1v.
Qed.

Definition component p g x : seq ptr := dfs p g (size (dom g)) [::] x.

Definition connect p g : rel ptr := [rel x y | y \in component p g x].
Canonical connect_app_pred p g x := ApplicativePred (connect p g x).

Corollary connectP p g x y :
  reflect (exists xs, [/\ path (prel p g) x xs, y = last x xs & p_val p g y])
          (connect p g x y).
Proof.
apply: (iffP (dfs_pathP _ _ _ _ _ _))=>//.
- by case=>xs P Ey Pv _; exists xs.
case=>xs [P Ey Pv]; apply: (DfsPath (xs:=xs))=>//.
by apply/sub_all/all_predT.
Qed.

Lemma connect_trans p g : transitive (connect p g).
Proof.
move=> x y z /connectP [xs][Hxs -> Hp] /connectP [ys][Hys -> Hp']; apply/connectP.
by exists (xs ++ ys); rewrite cat_path last_cat Hxs.
Qed.

Lemma connect0 p g x : p_val p g x -> connect p g x x.
Proof. by move=>H; apply/connectP; exists [::]. Qed.

Lemma eq_connect0 p g x y : x = y -> p_val p g x -> connect p g x y.
Proof. by move->; apply: connect0. Qed.

Lemma connect1 p g x y : prel p g x y -> p_val p g y -> connect p g x y.
Proof. by move=>/= Hp Hy; apply/connectP; exists [:: y]; rewrite /= Hp Hy. Qed.

Lemma connect_dom p g x :
  subpred (connect p g x) (fun x => x \in dom g).
Proof.
move=>z; rewrite app_predE.
by case/connectP=>_ [_ _]; apply: pval_dom.
Qed.

Lemma connect_notp p g x :
  ~~ p_val p g x -> connect p g x =i pred0.
Proof.
move=>Hx y; rewrite [RHS]inE; apply/negbTE/connectP.
case=>xs [+ {y}-> +]; case: xs=>/= [_ | h t];
by rewrite -?plink_val (negbTE Hx).
Qed.

Corollary connect_not p g x : x \notin dom g -> connect p g x =i pred0.
Proof.
move=>Hx; apply: connect_notp.
by rewrite plink_val (plinkF _ Hx).
Qed.

Lemma connect_sub p g1 g2 x :
  structure g1 = structure g2 ->
  {in dom g1, subpred (p_val p g1) (p_val p g2) } ->
  subpred (connect p g1 x) (connect p g2 x).
Proof.
move=>Hs Hp z; case/connectP=>xs [Hxs {z}-> H].
apply/connectP; exists xs; split=>//; last first.
- by apply: Hp=>//; apply/pval_dom/H.
elim: xs x Hxs H=>//= h xs IH y.
rewrite -!plink_val; case/andP; case/andP=>H1 H2 H3 H4.
rewrite -andbA; apply/and3P; split; last by apply: IH.
- by apply: Hp=>//; apply/pval_dom/H1.
rewrite -(plink_struct _ _ Hs) //; apply/pval_dom/H1.
Qed.

(*
Lemma connect_foo p g1 g2 x (q : pred ptr) :
  structure g1 = structure g2 ->
  {in dom g1, forall y, p_val p g1 y = (y \notin connect p g2 x) && p_val p g2 y} ->
  forall y, (y \in connect p g1 x) = (y \notin connect p g2 x).
Proof.
move=>Hs Hp z. case/connectP=>xs [Hxs {z}-> H].
apply/connectP; exists xs; split=>//; last first.
- by apply: Hp=>//; apply/pval_dom/H.
elim: xs x Hxs H=>//= h xs IH y.
rewrite -!plink_val; case/andP; case/andP=>H1 H2 H3 H4.
rewrite -andbA; apply/and3P; split; last by apply: IH.
- by apply: Hp=>//; apply/pval_dom/H1.
rewrite -(plink_struct _ _ Hs) //; apply/pval_dom/H1.
Qed.
*)

(*
Lemma connect_lift p g1 g2 x :
  structure g1 = structure g2 ->
  p_val p g1 =1 p_val p g2 ->
  connect p g1 x =i connect p g2 x.
Proof.
have connect_sub p' g3 g4 y:
  structure g3 = structure g4 ->
  p_val p' g3 =1 p_val p' g4 -> subpred (connect p' g3 y) (connect p' g4 y).
 - move=>Hs Hp z; case/connectP=>xs [Hxs {z}-> H].
   apply/connectP; exists xs; split=>//; last by rewrite -Hp.
   elim: xs y Hxs H=>//= h xs IH y.
   rewrite -!plink_val; case/andP; case/andP=>H1 H2 H3 H4.
   rewrite -Hp H1 /= IH // andbT -(plink_struct _ _ Hs) //.
   by apply/pval_dom/H1.
by move=>Hs Hp y; apply/iffE; split; apply: connect_sub.
Qed.
*)

Lemma connect_links_sub (p : pred A) g x l r :
  find x (structure g) = Some (BN l tt r) ->
  {subset connect p g x <= predU (pred1 x) (predU (connect p g l) (connect p g r))}.
Proof.
move=>Hx y; rewrite !inE.
case/connectP=>xs [Hp {y}-> H].
case: xs Hp H=>/=; first by move=>_ _; rewrite eq_refl.
move=>n xs; move: Hx; rewrite /plink find_structure.
case: (find x g)=>[[_ a _]|] // [->->].
case/andP; case/andP=>Hp.
rewrite mem_filter !inE; case/andP=>Hn; case/orP=>/eqP E; rewrite {n}E in Hn *;
move=>Hxs Hpv.
- suff: connect p g l (last l xs) by move=>-> /=; rewrite orbT.
  by apply/connectP; exists xs.
suff: connect p g r (last r xs) by move=>->; rewrite !orbT.
by apply/connectP; exists xs.
Qed.

(*
Lemma connect_links (p : pred A) g x l a r :
  find x g = Some (BN l a r) ->
  {subset connect p g x <= predU (pred1 x) (predU (connect p g l) (connect p g r))}.
Proof.
move=>Hx y; rewrite !inE.
case/connectP=>xs [Hp {y}-> H].
case: xs Hp H=>/=; first by move=>_ _; rewrite eq_refl.
move=>n xs; rewrite /plink Hx; case/andP; case/andP=>Hp.
rewrite mem_filter !inE; case/andP=>Hn; case/orP=>/eqP E; rewrite {n}E in Hn *;
move=>Hxs Hpv.
- suff: connect p g l (last l xs) by move=>-> /=; rewrite orbT.
  by apply/connectP; exists xs.
suff: connect p g r (last r xs) by move=>->; rewrite !orbT.
by apply/connectP; exists xs.
Qed.
*)

Lemma connect_eq_links (p : pred A) g x l a r :
  find x g = Some (BN l a r) ->
  p a ->
  good_ptr g l ->
  good_ptr g r ->
  connect p g x =i predU (pred1 x) (predU (connect p g l) (connect p g r)).
Proof.
move=>Hx Ha Hl Hr y; apply/iffE; split.
- by apply: connect_links_sub; rewrite find_structure Hx.
case/or3P.
- move/eqP=>->; apply: connect0.
  by rewrite plink_val /plink Hx.
- case/connectP=>xs [Hp {y}-> H]; apply/connectP.
  exists (l::xs)=>/=; split=>//; rewrite Hp andbT /plink Hx Ha /=.
  case/orP: Hl.
  - move/eqP=>E; move: Hp H; rewrite E; case: xs=>/=.
    - by move=>_ /umpreim_cond.
    by move=>??; case/andP; case/andP; rewrite -plink_val => /umpreim_cond.
  by move=>->; rewrite inE eq_refl.
case/connectP=>xs [Hp {y}-> H]; apply/connectP.
exists (r::xs)=>/=; split=>//; rewrite Hp andbT /plink Hx Ha /=.
case/orP: Hr.
- move/eqP=>E; move: Hp H; rewrite E; case: xs=>/=.
  - by move=>_ /umpreim_cond.
  by move=>??; case/andP; case/andP; rewrite -plink_val => /umpreim_cond.
by move=>->; case: ifP=>_; rewrite !inE eq_refl // orbT.
Qed.

(*)
Lemma path_connect p g x xs : path (prel p g) x xs -> p_val p g x ->
                              subpred (mem (x :: xs)) (connect p g x).
Proof.
move=>e_p Hx y p_y; case/splitPl: xs / p_y e_p => xs ys <-.
rewrite cat_path => /andP[e_p e_y]; apply/connectP; exists xs; split=>//.
elim: xs x Hx e_p e_y=>//=h xs IH x Hx; case/andP; case/andP=>??? H.
apply: IH=>//.
Qed.
*)

End Bingraph.

Section ExampleCyclic.
Definition p1 := ptr_nat 1.
Definition p2 := ptr_nat 2.
Definition p3 := ptr_nat 3.
Definition p4 := ptr_nat 4.
Definition p5 := ptr_nat 5.
Definition p6 := ptr_nat 6.
Definition p7 := ptr_nat 7.
Definition p8 := ptr_nat 8.

(* https://www.comp.nus.edu.sg/~hobor/Teaching/SW-PhD.pdf#1f *)

Definition ex : pregraph unit :=
  p1 &-> BN p2   tt p3   \+
  p2 &-> BN p4   tt p5   \+
  p3 &-> BN p6   tt p7   \+
  p4 &-> BN null tt null \+
  p5 &-> BN p5   tt p8   \+
  p6 &-> BN p1   tt p8   \+
  p7 &-> BN null tt null \+
  p8 &-> BN p4   tt p7.

End ExampleCyclic.

Section BoolGraph.

Definition upd_val {A} (p : ptr) (v : A) (g : pregraph A) : pregraph A :=
  match find p g with
  | Some (BN l _ r) => upd p (BN l v r) g
  | None => undef
  end.

Lemma struct_upd_val {A} p (v : A) g :
  p \in dom g ->
  structure (upd_val p v g) = structure g.
Proof.
rewrite /upd_val; case/um_eta=>[[l a r][-> {2}->]].
by rewrite upd_eta !structurePtUn.
Qed.

Lemma valid_upd_val {A} p (v : A) g :
  p \in dom g -> valid (upd_val p v g) = valid g.
Proof.
rewrite /upd_val=>/[dup]/dom_cond Hp; case/um_eta=>[[l a r][-> H]].
by rewrite validU Hp.
Qed.

Lemma upd_val_eta {A} (g : pregraph A) p (v : A) l r :
  find p (structure g) = Some (BN l tt r) ->
  upd_val p v g = p &-> BN l v r \+ free g p.
Proof.
rewrite find_structure /upd_val => Hs.
case: (find p g) Hs=>[[_ x _]|] // [->->].
by apply: upd_eta.
Qed.

(* TODO generalize to "frame"? *)
Lemma pval_neq {A} (g : pregraph A) p x y :
  valid g ->
  x \in dom g ->
  x != y ->
  p_val p (free g x) y = p_val p g y.
Proof.
move=>Vg + Nxy; case/um_eta=>[[l a r][E H]].
rewrite {2}H pvalPtUn /=; last by rewrite H in Vg.
by rewrite (negbTE Nxy).
Qed.

(* pval_neq baked in *)
Lemma pval_upd_val {A} (g : pregraph A) p (v : A) x y :
  valid g ->
  x \in dom g ->
  p_val p (upd_val x v g) y =
    if x == y then p v else p_val p g y.
Proof.
move=>Vg /[dup] Hx; case/um_eta=>[[l a r][E H]].
have Es : find x (structure g) = Some (BN l tt r) by rewrite find_structure E.
rewrite (upd_val_eta _ Es) pvalPtUn /=; last first.
- by move: Vg; rewrite {1}H !validPtUn.
case: eqP=>/= [{y}<-|/eqP]; last by apply: pval_neq.
case: (p v)=>//=.
by rewrite plink_val plinkF // domF inE eq_refl.
Qed.

(* TODO adhoc *)
Lemma connect_upd_true (g : pregraph bool) p l r y :
  valid g ->
  find p (structure g) = Some (BN l tt r) ->
  p != y ->
  (y \in connect negb g l) || (y \in connect negb g r) ->
  let g1 := upd_val p true g in
  (y \in connect negb g1 l) || (y \in connect negb g1 r).
Proof.
move=>Vg Hp Np.
have Hd: p \in dom g by rewrite -dom_structure; apply: (find_some Hp).
case/orP.
- case/connectP=>xs [Hxs Ey Hy].
  (* the difference between g and g1 is only the value of p *)
  (* so connectivity depends on whether it's reachable from l (use cycle lemmas?) *)
  case Hpxs: (p \in l::xs); last first.
  - apply/orP; left; apply/connectP; exists xs; split=>//; last first.
    - by rewrite pval_upd_val // (negbTE Np).

    rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
      by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
    move/negbT: Hpxs; rewrite inE negb_or; case/andP=>Hpl Hpxs.
    move: (full_path_dom Hxs Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
    apply/andP; split; first by rewrite eq_sym.
    rewrite all_predI Ha andbT; apply/allP=>z Hz.
    by apply/negP=>/eqP Ez; rewrite -Ez Hz in Hpxs.
  (* find the suffix of the path after the last p *)
  case: {-1}_ _ _ / (splitLastP Hpxs) (erefl (l::xs)) =>{Hpxs} xs1 xs2 Hxs2.
  case: xs1=>/=.
  - (* p's left link is a loop, so xs starts with r *)
    case=>Elp Exs; rewrite -{xs2}Exs in Hxs2.
    rewrite Elp in Hxs Ey.
    case: xs Hxs Ey Hxs2 =>/=.
    - by move=>_ Eyp; rewrite Eyp eq_refl in Np.
    move=>r' xs; case/andP; case/andP=>_.
    rewrite (plink_conn negb (l:=l) (r:=r)) // mem_filter; case/andP=>Hr'.
    rewrite !inE; case/orP.
    - by move/eqP=>-> _ _; rewrite Elp eq_refl.
    move/eqP=>E'; rewrite {r'}E' in Hr' *.
    rewrite negb_or=> Hr Ey; case/andP =>Npr Nxs.
    apply/orP; right; apply/connectP; exists xs.
    split=>//; last by rewrite pval_upd_val // (negbTE Np).

    rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
      by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
    move: (full_path_dom Hr Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
    apply/andP; split; first by rewrite eq_sym.
    rewrite all_predI Ha andbT; apply/allP=>z Hz.
    by apply/negP=>/eqP Ez; rewrite -Ez Hz in Nxs.
  (* xs2 can only start with l or p, this decides the component *)
  move=>_ xs1 [_ Exs]; rewrite {xs}Exs in Hxs Ey.
  case: xs2 Ey Hxs Hxs2 =>/=.
  - by rewrite cats0 last_rcons => Eyp; rewrite Eyp eq_refl in Np.
  move=>h xs2; rewrite cat_path last_cat last_rcons /= => Ey.
  case/and3P=>_; case/andP=>_.
  rewrite (plink_conn negb (l:=l) (r:=r)) // mem_filter; case/andP=>Hh.
  rewrite !inE negb_or; case/orP=>/eqP Eh;
  rewrite {h}Eh in Ey Hh *; move=>Hxs2; case/andP=>Np' Npxs2.
  - apply/orP; left.
    apply/connectP; exists xs2; split=>//; last first.
    - by rewrite pval_upd_val // (negbTE Np).

    rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
      by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
    move: (full_path_dom Hxs2 Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
    apply/andP; split; first by rewrite eq_sym.
    rewrite all_predI Ha andbT; apply/allP=>z Hz.
    by apply/negP=>/eqP Ez; rewrite -Ez Hz in Npxs2.

  apply/orP; right.
  apply/connectP; exists xs2; split=>//; last first.
  - by rewrite pval_upd_val // (negbTE Np).

  rewrite (eq_in_path (P:=fun x => (x != p) && (x \in dom g)) (e':=prel negb g)) //.
  - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
    have Hst : find x' (structure g) = Some (BN vl tt vr) by rewrite find_structure Hdx'.
    rewrite -!plink_val pval_upd_val // eq_sym (negbTE Hx') /=.
    rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite struct_upd_val.
    by rewrite !mem_filter (structure_dom_eq (g2:=g)) // struct_upd_val.
  move: (full_path_dom Hxs2 Ey Hy)=>/=; case/andP=>-> Ha; rewrite andbT.
  apply/andP; split; first by rewrite eq_sym.
  rewrite all_predI Ha andbT; apply/allP=>z Hz.
  by apply/negP=>/eqP Ez; rewrite -Ez Hz in Npxs2.

(* TOOO copypaste *)

Admitted.

Definition mark_eq (x : ptr) (g1 g2 : pregraph bool) :=
  forall y, p_val id g2 y = (y \in connect negb g1 x) || p_val id g1 y.

Lemma mark_eq_sub x g1 g2 :
  mark_eq x g1 g2 ->
  subpred (p_val id g1) (p_val id g2).
Proof. by move=>Hm z; move: (Hm z)=>->->; rewrite orbT. Qed.

Lemma mark_eq_neg x g1 g2 :
  dom g1 =i dom g2 ->
  mark_eq x g1 g2 ->
  {in dom g2, forall y, p_val negb g2 y = (y \notin connect negb g1 x) && p_val negb g1 y}.
Proof.
move=>Hd Hm z Hz; move: (Hm z); rewrite pvalNeg //.
move/negbRL; rewrite negb_or=>->; case: (z \notin connect negb g1 x)=>//=.
by rewrite pvalNeg; [rewrite negbK | rewrite Hd].
Qed.
(*
Lemma mark_eq_conn x g1 g2 :
  mark_eq x g1 g2 ->
  {in dom g1, forall y, y \in connect negb g1 x = p_val negb g1 y && p_val id g2 y}.
Proof.
move=>Hm z Hz; move: (Hm z)=>->.
case E: (z \in connect negb g1 x)=>/=.
- rewrite andbT; symmetry.
  by case/connectP: E=>? [].
by rewrite andbC pvalNeg // andNb.
Qed.
*)
Corollary mark_eq_sub_neg x g1 g2 :
  dom g1 =i dom g2 ->
  mark_eq x g1 g2 ->
  {in dom g2, subpred (p_val negb g2) (p_val negb g1) }.
Proof. by move=>Hd Hm z Hz; rewrite (mark_eq_neg Hd Hm) //; case/andP. Qed.

Definition mark_rel (x : ptr) (g1 g2 : pregraph bool) :=
  structure g1 = structure g2 /\ mark_eq x g1 g2.

Definition markT : Type := forall (p : ptr),
  {gr : pregraph bool},
  STsep (fun h => [/\ h \In shape gr, good_graph_b gr & good_ptr gr p],
        [vfun (_ : unit) h => exists gr',
                  [/\ h \In shape gr', valid gr' & mark_rel p gr gr']]).

Program Definition mark : markT :=
  Fix (fun (go : markT) p =>
    Do (if p == null then ret tt
        else m <-- !(p.+ 1);
             if m then ret tt
             else l <-- !p;
                  r <-- !(p.+ 2);
                  p.+ 1 ::= true;;
                  go l;;
                  go r)).
Next Obligation.
move=>go p [gr][] i /= [Hg Hgg Hp]; apply: vrfV=>V; case/orP: Hp.
- move=>/eqP->; rewrite eq_refl; step=>_.
  exists gr; do!split=>//; first by case/andP: Hgg.
  move=>x; rewrite connect_not //.
  by apply/find_none/cond_find.
move/[dup]/dom_cond/[dup]=>Np /negbTE ->.
case/um_eta; case=>l a r [Hp Hgr].
case/andP: (Hgg)=>Vg Eg; rewrite Hgr in Vg Hg.
case/(shapePtUn Vg): (Hg)=>i1[i2][E H1 H2].
rewrite E H1; step; case: a Hp Hgr Vg Hg H1=>/=Hp Hgr Vg Hg H1.
- step=>V1; exists gr; rewrite {1 2}Hgr Vg -H1 -E; do!split=>//.
  move=>y; rewrite orbC; case: (p_val id gr y)=>//=; symmetry; apply/negbTE.
  by rewrite connect_notp // plink_val /plink Hp.
do 3!step.
have Hp' : p_val negb gr p by rewrite plink_val /plink Hp.
set gr0 := p &-> BN l true r \+ free gr p.
have Hs0 : structure gr = structure gr0 by rewrite Hgr /gr0 !structurePtUn.
have V0 : valid gr0 by rewrite !validPtUn in Vg *.
have Hg0 : good_graph_b gr0 by rewrite (good_eq (g2:=gr)) // /gr0 {2}Hgr !validPtUn.
have Hgl0 : good_ptr gr0 l.
- case/andP: Hg0=>_ /allP /(_ (BN l tt r)).
  rewrite structurePtUn rangePtUn inE eq_refl /= andbT.
  rewrite !validPtUn in V0 *; rewrite valid_structure dom_structure V0.
  by move/(_ erefl); case/andP.
apply: [stepE gr0]=>//=; first by split=>//; apply/shapePtUn=>//; vauto.
move=>_ m [gr'][Hm V' [Hs Hmk]].
have Hgg' : good_graph_b gr'.
- rewrite (good_eq (g2:=gr0)) // /gr0 V'.
  by rewrite !validPtUn in V0 *.
have Hgr': good_ptr gr' r.
- case/andP: Hgg' =>_ /allP /(_ (BN l tt r)).
  rewrite -Hs structurePtUn rangePtUn inE eq_refl /= andbT.
  rewrite !validPtUn in V0 *; rewrite valid_structure dom_structure V0.
  by move/(_ erefl); case/andP.
apply: [gE gr']=>//=_ m' [g''][V'' Hm' [Hs' Hmk'] Vm']; exists g''; split=>//.
have Hs'' : structure gr = structure g'' by rewrite Hs0 Hs.
split=>// y.
(*
case/boolP: (p_val id gr y)=>Hfy.
- rewrite !orbT.
  apply/(mark_eq_sub Hmk')/(mark_eq_sub Hmk).
  move: Hfy; rewrite Hgr /gr0 !pvalPtUn //= andbT andbF /= =>->.
  by rewrite orbT.
rewrite !orbF.
case/boolP: (y \in dom gr)=>Hdy; last first.
- have ->: y \in connect negb gr p = false.
  - apply/negbTE; move: Hdy; apply: contra.
    by exact: connect_dom.
  by rewrite plink_val plinkF // (structure_dom_eq (g2:=gr)).
rewrite pvalNeg //= in Hfy; move/negbNE: Hfy=>Hfy.
*)
(* almost works *)
rewrite Hmk' Hmk.

have -> : p_val id gr0 y = (p==y) || p_val id gr y.
- by rewrite Hgr /gr0 !pvalPtUn // andbT andbF.

case/boolP: (p == y)=> [/eqP {y}<-| Hyp] /=.
- by rewrite !orbT; symmetry; apply/orP; left; apply/connect0.
case/boolP: (p_val id gr y)=>[|Hfy]; first by rewrite !orbT.
rewrite !orbF.

rewrite [RHS](@connect_eq_links _ _ _ _ l false r)=>//; first last.
- by rewrite (good_dom (g2:=gr')) //; apply: structure_dom_eq; rewrite Hs0.
- by rewrite (good_dom (structure_dom_eq Hs0)).
rewrite !inE !app_predE eq_sym (negbTE Hyp) /=.

have Hpeq0: subpred (p_val negb gr0) (p_val negb gr).
- move=>z; rewrite Hgr /gr0 !pvalPtUn //= andbT andbF /= => ->.
  by rewrite orbT.

apply/iffE; split.
- case/orP.
  - move: (Hgr'); rewrite /good_ptr; case/boolP: (r == null)=>/= [/eqP-> _ |_ Hrd].
    - by rewrite connect_notp // plink_val plinkF // no_null.
    have Hpeq: {in dom gr', subpred (p_val negb gr') (p_val negb gr) }.
    - by move=>z Hz /(mark_eq_sub_neg (structure_dom_eq Hs) Hmk Hz)/Hpeq0.
    move/(connect_sub _ Hpeq); rewrite Hs0 Hs app_predE=>/(_ erefl) ->.
    by rewrite orbT.
  move=>Hly; suff: y \in connect negb gr l by move=>->.
  by apply/(connect_sub (g1:=gr0))=>// + _.

have Vg': valid gr by case/andP: Hgg.
have Hps: find p (structure gr) = Some (BN l tt r) by rewrite find_structure Hp.
move/(connect_upd_true (p:=p) Vg' Hps Hyp)=>/=; rewrite (upd_val_eta _ Hps) -/gr0.
case/orP; first by move=>->; rewrite orbT.
(*
case Hyl: (y \in connect negb gr0 l)=>/=; first by rewrite orbT.
rewrite orbF.
*)
case/connectP=>xs [Hxs Ey Hy].

have Hd0: dom gr0 =i dom gr' by apply structure_dom_eq.

case/boolP: (all (fun z => z \notin component negb gr0 l) (r::xs))=>Hpxs.

- (* path doesn't go through the marked component *)
  apply/orP; left.
  apply/connectP.
  exists xs; split=>//; last first.
  - rewrite (mark_eq_neg Hd0 Hmk); last by rewrite -Hd0; apply/pval_dom/Hy.
    rewrite Hy andbT Ey.
    by move/allP: Hpxs; apply; exact: mem_last.

    rewrite (eq_in_path (P:=fun x => (x \notin component negb gr0 l) && (x \in dom gr')) (e':=prel negb gr0)) //.
    - move=>x' y'; rewrite -!topredE /= => /andP [Hx' /[dup] Hdx /um_eta [[vl va vr]][Hdx' ?]] /andP [Hy' Hdy'].
      have Hst : find x' (structure gr') = Some (BN vl tt vr) by rewrite find_structure Hdx'.
      rewrite -!plink_val (mark_eq_neg Hd0 Hmk) // Hx' /=; case: (p_val negb gr0 x')=>//=.
      rewrite !(plink_conn negb (l:=vl) (r:=vr)) //; last by rewrite Hs.
      by rewrite !mem_filter (structure_dom_eq (g2:=gr0)).
    rewrite all_predI Hpxs /=; move: (full_path_dom Hxs Ey Hy)=>/=.
    rewrite Hd0; case: (r \in dom gr')=>//=.
    by apply: sub_all=>z; rewrite Hd0.

apply/orP; right.

(* path goes through the marked component, so y is connected to l *)
rewrite -has_predC (eq_has (a2:=fun z=> z \in component negb gr0 l)) in Hpxs; last by move=>z /=; rewrite negbK.
case: {-1}_ _ _ / (split_find_last Hpxs) (erefl (r::xs))=>{Hpxs} z xs1 xs2 Hz. (* z is the last vertex in marked component, xs2 is the free path *)
rewrite -all_predC (eq_all (a2:=fun z=> z \notin component negb gr0 l)) // => Hxs2 Heq.

apply: (connect_trans (y:=z))=>//.
apply/connectP; exists xs2; split=>//; last first.
- by move: (erefl (last r (r :: xs))); rewrite {1}Heq /= last_cat last_rcons => ->.

case: xs1 Heq=>/=.
- by case=><- <-.
move=>h xs1; case=>? Exs; move: Hxs.
by rewrite Exs cat_path last_rcons; case/andP.
Qed.

End BoolGraph.