From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
(* temp*)
From mathcomp Require Import bigop.
From fcsl Require Import options axioms pred ordtype finmap.

From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import interlude model heapauto.

Section Sep.
Variable U : pcm.

Definition wand (p2 p : Pred U) : Pred U :=
  [Pred h1 | forall h2 h, h = h1 \+ h2 -> h2 \In p2 -> h \In p].

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

Notation "p2 '--#' p" := (wand p2 p)
  (at level 58, right associativity) : rel_scope.

Variant bin_node A := BN of ptr & A & ptr.

Definition bn_val {A} : bin_node A -> ptr * A * ptr :=
  fun '(BN l a r) => (l, a, r).

Definition bn_sub {A} : ptr * A * ptr -> bin_node A :=
  fun '(l, a, r) => BN l a r.

Lemma bn_ccl {A : Type} : ssrfun.cancel bn_val (@bn_sub A).
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

Lemma shapePtUnG g p n :
  valid (p &-> n \+ g) ->
  forall h, valid h ->
  h \In shape (pts p n \+ g) <-> h \In node_shape p n # shape g.
Proof.
move=>V h Vh; rewrite /shape.
move: (assocs_perm V)=>H.
rewrite (sepit_perm _ H) IterStar.sepit_cat assocsPt.
move: (validL V); rewrite validPt=>->; split.
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


End Bingraph.

Definition good_ptr {A} p (g : pregraph A) := (p == null) || (p \in dom g).

Lemma good_dom {A} (g1 g2 : pregraph A) p : dom_eq g1 g2 -> good_ptr p g1 -> good_ptr p g2.
Proof.
move=>H; rewrite /good_ptr; case/orP=>[->|] //.
move/domeqP: H=>[_ H] Hp.
by rewrite -(H p) Hp orbT.
Qed.

Definition good_graph {A} (g : pregraph A) :=
  forall p l a r, find p g = Some (BN l a r) -> good_ptr l g && good_ptr r g.

Definition good_graph_b {T : eqType} (g : pregraph T) :=
  valid g &&
  all (fun n : bin_node T => let: BN l _ r := n in good_ptr l g && good_ptr r g) (range g).

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

(*
Lemma goodex : good_graph_b ex.
Proof.
rewrite /ex /good_graph_b.
apply/allP; case=>l a r /mem_rangeX [k].
rewrite -!joinA =>/InPtUn /= [/andP [V1 H1]]; case.
- case; case=>{k}_->_->_.
  rewrite /good_ptr /= !domPtUn -!topredE /= !domPtUn -!topredE /= V1 /= domPtUn.
move=>p l a r; rewrite /ex -!joinA findPtUn2; last first.
rewrite validPtUn /=; apply/andP; split.
rewrite validPtUn /=; apply/andP; split.
rewrite validPtUn /=; apply/andP; split.
rewrite validPtUn /=; apply/andP; split.
rewrite validPtUn /=; apply/andP; split.
rewrite validPtUn /=; apply/andP; split.
rewrite validPtUn /=; apply/andP; split.
by apply: validPt.
by rewrite domPt.
by rewrite domPtUn -topredE /= domPt /= validPtUn /= validPt /= domPt.
byrewrite domPtUn -topredE /= !validPtUn /= domPt /= !domPtUn /= validPt /= -!topredE /= validPtUn /= validPt /= !domPt /=.




- apply/(@assocs_valid _ _ _ _ (p1, BN p2 tt p3))/In_assocs.




apply/andP; split.
  rewrite validPtUn /=; apply/andP; split.
  rewrite validPtUn /=; apply/andP; split.
  rewrite validPtUn /=; apply/andP; split.
  rewrite validPtUn /=; apply/andP; split.
  rewrite validPtUn /=; apply/andP; split.
  rewrite validPtUn /=; apply/andP; split.
  by apply: validPt.
  by rewrite domPt.

/= validPt /= !domPtUn /= !domPt].
  rewrite  !domPt.
case: eqP=>[{p}->|].
*)
(*
  [:: (p1, BN p2   tt p3);
      (p2, BN p4   tt p5);
      (p3, BN p6   tt p7);
      (p4, BN null tt null);
      (p5, BN p5   tt p8);
      (p6, BN p1   tt p8);
      (p7, BN null tt null);
      (p8, BN p4   tt p7)]. *)

End ExampleCyclic.

Section BoolGraph.

(*
Definition good_ptr {A} p (g : graph A) := p == null \/ exists n, (p, n) \In g.

Definition good_graph {A} (g : graph A) :=
  forall p l a r, (p, BN l a r) \In g -> good_ptr l g /\ good_ptr r g.
*)

Inductive un_path : pregraph bool -> ptr -> ptr -> Prop :=
| stop  : forall g p      , un_path g p p
| hopl  : forall g p l r q, (p, BN l false r) \In assocs g -> un_path g l q -> un_path g p q
| hopr  : forall g p l r q, (p, BN l false r) \In assocs g -> un_path g r q -> un_path g p q.

Definition linked_f (g : pregraph bool) (x y : ptr) : bool :=
  match find x g with
  | Some (BN l b r) => ~~b && ((y == l) || (y == r))
  | None => false
  end.

Lemma linked_null g x : ~~ linked_f g null x.
Proof.
by rewrite /linked_f; move: (no_null g)=>/find_none ->.
Qed.

Definition un_path_b (g : pregraph bool) (x y : ptr) : Prop :=
  if x == y then True
    else exists (xs : seq ptr), path (linked_f g) x (rcons xs y).

Lemma un_path_null gr x : x \in dom gr -> ~ un_path gr null x.
Proof.
move=>Hx H; case: {1}_ {2}_ {-1}_ / H (erefl gr) (erefl null) (erefl x).
- move=>_ _ _ -> E; rewrite {x}E in Hx.
  by move: (no_null gr); rewrite Hx.
- move=>g p l r _ H _ Eg Ep _; rewrite {g}Eg {p}Ep in H.
  by move: (no_null gr); move/In_assocs/In_dom: H=>->.
move=>g p l r _ H _ Eg Ep _; rewrite {g}Eg {p}Ep in H.
by move: (no_null gr); move/In_assocs/In_dom: H=>->.
Qed.

Lemma un_path_null_b gr x : x \in dom gr -> ~ un_path_b gr null x.
Proof.
move=>Hx; rewrite /un_path_b.
case: eqP.
- move=>E; rewrite -E in Hx.
  by move: (no_null gr); rewrite Hx.
move=>_ []; case=>/=.
- rewrite andbT; apply/negP; exact: linked_null.
by move=>y xs; case/andP=>+ _; apply/negP; exact: linked_null.
Qed.

(* TODO generalize *)
Lemma un_path_frame_b p x y l r g :
  p != null ->
  valid g ->
  p \notin dom g ->
  un_path_b (p &-> BN l true r \+ g) x y -> un_path_b (p &-> BN l false r \+ g) x y.
Proof.
move=>Hp V Hd; rewrite /un_path_b; case: eqP=>// _; case=>xs Hxs; exists xs.
elim: xs x Hxs=>/= [|a xs IH] z.
- rewrite !andbT /linked_f findPtUn2; last by rewrite validPtUn Hp V Hd.
  rewrite findPtUn2; last by rewrite validPtUn Hp V Hd.
  by case: eqP.
case/andP=>Hl /IH ->; rewrite andbT; move: Hl.
rewrite /linked_f findPtUn2; last by rewrite validPtUn Hp V Hd.
rewrite findPtUn2; last by rewrite validPtUn Hp V Hd.
by case: eqP.
Qed.

(*
Lemma un_path_frame p x y l r g :
  x != p ->
  y != p ->
  un_path (p &-> BN l true r \+ g) x y -> un_path (p &-> BN l false r \+ g) x y.
Proof.
move=>Hx Hy H; case: {1}_ {2}_ {-1}_ / H (erefl (p &-> BN l true r \+ g)) (erefl x) (erefl y).
- by move=>_ p' _ Hx' Hy'; rewrite Hx'; constructor.
- move=>g' p' l' r' q H Hp Eg Ex Ey; rewrite {g'}Eg in H Hp; rewrite -{q}Ey in Hp *; rewrite -{p'}Ex in H.
*)
Definition mark_rel (x : ptr) (g1 g2 : pregraph bool) :=
  forall y l r m2, (y, BN l m2 r) \In g2 <->
    exists m1 : bool, (y, BN l m1 r) \In g1 /\
                      if m2 then m1 \/ (~~ m1 /\ un_path_b g1 x y) else ~~ m1.

Lemma mark_good x g1 g2 : mark_rel x g1 g2 -> valid g2 -> good_graph_b g1 -> good_graph_b g2.
Proof.
move=>Hm V2 /andP [V1 H1]; apply/andP; split=>//.
apply/allP; case=>l a r /mem_rangeX; case=>p.
case/(Hm _ _ _ _)=>b [/mem_range Hg1 Hp1].
move/allP: (H1)=>/(_ _ Hg1) /andP [Hl1 Hr1].
apply/andP; split.
- rewrite /good_ptr; case/orP: Hl1=>[->|] //.
  case: eqP=>[->|] /= E; first by move: (no_null g1); rewrite E.
  move/In_domX; case; case=>l' a' r' H'.
  apply/In_domX; exists (BN l' a' r'); apply/Hm.
  by exists a'; split=>//; case: {H'}a'=>//; left.
rewrite /good_ptr; case/orP: Hr1=>[->|] //.
case: eqP=>[->|] /= E; first by move: (no_null g1); rewrite E.
move/In_domX; case; case=>l' a' r' H'.
apply/In_domX; exists (BN l' a' r'); apply/Hm.
by exists a'; split=>//; case: {H'}a'=>//; left.
Qed.

Definition markT : Type := forall (p : ptr),
  {gr : pregraph bool},
  STsep (fun h => [/\ h \In shape gr, good_graph_b gr & good_ptr p gr],
        [vfun (_ : unit) h => exists gr', [/\ valid gr', shape gr' h & mark_rel p gr gr']]).

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
move=>go p [gr][] i /= [Hg Hgr Hp]; apply: vrfV=>V; case/orP: Hp.
- move=>/eqP->; rewrite eq_refl; step=>_.
  exists gr; split=>//; first by case/andP: Hgr.
  move=>y l r; case.
  - split; first by move=>?; exists true; split=>//; left.
    case=>// m1 [Hy]; case; first by move=>Em; rewrite Em in Hy.
    by case=>_; move/In_dom: Hy=>/= /un_path_null_b /[apply].
  split; first by move=>?; exists false.
  by case=>m1 [Hy /negbTE Em]; rewrite Em in Hy.
case: eqP=>[{p}->|/eqP Hp].
- by move=>E; move: (no_null gr)=>En; rewrite E in En.
case/um_eta; case=>l a r [Hp' Hgr'].
case/andP: (Hgr)=>Vg Eg; rewrite Hgr' in Vg Hg.
(* wat *)
case/(@shapePtUnG bool _ _ _ Vg _ V): (Hg)=>i1[i2][E H1 H2].
rewrite E H1; step; case: a Hp' Hgr' Vg Hg H1=>/=Hp' Hgr' Vg Hg H1.
- step=>V1; exists gr; rewrite {1 2}Hgr' Vg -H1 -E; split=>// y l' r' m2; split.
  - by move=>Hm; exists m2; split=>//; case: m2 Hm=>// ?; left.
  case=>m1 [Hy]; case: m2; last by move/negbTE => Em; rewrite Em in Hy.
  case; first by move=> Em; rewrite Em in Hy.
  case=>/negbTE Em1; rewrite /un_path_b; case: eqP.
  - move=>Ep; rewrite -{y}Ep {m1}Em1 in Hy *.
    by move/In_find: Hy=>Ep; rewrite Ep in Hp'; case: Hp'.
  move=>_ []; case=>/=.
  - by rewrite andbT /linked_f Hp'.
  by move=>z xs; case/andP; rewrite /linked_f Hp'.
have Vg' : valid (pts p (BN l true r) \+ free gr p).
- by rewrite !validPtUn in Vg *.
do 3!step.
have Hgg : good_graph_b (p &-> BN l true r \+ free gr p).
- rewrite /good_graph_b Vg' /=.
  apply/allP; case=>l' a r'; rewrite rangePtUn -topredE /=; case/andP=>Vn; case/orP.
  - case/eqP=><- _ <-.
    rewrite Hgr' in Eg; move/allP: Eg=>/(_ (BN l false r)).
    rewrite rangePtUn -topredE /= Vg eq_refl /= => /(_ erefl).
    case/andP=>Hl Hr; apply/andP; split.
    - apply/good_dom/Hl/domeqP; rewrite !validPtUn; split=>//.
      by move=>h'; rewrite !domPtUn -!topredE /= !validPtUn.
    apply/good_dom/Hr/domeqP; rewrite !validPtUn; split=>//.
    by move=>h'; rewrite !domPtUn -!topredE /= !validPtUn.
  move=>H.
  rewrite Hgr' in Eg; move/allP: Eg=>/(_ (BN l' a r')).
  rewrite rangePtUn -topredE /= Vg H orbT => /(_ erefl).
  case/andP=>Hl Hr; apply/andP; split.
  - apply/good_dom/Hl/domeqP; rewrite !validPtUn; split=>//.
    by move=>h'; rewrite !domPtUn -!topredE /= !validPtUn.
  apply/good_dom/Hr/domeqP; rewrite !validPtUn; split=>//.
  by move=>h'; rewrite !domPtUn -!topredE /= !validPtUn.
apply: [stepE (p &-> BN l true r \+ free gr p)]=>//=.
- split=>//.
  - apply/shapePtUnG=>//.
    - rewrite (pull (p.+ 1 :-> _)) -!joinA.
      rewrite E H1 (pull (p.+ 1 :-> _)) -!joinA in V.
      by rewrite !validPtUn in V *.
    by exists (p :-> l \+ (p.+ 1 :-> true \+ p.+ 2 :-> r)), i2.
  case/andP: Hgg=>_ /allP /(_ (BN l true r)).
  by rewrite rangePtUn -topredE /= Vg' /= eq_refl /= => /(_ erefl); case/andP.
move=>_ m [gr'][V' Hm Hmk].
have Hgg' := mark_good Hmk V' Hgg.
apply: [gE gr']=>//=.
- split=>//.
  have Hr: BN l true r \in range gr'.
  - by apply/mem_rangeX; exists p; apply/Hmk; exists true; split=>//; left.
  by case/andP: Hgg'=>_ /allP /(_ _ Hr); case/andP.
move=>_ m' [g''][V'' Hm' Hmk' Vm']; exists g''; split=>//.

(*
move=>y0 l0 r0 b2; apply: iff_trans; first by apply: Hmk'.
split.
- case=>b1 [Hb1 Eb1].
  move/Hmk: Hb1; case=>b3 [Hb3 Eb3].
  case/(InPtUnEN _ Vg'): Hb3.
  - case=>E0 {l0}->E3' {r0}->; rewrite {y0}E0 in Eb1 Eb3 *; rewrite {b3}E3' /= in Eb3.
    case: b1 Eb1 Eb3=>//=; case: b2=>//= _ _.
    exists false; split; first by rewrite Hgr'; apply: InPtUnL.
    by right; split=>//; rewrite /un_path_b eq_refl.
  move=>[H0 /= Hn0]; exists b3; split.
  - by rewrite Hgr'; apply/InPtUnE=>//; right.
  case: b1 Eb1 Eb3=>/=; case: b2=>//=.
  - move=>_; case; first by move=>?; left.
    case=>/negbTE Eb3; rewrite {b3}Eb3 in H0 *; move=>Hup; right; split=>//.
    have{Hup}: un_path_b gr l y0.
    - rewrite Hgr'; apply: un_path_frame_b=>//.
      - by move/validR: Vg.
      by rewrite domF -topredE /= eq_refl.
    rewrite /un_path_b; move/negbTE: Hn0; rewrite eq_sym=>->.
    case: eqP.
    - by move=><- _; exists [::]=>/=; rewrite andbT /linked_f Hp' eq_refl.
    by move=>_ [xs Hpu]; exists (l::xs)=>/=; rewrite Hpu andbT /linked_f Hp' eq_refl.
  case=>//; case=>_ Hup /negbTE Eb3; rewrite {b3}Eb3 /= in H0 *; right; split=>//.
  move: Hup; rewrite /un_path_b; move/negbTE: Hn0; rewrite eq_sym=>->.
  case: eqP.
  - by move=><- _; exists [::]=>/=; rewrite andbT /linked_f Hp' eq_refl orbT.
  move=>_ [xs Hpu]; exists (l::xs)=>/=; apply/andP; split.
  - by rewrite /linked_f Hp' eq_refl.
  elim: xs Hpu=>/=.
  - rewrite !andbT /linked_f.
*)


have Hpm : mark_rel p gr gr'.
- move=>y0 l0 r0 b2; apply: iff_trans; first by apply: Hmk.
  split.
  - case=>b1 [H3 E3].
    case/(InPtUnEN _ Vg'): H3.
    - case=>E0 {l0}->E3' {r0}->; rewrite {y0}E0 in E3 *; rewrite {b1}E3' /= in E3.
      exists false; split; first by rewrite Hgr'; apply: InPtUnL.
      case: b2 E3=>//=; case; last by case.
      by move=>_; right; split=>//; rewrite /un_path_b eq_refl.
    move=>[H0 /= Hn0]; exists b1; split.
    - by rewrite Hgr'; apply/InPtUnE=>//; right.
    case: b2 E3=>//.
    case; first by move=>E3; left.
    case=>/negbTE Eb1; rewrite {b1}Eb1 /= in H0 *; move=>Hl; right; split=>//.
    have: un_path_b gr l y0.
    - rewrite Hgr'; apply: un_path_frame_b=>//.
      - by move/validR: Vg.
      by rewrite domF -topredE /= eq_refl.
    rewrite /un_path_b; move/negbTE: Hn0; rewrite eq_sym=>->.
    case: eqP.
    - by move=><- _; exists [::]=>/=; rewrite andbT /linked_f Hp' eq_refl.
    by move=>_ [xs Hpu]; exists (l::xs)=>/=; rewrite Hpu andbT /linked_f Hp' eq_refl.
  admit.

have Hpr : mark_rel p gr' gr''.
move=>????; rewrite /mark_rel in Hmk' Hpm.


  case=>b1 [H3 E3].

  case E0: (y0 == p).
  - move/eqP: E0=>{y0}->; case=>/In_find; rewrite Hp'; case=>{l0}<-{b1}<-{r0}<-/= _.
    exists true.
    case: b2=>/=.
   case exists b1; split.


    move/un_path_frame_b: Hl.
    rewrite Hgr'; apply/un_path_frame_b=>//. apply: (hopl (l:=l) (r:=r)).
      - by apply/In_assocs/InPtUnE=>//; left.

rewrite /mark_rel in Hmk Hmk' *; move=>y0 l0 r0 b2.
apply: iff_trans; first by apply: Hmk'.
split.
- case=>b1 [/Hmk][b3][H3 E3 E2].
  case/(InPtUnEN _ Vg'): H3.
  - case=>E0 {l0}->E3' {r0}->; rewrite {y0}E0 in E2 E3 *; rewrite {b3}E3' in E3.
    exists false; split; first by rewrite Hgr'; apply: InPtUnL.
    by case: b2 E2=>// _; right; constructor.
  move=>[H0 /= Hn0]; exists b3; split.
  - by rewrite Hgr'; apply/(InPtUnE)=>//; right.
  case: b2 E2; last by move/negbTE=>Eb1; rewrite Eb1 in E3.
  case.
  - move=>Eb1; rewrite Eb1 in E3; case: E3; first by move=>E3; left.
    move=>Hpu; right; rewrite Hgr'; apply: (hopl (l:=l) (r:=r)).
    - by apply/In_assocs/InPtUnE=>//; left.

    /mem_rangeX.


    =>/=. first last.
  - by case: (Hgr _ _ _ _ H).


move=>H; move: (Hg); case/(in_shape H V)=>h1[h2][E H1 H2].
rewrite E H1; step; case: m H H1 H2=>/=H H1 H2.
- step=>V1; exists gr; split.
  - by move: Hg; rewrite E H1.
  move=>y l' r' m2; split.
  - by move=>Hm; exists m2; split=>//; case: m2 Hm=>// ?; left.
  case=>m1 [Hy]; case: m2; last by move/negbTE => Em; rewrite Em in Hy.
  case; first by move => Em; rewrite Em in Hy.
  (* TODO graphs should really be PCMs so that we get `p :-> _ true _` vs `p :-> _ false _` contradiction here  *)
  admit.
do 3!step; apply: [stepE gr]=>//=.
- split; first last.
  - by case: (Hgr _ _ _ _ H).




move=>go p [tn][gn][] i /= [Hg Ht]; case: eqP Ht=>[{p}->|/eqP Ep] Ht.
- by step=>V; rewrite (tree_in_graph_null Ht V).
apply: vrfV=>Vi.
case: (tree_in_graph_nonnull Ep Ht)=>x[tl][pl][tr][pr][-> I Hl Hr].
move: (Hg); case/(in_shape I Vi)=>i1[i2][Ei Hi1 Hi2]; rewrite Ei Hi1.
do 3!step.
apply: [stepE tl, gn]=>//=; first by split=>//; rewrite -Hi1 -Ei.
move=>_ m [/eqP -> Hm].
rewrite (shapeK Hm Hg)=>{m Hm}.
by apply: [stepE tr, gn]=>//=_ m [/eqP -> Hm]; step.
Qed.


End BoolGraph.