From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From fcsl Require Import options prelude axioms pred ordtype.
From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import interlude model heapauto.
From HTT Require Import bintree graph.

Section Shape.
Variable (f : ptrmap nat).

Definition node_shape p (n : seq ptr) :=
  [Pred h | exists v, find p f = Some v /\
   h = p :-> get_nth n 0 \+ (p .+ 1 :-> v \+ p .+ 2 :-> get_nth n 1)].

Lemma node_shapeK h1 h2 p n :
  h1 \In node_shape p n -> h2 \In node_shape p n -> h1 = h2.
Proof.
case=>v1 [E1 ->]; case=>v2 [E2 ->].
by move: E2; rewrite E1; case=>->.
Qed.

Definition shape (gr : pregraph) :=
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

End Shape.

Section TIG.
Variable (f : ptrmap nat).

Fixpoint tree_in_graph_b (g : pregraph) (t : tree nat) (p : ptr) : bool :=
  if t is Node l a r then
    match find p g with
    | Some ns => [&& find p f == Some a,
                     tree_in_graph_b g l (get_nth ns 0) &
                     tree_in_graph_b g r (get_nth ns 1)]
    | None => false
    end
  else p == null.

Lemma tree_in_graph_null g t :
  tree_in_graph_b g t null -> t = leaf.
Proof.
case: t=>//=l a r.
by move: (no_null g)=>/find_none->.
Qed.

Lemma tree_in_graph_nonnull g t p :
  p != null -> n_graph 2 g -> tree_in_graph_b g t p ->
  exists (x : nat) tl (pl : ptr) tr (pr: ptr),
  [ /\ t = Node tl x tr,
       find p g = Some [::pl;pr],
       find p f = Some x,
       tree_in_graph_b g tl pl &
       tree_in_graph_b g tr pr ].
Proof.
move=>Hp H2; case: t; first by move=>/= Ep; rewrite Ep in Hp.
move=>tl x tr /=; case El: (find p g)=>[ns|] //.
case/and3P=>/eqP Hx Tl Tr; exists x, tl, (get_nth ns 0), tr, (get_nth ns 1); split=>//.
set l := get_nth ns 0.
set r := get_nth ns 1.
suff: ns == [::l; r] by move/eqP ->.
move/all_nth/allP: H2; apply.
by apply/(mem_range (k:=p))/In_find.
Qed.

Lemma tigUn g0 g t p :
  valid (g0 \+ g) ->
  tree_in_graph_b g t p ->
  tree_in_graph_b (g0 \+ g) t p.
Proof.
move=>V; elim: t p=>//=l IHl a r IHr p.
rewrite findUnR //; case: dom_find=>[|v]->// _.
case/and3P=>->/= Hl Hr.
by apply/andP; split; [apply: IHl | apply: IHr].
Qed.

(*
Lemma tigPtUn q ns g t p :
  valid (q &-> ns \+ g) ->
  tree_in_graph_b g t p ->
  tree_in_graph_b (q &-> ns \+ g) t p.
Proof.
move=>V; elim: t p=>//=l IHl a r IHr p.
rewrite findPtUn2 //; case/boolP: (p == q)=>Hp; last first.
- case El: (find p g)=>[qs|] //.
  case/and3P=>->/= Hl Hr.
  by apply/andP; split; [apply: IHl | apply: IHr].
move/eqP: Hp=>{p}->.
by move: V; rewrite validPtUn; case/and3P=>Nq Vg /In_findNE->.
Qed.
*)
(*
Inductive tree_in_graph (g: graph) : tree A -> ptr -> Prop :=
| TIG_L: tree_in_graph g leaf null
| TIG_N:
    forall (p : ptr) (x : A) tl (pl : ptr) tr (pr: ptr),
    (p, BN pl x pr) \In g ->
    tree_in_graph g tl pl ->
    tree_in_graph g tr pr ->
    tree_in_graph g (Node tl x tr) p.

Lemma tree_in_graph_null g t :
  tree_in_graph g t null -> forall h, valid h -> h \In shape g -> t = leaf.
Proof.
case: t=>//=l a r Ht h V Hg.
case: {-1}_ {1}_ / Ht (erefl (Node l a r)) (erefl null)=>// p x tl pl tr pr Ht _ _ {l a r}_ Hp.
exfalso=>{tl tr}; rewrite {p}Hp in Ht.
move: Hg; case/(in_shape Ht V)=>h1[h2][E H1 H2].
by rewrite E H1 in V.
Qed.

Lemma tree_in_graph_nonnull g t p :
  p != null -> tree_in_graph g t p -> forall h, valid h -> h \In shape g ->
  exists (x : A) tl (pl : ptr) tr (pr: ptr),
  [ /\ t = Node tl x tr,
       (p, BN pl x pr) \In g,
       tree_in_graph g tl pl &
       tree_in_graph g tr pr ].
Proof.
move=>Hp Ht; case: {-1}_ {1}_ / Ht (erefl t) (erefl p).
- by move=>_ Ep; rewrite -Ep in Hp.
move=>p1 x tl pl tr pr Hp1 Hl Hr Et E1 h Vh Hh.
by exists x, tl, pl, tr, pr; split=>//; rewrite -E1.
Qed.
*)

End TIG.
(*
Section ExampleDag.
Definition p1 := ptr_nat 1.
Definition p2 := ptr_nat 2.
Definition p3 := ptr_nat 3.

Definition graph1 : pregraph :=
  p1 &-> [::null; null] \+
  p2 &-> [::p1  ; p1  ] \+
  p3 &-> [::p1  ; p2  ].

Definition v (p : ptr) : nat :=
  if p == p1 then 2
    else if p == p2 then 3
    else if p == p3 then 1
    else 0.

Definition tree1 : tree nat :=
   Node (Node leaf 2 leaf)
        1
        (Node (Node leaf 2 leaf)
              3
              (Node leaf 2 leaf)).

Lemma tree1_in_graph1 : tree_in_graph_b v graph1 tree1 p3.
Proof.
rewrite /graph1 /=.
exists p1, p2; split=>//.
- by rewrite findUnPt // !validUnPt /= validPt /= domPtUn inE /= !domPt /= inE validPtUn /= validPt /= domPt inE.
- by apply/In_cons; right; apply/In_cons; right; apply/Mem_Seq1.
- exists null, null; split=>//.
  by apply/In_cons; left.
exists p1, p1; split.
- by apply/In_cons; right; apply/In_cons; left.
- exists null, null; split=>//.
  by apply/In_cons; left.
exists null, null; split=>//.
by apply/In_cons; left.
Qed.

(*
Lemma tree1_in_graph1 : tree_in_graph graph1 tree1 p3.
Proof.
rewrite /graph1; apply: TIG_N.
- by apply/In_cons; right; apply/In_cons; right; apply/Mem_Seq1.
- apply: TIG_N; try by apply: TIG_L.
  by apply/In_cons; left.
apply: TIG_N.
- by apply/In_cons; right; apply/In_cons; left.
- apply: TIG_N; try by apply: TIG_L.
  by apply/In_cons; left.
apply: TIG_N; try by apply: TIG_L.
by apply/In_cons; left.
Qed.
*)

End ExampleDag.
*)
Section SumDag.

Fixpoint sum_tree (t : tree nat) : nat :=
  if t is Node l n r
    then sum_tree l + n + sum_tree r
  else 0.

Definition treesumT' : Type := forall (p : ptr),
  {(t : tree nat) (gr : pregraph) (f : ptrmap nat)},
  STsep (fun h => [/\ shape f gr h, n_graph 2 gr, good_graph gr & tree_in_graph_b f gr t p],
        [vfun n h => n == sum_tree t /\ shape f gr h]).

Program Definition treesum' : treesumT' :=
  Fix (fun (go : treesumT') p =>
    Do (if p == null then ret 0
        else l <-- !p;
             n <-- !(p.+ 1);
             r <-- !(p.+ 2);
             ls <-- go l;
             rs <-- go r;
             ret (ls + n + rs))).
Next Obligation.
move=>go p [tn][gn][pn][] i /= [Hs H2 Hg Ht]; case: eqP Ht=>[{p}->|/eqP Ep] Ht.
- by step=>V; rewrite (tree_in_graph_null Ht).
case/andP: (Hg)=>Hv Ha.
case: (tree_in_graph_nonnull Ep H2 Ht)=>x[tl][pl][tr][pr][-> Hf Hx Hl Hr] /=.
move/um_eta2: (Hf)=>Egn; rewrite Egn in Hv Hs.
case/(shapePtUn _ Hv): (Hs)=>i1[i2][-> [v][Hx' ->] Hi2].
move: (Hx); rewrite Hx'; case=>{v Hx'}->.
do 3!step; apply: [stepE tl, gn, pn]=>//=.
- split=>//; rewrite Egn; apply/shapePtUn=>//.
  by exists (p :-> pl \+ (p.+ 1 :-> x \+ p.+ 2 :-> pr)), i2; split=>//; exists x.
move=>_ m [/eqP -> Hm].
rewrite -Egn in Hs; rewrite (shapeK Hm Hs)=>{m Hm}.
by apply: [stepE tr, gn, pn]=>//=_ m [/eqP -> Hm]; step.
Qed.

Definition treesumT : Type := forall (p : ptr),
  {(gr : pregraph) (f : ptrmap nat)},
  STsep (fun h => [/\ h \In shape f gr,
                      n_graph 2 gr, good_graph gr, acyclic gr,
                      good_ptr gr p & dom gr =i connect Unit gr p],
        [vfun n h => exists t, [/\ h \In shape f gr, tree_in_graph_b f gr t p &
                                   n == sum_tree t]]).

Program Definition treesum : treesumT :=
  Fix (fun (go : treesumT) p =>
    Do (if p == null then ret 0
        else l <-- !p;
             n <-- !(p.+ 1);
             r <-- !(p.+ 2);
             ls <-- go l;
             rs <-- go r;
             ret (ls + n + rs))).
Next Obligation.
move=>go p [gn][fn][] i /= [Hs Hg2 Hg Ha Hp Ho]; case/orP: Hp.
- by move=>E; rewrite E; step=>Vi; exists leaf.
move/[dup]/dom_cond/[dup]=>Np /negbTE -> /[dup] Hpd.
case/um_eta=>ns [Hp Egr].
case/andP: (Hg)=>Vg Eg; rewrite Egr in Vg Hs.
case/(shapePtUn _ Vg): (Hs)=>i1[i2][E][v][Hf E1] H2; rewrite E E1.
set l := get_nth ns 0.
set r := get_nth ns 1.
have /eqP Ens : ns == [::l; r].
- move/all_nth/allP: Hg2; apply.
  by apply/(mem_range (k:=p))/In_find.
have /andP [Npl Npr] : (p != l) && (p != r).
- by move: (acyclic_find Ha Hp); rewrite Ens !inE negb_or.
have Hgl : good_ptr gn l by apply: (all_good_get (p:=p)).
have Hgr : good_ptr gn r by apply: (all_good_get (p:=p)).
do 3!step.
rewrite -E1 -E; have Egr2 := (connect_split l gn).
rewrite -Egr Egr2 in Hs Vg.
case/(shapeUn _ Vg): (Hs)=>i3[i4][E34 H3 H4].
rewrite E34; apply: [stepX (subconnect l gn), fn] @ i3=>//=.
- move=>V2; split=>//.
  - by move: Hg2; case/andP: Hg; rewrite {1 4}Egr2=>V _ /(n_graphUnL V).
  - by apply: good_subconnect.
  - by move: Ha; rewrite {1}Egr2 joinC; apply/acyclicUn; rewrite joinC.
  - move: Hgl; rewrite /good_ptr; case/boolP: (l == null)=>//= Hnl Hl.
    rewrite dom_umfiltk inE /= Hl andbT.
    by apply: connect0=>//; rewrite dom0.
  move=>z; rewrite dom_umfiltk inE /=.
  rewrite connect_subconnect; case/boolP: (z \in connect Unit gn l)=>//=.
  by case/connect_dom.
move=>_ i5 [lt][H5 T5 /eqP->]; move: (shapeK H5 H3)=>{H5 i5}->.
rewrite -E34; have Egr3 := (connect_split r gn).
rewrite -Egr2 Egr3 in Hs Vg.
case/(shapeUn _ Vg): (Hs)=>i5[i6][E56 H5 H6].
rewrite E56; apply: [stepX (subconnect r gn), fn] @ i5=>//=.
- move=>V2; split=>//.
  - by move: Hg2; case/andP: Hg; rewrite {1 4}Egr3=>V _ /(n_graphUnL V).
  - by apply: good_subconnect.
  - by move: Ha; rewrite {1}Egr3 joinC; apply/acyclicUn; rewrite joinC.
  - move: Hgr; rewrite /good_ptr; case/boolP: (r == null)=>//= Hnr Hr.
    rewrite dom_umfiltk inE /= Hr andbT.
    by apply: connect0=>//; rewrite dom0.
  move=>z; rewrite dom_umfiltk inE /=.
  rewrite connect_subconnect; case/boolP: (z \in connect Unit gn r)=>//=.
  by case/connect_dom.
move=>_ i7 [rt][H7 T7 /eqP->]; move: (shapeK H7 H5)=>{H7 i7}->.
rewrite -E56 E; step=>V'; exists (Node lt v rt); split=>//.
- rewrite Egr; apply/shapePtUn; first by rewrite -Egr; case/andP: Hg.
  by exists i1, i2; split=>//; rewrite E1; exists v.
rewrite /= Hp Hf eqxx /=; apply/andP; split.
- suff: tree_in_graph_b fn gn lt l by [].
  rewrite Egr2 joinC; apply: tigUn=>//; rewrite joinC -Egr2.
  by rewrite -Egr3 in Vg.
suff: tree_in_graph_b fn gn rt r by [].
by rewrite Egr3 joinC; apply: tigUn=>//; rewrite joinC.
Qed.

End SumDag.
