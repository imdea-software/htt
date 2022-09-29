From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From fcsl Require Import options axioms pred ordtype.
From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import interlude model heapauto.
From HTT Require Import bintree.

Section Wand.
Variable U : pcm.

Definition wand (p2 p : Pred U) : Pred U :=
  [Pred h1 | forall h2 h, h = h1 \+ h2 -> h2 \In p2 -> h \In p].

End Wand.

Notation "p2 '--#' p" := (wand p2 p)
  (at level 58, right associativity) : rel_scope.

Section Bingraph.
Variable A : Type.

Variant bin_node := BN of ptr & A & ptr.

(* this looks like a `ptr :-> bin_node` aux PCM *)
Definition graph := seq (ptr * bin_node).

Definition node_shape p (n : bin_node) :=
  let '(BN l a r) := n in
  [Pred h | h = p :-> l \+ (p .+ 1 :-> a \+ p .+ 2 :-> r)].

Lemma node_shapeK h1 h2 p n :
  h1 \In node_shape p n -> h2 \In node_shape p n -> h1 = h2.
Proof. by case: n=>/= l a r ->->. Qed.

Definition shape (gr : graph) :=
  IterStar.sepit gr (fun '(p,n) => node_shape p n).

Lemma shapeK h1 h2 gr :
  h1 \In shape gr -> h2 \In shape gr -> h1 = h2.
Proof.
rewrite /shape; elim: gr h1 h2=>[|[p n] gr IH] h1 h2.
- by move/IterStar.sepit0=>->/IterStar.sepit0->.
case/IterStar.sepit_cons=>h11[h12][{h1}-> H11 H12].
case/IterStar.sepit_cons=>h21[h22][{h2}-> H21 H22].
by rewrite (node_shapeK H11 H21) (IH _ _ H12 H22).
Qed.

(* focusing on a node *)
Lemma in_shape g n p :
  (p, n) \In g ->
  forall h, valid h ->
  h \In shape g <-> h \In node_shape p n # (node_shape p n --# shape g).
Proof.
elim: g; first by move/In_nil.
move=>[q nq] g IH /In_cons; case.
- case=>[{q}<-{nq}<-] h Vh; rewrite /shape IterStar.sepit_cons; split.
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

Corollary no_null g n h :
  valid h -> h \In shape g -> (null, n) \Notin g.
Proof.
case: n=>p l r V + Hg; case/(in_shape Hg V)=>h1[h2][E H1 _].
by rewrite E H1 in V.
Qed.

End Bingraph.

Section TIG.
Variable A : Type.

Fixpoint tree_in_graph (g : graph A) (t : tree A) (p : ptr) : Prop :=
  if t is Node l a r then
    exists pl pr,
    [ /\ (p, BN pl a pr) \In g,
         tree_in_graph g l pl &
         tree_in_graph g r pr]
  else p = null.

Lemma tree_in_graph_null g t :
  tree_in_graph g t null -> forall h, valid h -> h \In shape g -> t = leaf.
Proof.
case: t=>//=l a r [pl][pr][Ht Hl Hr] h V Hg.
by move: (no_null V Hg Ht).
Qed.

Lemma tree_in_graph_nonnull g t p :
  p != null -> tree_in_graph g t p ->
  exists (x : A) tl (pl : ptr) tr (pr: ptr),
  [ /\ t = Node tl x tr,
       (p, BN pl x pr) \In g,
       tree_in_graph g tl pl &
       tree_in_graph g tr pr ].
Proof.
move=>Hp; case: t=>/=.
- by move=>Ep; rewrite Ep in Hp.
move=>tl x tr [pl][pr][Hp1 Hl Hr].
by exists x, tl, pl, tr, pr; split=>//; rewrite -E1.
Qed.

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

Section ExampleDag.
Definition p1 := ptr_nat 1.
Definition p2 := ptr_nat 2.
Definition p3 := ptr_nat 3.

Definition graph1 : graph nat :=
  [:: (p1, BN null 2 null);
      (p2, BN p1   3 p1  );
      (p3, BN p1   1 p2  )].

Definition tree1 : tree nat :=
   Node (Node leaf 2 leaf)
        1
        (Node (Node leaf 2 leaf)
              3
              (Node leaf 2 leaf)).

Lemma tree1_in_graph1 : tree_in_graph graph1 tree1 p3.
Proof.
rewrite /graph1 /=.
exists p1, p2; split.
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

Section SumDag.

Fixpoint sum_tree (t : tree nat) : nat :=
  if t is Node l n r
    then sum_tree l + n + sum_tree r
  else 0.

Definition treesumT : Type := forall (p : ptr),
  {(t : tree nat) (gr : graph nat)},
  STsep (fun h => shape gr h /\ tree_in_graph gr t p,
          [vfun n h => n == sum_tree t /\ shape gr h]).

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

End SumDag.
