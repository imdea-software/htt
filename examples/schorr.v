(*
Copyright 2024 IMDEA Software Institute
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
From Coq Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype ssrnat ssrbool seq path bigop.
From pcm Require Import options axioms pred prelude seqperm seqext.
From pcm Require Import pcm unionmap natmap heap autopcm automap.
From htt Require Import options model heapauto graph.

(*****************)
(* helper lemmas *)
(*****************)

Lemma eq_connect_aux A (g1 g2 : pregraph A) p:
        valid (g1 \+ g2) ->
        {subset dom g2 <= predC p} ->
        um_filterk p (g1 \+ g2) = um_filterk p g1.
Proof.
move=>V /(umfiltk_subdom0 p (validR V)) S.
by rewrite umfiltUn // S unitR. 
Qed.

Lemma connectUn_eq A (g g1 g2 : pregraph A) (p : pred node) x :
        valid (g \+ g1) ->
        valid (g \+ g2) ->
        {subset dom g1 <= p} ->
        {subset dom g2 <= p} ->
        connect p (g \+ g1) x =i connect p (g \+ g2) x.
Proof.
move=>V1 V2 S1 S2 z.
rewrite -connect_umfiltk eq_connect_aux //=; last first.
- by move=>y /S1; rewrite inE negbK.
rewrite -[RHS]connect_umfiltk eq_connect_aux //.
by move=>y /S2; rewrite !inE negbK.
Qed.

(*****************)
(* Binary graphs *)
(*****************)

(* short notation for left/right node of x *)
Notation lft g x := (get_nth g x 0).
Notation rgh g x := (get_nth g x 1).

Definition contents {A} (g : pregraph A) : nmap A := mapv fst g.

HB.instance Definition _ A := 
  OmapFun.copy (@contents A) (@contents A).

Lemma In_contentsX A (g : pregraph A) x v :
        (x, v) \In contents g <-> 
        exists lks, (x, (v, lks)) \In g.
Proof.
rewrite In_omfX; split; last by case=>lks H; exists (v, lks).
by case; case=>w lks /= H [<-{v}]; exists lks.
Qed.

Lemma In_contents A (g : pregraph A) x v lks :
        (x, (v, lks)) \In g ->
        (x, v) \In contents g.
Proof. by rewrite In_contentsX; exists lks. Qed.

Definition links {A} (g : pregraph A) : nmap (seq node) := mapv snd g.

HB.instance Definition _ A := 
  OmapFun.copy (@links A) (@links A).

Lemma In_linksX A (g : pregraph A) x lks : 
        (x, lks) \In links g <->
        exists v, (x, (v, lks)) \In g.
Proof.
rewrite In_omfX; split; last by case=>v H; exists (v, lks).
by case; case=>v lks' /= H [<-{lks}]; exists v.
Qed.

Lemma In_links A (g : pregraph A) x v lks : 
        (x, (v, lks)) \In g ->
        (x, lks) \In links g.
Proof. by rewrite In_linksX; exists v. Qed.

(* laying binary pregraph onto heap *)
Definition lay2_k {A} (v : A * seq node) : dynamic id :=
  idyn (v.1, (nth null v.2 0, nth null v.2 1)).
Definition lay2 {A} (g : pregraph A) : heap := mapv lay2_k g.

HB.instance Definition _ A := 
  OmapFun.copy (@lay2 A) (@lay2 A).


Canonical heap_PredType : PredType (nat * dynamic id) := 
  um_PredType heap.
Coercion Pred_of_nmap (x : heap) : {Pred _} := 
  [eta Mem_UmMap x].

Lemma In_layX A (g : pregraph A) x (v : A) lft rgh : 
        (x, idyn (v, (lft, rgh))) \In lay2 g <->
        exists lks, 
          [/\ lft = nth null lks 0, 
              rgh = nth null lks 1 & 
              (x, (v, lks)) \In g].
Proof.
rewrite In_omfX; split; last first.
- by case=>lks [->-> H]; exists (v, lks).
case=>-[w lks] H /Some_inj/inj_pair2 /= [<-{v} <-<-].
by exists lks.
Qed.

Lemma In_lay A (g : pregraph A) x (v : A) lks :
        (x, (v, lks)) \In g ->
        (x, idyn (v, (nth null lks 0, nth null lks 1))) \In lay2 g.
Proof. by rewrite In_layX=>H; exists lks. Qed.

Lemma In_lay2X A (g : pregraph A) x (v : A) lft rgh : 
        n_pregraph_axiom 2 g ->
        (x, idyn (v, (lft, rgh))) \In lay2 g <->
        (x, (v, [:: lft; rgh])) \In g.
Proof.
move=>H; split; last first.
- by move=>X; apply/In_layX; exists [:: lft; rgh].
case/In_layX=>lks [L R X]. 
rewrite -(_ : lks = [:: lft; rgh]) //.
rewrite (In_graph X) (links_nth H (In_dom X)) /=.
by rewrite /get_nth -(In_graph X) -L -R.
Qed.

Lemma In_lay2 A (g : pregraph A) x (v : A) lft rgh : 
        n_pregraph_axiom 2 g ->
        (x, (v, [:: lft; rgh])) \In g ->
        (x, idyn (v, (lft, rgh))) \In lay2 g.
Proof. by move=>H /In_lay2X-/(_ H). Qed.



(* updating binary pregraph at node x *)

(* pass v = None to just update links *)
Definition bupd A (g : pregraph A) x (v : option A) (lft rgh : node) :=
  if find x (contents g) is Some v' then 
    if v is Some w then upd x (w, [:: lft; rgh]) g 
    else upd x (v', [:: lft; rgh]) g
  else undef.

Lemma bupd_is_binary A (g : pregraph A) x v lft rgh : 
        n_pregraph_axiom 2 g ->
        n_pregraph_axiom 2 (@bupd A g x v lft rgh).
Proof.
move=>H z; rewrite /bupd find_omf /omfx /=.
case: (find x g)=>[[m lnk]|//].
case: v=>[w|]; rewrite domU inE /graph.links findU;
case: (x =P 0)=>//= /eqP Nx; case: (z =P x)=>[_ V|_ Dz].
- by rewrite V.
- by rewrite H.
- by rewrite V.
by rewrite H.
Qed.

(* updating just contents *)
Notation updC g x v := (bupd g x (Some v) (lft g x) (rgh g x)).
(* updating just left link *)
Notation updL g x l := (bupd g x (contents g x) l (rgh g x)).
(* updating just right link *)
Notation updR g x r := (bupd g x (contents g x) (lft g x) r).
(* updating just contents and left link *)
Notation updCL g x v l := (bupd g x (Some v) l (rgh g x)).
(* updating just contents and right link *)
Notation updCR g x v r := (bupd g x (Some v) (lft g x) r).

Lemma glE A (g : pregraph A) (x : node) : 
        n_pregraph_axiom 2 g ->
        x \in dom g ->
        graph.links g x = [:: lft g x; rgh g x].
Proof. by move=>H D; rewrite (links_nth H D). Qed.

Lemma glD A (g : pregraph A) (x : node) : 
        n_pregraph_axiom 2 g ->
        x \in dom g ->
        (x, [:: lft g x; rgh g x]) \In links g.
Proof.
move=>H /[dup]/In_graphX R /(glE H) <-.
by apply/In_linksX.
Qed.

Lemma getU A (g : pregraph A) (x : node) v lf rg i : 
        get_nth (bupd g x v lf rg) x i = 
        if x \notin dom g then null
        else nth null [:: lf; rg] i.
Proof.
rewrite /get_nth/graph.links/bupd find_omf/omfx /=.
case: (dom_find x)=>[|w /In_find H _]; first by rewrite nth_nil.
by case: v=>[v|] /=; rewrite findU eqxx /= (In_cond H) (In_valid H).
Qed.

(****************)
(* Schorr-Waite *)
(****************)

(* type of markings *)
Inductive mark := U | L | R | LR.
(* decidable equality on marks *)
Definition eq_mark l1 l2 : bool :=
  if (l1, l2) is ((U,U)|(L, L)|(R, R)|(LR, LR)) then true else false.
Lemma eq_markP : Equality.axiom eq_mark.
Proof. by case; case=>//=; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build mark eq_markP.

Notation pregraph := (pregraph mark).

Definition marked (g : pregraph) : pregraph := 
  um_filterv (fun v => v.1 != U) g.
HB.instance Definition _ := OmapFun.copy marked marked.


(* marking of children *)

(* given marking map m, x is m-child of y iff: *)
(* - m y = L and x is left child of y *)
(* - m y = R and x is right child of y *)
Definition ch (g : pregraph) (x y : nat) := 
  [|| (find y (contents g) == Some L) && (lft g y == x) |
      (find y (contents g) == Some R) && (rgh g y == x)].

Lemma chP (g : pregraph) x y : 
        reflect [\/ (y, L) \In contents g /\ lft g y = x |
                    (y, R) \In contents g /\ rgh g y = x]
                (ch g x y).
Proof.
rewrite /ch; case: orP=>H; constructor.
- by case: H=>H; [left|right]; case/andP: H=>/eqP/In_find H /eqP.
by case=>[][/In_find/eqP M /eqP G]; apply: H; [left|right]; apply/andP.
Qed.

Lemma chN0 g x y :
        ch g x y ->
        y != null.
Proof. by case/chP=>[][/In_dom/dom_cond]. Qed.

Lemma ch_fun g a b x :
        ch g a x ->
        ch g b x ->
        a = b.
Proof. by case/chP=>[][H <-] /chP [][/(In_fun H) {}H <-]. Qed.

Lemma ch_path g s x :
        x \in s -> 
        path (ch g) null s -> 
        exists y, y \in belast null s /\ ch g y x.
Proof. exact: path_prev. Qed.

Lemma ch_path_uniq g s :
        path (ch g) null s -> 
        uniq (null :: s).
Proof. by apply: path_uniq; [apply: chN0|apply: ch_fun]. Qed.


Definition upd_edge g x y : mark * seq node := 
  match find x (contents g) with
  | Some L => (L, [:: y; rgh g x])
  | _ => (R, [:: lft g x; y])
  end.

Fixpoint rev_graph' (g : pregraph) (ps : seq node) t : pregraph := 
  if ps is p :: ps then 
    rev_graph' (free g p) ps p \+ pts p (upd_edge g p t)
  else g.

Definition rev_graph g s t := rev_graph' g (rev s) t.

(* layout of graph+marking as heap *)


(*
Definition lay (g : pregraph) : heap := 
  \big[join/Unit]_(x <- dom g) (x :-> (gl g x, gr g x, odflt L (find x m))).

Lemma bigF (A : eqType) (xs : seq A) (f : A -> heap) k : 
        valid (\big[join/Unit]_(i <- xs) f i) ->
        free (\big[join/Unit]_(i <- xs) f i) k = 
        \big[join/Unit]_(i <- xs) free (f i) k.
Proof.
elim: xs=>[|x xs IH].
- by rewrite !big_nil free0.
rewrite !big_cons => V.
rewrite freeUn.
case: ifP=>D.
- rewrite IH //. rewrite (validR V). by [].
rewrite -IH; last by rewrite (validX V).
rewrite !freeND //.
- apply: contraFN D=>D.
  rewrite domUn inE D orbT andbT.
  by [].
apply: contraFN D=>D.
by rewrite domUn inE (validX V) D.
Qed.
*)


Lemma In_layE1 (g : pregraph) x pl pr c : 
        n_pregraph_axiom 2 g ->
        find x (lay2 g) = Some (idyn (c, (pl, pr))) ->
        (x, (c, [:: pl; pr])) \In g.
Proof. by move=>H /In_find /In_lay2X-/(_ H). Qed.

Lemma In_layE2 (g : pregraph) x pl pr c : 
        n_pregraph_axiom 2 g ->
        (x, (c, [:: pl; pr])) \In g ->
        find x (lay2 g) = Some (idyn (c, (pl, pr))).
Proof. by move=>H /In_lay2X-/(_ H)/In_find. Qed.

Lemma In_layX2 (g : pregraph) x c pl pr : 
        n_pregraph_axiom 2 g ->
        (x, (c, [:: pl; pr])) \In g ->
        exists h, lay2 g = x :-> (c, (pl, pr)) \+ h.
Proof. by move=>H Gx; eexists _; apply/heap_eta2/In_layE2. Qed.

Lemma In_layX3 (g : pregraph) x l r c : 
         lay2 (bupd g x (Some c) l r) = 
         if x \in dom g then 
           upd x (idyn (c, (l, r))) (lay2 g)
         else undef.
Proof.
rewrite /lay2/bupd find_omf/omfx /=.
case: (dom_find x)=>[|v]; first by rewrite omap_undef.
move/In_find=>E _; rewrite (upd_eta x).
rewrite omapPtUn -(upd_eta x) validU.
rewrite (In_cond E) (In_valid E) /=.
rewrite (upd_eta x) !omap_free !omap_omap.
congr (_ \+ _); apply/eq_in_omap.
by case=>k w /= H; case: (k =P x).
Qed.

Lemma In_layX4 (g : pregraph) x l r c : 
         lay2 (x &-> (c, [:: l; r]) \+ g) = 
         x :-> (c, (l, r)) \+ lay2 g.
Proof.
rewrite omfPtUn /=; case: ifP=>// V; set j := (_ \+ _).
case: (normalP j)=>[->//|].
rewrite !validPtUn valid_omap dom_omf_some // in V *.
by rewrite V.
Qed.

(* reach g s t holds iff *)
(* each unmarked node x in g is reachable through unmarked nodes *)
(* - either starting from t, or *)
(* - starting from a right child of some node in s *)

Definition reach (g : pregraph) (s : seq node) (t : node) := 
  forall x, 
    (* if x is unmarked node in g *)
    (x, U) \In contents g ->
    (* then x is reachable from t avoiding marked nodes *)
    x \in connect (mem (dom (marked g))) g t \/
    (* or x is reachable from some right child of a node in s *)
    (* avoiding marked nodes *)
    exists2 y, y \in s &
      x \in connect (mem (dom (marked g))) g (rgh g y).

UP TO HERE

Definition shape (g0 g : pregraph) (m : nmap mark) (r p t : node) :=
  fun h => exists stack, 
    [/\ h = lay m g, 
        {subset dom m <= dom g},
        path (ch m g) null stack, 
        rev_graph m g stack t = g0, 
        reach m g stack t, 
        {subset dom (um_filterv (predU (pred1 L) (pred1 LR)) m) <= stack},
        p = last null stack, 
        r = head t stack, 
        n_pregraph_axiom 2 g &
        graph_axiom g].

Program Definition pop (p t : ptr): 
  STsep {g0 g m r} (fun h => 
    [/\ shape g0 g m r p t h,
        (p, R) \In m &
        t \in dom m \/ t = null],
    [vfun res h => 
       let: g' := upd p [:: gl g p; t] g in
       let: m' := upd p LR m in
         shape g0 g' m' r res.1 res.2 h /\
         res = (gr g p, p)]) :=
  Do (q <-- read (A:=node*node*mark) p;
      p ::= (q.1.1, t, LR);;
      ret (q.1.2, p)).
Next Obligation.
move=>p t [g0][g][m][r][/= h][H Pm D]. 
case: H=>stack [-> H1 H2 H3 H4 H5 H6 H7 H8 H9].
move: (H1 p (In_dom Pm))=>Pg.
case/(glD H8)/(In_layX2 H8 H1): (Pg)=>h' E.
rewrite E.
do 3!step; split=>//; exists stack; split.
- rewrite In_layX3.
  - by rewrite upd_eta E freePtUn // (validX H).
  - by rewrite (dom_valid Pg).
  - by rewrite (In_valid Pm).
  - by rewrite (In_cond Pm).

Search upd.


admit. 
Admitted.

Program Definition swing (p t : ptr):
  STsep {g0 g m r} (fun h =>
    [/\ shape g0 g m r p t h,
        (p, L) \In m &
        t \in dom m \/ t = null],
    [vfun res h =>
       let: g' := upd p [:: t; gl g p] g in
       let: m' := upd p R m in
         shape g0 g' m' r res.1 res.2 h /\
         res = (t, gl g t) ]) :=
  Do (q <-- read (A:=node*node*mark) p;
      p ::= (t, q.1.1, R);;
      ret (p, q.1.2)).
Next Obligation.
move=>p t [g0][g][m][r][/= h][H P D].
case: H=>stack [-> H1 H2 H3 H4 H5 H6 H7 H8 H9].
move: (H1 p (In_dom P))=>/(glD H8) /(In_layX2 H8 H1) [h' ->].
do 3!step; split=>//. 
exists stack; split =>//.
admit.
Admitted.

Program Definition push (p t : ptr):
  STsep {g0 g m r} (fun h =>
    [/\ shape g0 g m r p t h,
        t \in dom g &
        t \notin dom m],
    [vfun res h =>
       let: g' := upd t [:: p; gr g t] g in
       let: m' := upd t L m in
         shape g0 g' m' r res.1 res.2 h /\
         res = (t, gl g t) ]) :=
  Do (q <-- read (A:=node*node*mark) t;
      t ::= (p, q.1.2, L);;
      ret (t, q.1.1)).
Next Obligation.
move=>p t [g0][g][m][r][/= h][H P D].
case: H=>stack [-> H1 H2 H3 H4 H5 H6 H7 H8 H9].
admit.
Admitted.

