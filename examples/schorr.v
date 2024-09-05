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

(****************)
(* Schorr-Waite *)
(****************)

(* type of markings *)
(* U = unmarked *)
(* M m = marked, but still exploring m (LL or RR) subgraph *)
(* MM = fully marked and explored both subgraphs *)
Inductive mark := U | M of Side | MM.
(* decidable equality on marks *)
Definition eq_mark l1 l2 : bool :=
  if (l1, l2) is ((U,U)|(M LL, M LL)|(M RR, M RR)|(MM, MM)) 
  then true else false.
Lemma eq_markP : Equality.axiom eq_mark.
Proof. 
case; case=>//=; try by [constructor];
by case=>[|[]|]; constructor.
Qed.
HB.instance Definition _ := hasDecEq.Build mark eq_markP.

Notation pregraph := (pregraph mark).

Definition marked (g : pregraph) : pregraph := 
  um_filterv (fun v => v.1 != U) g.
HB.instance Definition _ := OmapFun.copy marked marked.

Definition omark (g : pregraph) x : option Side :=
  if olabel g x is Some (M m) then Some m else None.

(* marking of children *)

(*
(* given marking map m, x is m-child of y iff: *)
(* - m y = L and x is left child of y *)
(* - m y = R and x is right child of y *)
Definition ch (g : pregraph) (x y : nat) := 
  [|| (olabel g y == Some LL) && (lft g y == x) |
      (olabel g y == Some RR) && (rgh g y == x)].

Lemma chP (g : pregraph) x y : 
        reflect [\/ (y, L) \In labels g /\ lft g y = x |
                    (y, R) \In labels g /\ rgh g y = x]
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
*)

(* node in the stack are marked L or R *)
(* other direction also holds, but isn't stated explicitly *)
(* as it's implied by graph_diff (defined below) *)
Definition stack_marked (g : pregraph) (s : seq node) := 
  forall x, x \in s -> isSome (omark g x).

(* consecutive stack nodes respect marking *)
Definition stack_consec (g : pregraph) (s : seq node) := 
  forall x y m, 
    (* if x is just under y in the stack *)
    consec (null :: s) x y -> 
    (* and y is marked by m *)
    omark g y = Some m ->
    (* then x is y's child, left or right determined by m *)
    x = sel2 m g y.

(* graph g differs from g0 only in reversing edges on the stack *)
Definition graph_diff (g0 g : pregraph) (s : seq node) t := 
  [/\ (* graphs have equal nodes, and *)
      dom g0 = dom g & forall x, 
      (* if x is marked m, then *)
      if omark g x is Some m then
      (* m-child of x in g is predecessor of x (or null, if stack empty) *)
        [/\ consec (null :: s) (sel2 m g x) x, 
      (* m-child of x in g0 is successor of x (or t, if x last) *)
            consec (rcons s t) x (sel2 m g0 x) &
      (* graphs agree on children of flipped marking *)
            sel2 (flip m) g x = sel2 (flip m) g0 x] 
      (* otherwise, if x is unmarked or fully marked, then *)
      (* graphs agree on children of x *)
      else forall m, sel2 m g x = sel2 m g0 x].
      
(* each unmarked node is reachable either from t *)
(* or from stack's right spine, *)
(* in both cases by avoiding marked nodes *)
Definition reach (g : pregraph) (s : seq node) (t : node) := 
  forall x, 
    (* if x is unmarked node in g *)
    (x, U) \In labels g ->
    (* then x is reachable from t avoiding marked nodes *)
    x \in connect [dom (marked g)] g t \/
    (* or x is reachable from some right child of a node in stack s *)
    (* avoiding marked nodes *)
    exists2 y, y \in s &
      x \in connect [dom (marked g)] g (rgh g y).

Definition shape (g0 g : pregraph) (r p t : node) :=
  fun h => exists s, 
    [/\ h = lay2 g, p = last null s, r = head t s, 
        stack_marked g s, stack_consec g s,
        graph_diff g0 g s t, reach g s t,
        n_pregraph_axiom 2 g & graph_axiom g].

Program Definition pop (p t : ptr): 
  STsep {g0 g r} (fun h => 
    [/\ shape g0 g r p t h,
        (p, M RR) \In labels g &
        t \in dom (marked g) \/ t = null],
    [vfun res h => 
       shape g0 (updCR g p MM t) r res.1 res.2 h /\
       res = (rgh g p, p)]) :=
  Do ('(_, (l, r)) <-- read (mark*(node*node)) p;
      p ::= (MM, (l, t));;
      ret (r, p)).
Next Obligation.
move=>p t [g0][g][r][_][[s [->]] S Sel Dg C Rc Ep Er H G Pm D] /=.
case/In_marksX: Pm=>lks /[dup] /(In_blinks H) -> Pm.
have Uq : uniq (null :: s).
- admit.
have Ps : p \in s.
- by rewrite Ep last_change // -Ep (In_cond Pm).
rewrite Ep in Ps.
case/rcons_lastP: Ps=>s'.  rewrite -Ep.
move=>E. subst s.
clear Ep. 
have Nxs' : p \notin s'.
- simpl in Uq. rewrite rcons_uniq in Uq.
  by case/and3P: Uq.

case: (In_layX2 H Pm)=>h /[dup] E ->; do 3!step; move=>V.
split=>//; exists s'; split. 
- by rewrite In_layX3 /= (In_dom Pm) upd_eta E freePtUn ?(validX V).
- move=>x. 
  rewrite /bupd (In_findE (In_marks Pm)) omfU ?(In_cond Pm) //=. 
  split.
  - move=>B.
    have Nxp : x != p.
    - by case: eqP B Nxs'=>// ->->.
    have : x \in rcons s' p. rewrite mem_rcons inE B orbT. by [].
    move/S. case=>X; [left|right].
    - apply/InU=>/=. rewrite validU (In_cond Pm) (negbTE Nxp). rewrite pfVE (In_valid Pm). by [].
    - apply/InU=>/=. rewrite validU (In_cond Pm) (negbTE Nxp). rewrite pfVE (In_valid Pm). by [].
    rewrite !InU /=.
    case; case; case: eqP=>// /eqP Nxp _ X; 
    suff : x \in rcons s' p by [rewrite mem_rcons inE (negbTE Nxp)].
    - by apply/S; left.
    by apply/S; right.
k

  

    have : x != p /\ x \in s.
    - 


  - move/mem_belast.

    - rewrite /bupd (In_findE (In_marks Pm)). 




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

