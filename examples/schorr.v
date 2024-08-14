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

Lemma eq_connect_aux (g1 g2 : pregraph) p:
        valid (g1 \+ g2) ->
        {subset dom g2 <= predC p} ->
        um_filterk p (g1 \+ g2) = um_filterk p g1.
Proof.
move=>V /(umfiltk_subdom0 p (validR V)) S.
by rewrite umfiltUn // S unitR. 
Qed.

Lemma connectUn_eq (g g1 g2 : pregraph) (p : pred node) x :
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

(* short notation for left/right child of x *)
Notation gl g x := (get_nth g x 0).
Notation gr g x := (get_nth g x 1).

(* type of markings *)
(* Aleks NOTE: Should we need U? My impression was that *)
(* being unmarked is represented by not being in *)
(* the appropriate map? *)
Inductive mark := U | L | R | LR.
(* decidable equality on marks *)
Definition eq_mark l1 l2 : bool :=
  if (l1, l2) is ((U, U)|(L, L)|(R, R)|(LR, LR)) then true else false.
Lemma eq_markP : Equality.axiom eq_mark.
Proof. by case; case=>//=; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build mark eq_markP.

(* marking of children *)

(* given marking map m, x is m-child of y iff: *)
(* - m y = L and x is left child of y *)
(* - m y = R and x is right child of y *)
Definition ch (m : nmap mark) (g : pregraph) (x y : nat) := 
  [|| (find y m == Some L) && (gl g y == x) |
      (find y m == Some R) && (gr g y == x)].

Lemma chP (m : nmap mark) g x y : 
        reflect [\/ (y, L) \In m /\ gl g y = x |
                    (y, R) \In m /\ gr g y = x]
                (ch m g x y).
Proof.
rewrite /ch; case: orP=>H; constructor.
- by case: H=>H; [left|right]; case/andP: H=>/eqP/In_find H /eqP.
by case=>[][/In_find/eqP M /eqP G]; apply: H; [left|right]; apply/andP.
Qed.

Lemma chN0 m g x y :
        ch m g x y ->
        y != null.
Proof. by case/chP=>[][/In_dom/dom_cond]. Qed.

Lemma ch_fun m g a b x :
        ch m g a x ->
        ch m g b x ->
        a = b.
Proof. by case/chP=>[][H <-] /chP [][/(In_fun H) {}H <-]. Qed.

Lemma ch_path m g s x :
        x \in s -> 
        path (ch m g) null s -> 
        exists y, y \in belast null s /\ ch m g y x.
Proof. exact: path_prev. Qed.

Lemma ch_path_uniq m g s :
        path (ch m g) null s -> 
        uniq (null :: s).
Proof. by apply: path_uniq; [apply: chN0|apply: ch_fun]. Qed.

Definition upd_edge (m : nmap mark) g x y : seq node := 
  if find x m is Some L then [:: y; gr g x] else [:: gl g x; y].

Fixpoint rev_graph' m g ps t : pregraph := 
  if ps is p :: ps then 
    rev_graph' m (free g p) ps p \+ pts p (upd_edge m g p t)
  else g.

Definition rev_graph m g s t := rev_graph' m g (rev s) t.

(* layout of graph+marking as heap *)
Definition lay (m : nmap mark) (g : pregraph) : heap := 
  \big[join/Unit]_(x <- dom g) (x :-> (gl g x, gr g x, odflt L (find x m))).

(* reach m g s t holds iff *)
(* each unmarked node x in g is reachable through unmarked nodes *)
(* - either starting from t, or *)
(* - starting from a right child of some node in s *)
Definition reach (m : nmap mark) (g : pregraph) (s : seq node) t := 
  forall x, 
    (* x is node in g *)
    x \in dom g ->
    (* x is unmarked *)
    x \notin dom m ->
    (* x is reachable from t avoiding marked nodes *)
    (* Aleks note: if unmarked nodes are represented by a marking U *)
    (* then this conjunct will have to change, as it currently assumes *)
    (* that unmarked nodes are just those that aren't in m *)
    x \in connect (mem (dom m)) g t \/
    (* or x is reachable from some right child of a node y in s *)
    (* avoiding marked nodes *)
    exists y, y \in s /\ x \in connect (mem (dom m)) g (gr g y).

Definition shape g0 r p t :=
  fun h:heap =>  (exists s g m,
              dom g  = dom h /\
              h = lay m g /\ 
              path (ch m g) null s /\ 
              rev_graph m g s t = g0 /\
              reach m g s t /\ 
              p = last null s /\
              r = head t s).
