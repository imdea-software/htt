(*
Copyright 2025 IMDEA Software Institute
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
From Stdlib Require Import Recdef ssreflect ssrfun.
From mathcomp Require Import eqtype ssrnat ssrbool seq path bigop.
From pcm Require Import options axioms pred prelude seqperm seqext.
From pcm Require Import pcm unionmap natmap heap auto autouniq autopcm automap.
From htt Require Import options model heapauto graph.

(*****************************)
(*****************************)
(* Union-find data structure *)
(*****************************)
(*****************************)

(* The structure maintains a set of equivalence classes     *)
(* each with its own representative. Exported methods are:  *)
(* - new : allocates a new element in its own equiv_class   *)
(* - find x : finds representative of x's equivalence class *)
(* - union x1 x2 : joins the classes of x1 and x2, with one *)
(*    of x1 or x2 the new overall representative            *)

(* NOTE: Types below are *unique* in using small-footprint  *)
(* specs for the structure's methods. Quite surprisingly,   *)
(* the related work on the union-find structure seems to    *)
(* exclusively use large footprint specs, in contravention  *)
(* to the key reasoning patterns of separation logic.       *)

(***************************************)
(*  Abstractions for the specification *)
(***************************************)

(* equiv_class s x = nodes in set s have x as representative *)
(* describes *one* inverted tree in the union-find structure *)

Definition equiv_class (s : fset node) (x : node) : Pred heap :=
  fun h => exists (g : unary_graph unit),
     [/\ h \In graph1 g, summits g =i loops g,
         summits g =i [:: x] & dom s =i nodes g].

(* common inference out of equiv_class exposes graph g *)
Lemma eqcE h s x :
        h \In equiv_class s x <->
        exists (g : unary_graph unit),
        [/\ h \In graph1 g, valid g, valid s, x != 0,
            summits g =i loops g, summits g =i [:: x], dom s =i nodes g,
            x \in summits g, x \in loops g, x \in nodes g & x \in dom s].
Proof.
split=>[[g][H1 H2 H3 H4]|[g][]]; exists g=>//.
have [N D] : x \in nodes g /\ x \in dom s by rewrite H4 loopsD // -H2 H3 inE.
by rewrite (dom_valid N) (dom_cond N) (dom_valid D) -H2 H3 inE.
Qed.

(* clients don't need g, but reason out of disjointness of *)
(* represented classes and the representative being inside the class *)

Lemma eqcD h s x :
        h \In equiv_class s x ->
        x \in dom s.
Proof. by case/eqcE=>g []. Qed.

Lemma eqcV2 h1 h2 s1 s2 x1 x2 :
        h1 \In equiv_class s1 x1 ->
        h2 \In equiv_class s2 x2 ->
        valid (h1 \+ h2) ->
        valid (s1 \+ s2).
Proof.
case/eqcE=>g1 [H1 _ V1 ????????] /eqcE [g2][H2 _ V2 ????????].
move/(In_graph1V2 H1 H2)=>V; apply/domeqVUn/V; apply/domeqP;
by (split; [|apply/domE]); rewrite ?(validX V, V1, V2).
Qed.

(******************************)
(* Union-find code and proof  *)
(* in small footprint style   *)
(******************************)

(* new : creates fresh equivalence class with single element *)

Program Definition new :
    STsep (emp, [vfun r h => h \In equiv_class (#r) r]) :=
  Do (p <-- allocb tt 2;
      p.+1 ::= p;;
      ret p).
Next Obligation.
case=>h ->; step=>p; do !step; rewrite !unitR=>V.
exists (p &1-> (tt, p)); rewrite graph1Pt; split=>// x;
by rewrite ?(summitsPt,loops1Pt,domPtK,defPt_nullO V,inE,eqxx,andbT).
Qed.

(* find x : returns the equiv_class representative of x *)

(* loop invariant of find *)
Definition find_tp := forall (x : node), STsep {s y}
  (fun h => h \In equiv_class s y /\ x \in dom s,
   [vfun r h => h \In equiv_class s y /\ r = y]).

Program Definition find :=
  ffix (fun (go : find_tp) (x : node) =>
    Do (p <-- !x.+1;
        if x == p then ret p else go p)).
Next Obligation.
move=>go x [s][y][_][[g][-> Sl Sy /[dup] Dg ->]] /[dup] Dx /In_graph1X /=.
case=>-[[/= z]][/[swap] N] /[dup]/In_eta/[dup] E -> /In_valid V.
rewrite graph1layPtUn; step; rewrite -(graph1layPtUn _ (_, _)) -E.
case: (x =P z) E V N=>[<-{z}|_] E V N.
- step; split; [by exists g|apply/eqP].
  by rewrite -mem_seq1 -Sy Sl E loopsUn // loops1Pt ?(dom_cond Dx,eqxx).
apply: [gE s, y]=>//=; split; first by exists g.
case: (part_char (g:=g))=>[t|C _ /nilP L]; first by rewrite Sl.
by rewrite -N Dg nxt_leaves_closed ?L.
Qed.

(* union : joins equivalence classes of two representatives x1, x2 *)
(* and returns one of x1, x2 as the representative of the new class *)
(* NOTE: current implementation always returns x2, *)
(* but there are implementations that return either x1 or x2, *)
(* so the spec makes no commitment *)

Program Definition union (x1 x2 : node) : STsep {s1 s2}
    (equiv_class s1 x1 # equiv_class s2 x2,
     [vfun r h => h \In equiv_class (s1 \+ s2) r /\
                  r \in [:: x1; x2]]) :=
  Do (x1.+1 ::= x2;;
      ret x2).
Next Obligation.
move=>x1 x2 [s1][s2][_][h1][h2][->] H1 H2 /=; apply: vrfV=>V.
case/eqcE: (H1)=>g1 [G1 _ _ Nx1 Se1 Sx1 Dn1 X Lx1 _   _].
case/eqcE: (H2)=>g2 [G2 _ _ _   Se2 Sx2 Dn2 _ _   Dx2 _].
move/(eqcV2 H1 H2): V (V) Dx2=>{H1 H2}Vs /(In_graph1V2 G1 G2) Vg.
move/(dom_inNR Vg)=>Ng; case/(part_loop_eta (eq_subsetL Se1)): X=>-[Eg1].
rewrite {}G1 {}G2 -graph1layUn Eg1 -joinA graph1layPtUn; do 2!step.
rewrite -(graph1layPtUn _ (_, _)) joinA.
set g1' := pts _ _ \+ _; move/graph1layVI=>Vg'.
have {Se1}Pr1' : preacyclic g1'.
- move/eq_subsetL/part_preacyclic: Se1; rewrite Eg1.
  by apply: preacyclic_mutation; rewrite -Eg1 ?(validL Vg).
have Es : summits g1' =i summits g2.
- move=>z; rewrite summitsUn ?(validL Vg') // Sx2 !mem_filter /=.
  rewrite domF domPt summitsPt {}Nx1 //= !inE (eq_sym x1) andbC.
  case: (z =P x1)=>[|Nz /=]; first by rewrite andbT orbF.
  case: (z =P x2) Ng=>[->->|_ _] //=; apply/negP.
  by move/(part_summits1_free Lx1); rewrite Sx1 inE=>/eqP/Nz.
split; last by rewrite !inE eqxx orbT.
exists (g1' \+ g2); split=>// z; last first.
- by rewrite domUnE // domUnE // Dn1 Dn2 Eg1 !domPtUn !inE !validPtUn.
- by rewrite (summits1EqUnL Vg') // Es Sx2.
rewrite (summits1EqUnL Vg' Es) loopsUn // -Se2 -Es orb_idl //.
by apply: loops_summits_sub.
Qed.

(* unit test for client-side reasoning *)

Program Definition test1 :
    STsep (emp, [vfun r h => exists s, h \In equiv_class s r /\ r \in dom s]) :=
  Do (x <-- new;
      y <-- new;
      rx <-- find x;
      ry <-- find y;
      union rx ry).
Next Obligation.
case=>h ->; apply: stepE=>//= x1 h1 C1; apply: stepV=>//= x2 h2 C2.
apply: [stepR #x1, x1] @ h1=>//= [|_ {}h1 [{}C1 ->]]; first by rewrite domPtV.
apply: [stepR #x2, x2] @ h2=>//= [|_ {}h2 [{}C2 ->]]; first by rewrite domPtV.
apply: [gE #x1, #x2]=>//= [|??]; first by eexists _, _.
by case=>/[dup]/eqcD; exists (#x1 \+ #x2).
Qed.


