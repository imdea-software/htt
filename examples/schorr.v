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
From Stdlib Require Import ssreflect ssrfun.
From mathcomp Require Import eqtype ssrnat ssrbool seq path bigop.
From pcm Require Import options axioms pred prelude seqperm seqext.
From pcm Require Import pcm unionmap natmap heap auto autouniq autopcm automap.
From htt Require Import options model heapauto graph.

(****************)
(* Schorr-Waite *)
(****************)

(* type of markings *)
(* O = unmarked *)
(* L = traversal of left subgraph started *)
(* R = left subgraph finished, traversal of right subgraph started *)
(* X = both subgraphs finished *)
Inductive mark := O | L | R | X.

(* decidable equality on marks *)
Definition eq_mark c1 c2 : bool :=
  if (c1, c2) is ((O,O)|(L,L)|(R,R)|(X,X)) then true else false.
Lemma eq_markP : Equality.axiom eq_mark.
Proof. by case; case=>//; constructor. Qed.
HB.instance Definition _ := hasDecEq.Build mark eq_markP.

Implicit Type g : binary_graph mark.

Notation "g /LR" := (cfilt g [:: L; R]) (at level 1, format "g /LR").
Notation "g /O" := (cfilt g [:: O]) (at level 1, format "g /O").
Notation "g /X" := (cfilt g [:: X]) (at level 1, format "g /X").
Notation "g /OLR" := (cfilt g [:: O; L; R]) (at level 1, format "g /OLR").
Abbreviation marked0 g := (nodes0 (cfilt g [:: L; R; X])).

Definition if_mark (f : node -> node) x '(m, (l, r)) :=
  (tt, match m with L => (f x, r) | R => (l, f x) | _ => (l, r) end).

Definition inset a := graph_map (if_mark (prev (null :: a))).
HB.instance Definition _ a := MapFun.on (inset a).
Definition restore a t := graph_map (if_mark (next (rcons a t))).
HB.instance Definition _ a t := MapFun.on (restore a t).

Lemma eq_ifmark f1 f2 g :
        {in nodes g/LR, f1 =1 f2} ->
        graph_map (if_mark f1) g = graph_map (if_mark f2) g.
Proof. by rewrite /if_mark -eq_in_graphmap=>+x [[]]//v /nodes_cfilt X=>->. Qed.

Lemma ifmark_erase f g :
        nodes g/LR =i [::] ->
        graph_map (if_mark f) g = erase g.
Proof. by rewrite -eq_in_graphmap=>+ k [][][??]/(nodes_cfilt [::L;R])=>->. Qed.

Lemma inset_rcons a p g :
        nodes g/LR =i a ->
        inset (rcons a p) g = inset a g.
Proof. by move=>S; apply/eq_ifmark=>x; rewrite S /= prevat_rcons=>->. Qed.

Lemma restore_rcons a p t g :
        nodes g/LR =i a ->
        restore (rcons a p) t g = restore a p g.
Proof. by move=>S; apply/eq_ifmark=>x; rewrite S next_rcons=>->. Qed.

Definition inv' g0 g a t p :=
  [/\ p = last null a, uniq (null :: a), t \in nodes0 g,
      closed g,
      inset a g = erase g,
      restore a t g = erase g0,
      nodes g/LR =i a &
      {subset nodes g/O <=
        [predU \big[cat/[::]]_(x <- a) (reach g/O (rgh g x)) & reach g/O t]}].

Definition inv g0 g t p := exists a, inv' g0 g a t p.

(*******************************)
(* Schorr-Waite code and proof *)
(*******************************)

Program Definition push (t p : node) :
  STsep {g0} (fun h => exists g,
    [/\ graph2 g h, inv g0 g t p & t \notin marked0 g],
    [vfun tp h => exists g, h \In graph2 g /\ inv g0 g tp.1 tp.2]) :=
  Do (tmp <-- read node t.+1;
      t.+1 ::= p;;
      t ::= L;;
      ret (tmp, t)).
Next Obligation.
move=>t p [/= g0][i][g][+ I M]; case: I=>a [Ep U + C I Rx N Ro].
rewrite (nodes0_cfiltC [::O] M)=>[[]|]///In_dom_umfilt [[[]]]//[tl tr] _ T.
move: (In_eta T) (In_valid T)=>/[dup] E -> V /graph2PtUn [_][h][->-> H].
do ![step]=>_; set g' := pts t (L, (p, tr)) \+ free g t; exists g'.
split=>[|{h H}]; first by rewrite graph2PtUn; eexists _, h.
have Ta : (t \in a) = false by rewrite -N; apply/negbTE/nodes0_cfiltSN/M.
have S : nodes (free g t)/LR =i a.
- by move=>z; rewrite dom_umfiltF N; case: eqP Ta=>// ->.
exists (rcons a t); rewrite /inv' 3!omfPtUn !(validX V) /= prevat_rcons
next_rcons eqxx Ta last_rcons; split=>//=.
- by rewrite !(uniqX U) -N eq_sym -negb_or -in_cons (nodes00_cfiltSN _ M).
- by rewrite -(domPtUnE2 t (O, (tl, tr))) -E (closed2_links T).
- rewrite (In_closed2PtUn (In_dom T) C) (closed2_links T C) andbT.
  by move/last_mem: Ep; rewrite -N; apply: omf_subdom0.
- by rewrite -Ep !omfF /= inset_rcons ?I.
- by rewrite -Rx {2}E mfPtUn restore_rcons.
- by move=>z; rewrite dom_omfPtUn inE (validX V) S mem_rcons.
move=>z; rewrite omfPtUn big_rcons rghPtUn (validX V) eqxx !omfF domF=>/andP
[/negbTE Nzt /Ro]; rewrite !inE mem_cat -orbA /= => /orPr [[Dz]|].
- rewrite !big_cat_mem_has=>/hasP [x X] Z; apply/or3P/Or31/hasP; exists x=>//.
  by rewrite (reach_avoid1 Dz) E !rghPtUn !(validX V) in Z *.
rewrite reachEA (nodes_cfilt _ T) Nzt=>/hasP [x /adj_cfiltS].
by rewrite (In_graph T) !inE=>/orP [] /eqP ->->; rewrite ?orbT.
Qed.

Program Definition swing (t p : node) :
  STsep {g0} (fun h => exists g,
    [/\ h \In graph2 g, inv g0 g t p, t \in marked0 g & (p, L) \In labels g],
    [vfun tp h => exists g, h \In graph2 g /\ inv g0 g tp.1 tp.2]) :=
  Do (tmp1 <-- read node p.+2;
      tmp2 <-- read node p.+1;
      p.+2 ::= tmp2;;
      p.+1 ::= t;;
      p ::= R;;
      ret (tmp1, p)).
Next Obligation.
move=>t p [/= g0][i][g][+ I M] /In_labelsX -[[pl pr]] P.
move: (In_eta P) (In_valid P)=>/[dup] E -> V /graph2PtUn [_][h][->-> H].
do ![step]=>_; set g' := (pts p (R, (t, pl)) \+ free g p); exists g'.
split=>[|{h H}]; first by rewrite graph2PtUn; eexists _, h.
case: I=>_ [/(rcons_lastN (In_cond P)) [a ->] U /= Dt C I Rx N Ro].
have Lp : lft g p = pl by rewrite E /lft findPtUn.
have Na : (p \in a) = false by rewrite (uniqX U).
have Npl : pl = last null a by rewrite -Lp -lft_erase -I
  lft_graphmap (In_findE P) /= prevat_rcons eqxx Na.
have S : nodes (free g p)/LR =i a.
- by move=>z; rewrite dom_umfiltF N mem_rcons inE; case: eqP Na=>//= ->->.
exists (rcons a p); rewrite /inv' last_rcons (uniqX U) 3!omfPtUn (validX V) /=
prevat_rcons next_rcons eqxx Na; split=>//=.
- by rewrite -(domPtUnE2 p (L, (pl, pr))) -E (closed2_links P).
- by rewrite (In_closed2PtUn (In_dom P) C) Dt (closed2_links P C).
- by rewrite !omfF /= I -Npl.
- by rewrite -Rx {2}E !mfPtUn /= next_rcons Na eqxx !restore_rcons.
- by move=>z; rewrite dom_omfPtUn inE (validX V) S mem_rcons.
move=>z; rewrite omfPtUn omfF (validX V) domF=>/andP [Nzp /Ro]; rewrite !inE
reachDN ?(nodes0_cfiltN _ M) ?orbF // !big_rcons !mem_cat {1 3 4}E omfPtUn
omfF rghPtUn ?(validX V) eqxx -orbA /= => /orP [Z|->]; last by rewrite ?orbT.
apply/or3P/Or31; congr (z \in _): Z; apply: eq_bigR=>w W _.
by rewrite rghPtUn (validX V) rghF; case: eqP W Na=>// ->->.
Qed.

Program Definition pop (t p : node) :
  STsep {g0} (fun h => exists g,
    [/\ h \In graph2 g, inv g0 g t p, t \in marked0 g & (p, R) \In labels g],
    [vfun tp h => exists g, h \In graph2 g /\ inv g0 g tp.1 tp.2]) :=
  Do (tmp <-- read node p.+2;
      p.+2 ::= t;;
      p ::= X;;
      ret (p, tmp)).
Next Obligation.
move=>t p [/= g0][i][g][+ I M] /In_labelsX [[pl pr] P].
move: (In_eta P) (In_valid P)=>/[dup] E -> V /graph2PtUn [_][h][->-> H].
do ![step]=>_; set g' := pts p (X, (pl, t)) \+ free g p; exists g'.
split=>[|{h H}]; first by rewrite graph2PtUn; eexists _, h.
case: I=>_ [/(rcons_lastN (In_cond P)) [a ->] U /= Dt C I Rx N Ro].
have Rp : rgh g p = pr by rewrite E /rgh findPtUn.
have Na : (p \in a) = false by rewrite (uniqX U).
have Npr : pr = last null a by rewrite -Rp -rgh_erase -I
 rgh_graphmap (In_findE P) /= prevat_rcons eqxx Na.
have Pr : pr \in nodes0 g/LR.
- by rewrite inE N mem_rcons inE orbCA orbC Npr last_mem.
have S : nodes (free g p)/LR =i a.
- by move=>z; rewrite dom_umfiltF N mem_rcons inE; case: eqP Na=>//->->.
exists a; rewrite /inv' (uniqX U) !omfPtUn nodes0PtUn ?(validX V) ?eqxx //=.
split=>//; first by rewrite (In_closed2PtUn (In_dom P) C) (closed2_links P C).
- by rewrite -(inset_rcons p S) !omfF /= I.
- by rewrite -Rx {2}E mfPtUn /= next_rcons Na eqxx -(restore_rcons p t).
rewrite omfF freeND ?reachDN ?(nodes_cfilt _ P) //= => z /Ro.
rewrite !inE big_rcons mem_cat !reachDN ?orbF ?(nodes0_cfiltN _ M) ?Rp
?(nodes0_cfiltN _ Pr) //=; congr (_ \in _); apply: eq_bigR=>w W _.
by rewrite rghPtUn (validX V) rghF; case: eqP W Na=>// ->->.
Qed.

Program Definition read_mark (t p : node) :
  STsep {g0} (fun h => exists g, h \In graph2 g /\ inv g0 g t p,
    [vfun tm h => exists g, [/\ h \In graph2 g, inv g0 g t p &
       tm = (t \in marked0 g)]]) :=
  Do (if t == null then ret true
      else v <-- read mark t;
           ret (v != O)).
Next Obligation.
move=>t p [g0][i][g][/[swap]]/[dup]-[a][_ _ + _ _ _ _ _]; rewrite inE /=.
case: eqP=>[-> *|/eqP N /In_domX [[v tx]] T I]; first by step; exists g.
move: (In_eta T)=>/[dup] E -> /graph2PtUn [_][h][->-> H]; do ![step]=>_.
exists g; split=>//; first by rewrite E graph2PtUn; eexists _, h.
by rewrite inE (negbTE N) (nodes_cfilt _ T); case: v {E T}.
Qed.

(* Precondition of loopTp is the loop invariant. *)
(* In the imperative code (in the paper), *)
(* the loop invariant also keeps tm = t \in marked0 g *)
(* but that's unnecessary in functional code. *)
Definition loopTp := forall tp, STsep {g0}
   (fun h => exists g, h \In graph2 g /\ inv g0 g tp.1 tp.2,
   [vfun (_ : unit) h => exists g, [/\ h \In graph2 g,
     erase g0 = erase g & g/X = g]]).

(* main program *)

(* specification for connected graphs *)
Program Definition schorr_waite_connect (r : node) :
  STsep {g0} (fun h => [/\ h \In graph2 g0, closed g0,
      r \in nodes g0 & nodes g0 =i reach g0/O r],
    [vfun _ h => exists g, [/\ h \In graph2 g,
      erase g0 = erase g & g/X = g]]) :=
  Do (let loop := ffix (fun (loop : loopTp) '(t, p) =>
        Do (tm <-- read_mark t p;
            if tm && (p == null) then ret tt
            else
              tp <-- if tm then
                       pm <-- read mark p;
                       if pm is R then pop t p : ST _
                       else swing t p
                     else push t p;
              loop tp))
      in loop (r, null)).
Next Obligation.
(* proof outline in the paper *)
move=>r loop _ t p [g0][i H]; apply: [stepE g0]=>//= tm {H}i [g][H I ->].
case: ifPn=>[/andP [T /eqP P]|X]; last first.
- apply: [bnd_vrf g0]=>//; case: ifPn X=>/= T P; last first.
  - by apply: [gE g0]=>//; exists g.
  by case: (I)=>a [/last_mem Ep ????? Na _]; move: Na Ep P H=><- /orP [->//|]
  /In_domX [[pm [pl pr]]] /In_umfiltX [X /[dup] P] /In_eta/[dup] E -> _
  /graph2PtUn [_][h][->-> H]; step; case: pm E X P=>//= E _ /In_labels P;
  apply: [gE g0]=>//; exists g; split=>//; rewrite E graph2PtUn; eexists _, h.
(* line 31 implies line 32 in the paper *)
step=>V; exists g; case: I P=>a [-> U _ _ _ <- ++] /last_nochange_nil P.
move/andX: U P=>->-> // Na S; split=>//; first by apply: ifmark_erase.
apply/id_cfiltD/domE/(nodes_cfiltCE [::O;L;R]); first by case.
rewrite cfilt_cons // (dom0E _ Na) ?pfVE ?(In_graph2V H V) // unitR => z.
by apply/negP=>/S; rewrite big_nil=>/reachD1/(nodes0_cfiltNX _ T); apply.
Qed.
Next Obligation.
(* line 1 implies line 2 in the paper *)
move=>r [g0][/= i][H C Rn E]; apply: [gE g0]=>//=; exists g0; split=>//.
have Na : nodes g0/LR =i [::] by move=>z; rewrite (nodes_cfiltX O) E;
  apply/andP=>-[/reachD2]; rewrite (nodes_cfiltX O) andbC; case: (odflt _).
exists [::]; rewrite /inv' inE Rn orbT; split=>//; try by apply: ifmark_erase.
by move=>z; rewrite (nodes_cfiltX O) E inE big_nil=>/andP [].
Qed.

(* framed specification for general graphs *)
Program Definition schorr_waite (r : node) :
  STsep {g0} (fun h =>
    [/\ h \In graph2 g0, closed g0, r \in nodes g0 & g0/O = g0],
    [vfun _ h => exists g, [/\ h \In graph2 g,
        erase g0 = erase g, g/X \+ g/O = g & nodes g/X =i reach g0 r]]) :=
  Do (schorr_waite_connect r).
Next Obligation.
move=>r [g0][i][]; set x := [in reach g0 r]; set g1 := kfilt g0 x.
set g2 := kfilt g0 [predC x]=>H C N Eg; apply: vrfV=>/(In_graph2V H) V /=.
rewrite (kfiltC g0 x) graph2Un in H C N; case: H=>h1 [h2][-> H1 H2].
case/(closed_reachUnX C): N=>[z|{}C N En]; first by rewrite nodes_reach -kfiltC.
apply: [gR g1] @ h1=>[|[u1][k1][U K Ek]|] //=; first by rewrite ckfilt Eg.
by move/(In_graph2V2 U H2)=>W; exists (k1 \+ g2); rewrite !omfUn //= Ek !ckfilt
-[in _/O]Ek -Eg !cfilt_predI !cfilt_nil ?(validX W) // pfunit Eg unitL unitR
-(nodes_erase k1) -K -mfUn dom_mf -kfiltC graph2Un; hhauto; apply: nodes_reach.
Qed.

