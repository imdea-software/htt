From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From pcm Require Import options axioms pred prelude seqperm.
From pcm Require Import pcm unionmap heap autopcm automap.
From htt Require Import options interlude model heapauto.
From htt Require Import graph.

Section Shape.

Definition node_shape p (n : seq ptr) (s : nodeset) :=
  [Pred h | h = p :-> get_nth n 0 \+ (p .+ 1 :-> (p \in dom s) \+ p .+ 2 :-> get_nth n 1)].

Lemma node_shapeK h1 h2 p n s :
  h1 \In node_shape p n s -> h2 \In node_shape p n s -> h1 = h2.
Proof. by move=>->->. Qed.

Definition shape (gr : pregraph) (m : nodeset) :=
  IterStar.sepit (assocs gr) (fun '(p,n) => node_shape p n m).

Lemma shapeK h1 h2 gr m :
  h1 \In shape gr m -> h2 \In shape gr m -> h1 = h2.
Proof.
rewrite /shape; elim/um_indf: gr h1 h2=>[||p n gr IH V P] h1 h2 /=.
- by rewrite assocs_undef; move/IterStar.sepit0=>->/IterStar.sepit0->.
- by rewrite assocs0; move/IterStar.sepit0=>->/IterStar.sepit0->.
rewrite assocsPtUn //; last by apply: path_all.
case/IterStar.sepit_cons=>h11[h12][{h1}-> H11 H12].
case/IterStar.sepit_cons=>h21[h22][{h2}-> H21 H22].
by rewrite (node_shapeK H11 H21) (IH _ _ H12 H22).
Qed.

Lemma shapeUn g1 g2 m :
  valid (g1 \+ g2) ->
  shape (g1 \+ g2) m =p shape g1 m # shape g2 m.
Proof.
move=>V h; rewrite /shape.
move: (assocs_perm V)=>H.
by rewrite (IterStar.sepit_perm _ H) IterStar.sepit_cat.
Qed.

Lemma shapePtUn (g : pregraph) p n m :
  valid (p &-> n \+ g) ->
  shape (pts p n \+ g) m =p node_shape p n m # shape g m.
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

Lemma shapeMPtUn g p m :
  valid m ->
  p \notin dom m ->
  p \notin dom g ->
  shape g (#p \+ m) =p shape g m.
Proof.
move=>Vm Hm Hg h; rewrite /shape; apply: IterStar.sepitF; case=>q ns /=.
move/In_assocs/In_find=>Hq z.
rewrite !InE /= domPtUn validPtUn /= inE /= Vm Hm /=.
suff: p != q by move/negbTE=>->.
apply/negP=>/eqP E; rewrite E in Hg.
by move/In_findNE: Hg; rewrite Hq.
Qed.

End Shape.

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

Definition ex : pregraph :=
  p1 &-> [::p2  ;p3]   \+
  p2 &-> [::p4  ;p5]   \+
  p3 &-> [::p6  ;p7]   \+
  p4 &-> [::null;null] \+
  p5 &-> [::p5  ;p8]   \+
  p6 &-> [::p1  ;p8]   \+
  p7 &-> [::null;null] \+
  p8 &-> [::p4  ;p7].

End ExampleCyclic.

Definition markT : Type := forall (p : ptr),
  {(gr : pregraph) (m_o : nodeset)},
  STsep (fun h => [/\ valid m_o, h \In shape gr m_o, good_graph gr, n_graph 2 gr & good_ptr gr p ],
        [vfun (_ : unit) h => exists m_s,
                  [/\ valid (m_s \+ m_o), h \In shape gr (m_s \+ m_o) & dom m_s =i connect m_o gr p]]).

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
move=>go p [gr][m_o][] i /= [Vmo Hi Hgg Hg2 Hp]; apply: vrfV=>V; case/orP: Hp.
- move=>/eqP->; rewrite eq_refl; step=>_.
  exists Unit; rewrite unitL; split=>//; rewrite dom0=>z; rewrite in_nil.
  by rewrite connect_notd {z}//; exact: no_null.
move/[dup]/dom_cond/[dup]=>Np /negbTE ->.
case/um_eta=>ns [Hp Egr].
case/andP: (Hgg)=>Vg Eg; rewrite Egr in Vg Hi.
case/(shapePtUn _ Vg): Hi=>i1[i2][->-> H2].
set l := get_nth ns 0.
set r := get_nth ns 1.
have /eqP Ens : ns == [::l; r].
- move/all_nth/allP: Hg2; apply.
  by apply/(mem_range (k:=p))/In_find.
have Hgl : good_ptr gr l by apply: (all_good_get (p:=p)).
have Hgr : good_ptr gr r by apply: (all_good_get (p:=p)).
step; case: ifP=>[Mp|/negbT Mp].
- step=>V1; exists Unit; rewrite unitL {1}Egr dom0; split=>//.
  - by rewrite (shapePtUn _ Vg) /node_shape Mp; vauto.
  by move=>z; rewrite in_nil connect_notp.
do 3!step; apply: [stepE gr, #p \+ m_o]=>//=.
- split=>//; first by rewrite validPtUn Mp /= andbT.
  rewrite Egr; apply/shapePtUn=>//.
  exists (p :-> l \+ (p.+ 1 :-> true \+ p.+ 2 :-> r)), i2; split=>//=.
  - by rewrite InE /= domPtUn /= inE validPtUn /= Vmo Mp eq_refl.
  by apply/shapeMPtUn=>//; rewrite domF inE eq_refl.
move=>_ m [m_l][Vml Sml Hml].
apply: [gE gr, m_l \+ (#p \+ m_o)]=>//=_ m' [m_r][Vmr Smr Hmr] V'.
exists (m_r \+ (m_l \+ (# p))); rewrite -!joinA; split=>//.
move=>z; rewrite domUn inE (validX Vmr) /= domUn inE (validX Vml) /= domPt inE /= Hml Hmr.
rewrite [RHS](connectMPtUnHas Vmo Mp Hp) eq_sym [RHS]orbC orbCA.
rewrite (connectMUnHas Vml Hp _ Hgl Hml) Ens /=; last by rewrite inE eq_refl.
rewrite eq_refl /=; case/boolP: (r == l)=>/=; rewrite orbF orbA //.
move/eqP=>->; case Hz: (z \in connect (m_l \+ (# p \+ m_o)) gr l)=>/=; last by rewrite orbF.
by rewrite !orbT /=; move/(connectMUnSub Vml): Hz=>->.
Qed.
