From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype fintype finset bigop.
From fcsl Require Import axioms pred.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import interlude stmod.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope stsep_scope.
Delimit Scope stsep_scope with stsep.
Open Scope stsep_scope.

Definition star (p1 p2 : Pred heap) : Pred heap :=
  [Pred h | exists h1 h2, h = h1 \+ h2 /\ h1 \In p1 /\ h2 \In p2].
Definition emp : Pred heap := eq^~ Unit.
Definition top : Pred heap := PredT.

Notation "p1 '#' p2" := (star p1 p2)
  (at level 57, right associativity) : rel_scope.

(*
Definition lolli (p : Pred heap) q (i m : heap) : Prop :=
  forall i1 h, i = i1 \+ h -> valid i -> p i1 ->
    exists m1, m = m1 \+ h /\ valid m /\ q i1 m1.

Notation "p '--o' q"   := (lolli p q) (at level 75) : stsep_scope.

Lemma antiframe p q i m h :
        valid (i \+ h) -> (p --o q) (i \+ h) (m \+ h) -> (p --o q) i m.
Proof.
move=>D1 H i2 m2 E D2 H1; rewrite {i}E in H D1 D2 *.
move: (H i2 (m2 \+ h)); rewrite joinA; case/(_ (erefl _) D1 H1)=>h2 [E][D3].
rewrite joinA in E; exists h2; rewrite (joinKx D3 E).
by rewrite E in D3; rewrite (validL D3).
Qed.

(* p --o q is local *)
Lemma locality p q i1 m h :
        valid (i1 \+ h) -> (p # top) i1 -> (p --o q) (i1 \+ h) m ->
          exists m1, m = m1 \+ h /\ valid m /\ (p --o q) i1 m1.
Proof.
move=>D [h1][h2][E][H1] _ H2; rewrite {i1}E in D H2 *.
move: (H2 h1 (h2 \+ h)); rewrite joinA; case/(_ (erefl _) D H1)=>m1 [E][D2].
rewrite {m}E joinA in H2 D2 *; exists (m1 \+ h2); do !split=>//.
by apply: antiframe D H2.
Qed.

Lemma fr_pre p i j : (p # top) i -> (p # top) (i \+ j).
Proof. by case=>i1 [i2][->][H] _; rewrite -joinA; exists i1, (i2 \+ j). Qed.
*)
Module Iter.
Section Iter.
Variable A : Type.

Definition bigjoin (s : seq heap) : heap := \big[PCM.join/Unit]_(i <- s) i.

Definition bigand {T : Type} (s : seq T) (f : T -> Prop) : Prop := \big[and/True]_(i <- s) (f i).

Lemma bigand_cat {T : Type} (s1 s2 : seq T) f : bigand (s1 ++ s2) f <-> bigand s1 f /\ bigand s2 f.
Proof.
rewrite /bigand big_cat_nested; elim: s1.
- by rewrite !big_nil; split=>// [[]].
move=>a l IH; rewrite !big_cons; split.
- by case=>?; move/IH=>[??].
by case=>[[??]?]; split=>//; rewrite IH.
Qed.

Definition sepit (s : seq A) (f : A -> Pred heap) : Pred heap :=
  [Pred h | exists hs : seq heap, size hs = size s
                               /\ h = bigjoin hs
                               /\ bigand (zip s hs) [pts a h | h \In f a] ].

Lemma sepit0 f : sepit [::] f =p emp.
Proof.
move=>h; split.
- by case=>/= hs [/size0nil -> []]; rewrite /bigjoin !big_nil.
by move=>->; exists [::]; rewrite /bigjoin /bigand !big_nil.
Qed.

Lemma sepit_cons x s f : sepit (x::s) f =p f x # sepit s f.
Proof.
move=>h; split.
- case=>/=; case=>[|h0 hs]; case=>//= /eqP; rewrite eqSS =>/eqP Hs.
  rewrite /bigjoin /bigand !big_cons /=; case=>->[H0 H1].
  by exists h0, (bigjoin hs); do!split=>//; exists hs.
case=>h1[h2][-> [H1 [hs [Hs [-> H]]]]].
by exists (h1 :: hs); rewrite /= Hs /bigjoin /bigand !big_cons.
Qed.

Lemma sepit_cat s1 s2 f : sepit (s1 ++ s2) f =p sepit s1 f # sepit s2 f.
Proof.
elim: s1 s2=>[|x s1 IH] s2 h /=; split.
- case=>hs [H1][-> H2].
  by exists Unit, (bigjoin hs); rewrite unitL; do!split=>//; [rewrite sepit0|exists hs].
- by case=>h1[h2][-> []]; rewrite sepit0=>->; rewrite unitL.
- case=>/=; case=>[|h0 hs]; case=>//= /eqP; rewrite eqSS=>/eqP Hs.
  rewrite /bigjoin /bigand !big_cons /=; case=>->[H0 HS].
  case: (IH s2 (bigjoin hs)).1; first by exists hs.
  move=>h1[h2][HJ [H1 H2]].
  exists (h0 \+ h1), h2. rewrite /bigjoin in HJ; rewrite HJ joinA; do!split=>//.
  by rewrite sepit_cons; exists h0, h1.
case=>h1[h2][->][[]]; case=>[|h0 hs1]; case=>//= /eqP; rewrite eqSS=>/eqP Hs1.
rewrite /bigjoin /bigand !big_cons /=; case=>{h1}->[H0 H1]; case=>hs2[Hs2][-> H2].
exists (h0 :: hs1 ++ hs2); rewrite /bigjoin /bigand big_cons big_cat joinA; do!split=>//=.
- by rewrite !size_cat Hs1 Hs2.
rewrite big_cons zip_cat //=; split=>//.
by apply/bigand_cat.
Qed.

End Iter.

Section IterEq.
Variable A : eqType.

Lemma sepitP (x : A) (s : seq A) f : uniq s ->
       sepit s f =p if x \in s then f x # sepit (filter (predC1 x) s) f
                    else sepit s f.
Proof.
case E: (x \in s)=>//.
elim: s E=>[|y s IH] //= /[swap]; case/andP=>Hy Hu; rewrite inE=>/orP.
case; [move/eqP=>->; rewrite eq_refl /=|move=>Hx]; rewrite sepit_cons=>h0.
- by split; case=>h1[h2][->][? H]; exists h1, h2; do!split=>//;
  [rewrite filter_predC1 | rewrite filter_predC1 in H].
have ->: (y != x) by apply/eqP=>Hxy; rewrite Hxy Hx in Hy.
by split; case=>ha[?][->][?]; [rewrite (IH Hx Hu) | rewrite sepit_cons];
case=>hb[h][->][??]; rewrite joinCA;
exists hb, (ha \+ h); do!split=>//;
[rewrite sepit_cons | rewrite (IH Hx Hu)]; exists ha, h.
Qed.

Lemma eq_sepitF (s : seq A) (f1 f2 : A -> Pred heap) :
        (forall x, x \in s -> f1 x =p f2 x) -> sepit s f1 =p sepit s f2.
Proof.
elim: s=>[|x s IH] H h; first by rewrite !sepit0.
have H': forall x : A, x \in s -> f1 x =p f2 x
  by move=>? H0; apply: H; rewrite !inE H0 orbT.
have Hx : x \in x :: s by rewrite inE eq_refl.
by rewrite !sepit_cons; split; case=>h1[h2][->][H1 H2]; exists h1, h2;
split=>//; [rewrite -IH // -H | rewrite IH // H].
Qed.

Lemma perm_sepit (s1 s2 : seq A) f :
        perm_eq s1 s2 -> sepit s1 f =p sepit s2 f.
Proof.
elim: s1 s2 =>[|x s1 IH] s2 /=.
- by move/perm_size; move/eqP; rewrite eq_sym; move/eqP; move/size0nil=>->.
move=>H.
have L1: has (pred1 x) s2.
- rewrite has_count; case: permP H=>//; move/(_ (pred1 x))=><-.
  by rewrite /= eq_refl.
have L2: x \in s2.
- by case: hasP L1=>//= [[y]] H1; move/eqP=><-.
move: (mem_split L2)=>[t1][t2] E.
rewrite E in H *.
have L3: perm_eq (x::s1) ([:: x] ++ t1 ++ t2).
- apply: (perm_trans H).
  by rewrite perm_catCA.
rewrite /= perm_cons in L3.
rewrite sepit_cons sepit_cat /=.
move=>h0; split.
- case=>h1[h2][->][H1]; rewrite (IH _ L3).
  rewrite sepit_cat; case=>h3[h4][->][[hs3 [?][->?]][hs4 [?][->?]]]; rewrite joinCA.
  exists (bigjoin hs3), (h1 \+ bigjoin hs4); do!split=>//.
  - by exists hs3.
  by rewrite sepit_cons; exists h1, (bigjoin hs4); do!split=>//; exists hs4.
case=>h1[h2][->][[hs1][Hs1][-> H1]]; rewrite sepit_cons.
case=>h3[h4][->][H3][hs2][Hs2][-> H2]; rewrite joinCA.
exists h3, (bigjoin hs1 \+ bigjoin hs2); do!split=>//.
rewrite (IH _ L3); exists (hs1 ++ hs2); do!split.
- by rewrite !size_cat Hs1 Hs2.
- by rewrite /bigjoin big_cat.
rewrite /bigand zip_cat //.
by apply/bigand_cat.
Qed.

End IterEq.

End Iter.

Module FinIter.
Section FinIter.
Variable I : finType.

Definition seq_of (s : {set I}) := [seq x <- enum I | x \in s].

Lemma mem_seq_of (s : {set I}) x : (x \in seq_of s) = (x \in s).
Proof. by rewrite /seq_of mem_filter mem_enum andbT. Qed.

Lemma setq (s1 s2 : {set I}) : s1 = s2 <-> seq_of s1 =i seq_of s2.
Proof.
split=>[->|H] //; rewrite -setP=>x; move: (H x).
by rewrite /seq_of !mem_filter -enumT mem_enum !andbT /in_mem.
Qed.

Lemma uniq_seq_of (s : {set I}) : uniq (seq_of s).
Proof. by rewrite /seq_of filter_uniq // enum_uniq. Qed.

Lemma perm_seqP (s1 s2 : {set I}) :
       reflect (seq_of s1 =i seq_of s2)
               (perm_eq (seq_of s1) (seq_of s2)).
Proof.
case E: (perm_eq _ _); constructor.
- by apply: perm_mem.
by move=>H; elim: (elimF idP E); apply: uniq_perm H; rewrite uniq_seq_of.
Qed.

Definition sepit (s : {set I}) (Ps : I -> Pred heap) :=
  Iter.sepit (seq_of s) Ps.

Lemma sepit0 f : sepit set0 f =p emp.
Proof.
rewrite /sepit /seq_of.
rewrite (Iter.perm_sepit (s2 := filter pred0 (enum I))); first by rewrite filter_pred0 Iter.sepit0.
apply: uniq_perm; try by rewrite filter_uniq // enum_uniq.
by move=>x; rewrite !mem_filter /= in_set0.
Qed.

Lemma sepitF (s : {set I}) f1 f2 :
        (forall x, x \in s -> f1 x =p f2 x) -> sepit s f1 =p sepit s f2.
Proof.
move=>H; apply: Iter.eq_sepitF=>x H1; apply: H.
by rewrite -mem_seq_of.
Qed.

Lemma eq_sepit (s1 s2 : {set I}) f : s1 =i s2 -> sepit s1 f =p sepit s2 f.
Proof.
rewrite setP setq.
suff: perm_eq (seq_of s1) (seq_of s2) -> sepit s1 f =p sepit s2 f.
- by move=>H H2; apply: H; case: perm_seqP.
by apply: Iter.perm_sepit.
Qed.

Lemma sepitS x (s : {set I}) f :
        sepit s f =p if x \in s then f x # sepit (s :\ x) f
                     else sepit s f.
Proof.
case E: (x \in s)=>//.
rewrite (Iter.sepitP x (s:=seq_of s) f (uniq_seq_of s)) mem_seq_of E.
have Hp: perm_eq [seq y <- seq_of s | predC1 x y] (seq_of (s :\ x)).
- rewrite /seq_of -filter_predI.
  apply: uniq_perm=>[||y]; try by rewrite filter_uniq // enum_uniq.
  by rewrite !mem_filter /= in_setD1.
by move=>h0; split; case=>h1[h2][->][? H]; exists h1, h2; do!split=>//;
rewrite Iter.perm_sepit; try by [exact: H]; [rewrite perm_sym |].
Qed.

Lemma sepitT1 x f : sepit setT f =p f x # sepit (setT :\ x) f.
Proof. by rewrite (sepitS x) in_setT. Qed.

End FinIter.
End FinIter.
(*
(********************)
(* Separation monad *)
(********************)

Definition fr G A (s : spec G A) : spec (G*heap) A :=
  fun '(g,h) => ((s g).1 # eq h, fun x => (s g).2 x # eq h).


Definition fr A (s : spec A) : spec A :=
  (s.1 # top, fun x => s.1 --o s.2 x).

Prenex Implicits fr.

Notation "[ s ]" := (fr s).

Definition STbin A (s : spec A) := STspec [s].

(* hide the spec *)
Inductive ST A := with_spec (s : spec A) of STbin s.

Definition spec_of A (e : ST A) := let: with_spec s _ := e in s.
Definition pre_of A := [fun e : ST A => (spec_of e).1].
Definition post_of A := [fun e : ST A => (spec_of e).2].
Definition code_of A (e : ST A) :=
  let: with_spec _ c := e return STbin (spec_of e) in c.

Arguments pre_of {A}.
Arguments post_of {A}.
Arguments with_spec [A].
Prenex Implicits pre_of post_of.

Coercion with_spec : STbin >-> ST.

Section SepReturn.
Variable (A : Type) (x : A).

Definition ret_s : spec A := (emp, fun y i m => m = i /\ y = Val x).

Lemma retP : Model.conseq (Model.ret_s x) [ret_s].
Proof.
move=>i /= H1 D1; split=>// y m [->] -> _ i1 i2 -> D ->.
by exists Unit; rewrite unitL (validR D).
Qed.

Definition ret := with_spec _ (Model.Do (Model.ret x) retP).

End SepReturn.


Section SepBind.
Variables (A B : Type) (e1 : ST A) (e2 : A -> ST B).
Notation s1 := (spec_of e1).
Notation s2 := (fun x => spec_of (e2 x)).

Definition bind_s : spec B :=
  (Model.bind_pre [s1] (fr \o s2), Model.bind_post [s1] (fr \o s2)).

Lemma bindP : Model.conseq (Model.bind_s [s1] (fr \o s2)) [bind_s].
Proof.
move=>i H D; split=>[|{H D}].
- case: H D=>i1 [i2][->][[H S]] _ D.
  split=>[|y m]; first by apply: fr_pre.
  by case/(locality D H)=>m1 [->][_]; move/S; apply: fr_pre.
move=>y m H _ i1 i2 E D1 [H1 S1]; rewrite {i}E in H D1 *.
case: H=>[[x][h][]|[e][->]]; case/(locality D1 H1)=>h1 [->][D2] T2.
- move/S1: (T2)=>H2; case/(locality D2 H2)=>m1 [->][D3] T3.
  by exists m1; do !split=>//; left; exists x; exists h1.
by exists h1; do !split=>//; right; exists e.
Qed.

Definition bind :=
  with_spec _ (Model.Do (Model.bind (code_of e1) (fun x => code_of (e2 x))) bindP).

End SepBind.


Definition verify'' A (s : spec A) i (r : ans A -> heap -> Prop) :=
  valid i -> s.1 i /\ forall y m, s.2 y i m -> valid m -> r y m.

Definition verify' A (e : ST A) i r := verify'' [spec_of e] i r.

Notation verify i e r := (@verify' _ e i r).

Section SepFrame.
Variables (A : Type) (e : ST A).

Lemma frame i j (r : ans A -> heap -> Prop) :
        verify i e (fun y m => valid (m \+ j) -> r y (m \+ j)) ->
        verify (i \+ j) e r.
Proof.
move=>H D; case: (H (validL D))=>H1 H2.
split=>[|y m]; first by apply: fr_pre.
case/(locality D H1)=>m1 [->][D1]; move/H2.
by apply; apply: validL D1.
Qed.

Lemma frame_star i (r : ans A -> heap -> Prop) (q : Pred heap) :
  i \In (fun h => verify h e r) # q -> verify i e (fun v => r v # q).
Proof.
case=>h1[h2][->][H1 H2].
apply: frame=>/H1 [Hp Hr].
split=>// y m Hq Vm _.
exists m, h2; do!split=>//.
by apply: Hr.
Qed.

Lemma frame0 i r : verify'' (spec_of e) i r -> verify i e r.
Proof.
move=>H D; case: (H D)=>H1 H2.
split=>[|y m]; first by exists i, Unit; rewrite unitR.
move/(_ i Unit); rewrite unitR; case/(_ (erefl _) D H1)=>m1.
by rewrite unitR=>[[<-]][_]; apply: H2.
Qed.

Lemma frame1 i (r : ans A -> heap -> Prop) :
        verify'' (spec_of e) Unit (fun y m => valid (m \+ i) -> r y (m \+ i)) ->
        verify i e r.
Proof. by move=>H; rewrite -[i]unitL; apply: frame; apply: frame0. Qed.

End SepFrame.

Definition conseq A (e : ST A) (s : spec A) :=
  forall i, s.1 i -> verify i e (fun y m => s.2 y i m).

(*
Local Notation conseq1 e s :=
  (conseq e (let 'pair x _ := s in x)
            (let 'pair _ x := s in x)).
*)

Lemma conseq_refl A (e : ST A) : conseq e (spec_of e).
Proof. by case: e=>s e i H; apply: frame0. Qed.

#[export]
Hint Resolve conseq_refl : core.

Section SepConseq.
Variables (A : Type) (s2 : spec A) (e : ST A) (pf : conseq e s2).

Lemma doP : Model.conseq [spec_of e] [s2].
Proof.
move=>i H D; split=>[|y m {H D} /=].
- case: H D=>i1 [i2][->][H] _ D.
  by case: (@pf i1 H (validL D))=>H1 _; apply: fr_pre.
move=>S D i1 i2 E D2 H2; rewrite {i}E in D S D2 H2.
case: (@pf i1 H2 (validL D2))=>H1 T1.
case: (locality D2 H1 S)=>m1 [->][D3] {S}.
by move/T1; move/(_ (validL D3))=>T2; exists m1.
Qed.

Definition do' : STbin s2 := Model.Do (code_of e) doP.

End SepConseq.

Notation "'Do' e" := (@do' _ _ e _) (at level 80).

Section SepRead.
Variables (A : Type) (x : ptr).

Definition read_s : spec A :=
  (fun i => exists v : A, i = x :-> v,
   fun y i m => i = m /\ forall v, i = x :-> v -> y = Val v).

Lemma readP : Model.conseq (Model.read_s A x) [read_s].
Proof.
move=>i H D; split=>[|{H D} y _ [->] H _ i1 h E1 D E2].
- case: H D=>i1 [i2][->][[v]] -> _ D /=.
  rewrite domPtUn inE /= D eq_refl; split=>//.
  by exists v; rewrite findPtUn.
move: E1 E2 H D=>-> [v ->] H D; exists (x :-> v); do 3!split=>//.
move=>w /(hcancelPtV (validL D)) <-; apply: H.
by rewrite findPtUn.
Qed.

Definition read := with_spec _ (Model.Do (Model.read A x) readP).

End SepRead.


Section SepWrite.
Variables (A : Type) (x : ptr) (v : A).

Definition write_s : spec unit :=
  (fun i => exists B : Type, exists y : B, i = x :-> y,
   fun y i m => y = Val tt /\ m = x :-> v).

Lemma writeP : Model.conseq (Model.write_s x v) [write_s].
Proof.
move=>i H D; split=>[|{H D} y m [->] <- D1 i1 h E1 D2 [B][w] E2].
- case: H D=>i1 [i2][->][[B]][y] -> _ D /=.
  by rewrite domPtUn inE /= D eq_refl.
move: E1 E2 D1 D2=>->->-> D; exists (x :-> v).
rewrite updUnL domPt inE /= eq_refl.
case: ifP => //=.
- move/andP => [Hx Ht].
  split => //.
  rewrite updU.
  case: ifP => //=.
  by move/eqP => Hx'.
- move/andP => Hx.
  case: Hx; split => //.
  rewrite validPtUn in D.
  move/and3P: D.
  by case.
Qed.

Definition write := with_spec _ (Model.Do (Model.write x v) writeP).

End SepWrite.


Section SepAlloc.
Variables (A : Type) (v : A).

Definition alloc_s : spec ptr :=
  (emp, fun y i m => exists x, y = Val x /\ m = x :-> v).

Lemma allocP : Model.conseq (Model.alloc_s v) [alloc_s].
Proof.
move=>i H D; split=>[|{H D} y m [x][H1][->][H2] <- D1 i1 h E1 D E2].
- by case: H D=>i1 [i2][->][->].
move: E1 E2 H2 D D1=>-> ->; rewrite {1 2}unitL=>H2 D D1.
exists (x :-> v); rewrite updUnR (negbTE H2).
rewrite validPtUn.
split => //=.
split => //; last by exists x.
apply/andP; split => //=.
by apply/andP.
Qed.

Definition alloc := with_spec _ (Model.Do (Model.alloc v) allocP).

End SepAlloc.


Section SepBlockAlloc.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_s : spec ptr :=
  (emp, fun y i m => exists x:ptr, y = Val x /\ m = updi x (nseq n v)).

Lemma allocbP : Model.conseq (Model.allocb_s v n) [allocb_s].
Proof.
move=>i H D; split=>[|y m].
- by case: H D=>i1 [i2][->][->][]; rewrite joinC.
case=>x [->] -> D1 i1 h E1 D2 E2.
move: E1 E2 D1 D2=>->->; rewrite unitL {2}joinC=>D1 D2.
by exists (updi x (nseq n v)); do !split=>//; exists x.
Qed.

Definition allocb := with_spec _ (Model.Do (Model.allocb v n) allocbP).

End SepBlockAlloc.


Section SepDealloc.
Variable x : ptr.

Definition dealloc_s : spec unit :=
  (fun i => exists A : Type, exists v:A, i = x :-> v,
   fun y i m => y = Val tt /\ m = Unit).

Lemma deallocP : Model.conseq (Model.dealloc_s x) [dealloc_s].
Proof.
move=>i H D; split=>[|{H D} y m [->] <- D1 i1 h E1 D2 [A][v] E2].
- case: H D=>i1 [i2][->][[A]][v] -> _ D /=.
  by rewrite domPtUn inE /= D eq_refl.
move: E1 E2 D1 D2=>->->->; rewrite validPtUn; case/and3P=>H1 _ H2.
by exists Unit; rewrite freeUnR // freeU eq_refl H1 free0.
Qed.

Definition dealloc := with_spec _ (Model.Do (Model.dealloc x) deallocP).

End SepDealloc.


Section SepThrow.
Variables (A : Type) (e : exn).

Definition throw_s : spec A :=
  (emp, fun y i m => m = i /\ y = Exn e).

Lemma throwP : Model.conseq (Model.throw_s A e) [throw_s].
Proof.
move=>i H D; split=>{H D} // y m [->] -> _ i1 h -> D ->.
by exists Unit; rewrite unitL; do !split=>//; apply: validR D.
Qed.

Definition throw := with_spec _ (Model.Do (Model.throw A e) throwP).

End SepThrow.


Section SepTry.
Variables (A B : Type) (e : ST A) (e1 : A -> ST B) (e2 : exn -> ST B).
Notation s := (spec_of e).
Notation s1 := (fun x => spec_of (e1 x)).
Notation s2 := (fun x => spec_of (e2 x)).

Definition try_s : spec B :=
  (Model.try_pre [s] (fr \o s1) (fr \o s2),
   Model.try_post [s] (fr \o s1) (fr \o s2)).

Lemma tryP : Model.conseq (Model.try_s [s] (fr \o s1) (fr \o s2)) [try_s].
Proof.
move=>i H D; split=>[|{H D} y m H1 D1 i1 h E1 D2 /= [H2][H3] H4].
- case: H D=>i1 [i2][->][[H [S1 S2]]] _ D.
  split; first by apply: fr_pre.
  split=>y m; case/(locality D H)=>m1 [->][_]; [move/S1 | move/S2];
  by apply: fr_pre.
rewrite {i}E1 /= in H1 D2.
case: H1=>[[x]|[x]][h1][];
case/(locality D2 H2)=>m1 [->][D3] T1; move: (T1);
[move/H3 | move/H4]=>T'; case/(locality D3 T')=>m2 [->][D4] T2;
exists m2; do 2!split=>//; [left | right];
by exists x, m1.
Qed.

Definition ttry :=
  with_spec _ (Model.Do (Model.try (code_of e)
                                   (fun x => code_of (e1 x))
                                   (fun x => code_of (e2 x))) tryP).

End SepTry.

Section SepFix.
Variables (A : Type) (B : A -> Type) (s : forall x, spec (B x)).
Notation tp := (forall x, STbin (s x)).

Definition Fix (f : tp -> tp) : tp := Model.ffix f.

End SepFix.
*)
(****************************************************)
(* Notation to move from binary posts to unary ones *)
(****************************************************)

Notation "'Do' e" := (@STprog _ _ _ e _) (at level 80).

Definition bind A B (e1 : ST A) (e2 : A -> ST B) := Model.bind_st e1 e2.

Definition logbase A (p : pre) (q : post A) : spec unit A :=
  fun => (p, q).

Definition logvar {B A} (G : A -> Type) (s : forall x : A, spec (G x) B) :
  spec {x : A & G x} B :=
  fun '(existT x g) => s x g.

Notation "'STsep' ( p , q ) " := (STspec (logbase p q)) (at level 0).

Notation "{ x .. y }, 'STsep' ( p , q ) " :=
  (STspec (logvar (fun x => .. (logvar (fun y => logbase p q)) .. )))
   (at level 0, x binder, y binder, right associativity).

Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2))
  (at level 78, right associativity) : stsep_scope.
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2))
  (at level 78, right associativity) : stsep_scope.
Notation "'!' x" := (Model.read_st _ x) (at level 50) : stsep_scope.
Notation "e1 '::=' e2" := (Model.write_st e1 e2) (at level 60) : stsep_scope.
