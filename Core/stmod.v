From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From fcsl Require Import axioms pred prelude.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Exceptions are an equality type *)
Inductive exn : Type := exn_from_nat of nat.

Definition exn_to_nat :=
  fun '(exn_from_nat y) => y.

Definition eqexn :=
  fun '(exn_from_nat m) '(exn_from_nat n) => m == n.

Lemma eqexnP : Equality.axiom eqexn.
Proof.
by move=>[x][y]/=; case: eqP=>[->|*]; constructor=>//; case.
Qed.

Canonical Structure exn_eqMixin := EqMixin eqexnP.
Canonical Structure exn_eqType := EqType exn exn_eqMixin.

(* Answer type *)
Inductive ans (A : Type) : Type := Val of A | Exn of exn.
Arguments Exn [A].

Notation pre := (Pred heap).
Notation post A := (ans A -> heap -> heap -> Prop).
Definition spec G B := G -> pre * post B : Type.

(********************************)
(* Definition of the Hoare type *)
(********************************)

Definition defed (P : Pred heap) : Pred heap :=
  fun i => i \In P /\ valid i.

Lemma defed_leq h1 h2 : h1 <== h2 -> defed h1 <== defed h2.
Proof. by move=>H1 i [H2 V]; split=>//; apply: H1 H2. Qed.

Notation ideald P := (ideal (defed P)).

Definition relaxd P1 P2 (p : ideald P2) (pf : P2 <== P1) : ideald P1 :=
  relax p (defed_leq pf).

Section BasePrograms.
Variables (A : Type) (P : Pred heap).

Lemma singleP i : i \In defed P -> eq i <== defed P.
Proof. by case=>pf1 pf2 h <-. Qed.

Definition single i (pf : i \In defed P) := Ideal (singleP pf).

Lemma bound (p : ideald P) i : i \In id_val p -> i \In defed P.
Proof. by case: p=>p H; case/H. Qed.

(* we carve out the model out of the following base type *)
Definition prog := ideald P -> ans A -> Pred heap.

(* we take progs with only special properties *)
(* which we defined next *)

(* coherence is continuity stated with *)
(* directed sets instead of chains *)
Definition coherent (e : prog) :=
  forall p x m,
    m \In e p x <-> exists i (pf : i \In id_val p),
                    m \In e (single (bound pf)) x.

(* defined heaps map to defined heaps *)
Definition def_strict (e : prog) := forall p x, Heap.Undef \Notin e p x.

(* set of program runs *)
Definition runs_of (e : prog) : Pred (heap * ans A * heap) :=
  fun '(i,y,m) => exists pf : i \In defed P, m \In e (single pf) y.

End BasePrograms.

Section STDef.
Variable (A : Type).

Structure ST := Prog {
  pre_of : pre;
  prog_of : prog A pre_of;
  _ : coherent prog_of;
  _ : def_strict prog_of}.

Arguments prog_of : clear implicits.

Lemma coh_st e : coherent (prog_of e).
Proof. by case: e. Qed.

Arguments coh_st : clear implicits.

Definition has_spec G (s : spec G A) (c : ST) :=
  forall g i, (s g).1 i ->
    pre_of c i /\
    forall y m, (i, y, m) \In runs_of (prog_of c) -> (s g).2 y i m.

(* poset structure on ST *)

Definition st_leq e1 e2 :=
  exists pf : pre_of e2 <== pre_of e1,
  forall (p : ideald (pre_of e2)) y m,
     id_val p <== pre_of e2 ->
     prog_of e1 (relaxd p pf) y m -> prog_of e2 p y m.

Lemma st_refl e : st_leq e e.
Proof.
have Cx := coh_st e.
exists (poset_refl _)=>p y m _.
case/Cx=>x [pf H2]; apply/Cx; exists x.
have J : x \In id_val p by exact: pf.
exists J.
by rewrite (_ : bound J = bound pf) //; apply: pf_irr.
Qed.

Lemma st_asym e1 e2 : st_leq e1 e2 -> st_leq e2 e1 -> e1 = e2.
Proof.
case: e1 e2=>p1 e1 C1 D1 [p2 e2 C2 D2]; rewrite /st_leq /=.
case=>E1 R1 [E2 R2].
move: (poset_asym E1 E2)=>?; subst p2.
have : e1 = e2.
- apply: fext=>p; apply: fext=>y; apply: fext=>m.
  have I : id_val p <== p1.
  - by move=>i; case: p=>p pf /=; move: (pf i)=>X /X; case.
  move/R2: (I)=>/(_ y m) R2'.
  move/R1: (I)=>/(_ y m) R1'.
  apply: pext; split.
  - move=>H1; apply: R1'.
    case/C1: H1=>i [pf1] H1; apply/C1; exists i.
    have J : i \In id_val (relaxd p E1) by exact: pf1.
    exists J.
    by rewrite (_ : bound J = bound pf1) //; apply: pf_irr.
  move=>H2; apply: R2'.
  case/C2: H2=>i [pf1] H2; apply/C2; exists i.
  have J : i \In id_val (relaxd p E2) by exact: pf1.
  exists J.
  by rewrite (_ : bound J = bound pf1) //; apply: pf_irr.
move=>?; subst e2.
by congr Prog; apply: pf_irr.
Qed.

Lemma st_trans e1 e2 e3 : st_leq e1 e2 -> st_leq e2 e3 -> st_leq e1 e3.
Proof.
move: e1 e2 e3=>[p1 e1 C1 D1][p2 e2 C2 D2][p3 e3 C3 D3].
case=>/= E1 R1 [/= E2 R2]; rewrite /st_leq /=.
have E3 := poset_trans E2 E1; exists E3=>p y m H.
set p' := relaxd p E2.
move: (R1 p' y m (poset_trans H E2))=>{}R1.
move: (R2 p y m H)=>{}R2.
move=>H1; apply/R2/R1.
case/C1: H1=>i [pf] Hm; apply/C1; exists i.
have J : i \In id_val (relaxd p' E1) by exact: pf.
exists J.
by rewrite (_ : bound J = bound pf) //; apply: pf_irr.
Qed.

Lemma coherent_bot : @coherent A (fun => True) (fun _ _ _ => False).
Proof. by move=>p y m; split=>//; case=>i []. Qed.

Lemma dstrict_bot : @def_strict A (fun => True) (fun _ _ _ => False).
Proof. by move=>*. Qed.

Definition st_bot := Prog coherent_bot dstrict_bot.

Lemma st_botP e : st_leq st_bot e.
Proof. by case: e=>p e C D; rewrite /st_leq /=. Qed.

Definition stPosetMixin := PosetMixin st_botP st_refl st_asym st_trans.
Canonical stPoset := Eval hnf in Poset ST stPosetMixin.

(* lattice structure on ST *)

(* intersection of preconditions *)
Definition pre_sup (u : Pred ST) h :=
  forall e, e \In u -> h \In pre_of e.

Definition pre_sup_leq u e (pf : e \In u) :
  pre_sup u <== pre_of e :=
  fun h (pf1 : pre_sup u h) => pf1 e pf.

(* union of postconditions *)
Definition prog_sup (u : Pred ST) :=
  fun p y m => exists e (pf1 : e \In u),
    prog_of e (relaxd p (pre_sup_leq pf1)) y m.

Arguments prog_sup : clear implicits.

Lemma prog_sup_coh u : coherent (prog_sup u).
Proof.
move=>p y m; split.
- case=>e [H1 H2]; have Cx := coh_st e.
  case/Cx: H2=>i [pf1] M; exists i.
  have I : i \In id_val p by exact: pf1.
  exists I; rewrite -toPredE /=; exists e, H1.
  apply/Cx; exists i.
  set y' := id_val _; have J2 : i \In y' by [].
  exists J2.
  by rewrite (_ : bound J2 = bound pf1) //; apply: pf_irr.
case=>i[pf][e][H1 H2]; rewrite -toPredE /=.
exists e, H1; have Cx := coh_st e.
case/Cx: H2=>i0 [pf0] M0; apply/Cx; exists i0.
have J2 : i0 \In id_val (relaxd p (pre_sup_leq H1)).
- by move: pf0 {M0}=><-.
exists J2.
by rewrite (_ : bound J2 = bound pf0) //; apply: pf_irr.
Qed.

Lemma prog_sup_dstrict u : def_strict (prog_sup u).
Proof.
move=>p y; rewrite -toPredE /=.
case; case=>e_pre e_prog Cx Df [H1].
by move/Df.
Qed.

Definition st_sup u :=
  Prog (@prog_sup_coh u) (@prog_sup_dstrict u).

Lemma st_supP u e : e \In u -> e <== st_sup u.
Proof.
case: e=>p e' C D R.
exists (pre_sup_leq R)=>/=p0 y m H H2; exists (Prog C D), R.
case/C: H2=>i[pf e]; apply/C; exists i.
have J2 : i \In id_val (relaxd p0 (pre_sup_leq R)).
- by exact: pf.
exists J2.
by rewrite (_ : bound J2 = bound pf) //; apply: pf_irr.
Qed.

Lemma st_supM u e :
  (forall e1, e1 \In u -> e1 <== e) -> st_sup u <== e.
Proof.
case: e=>p e' C D R.
have J : p <== pre_sup u.
- by move=>/= x Px e He; case: (R e He)=>/= + _; apply.
exists J=>p0 y m H [e0][pf1 H1].
case: (R e0 pf1)=>/= Hx; apply=>//.
have Cx := coh_st e0.
case/Cx: H1=>i [pf e]; apply/Cx; exists i.
have J2 : i \In id_val (relaxd p0 Hx) by exact: pf.
exists J2.
by rewrite (_ : bound J2 = bound pf) //; apply: pf_irr.
Qed.

Definition stLatticeMixin := LatticeMixin st_supP st_supM.
Canonical stLattice := Lattice ST stLatticeMixin.

End STDef.

Arguments prog_of [A].
Arguments coh_st [A].

Section STspecDef.
Variables (G A : Type) (s : spec G A).

Structure STspec := STprog {
  model : ST A;
  _ : model \In has_spec s}.

Lemma modelE e1 e2 : e1 = e2 <-> model e1 = model e2.
Proof.
move: e1 e2=>[e1 H1][e2 H2] /=; split=>[[//]|E].
by subst e2; congr STprog; apply: pf_irr.
Qed.

(* poset structure on STspec *)

Definition stsp_leq e1 e2 := model e1 <== model e2.

Lemma stsp_refl e : stsp_leq e e.
Proof. by case: e=>e He; apply: poset_refl. Qed.

Lemma stsp_asym e1 e2 : stsp_leq e1 e2 -> stsp_leq e2 e1 -> e1 = e2.
Proof.
move: e1 e2=>[e1 H1][e2 H2]; rewrite /stsp_leq /= =>E1 E2.
have E := poset_asym E1 E2.
by subst e2; congr STprog; apply: pf_irr.
Qed.

Lemma stsp_trans e1 e2 e3 : stsp_leq e1 e2 -> stsp_leq e2 e3 -> stsp_leq e1 e3.
Proof.
move: e1 e2 e3=>[e1 H1][e2 H2][e3 H3].
by apply: poset_trans.
Qed.

Lemma st_bot_has_spec : @st_bot A \In has_spec s.
Proof. by move=>g i H; split=>// y m; case. Qed.

Definition stsp_bot := STprog st_bot_has_spec.

Lemma stsp_botP e : stsp_leq stsp_bot e.
Proof. by case: e=>*; apply: botP. Qed.

Definition stspPosetMixin := PosetMixin stsp_botP stsp_refl stsp_asym stsp_trans.
Canonical stspPoset := Eval hnf in Poset STspec stspPosetMixin.

(* lattice structure on STspec *)

Definition st_sup' (u : Pred STspec) : ST A :=
  sup [Pred p | exists e, p = model e /\ e \In u].

Lemma st_sup_has_spec' u : st_sup' u \In has_spec s.
Proof.
move=>g m p; split=>/=.
- by move=>e; rewrite -!toPredE /= => [[[e' S'][/= -> _]]]; case: (S' g m p).
move=>y m0; case=>/= Hd; rewrite -!toPredE /= => [[e][pf H]].
have Cx := coh_st e.
case: pf H=>[[e' S'][/= He HS]] H2; subst e'.
case: (S' g m p)=>_; apply; rewrite -toPredE /=.
have J : m \In defed (pre_of e).
- case: {H2}Hd =>Hp Hv; split=>//.
  by apply: Hp; exists (STprog S').
exists J.
case/Cx: H2=>i[ph e2]; apply/Cx; exists i.
have J2 : i \In id_val (single J) by exact: ph.
exists J2.
by rewrite (_: bound J2 = bound ph) //; apply: pf_irr.
Qed.

Definition stsp_sup u := STprog (@st_sup_has_spec' u).

Lemma stsp_supP u e : e \In u -> e <== stsp_sup u.
Proof. by case: e=>p S R; apply: supP; exists (STprog S). Qed.

Lemma stsp_supM u e :
        (forall e1, e1 \In u -> e1 <== e) -> stsp_sup u <== e.
Proof. by case: e=>p S R; apply: supM=>/= y[q][->]; apply: R. Qed.

Definition stspLatticeMixin := LatticeMixin stsp_supP stsp_supM.
Canonical stspLattice := Lattice STspec stspLatticeMixin.

(* In proofs, we keep goals in form (i, x, m) \In runs_of (prog_of (model e)). *)(* We need a couple of lemmas about this form. *)
(* We need a couple of lemmas about this form. *)

Lemma bot_runs : runs_of (prog_of (bot : ST A)) =p Pred0.
Proof. by move=>[[i y]m]; split=>//=; case. Qed.

Lemma model_runs (e : ST A) p y m :
        m \In prog_of e p y <->
        exists i, i \In id_val p /\ (i, y, m) \In runs_of (prog_of e).
Proof.
case: e p =>pr e C _ /= p; split.
- by case/C=>i [H1 H2]; exists i; split=>//; exists (bound H1).
case=>i [H1 H2]; apply/C.
exists i, H1; case: H2 =>/= H2.
by rewrite (pf_irr H2 (bound H1)).
Qed.

Lemma def_runs i y m (e : ST A) :
        (i, y, m) \In runs_of (prog_of e) ->
        [/\ valid i, pre_of e i & valid m].
Proof.
case: e=>/= p e _ D; case=>/=; case=>Hi Hv Hm; split=>//.
by case: m Hm=>//; move/D.
Qed.

Lemma spec_runs i y m g (e : STspec) :
        (i, y, m) \In runs_of (prog_of (model e)) ->
        (s g).1 i -> (s g).2 y i m.
Proof.
case: e; case=>p e C S H /= R.
by move/H=>/= [_]; apply.
Qed.

End STspecDef.

Arguments spec_runs [G A s i y m g].
Prenex Implicits bot_runs model_runs def_runs spec_runs.

(************************************)
(* modeling the language primitives *)
(************************************)

Module Model.

(* recursion *)
Section Fix.
Variables (G A : Type) (B : A -> Type) (s : forall x, spec G (B x)).
Notation tp := (forall x, STspec (s x)).
Notation lat := (dfunLattice (fun x => [lattice of STspec (s x)])).
Variable (f : tp -> tp).

(* we take a fixpoint not of f, but of its monotone completion f' *)
(* should eventually prove that f' is monotone *)

Definition f' (e : lat) :=
  sup [Pred t : lat | exists e', e' <== e /\ t = f e'].

Definition ffix : tp := tarski_lfp f'.

End Fix.

Section Return.
Variables (G A : Type) (x : A).

Definition ret_pre : pre :=
  fun => True.

Definition ret_prog (p : ideald ret_pre) y m :=
  m \In id_val p /\ y = Val x.

Lemma ret_coherent : coherent ret_prog.
Proof.
move=>p y m; split; first by case=>H ->{y}; exists m, H.
by case=>i [H1][<-] ->.
Qed.

Lemma ret_dstrict : def_strict ret_prog.
Proof. by case=>p H y /= []; case/H. Qed.

Definition ret_st := Prog ret_coherent ret_dstrict.

Definition ret_spec : spec G A :=
  fun => (ret_pre, fun y i m => m = i /\ y = Val x).

Lemma ret_has_spec : ret_st \In has_spec ret_spec.
Proof. by move=>/= _ i p; split=>// y m; case=>/= _ [->->]. Qed.

Definition ret := STprog ret_has_spec.

End Return.

Section Throw.
Variables (G A : Type) (e : exn).

Definition throw_pre : pre :=
  fun => True.

Definition throw_prog (p : ideald throw_pre) y m :=
  m \In id_val p /\ y = @Exn A e.

Lemma throw_coherent : coherent throw_prog.
Proof.
move=>p y m; split; first by case=>H ->{y}; exists m, H.
by case=>i [H1] [<-{m}] ->{y}.
Qed.

Lemma throw_dstrict : def_strict throw_prog.
Proof. by case=>p H y /= []; case/H. Qed.

Definition throw_st := Prog throw_coherent throw_dstrict.

Definition throw_spec : spec G A :=
  fun => (throw_pre, fun y i m => m = i /\ y = Exn e).

Lemma throw_has_spec : throw_st \In has_spec throw_spec.
Proof. by move=>/=_ i p; split=>// y m; case=>/= _ [->->]. Qed.

Definition throw := STprog throw_has_spec.

End Throw.

Section BindST.
Variables (A B : Type).
Variables (po1 : post A).
Variables (e1 : ST A) (e2 : A -> ST B).

Definition bind_pre : pre :=
  fun i => pre_of e1 i /\ forall x m, po1 (Val x) i m -> pre_of (e2 x) m.

Definition bind_sp (p : ideald bind_pre) y m :=
   exists i x h, i \In id_val p /\
     (i, x, h) \In runs_of (prog_of e1) /\
     match x with
     | Val x' => (h, y, m) \In runs_of (prog_of (e2 x'))
     | Exn e => y = Exn e /\ m = h
     end.

Lemma bind_coherent : coherent bind_sp.
Proof.
case=>p H y m; split.
- case=>i [x][h][/= H1][H2] H3.
  by exists i, H1, i, x, h.
case=>i [/= H1][_][x][h][<-][T1 T2].
by exists i, x, h.
Qed.

Lemma bind_dstrict : def_strict bind_sp.
Proof.
move=>p y [i][x][h][H1][].
case: x=>[x'|e] H2; first by case/def_runs.
by case=>_ E; case/def_runs: H2; rewrite -E.
Qed.

Definition bind_st := Prog bind_coherent bind_dstrict.

End BindST.

Section Bind.
Variables (G A B : Type).
Variables (s1 : spec G A) (s2 : A -> spec G B).
Variables (e1 : STspec s1) (e2 : forall x, STspec (s2 x)).

Definition bind_post g : post B :=
  fun y i m => (exists x h, (s1 g).2 (Val x) i h /\ (s2 x g).2 y h m) \/
               (exists e, y = Exn e /\ (s1 g).2 (Exn e) i m).
Definition bind_spec : spec G B :=
  fun g => (bind_pre (s1 g).2 (model e1) (fun x => model (e2 x)), bind_post g).

Lemma bind_has_spec : bind_st \In has_spec bind_spec.
Proof.
move=>g' i /=; rewrite /bind_pre. Pg. y m.
case=>[[[/= S1 S2]]] D [h][x][j][<-][].
case: x=>[x|e] T1; last first.
- case=>->->; right; exists e; split=>//.
  by apply: spec_runs T1.
move=>T2; left; exists x, j.
by split; [apply: spec_runs T1 | apply: spec_runs T2].
Qed.

Definition bind := STprog bind_coherent bind_dstrict bind_has_spec.

End Bind.


Section Try.
Variables (A B : Type) (s : spec A) (s1 : A -> spec B) (s2 : exn -> spec B).
Variables (e : STspec s) (e1 : forall x, STspec (s1 x))
          (e2 : forall x, STspec (s2 x)).

Definition try_pre : pre :=
  fun i => s.1 i /\ (forall y m, s.2 (Val y) i m -> (s1 y).1 m) /\
                     forall e m, s.2 (Exn e) i m -> (s2 e).1 m.
Definition try_post : post B :=
  fun y i m => (exists x h, s.2 (Val x) i h /\ (s1 x).2 y h m) \/
               (exists e h, s.2 (Exn e) i h /\ (s2 e).2 y h m).
Definition try_s := (try_pre, try_post).

Definition try_sp (p : ideald try_s.1) y m :=
   exists i x h, i \In id_val p /\
     (i, x, h) \In runs_of (model e) /\
     match x with
       Val x' => (h, y, m) \In runs_of (model (e1 x'))
     | Exn e => (h, y, m) \In runs_of (model (e2 e))
     end.

Lemma try_coherent : coherent try_sp.
Proof.
case=>p H y m; split.
- case=>i [x][h][/= H1][H2] H3.
  by exists i, H1, i, x, h.
case=>i [/= H1][_][x][h][<-][T1 T2].
by exists i, x, h.
Qed.

Lemma try_dstrict : def_strict try_sp.
Proof.
move=>p y [i][x][h][H1][].
by case: x=>[x'|e'] H2; case/def_runs.
Qed.

Lemma try_has_spec : try_sp \In has_spec try_s.
Proof.
move=>i y m; case=>[[[/= S1 [S2 S3]]]] D [h][x][j][<-][].
case: x=>[x'|e'] T1 T2; [left; exists x' | right; exists e'];
exists j; by split; [apply: spec_runs T1 | apply: spec_runs T2].
Qed.

Definition try := STprog try_coherent try_dstrict try_has_spec.

End Try.


Definition conseq A (s1 s2 : spec A) :=
  forall i, s2.1 i -> valid i ->
    s1.1 i /\ forall y m, s1.2 y i m -> valid m -> s2.2 y i m.

Lemma conseq_refl (A : Type) (s : spec A) : conseq s s.
Proof. by []. Qed.

#[export]
Hint Resolve conseq_refl : core.

Section Consequence.
Variables (A : Type) (s1 s2 : spec A) (e : STspec s1) (pf : conseq s1 s2).

Definition do_sp (p : ideald s2.1) y m :=
  exists i, i \In id_val p /\ (i, y, m) \In runs_of (model e).

Lemma do_coherent : coherent do_sp.
Proof.
case=>q H y m; split.
- by case=>i [/= H1 T1]; exists i, H1, i.
by case=>i [/= H1][_][<-] T1; exists i.
Qed.

Lemma do_dstrict : def_strict do_sp.
Proof. by move=>q y [h][/= H]; case/def_runs. Qed.

Lemma do_has_spec : do_sp \In has_spec s2.
Proof.
move=>i y m [[/= S1 D1]][_][<-] T; case/def_runs: (T)=>_ S2 D2.
by apply: (proj2 (pf S1 D1)) D2; apply: spec_runs T.
Qed.

Definition Do := STprog do_coherent do_dstrict do_has_spec.

End Consequence.


Section Read.
Variable (A : Type) (x : ptr).

Local Notation idyn v := (@dyn _ id _ v).

Definition read_s : spec A :=
  (fun i : heap => x \in dom i /\ exists v : A, find x i = Some (idyn v),
   fun y (i : heap) m => m = i /\
     forall v, find x i = Some (idyn v) -> y = Val v).

Definition read_sp (p : ideald read_s.1) (v : ans A) m :=
  m \In id_val p /\ exists w, v = Val w /\ find x m = Some (idyn w).

Lemma read_coherent : coherent read_sp.
Proof.
move=>p v m; split; last first.
- by case=>i [H1][<-][w][->]; split=>//; exists w.
case=>H1 [w][->] H2.
by exists m, H1; split=>//; exists w.
Qed.

Lemma read_dstrict : def_strict read_sp.
Proof. by case=>p H y []; case/H. Qed.

Lemma read_has_spec : read_sp \In has_spec read_s.
Proof.
move=>i y m [[[/= H1]]][v] H2 D [<-][w][->] H3.
by split=>// b1; rewrite H3; case; move/inj_pair2=>->.
Qed.

Definition read := STprog read_coherent read_dstrict read_has_spec.

End Read.


Section Write.
Variable (A : Type) (x : ptr) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition write_s : spec unit :=
  (fun i : heap => x \in dom i : Prop,
   fun y (i : heap) m => y = Val tt /\ upd x (idyn v) i = m).

Definition write_sp (p : ideald write_s.1) (y : ans unit) m :=
  exists i, i \In id_val p /\ x \in dom i /\
            y = Val tt /\ m = upd x (idyn v) i.

Lemma write_coherent : coherent write_sp.
Proof.
move=>p y m; split; case=>i [H1].
- by case=>H2 [->->]; exists i, H1,i.
by case=>_ [<-][H2][->] ->; exists i.
Qed.

Lemma write_dstrict : def_strict write_sp.
Proof.
case=>p H y [i] /= [H1][H2][H3].
suff L: valid (upd x (idyn v) i) by move=>H4; rewrite -H4 in L.
by rewrite validU (dom_cond H2) (dom_valid H2).
Qed.

Lemma write_has_spec : write_sp \In has_spec write_s.
Proof. by move=>i y m [[/= H1 D1]][_][<-][H2][->] ->. Qed.

Definition write := STprog write_coherent write_dstrict write_has_spec.

End Write.


Section Allocation.
Variables (A : Type) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition alloc_s : spec ptr :=
  (fun i => valid i : Prop,
   fun y (i : heap) m => exists x, x != null /\ y = Val x /\ x \notin dom i /\
                                   upd x (idyn v) i = m).

Definition alloc_sp (p : ideald alloc_s.1) y m :=
  exists i, i \In id_val p /\ exists l : ptr, y = Val l /\
    m = i \+ l :-> v /\ l != null /\ l \notin dom i.

Lemma alloc_coherent : coherent alloc_sp.
Proof.
move=>p x m; split.
- case=>i [H1][l][->][->][H2] H3.
  by exists i, H1, i; split=>//; exists l.
case=>i [H1][_][<-][l][->][->][H2 H3].
by exists i; split=>//; exists l.
Qed.

Lemma alloc_dstrict : def_strict alloc_sp.
Proof.
case=>p H y [m][/= H1][l][H2][H3][H4 H5]; case/H: H1=>_ D.
suff {H3}: valid (m \+ l :-> v) by rewrite -H3.
rewrite joinC.
rewrite validPtUn.
apply/andP; split => //.
by apply/andP; split.
Qed.

Lemma alloc_has_spec : alloc_sp \In has_spec alloc_s.
Proof.
move=>i y m [[/= H D]][_][<-][l][->][->][H1] H2.
exists l; do !split=>//.
by rewrite -[i]unitR updUnL (negbTE H2) unitR.
Qed.

Definition alloc := STprog alloc_coherent alloc_dstrict alloc_has_spec.

End Allocation.


Section BlockAllocation.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_s : spec ptr :=
  (fun i => valid i : Prop,
   fun y i m => exists r, y = Val r /\ m = i \+ updi r (nseq n v)).

Definition allocb_sp (p : ideald allocb_s.1) y m :=
  exists i, i \In id_val p /\ y = Val (fresh i) /\
            m = i \+ updi (fresh i) (nseq n v).

Lemma allocb_coherent : coherent allocb_sp.
Proof.
move=>p x m; split.
- by case=>i [H1][->] ->; exists i; exists H1; exists i.
by case=>i [H1][_][<-][->] ->; exists i.
Qed.

Lemma allocb_dstrict : def_strict allocb_sp.
Proof.
case=>p H y [m][/= H1][_] H2; case/H: H1=>_ D.
suff {H2}: valid (m \+ updi (fresh m) (nseq n v)) by rewrite -H2.
elim: n =>[|k IH]; first by rewrite /= unitR.
rewrite (_ : nseq k.+1 v = rcons (nseq k v) v); last first.
- by elim: {IH} k=>[|k IH] //=; rewrite -IH.
rewrite updi_last joinA joinC validPtUn IH /=.
rewrite ptr_null negb_and fresh_null /=.
rewrite domUn !inE /= negb_and IH negb_or /=.
by rewrite dom_fresh updimV negb_and fresh_null ltnn.
Qed.

Lemma allocb_has_spec : allocb_sp \In has_spec allocb_s.
Proof. by move=>i y m [[/= H D]][_][<-][->] ->; exists (fresh i). Qed.

Definition allocb := STprog allocb_coherent allocb_dstrict allocb_has_spec.

End BlockAllocation.


Section Deallocation.
Variable x : ptr.

Definition dealloc_s : spec unit :=
  (fun i : heap => x \in dom i : Prop,
   fun y (i : heap) m => y = Val tt /\ free i x = m).

Definition dealloc_sp (p : ideald dealloc_s.1) (y : ans unit) m :=
  exists i, i \In id_val p /\ y = Val tt /\ x \in dom i /\ m = free i x.

Lemma dealloc_coherent : coherent dealloc_sp.
Proof.
move=>p y m; split.
- by case=>i [H1][->][H2] ->; exists i; exists H1; exists i.
by case=>i [H1][_][<-][->][H2] ->; exists i.
Qed.

Lemma dealloc_dstrict : def_strict dealloc_sp.
Proof.
case=>p H y [h][/=]; case/H=>_ H1 [H2][H3] H4.
suff: valid (free h x) by rewrite -H4.
by rewrite validF.
Qed.

Lemma dealloc_has_spec : dealloc_sp \In has_spec dealloc_s.
Proof. by move=>i y m [[/= H1 D1]][_][<-][->][H2] ->. Qed.

Definition dealloc :=
  STprog dealloc_coherent dealloc_dstrict dealloc_has_spec.

End Deallocation.

End Model.

