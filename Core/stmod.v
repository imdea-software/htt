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
Notation post A := (ans A -> heap -> Prop).
Definition spec G B := G -> pre * post B : Type.

(********************************)
(* Definition of the Hoare type *)
(********************************)

Definition defed (P : Pred heap) : Pred heap :=
  [Pred i \In P | valid i].

Lemma defed_leq h : defed h <== h.
Proof. by move=>i []. Qed.

Lemma defed_mono : monotone defed.
Proof. by move=>h1 h2 H1 i [H2 V]; split=>//; apply: H1 H2. Qed.

Notation ideald P := (ideal (defed P)).

Definition relaxd P1 P2 (p : ideald P2) (pf : P2 <== P1) : ideald P1 :=
  relax p (defed_mono pf).

Lemma relaxd_refl P (p : ideald P) (pf : P <== P): relaxd p pf = p.
Proof. by case: p=>p H; congr Ideal; apply: pf_irr. Qed.

Lemma relaxd_trans P1 P2 P3 (p : ideald P1) (pf12 : P1 <== P2) (pf23 : P2 <== P3) (pf13 : P1 <== P3) :
        relaxd (relaxd p pf12) pf23 = relaxd p pf13.
Proof. by congr Ideal; apply: pf_irr. Qed.

Section BasePrograms.
Variables (P : pre) (A : Type).

Lemma bound (p : ideald P) i : i \In id_val p -> i \In defed P.
Proof. by case: p=>p; apply. Qed.

(* we carve out the model out of the following base type *)
Definition prog := ideald P -> ans A -> Pred heap.

(* we take only progs with special properties *)
(* which we define next *)

(* coherence is continuity stated with *)
(* directed sets instead of chains *)
Definition coherent (e : prog) :=
  forall p x m,
    m \In e p x <-> exists i (pf : i \In id_val p),
                    m \In e (single (bound pf)) x.

(* defined heaps map to defined heaps *)
Definition def_strict (e : prog) := forall p x, Heap.Undef \Notin e p x.

Definition frameable (e : prog) :=
  forall i j (pf0 : i \In defed P) (V : valid (i \+ j)),
    exists (pf : i \+ j \In defed P),
      forall y m, e (single pf) y m ->
        exists h, m = h \+ j /\ valid (h \+ j) /\ e (single pf0) y h.

End BasePrograms.

Section STDef.
Variable (A : Type).

Structure ST := Prog {
  pre_of : pre;
  prog_of : prog pre_of A;
  _ : coherent prog_of;
  _ : def_strict prog_of;
  _ : frameable prog_of}.

Arguments prog_of : clear implicits.

Lemma coh_st e : coherent (prog_of e).
Proof. by case: e. Qed.

Arguments coh_st : clear implicits.

Lemma dstr_st e : def_strict (prog_of e).
Proof. by case: e. Qed.

Arguments dstr_st : clear implicits.

Lemma fr_st e : frameable (prog_of e).
Proof. by case: e. Qed.

Arguments fr_st : clear implicits.

Definition vrf i (c : ST) (Q : post A) :=
  forall (v : valid i),
    exists (pf : i \In pre_of c), forall y m,
    prog_of c (single (conj pf v)) y m -> Q y m.

Definition has_spec G (s : spec G A) (c : ST) :=
  forall g i, (s g).1 i -> vrf i c (s g).2.

Lemma vrf_frame i j (e : ST) (Q : post A) :
        vrf i e (fun y m => valid (m \+ j) -> Q y (m \+ j)) ->
        vrf (i \+ j) e Q.
Proof.
move=>H V; have Vi := validL V.
case: (H Vi)=>Hi {}H.
case: (fr_st e _ _ (conj Hi Vi) V); case=>pf' V' H2.
exists pf'=>y m.
rewrite (_ : V = V'); last by apply: pf_irr.
case/H2=>h [->][Hv Hp]{H2}.
by apply: H.
Qed.

Lemma vrf_conseq (e : ST) (Q1 Q2 : post A) i :
        valid i ->
        (forall y m, valid m -> Q1 y m -> Q2 y m) ->
        vrf i e Q1 -> vrf i e Q2.
Proof.
move=>_ H H1 Vi; case: (H1 Vi)=>pf P.
exists pf=>y m Hm.
have Vm: valid m by case: m Hm=>// /dstr_st.
by apply: H=>//; apply: P.
Qed.

(* poset structure on ST *)

Definition st_leq e1 e2 :=
  exists pf : pre_of e2 <== pre_of e1,
  forall p : ideald (pre_of e2),
    prog_of e1 (relaxd p pf) <== prog_of e2 p.

Lemma st_refl e : st_leq e e.
Proof. by exists (poset_refl _)=>p y m; rewrite relaxd_refl. Qed.

Lemma st_asym e1 e2 : st_leq e1 e2 -> st_leq e2 e1 -> e1 = e2.
Proof.
move: e1 e2=>[p1 e1 C1 D1 F1][p2 e2 C2 D2 F2]; rewrite /st_leq /=.
case=>E1 R1 [E2 R2].
move: (poset_asym E1 E2)=>?; subst p2.
have : e1 = e2.
- apply: fext=>p; apply: fext=>y; apply: fext=>m.
  move: (R2 p y m)=>{}R2; move: (R1 p y m)=>{}R1.
  apply: pext; split.
  - by move=>H1; apply: R1; rewrite relaxd_refl.
  by move=>H2; apply: R2; rewrite relaxd_refl.
move=>?; subst e2.
by congr Prog; apply: pf_irr.
Qed.

Lemma st_trans e1 e2 e3 : st_leq e1 e2 -> st_leq e2 e3 -> st_leq e1 e3.
Proof.
move: e1 e2 e3=>[p1 e1 C1 D1 F1][p2 e2 C2 D2 F2][p3 e3 C3 D3 F3].
case=>/= E1 R1 [/= E2 R2]; rewrite /st_leq /=.
have E3 := poset_trans E2 E1; exists E3=>p y m.
set p' := relaxd p E2.
move: (R1 p' y m)=>{}R1; move: (R2 p y m)=>{}R2.
move=>H1; apply/R2/R1.
by rewrite relaxd_trans.
Qed.

(* a program that can always run but never returns (an endless loop) *)
Definition prog_bot : prog PredT A :=
  fun _ _ _ => False.

Lemma coherent_bot : coherent prog_bot.
Proof. by move=>p y m; split=>//; case=>i []. Qed.

Lemma dstrict_bot : def_strict prog_bot.
Proof. by move=>*. Qed.

Lemma frame_bot : frameable prog_bot.
Proof.
move=>i j [Hij Hv] Vij.
have J : i \+ j \In defed PredT by [].
by exists J.
Qed.

Definition st_bot := Prog coherent_bot dstrict_bot frame_bot.

Lemma st_botP e : st_leq st_bot e.
Proof. by case: e=>p e C D; exists (@pred_topP _ _)=>?; apply: botP. Qed.

Definition stPosetMixin := PosetMixin st_botP st_refl st_asym st_trans.
Canonical stPoset := Eval hnf in Poset ST stPosetMixin.

(* lattice structure on ST *)

(* intersection of preconditions *)
Definition pre_sup (u : Pred ST) : pre :=
  fun h => forall e, e \In u -> h \In pre_of e.

Definition pre_sup_leq u e (pf : e \In u) : pre_sup u <== pre_of e :=
  fun h (pf1 : pre_sup u h) => pf1 e pf.

(* union of postconditions *)
Definition prog_sup (u : Pred ST) : prog (pre_sup u) A :=
  fun p y m => exists e (pf : e \In u),
    prog_of e (relaxd p (pre_sup_leq pf)) y m.

Arguments prog_sup : clear implicits.

Lemma prog_sup_coh u : coherent (prog_sup u).
Proof.
move=>p y m; split.
- case=>e [H1 H2]; have Cx := coh_st e.
  case/Cx: H2=>i [pf1] M; exists i.
  have I : i \In id_val p by exact: pf1.
  exists I, e, H1.
  apply/Cx; exists i.
  set y' := id_val _; have J2 : i \In y' by [].
  exists J2.
  by rewrite (_ : bound J2 = bound pf1) //; apply: pf_irr.
case=>i[pf][e][H1 H2]; have Cx := coh_st e.
exists e, H1.
case/Cx: H2=>i0 [pf0] M0; apply/Cx; exists i0.
have J2 : i0 \In id_val (relaxd p (pre_sup_leq H1)).
- by move: pf0 {M0}=><-.
exists J2.
by rewrite (_ : bound J2 = bound pf0) //; apply: pf_irr.
Qed.

Lemma prog_sup_dstrict u : def_strict (prog_sup u).
Proof. by move=>p y; case; case=>p0 e C D F [H1] /D. Qed.

Lemma prog_sup_frame u : frameable (prog_sup u).
Proof.
move=>i j [Hi Vi] Vij.
have J : i \+ j \In defed (pre_sup u).
- split=>// e He.
  move: (Hi e He)=>{}Hi.
  by case: (fr_st e _ _ (conj Hi Vi) Vij); case.
exists J=>y m [e][He]Pe.
move: (Hi e He)=>Hi'.
case: (fr_st e _ _ (conj Hi' Vi) Vij)=>pf P.
move: Pe.
rewrite (_ : relaxd (single J) (pre_sup_leq He) = single pf); last first.
- by congr Ideal; apply: pf_irr.
case/P=>h' [E][V']P'.
exists h'; do!split=>//.
exists e, He.
rewrite (_ : relaxd (single (conj Hi Vi)) (pre_sup_leq He) = single (conj Hi' Vi)) //.
by congr Ideal; apply: pf_irr.
Qed.

Definition st_sup u := Prog (@prog_sup_coh u) (@prog_sup_dstrict u) (@prog_sup_frame u).

Lemma st_supP u e : e \In u -> e <== st_sup u.
Proof.
case: e=>p e' C D F R.
exists (pre_sup_leq R)=>/=p0 y m H.
by exists (Prog C D F), R.
Qed.

Lemma st_supM u e :
  (forall e1, e1 \In u -> e1 <== e) -> st_sup u <== e.
Proof.
case: e=>p e C D F R.
have J : p <== pre_sup u.
- by move=>/= x Px e' pf; case: (R _ pf)=>/= + _; apply.
exists J=>p0 y m [e0][pf H1]; have Cx := coh_st e0.
case: (R _ pf)=>/= Hx; apply=>//.
case/Cx: H1=>i [pf1 M1]; apply/Cx; exists i.
have J2 : i \In id_val (relaxd p0 Hx) by exact: pf1.
exists J2.
by rewrite (_ : bound J2 = bound pf1) //; apply: pf_irr.
Qed.

Definition stLatticeMixin := LatticeMixin st_supP st_supM.
Canonical stLattice := Lattice ST stLatticeMixin.

End STDef.

Arguments prog_of [A].
Arguments coh_st [A].
Arguments dstr_st [A].

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
have E := poset_asym E1 E2; subst e2.
by congr STprog; apply: pf_irr.
Qed.

Lemma stsp_trans e1 e2 e3 : stsp_leq e1 e2 -> stsp_leq e2 e3 -> stsp_leq e1 e3.
Proof.
move: e1 e2 e3=>[e1 H1][e2 H2][e3 H3].
by apply: poset_trans.
Qed.

Lemma st_bot_has_spec : @st_bot A \In has_spec s.
Proof.
move=>g i H V /=.
have J: i \In PredT by [].
by exists J.
Qed.

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
move=>g i p Vi.
have J : i \In pre_of (st_sup' u).
- move=>e [e1][{e}->]; case: e1=>/= e P _.
  by case: (P _ _ p Vi).
exists J=>y m /= [e][[[e1 P][/= E He1]]] H; subst e1.
case: (P _ _ p Vi)=>Hi; apply.
rewrite (_ : single (conj Hi Vi) =
             relaxd (single (conj J Vi))
                    (pre_sup_leq
                      (ex_intro (fun e0 => e = model e0 /\ e0 \In u)
                                (STprog P) (conj (erefl e) He1)))) //.
by congr Ideal; apply: pf_irr.
Qed.

Definition stsp_sup u := STprog (@st_sup_has_spec' u).

Lemma stsp_supP u e : e \In u -> e <== stsp_sup u.
Proof. by case: e=>p S R; apply: supP; exists (STprog S). Qed.

Lemma stsp_supM u e :
        (forall e1, e1 \In u -> e1 <== e) -> stsp_sup u <== e.
Proof. by case: e=>p S R; apply: supM=>/= y[q][->]; apply: R. Qed.

Definition stspLatticeMixin := LatticeMixin stsp_supP stsp_supM.
Canonical stspLattice := Lattice STspec stspLatticeMixin.

End STspecDef.

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
Variables (A : Type) (x : A).

Definition ret_pre : pre := PredT.

Definition ret_prog : prog ret_pre A :=
  fun p y m =>
    m \In id_val p /\ y = Val x.

Lemma ret_coherent : coherent ret_prog.
Proof.
move=>p y m; split; first by case=>H ->{y}; exists m, H.
by case=>i [H1][<-] ->.
Qed.

Lemma ret_dstrict : def_strict ret_prog.
Proof. by case=>p H y /= []; case/H. Qed.

Lemma ret_frame : frameable ret_prog.
Proof.
move=>i j [[] Hv] Vij.
have J : i \+ j \In defed ret_pre by [].
by exists J=>y m [<- ->]; exists i.
Qed.

Definition ret_st := Prog ret_coherent ret_dstrict ret_frame.

Lemma vrf_ret (Q : post A) i :
        valid i -> Q (Val x) i ->
        vrf i ret_st Q.
Proof.
move=>_ Hi V.
have J : i \In pre_of ret_st by [].
by exists J=>y m [/= <- ->].
Qed.

End Return.

Section Throw.
Variables (A : Type) (e : exn).

Definition throw_pre : pre := PredT.

Definition throw_prog : prog throw_pre A :=
  fun p y m =>
    m \In id_val p /\ y = @Exn A e.

Lemma throw_coherent : coherent throw_prog.
Proof.
move=>p y m; split; first by case=>H ->{y}; exists m, H.
by case=>i [H1] [<-{m}] ->{y}.
Qed.

Lemma throw_dstrict : def_strict throw_prog.
Proof. by case=>p H y /= []; case/H. Qed.

Lemma throw_frame : frameable throw_prog.
Proof.
move=>i j [[] Hv] Vij.
have J : i \+ j \In defed throw_pre by [].
by exists J=>y m [<- ->]; exists i.
Qed.

Definition throw_st := Prog throw_coherent throw_dstrict throw_frame.

Lemma vrf_throw (Q : post A) i :
        valid i -> Q (Exn e) i ->
        vrf i throw_st Q.
Proof.
move=>_ Hi V.
have J : i \In pre_of throw_st by [].
by exists J=>y m [/= <- ->].
Qed.

End Throw.

Section Bind.
Variables (A B : Type).
Variables (e1 : ST A) (e2 : A -> ST B).

Definition bind_pre : pre :=
  fun i => exists pf : i \In defed (pre_of e1),
    forall x m, prog_of e1 (single pf) (Val x) m -> pre_of (e2 x) m.

Definition bind_prog : prog bind_pre B :=
  fun p y m =>
    exists i x h, i \In id_val p /\
      exists pf : i \In defed (pre_of e1), h \In prog_of e1 (single pf) x /\
      match x with
      | Val x' => exists pf' : h \In defed (pre_of (e2 x')),
                    m \In prog_of (e2 x') (single pf') y
      | Exn e => y = Exn e /\ m = h
      end.

Lemma bind_coherent : coherent bind_prog.
Proof.
move=>p y m; split=>/=.
- case=>i [x][h][H1][H2]H3.
  by exists i, H1, i, x, h; split=>//; exists H2.
case=>i [/= H1][_][x][h][<-][H2 H3].
by exists i, x, h; split=>//=; exists H2.
Qed.

Lemma bind_dstrict : def_strict bind_prog.
Proof.
move=>p y [i][x][h][H1][H2][].
case: x=>[x'|e] H3.
- by case=>H4 /dstr_st.
by case=>_; move: H3=>/[swap]<- /dstr_st.
Qed.

Lemma bind_frame : frameable bind_prog.
Proof.
move=>i j [[Hi P] Hv] Vij.
have J : i \+ j \In defed bind_pre.
- split=>//.
  case: (fr_st Hi Vij)=>pf H.
  exists pf=>x m /H [h][->][Vhj] /P P1.
  have J' : h \In defed (pre_of (e2 x)) by split=>//; apply: (validL Vhj).
  by case: (fr_st J' Vhj); case.
exists J=>y m; case=>h0[x][h1][/= <-][H0][H1].
case: x H1=>[x|e] H1.
- case=>H1' P2.
  case: (fr_st Hi Vij)=>pf H.
  move: H1; rewrite (_ : single H0 = single pf); last by congr Ideal; apply: pf_irr.
  case/H=>h' [E1][V1]P1.
  rewrite E1 in H1' P2; move: (P _ _ P1)=>H1''.
  have J' : h' \In defed (pre_of (e2 x)) by split=>//; apply: (validL V1).
  case: (fr_st J' V1)=>pf2 H2.
  move: P2; rewrite (_ : single H1' = single pf2); last by congr Ideal; apply: pf_irr.
  case/H2=>h'' [E''][V'']P''.
  exists h''; do!split=>//.
  by exists i, (Val x), h'=>/=; split=>//; exists Hi; split=>//; exists J'.
case=>->->.
case: (fr_st Hi Vij)=>pf H.
move: H1; rewrite (_ : single H0 = single pf); last by congr Ideal; apply: pf_irr.
case/H=>h' [E1][V1]P1.
exists h'; do!split=>//.
by exists i, (Exn e), h'; split=>//; exists Hi.
Qed.

Definition bind_st := Prog bind_coherent bind_dstrict bind_frame.

Lemma vrf_bind (Q : post B) i :
        vrf i e1 (fun x m => match x with
                  | Val x' => vrf m (e2 x') Q
                  | Exn e => Q (Exn e) m
                  end) ->
        vrf i bind_st Q.
Proof.
move=>H Vi.
case: (H Vi)=>pf P.
have J : i \In pre_of bind_st.
- exists (conj pf Vi)=>x m P1.
  have Vm: valid m by case: m P1=>// /dstr_st.
  by case: (P _ _ P1 Vm).
exists J=>y j /= [h][x][m][{h}<-][pf'][Hm]F.
have Vm: valid m by case: m Hm {F}=>// /dstr_st.
case: x Hm F=>[x|e] Pm.
- case=>Hm2 Hj.
  move: Pm; rewrite (_ : single pf' = single (conj pf Vi)); last by congr Ideal; apply: pf_irr.
  move/P=>P'; case: (P' Vm)=>pf''; apply.
  rewrite (_ : single (conj pf'' Vm) = single Hm2) //.
  by congr Ideal; apply: pf_irr.
case=>->->.
move: Pm; rewrite (_ : single pf' = single (conj pf Vi)); last by congr Ideal; apply: pf_irr.
by move/P.
Qed.

End Bind.


Section Try.
Variables (A B : Type).
Variables (e : ST A) (e1 : A -> ST B) (e2 : exn -> ST B).

Definition try_pre : pre :=
  fun i => exists pf : i \In defed (pre_of e),
             (forall y m, prog_of e (single pf) (Val y) m -> pre_of (e1 y) m) /\
              forall ex m, prog_of e (single pf) (Exn ex) m -> pre_of (e2 ex) m.

Definition try_prog : prog try_pre B :=
  fun p y m =>
    exists i x h, i \In id_val p /\
      exists pf : i \In defed (pre_of e), h \In prog_of e (single pf) x /\
      match x with
      | Val x' => exists pf' : h \In defed (pre_of (e1 x')),
                    m \In prog_of (e1 x') (single pf') y
      | Exn ex => exists pf' : h \In defed (pre_of (e2 ex)),
                    m \In prog_of (e2 ex) (single pf') y
      end.

Lemma try_coherent : coherent try_prog.
Proof.
move=>p y m; split.
- case=>i [x][h][/= H1][H2] H3.
  by exists i, H1, i, x, h; split=>//; exists H2.
case=>i [/= H1][_][x][h][<-][H2 H3].
by exists i, x, h; split=>//; exists H2.
Qed.

Lemma try_dstrict : def_strict try_prog.
Proof.
move=>p y [i][x][h][H1][H2][].
by case: x=>[x'|e'] H3; case=>H4 /dstr_st.
Qed.

Lemma try_frame : frameable try_prog.
Proof.
move=>i j [[Hi [P1 P2]] Vi] Vij.
have J : i \+ j \In defed try_pre.
- split=>//.
  case: (fr_st Hi Vij)=>pf H.
  exists pf; split.
  - move=>x m /H [h][->][Vhj] /P1 P1'.
    have J' : h \In defed (pre_of (e1 x)) by split=>//; apply: (validL Vhj).
    by case: (fr_st J' Vhj); case.
  move=>ex m /H [h][->][Vhj] /P2 P2'.
  have J' : h \In defed (pre_of (e2 ex)) by split=>//; apply: (validL Vhj).
  by case: (fr_st J' Vhj); case.
exists J=>y m; case=>h0[x][h1][/= <-][H0][H1].
case: x H1=>[x|ex] H1.
- case=>H1' Po.
  case: (fr_st Hi Vij)=>pf H.
  move: H1; rewrite (_ : single H0 = single pf); last by congr Ideal; apply: pf_irr.
  case/H=>h'[E'][V']P'.
  rewrite E' in H1' Po; move: (P1 _ _ P')=>H1''.
  have J' : h' \In defed (pre_of (e1 x)) by split=>//; apply: (validL V').
  case: (fr_st J' V')=>pf2 H2.
  move: Po; rewrite (_ : single H1' = single pf2); last by congr Ideal; apply: pf_irr.
  case/H2=>h''[E''][V'']P''.
  exists h''; do!split=>//.
  exists i, (Val x), h'=>/=; split=>//.
  by exists Hi; split=>//; exists J'.
case=>H1' Po.
case: (fr_st Hi Vij)=>pf H.
move: H1; rewrite (_ : single H0 = single pf); last by congr Ideal; apply: pf_irr.
case/H=>h'[E'][V']P'.
rewrite E' in H1' Po; move: (P2 _ _ P')=>H1''.
have J' : h' \In defed (pre_of (e2 ex)) by split=>//; apply: (validL V').
case: (fr_st J' V')=>pf2 H2.
move: Po; rewrite (_ : single H1' = single pf2); last by congr Ideal; apply: pf_irr.
case/H2=>h''[E''][V'']P''.
exists h''; do!split=>//.
exists i, (Exn ex), h'=>/=; split=>//.
by exists Hi; split=>//; exists J'.
Qed.

Definition try_st := Prog try_coherent try_dstrict try_frame.

Lemma vrf_try (Q : post B) i :
        vrf i e (fun x m => match x with
                 | Val x' => vrf m (e1 x') Q
                 | Exn ex => vrf m (e2 ex) Q
                 end) ->
        vrf i try_st Q.
Proof.
move=>H Vi.
case: (H Vi)=>pf P.
have J : i \In pre_of try_st.
- exists (conj pf Vi); split.
  - move=>x m P1.
    have Vm: valid m by case: m P1=>// /dstr_st.
    by case: (P _ _ P1 Vm).
  move=>ex m P2.
  have Vm: valid m by case: m P2=>// /dstr_st.
  by case: (P _ _ P2 Vm).
exists J=>y j /= [h][x][m][{h}<-][pf'][Hm]F.
have Vm: valid m by case: m Hm {F}=>// /dstr_st.
case: x Hm F=>[x|ex] Pm.
- case=>Hm2 Hj.
  move: Pm; rewrite (_ : single pf' = single (conj pf Vi)); last by congr Ideal; apply: pf_irr.
  move/P=>P'; case: (P' Vm)=>pf''; apply.
  rewrite (_ : single (conj pf'' Vm) = single Hm2) //.
  by congr Ideal; apply: pf_irr.
case=>Hm2 Hj.
move: Pm; rewrite (_ : single pf' = single (conj pf Vi)); last by congr Ideal; apply: pf_irr.
move/P=>P'; case: (P' Vm)=>pf''; apply.
rewrite (_ : single (conj pf'' Vm) = single Hm2) //.
by congr Ideal; apply: pf_irr.
Qed.

End Try.


Section Read.
Variable (A : Type) (x : ptr).

Local Notation idyn v := (@dyn _ id _ v).

Definition read_pre : pre :=
  fun i => x \in dom i /\ exists v : A, find x i = Some (idyn v).

Definition read_prog : prog read_pre A :=
  fun p y m =>
    m \In id_val p /\ exists w, y = Val w /\ find x m = Some (idyn w).

Lemma read_coherent : coherent read_prog.
Proof.
move=>p v m; split; last first.
- by case=>i [H1][<-][w][->]; split=>//; exists w.
case=>H1 [w][->] H2.
by exists m, H1; split=>//; exists w.
Qed.

Lemma read_dstrict : def_strict read_prog.
Proof. by case=>p H y []; case/H. Qed.

Lemma read_frame : frameable read_prog.
Proof.
move=>i j [[Hx][v E] Vi] Vij.
have J : i \+ j \In defed read_pre.
- split=>//; split.
  - by rewrite domUn inE Vij Hx.
  by exists v; rewrite findUnL // Hx.
exists J=>y m [/= <-][w][->]H.
exists i; do!split=>//; exists w; split=>//.
by rewrite findUnL // Hx in H.
Qed.

Definition read_st := Prog read_coherent read_dstrict read_frame.

Lemma vrf_read (i : heap) (Q : post A) (v : A) j :
       valid i ->
       i = x :-> v \+ j ->
       (forall w h, i = x :-> w \+ h -> Q (Val w) i) ->
       vrf i read_st Q.
Proof.
move=>_ E H2 Vi.
have J : i \In read_pre.
- rewrite E in Vi *; split; first by rewrite domPtUnE.
  by exists v; rewrite findPtUn.
exists J=>y m [/= <-][w][->] H'; rewrite E in Vi H'.
rewrite findPtUn // in H'; case: H' =>/inj_pair2 E'.
by apply: H2; rewrite -E'; apply: E.
Qed.

End Read.


Section Write.
Variable (A : Type) (x : ptr) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition write_pre : pre :=
  fun i => x \in dom i.

Definition write_prog : prog write_pre unit :=
  fun p y m =>
    exists i, i \In id_val p /\ x \in dom i /\
              y = Val tt /\ m = upd x (idyn v) i.

Lemma write_coherent : coherent write_prog.
Proof.
move=>p y m; split; case=>i [H1].
- by case=>H2 [->->]; exists i, H1,i.
by case=>_ [<-][H2][->] ->; exists i.
Qed.

Lemma write_dstrict : def_strict write_prog.
Proof.
case=>p H y [i] /= [H1][H2][H3].
suff L: valid (upd x (idyn v) i) by move=>H4; rewrite -H4 in L.
by rewrite validU (dom_cond H2) (dom_valid H2).
Qed.

Lemma write_frame : frameable write_prog.
Proof.
move=>i j [Hi Vi] Vij.
have J : i \+ j \In defed write_pre.
- by split=>//; rewrite /write_pre -toPredE /= domUn inE Vij Hi.
exists J=>y m [h][/= {h}<-][Hx][->->].
exists (upd x (idyn v) i); do!split.
- by rewrite updUnL Hi.
- by rewrite validUUn.
by exists i.
Qed.

Definition write_st := Prog write_coherent write_dstrict write_frame.

Lemma vrf_write (Q : post unit) i j B (w : B) :
        valid i ->
        i = x :-> w \+ j ->
        (valid (x :-> v \+ j) -> Q (Val tt) (x :-> v \+ j)) -> (* maybe erase valid j *)
        vrf i write_st Q.
Proof.
move=>_ E H Vi.
have J : i \In write_pre.
- rewrite E in Vi *.
  by rewrite /write_pre -toPredE /= domPtUnE.
exists J=>y m /= [h][/= {h}<-][_][->->].
rewrite E in Vi *; rewrite updPtUn; apply: H.
by rewrite (@validPtUnE _ _ _ _ (idyn w)).
Qed.

End Write.


Section Allocation.
Variables (A : Type) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition alloc_pre : pre := valid.  (* should this be just PredT? *)

Definition alloc_prog : prog alloc_pre ptr :=
  fun p y m =>
    exists i, i \In id_val p /\ exists l : ptr, y = Val l /\
      m = l :-> v \+ i /\ l != null /\ l \notin dom i.

Lemma alloc_coherent : coherent alloc_prog.
Proof.
move=>p x m; split.
- case=>i [H1][l][->][->][H2] H3.
  by exists i, H1, i; split=>//; exists l.
case=>i [H1][_][<-][l][->][->][H2 H3].
by exists i; split=>//; exists l.
Qed.

Lemma alloc_dstrict : def_strict alloc_prog.
Proof.
case=>p H y [m][/= H1][l][H2][H3][H4 H5]; case/H: H1=>_ D.
suff {H3}: valid (l :-> v \+ m) by rewrite -H3.
by rewrite validPtUn; apply/and3P.
Qed.

Lemma alloc_frame : frameable alloc_prog.
Proof.
move=>i j [Vi] Vi' Vij.
have J: i \+ j \In defed alloc_pre by [].
exists J=>y m [h][/= {h}<-][x][{y}->][{m}->][Hx Hx2].
exists (x :-> v \+ i). rewrite -joinA; do!split=>//.
- rewrite validUnAE validPt Hx Vij domPtK Hx /= all_predC.
  apply/hasP=>[[y Hy]]; rewrite !inE=>/eqP E.
  by move: Hy Hx2; rewrite E=>->.
exists i; split=>//; exists x; do!split=>//.
by apply/dom_NNL/Hx2.
Qed.

Definition alloc_st := Prog alloc_coherent alloc_dstrict alloc_frame.

Lemma vrf_alloc (Q : post ptr) i:
  (forall x, valid (x :-> v \+ i) -> Q (Val x) (x :-> v \+ i)) ->
  vrf i alloc_st Q.
Proof.
move=>H Vi /=.
have J: i \In alloc_pre by [].
exists J=>y m [h][/= {h}<-][x][{y}->][{m}->][Hx Hx2].
apply: H.
by rewrite validPtUn Hx Vi.
Qed.

End Allocation.


Section BlockAllocation.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_pre : pre := valid.  (* should this also be just PredT? *)

Definition allocb_prog : prog allocb_pre ptr :=
  fun p y m =>
    exists i, i \In id_val p /\ y = Val (fresh i) /\
              m = updi (fresh i) (nseq n v) \+ i.

Lemma allocb_coherent : coherent allocb_prog.
Proof.
move=>p x m; split.
- by case=>i [H1][->] ->; exists i, H1, i.
by case=>i [H1][_][<-][->] ->; exists i.
Qed.

Lemma allocb_dstrict : def_strict allocb_prog.
Proof.
case=>p H y [m][/= H1][_] H2; case/H: H1=>_ D.
suff {H2}: valid (updi (fresh m) (nseq n v) \+ m) by rewrite -H2.
elim: n =>[|k IH]; first by rewrite /= unitL.
rewrite -addn1 nseqD cats1.
rewrite updi_last -joinA joinCA validPtUn IH /=.
rewrite ptr_null negb_and fresh_null /=.
rewrite domUn !inE /= negb_and IH negb_or /=.
by rewrite dom_fresh updimV negb_and fresh_null ltnn.
Qed.

Lemma allocb_frame : frameable allocb_prog.
Proof.
move=>i j [Vi Vi'] Vij.
have J : i \+ j \In defed allocb_pre by [].
exists J=>y m [h][/= {h}<-][{y}-> {m}->].
exists (updi (fresh (i \+ j)) (nseq n v) \+ i); rewrite -joinA.
do!split=>//.
- rewrite validUnAE updiD fresh_null Vij /= all_predC.
  apply/hasP=>[[x Hx]] /= /updiP [_ [m [E _]]].
  move: (dom_fresh (i \+ j) m).
  by rewrite E in Hx; rewrite Hx.
exists i. do!split=>//=.
rewrite /allocb_prog /=.
Admitted.

Definition allocb_st := Prog allocb_coherent allocb_dstrict allocb_frame.

Lemma vrf_allocb (Q : post ptr) i :
        valid i ->
        (forall x, valid (updi x (nseq n v) \+ i) ->
           Q (Val x) (updi x (nseq n v) \+ i)) ->
        vrf i allocb_st Q.
Proof.
(*
move=>_ H; case=>/= Hi Hi' y m.
case=>h [/= {h}<-][->->]; apply: H.
rewrite validUnAE Hi updiD fresh_null /=.
apply/allP=>z Hz /=; apply/updiP; case=>_ [x][E _].
by move: Hz; rewrite E; apply/negP/dom_fresh.
Qed.
*)
Admitted.

End BlockAllocation.


Section Deallocation.
Variable x : ptr.

Definition dealloc_pre : pre :=
  fun i => x \in dom i.

Definition dealloc_prog (p : ideald dealloc_pre) (y : ans unit) m :=
  exists i, i \In id_val p /\ y = Val tt /\ x \in dom i /\ m = free i x.

Lemma dealloc_coherent : coherent dealloc_prog.
Proof.
move=>p y m; split.
- by case=>i [H1][->][H2] ->; exists i, H1, i.
by case=>i [H1][_][<-][->][H2] ->; exists i.
Qed.

Lemma dealloc_dstrict : def_strict dealloc_prog.
Proof.
case=>p H y [h][/=]; case/H=>_ H1 [H2][H3] H4.
suff: valid (free h x) by rewrite -H4.
by rewrite validF.
Qed.

Lemma dealloc_frame : frameable dealloc_prog.
Proof.
move=>i j [Hi Vi] Vij.
have J: i \+ j \In defed dealloc_pre.
- by split=>//; rewrite /dealloc_pre -toPredE /= domUn inE Vij Hi.
exists J=>y m [h][/= {h}<-][{y}->][Hx {m}->].
exists (free i x); do!split.
- by apply/freeUnR/dom_inNL/Hi.
- by apply: validFUn.
by exists i.
Qed.

Definition dealloc_st :=
  Prog dealloc_coherent dealloc_dstrict dealloc_frame.

Lemma vrf_dealloc i (Q : post unit) B (v : B) j:
        valid i ->
        i = x :-> v \+ j ->
        (valid j -> Q (Val tt) j) ->
        vrf i dealloc_st Q.
Proof.
move=>_ E H Vi /=.
have J: i \In dealloc_pre.
- by rewrite E in Vi *; rewrite /dealloc_pre -toPredE /= domPtUnE.
exists J=> y m [h][/= {h}<-][{y}->][Hx {m}->]; rewrite E in Vi *.
by rewrite freePtUn //; apply/H/(validR Vi).
Qed.

End Deallocation.

End Model.
