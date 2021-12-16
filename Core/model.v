From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From fcsl Require Import axioms pred prelude.
From fcsl Require Import pcm unionmap heap.
From HTT Require Import domain heap_extra.
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

(* safety monotonicity + frame property *)
Definition frameable (e : prog) :=
  forall i j (pf : i \In defed P) (V : valid (i \+ j)),
    exists (pf' : i \+ j \In P),
      forall y m, e (single (conj pf' V)) y m ->
        exists h, m = h \+ j /\ valid (h \+ j) /\ e (single pf) y h.

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

Corollary dstr_valid e p x m : m \In prog_of e p x -> valid m.
Proof. by case: m=>// /dstr_st. Qed.

Arguments dstr_st : clear implicits.

Lemma fr_st e : frameable (prog_of e).
Proof. by case: e. Qed.

Arguments fr_st : clear implicits.

Definition vrf i (c : ST) (Q : post A) :=
  forall (V : valid i),
    exists (pf : i \In pre_of c), forall y m,
    prog_of c (single (conj pf V)) y m -> Q y m.

Definition has_spec G (s : spec G A) (c : ST) :=
  forall g i, (s g).1 i -> vrf i c (s g).2.

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
Proof. by move=>i j [[] Vi] Vij; exists I. Qed.

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
  case/Cx: H2=>i [pf1] M; exists i, pf1, e, H1.
  apply/Cx; exists i.
  set y' := id_val _; have J2 : i \In y' by [].
  by exists J2; rewrite (pf_irr (bound J2) (bound pf1)).
case=>i[pf][e][H1 H2]; have Cx := coh_st e.
exists e, H1.
case/Cx: H2=>i0 [E] M0; apply/Cx; exists i0.
have J2 : i0 \In id_val (relaxd p (pre_sup_leq H1)).
- by rewrite -E /=.
by exists J2; rewrite (pf_irr (bound J2) (bound E)).
Qed.

Lemma prog_sup_dstrict u : def_strict (prog_sup u).
Proof. by move=>p y; case; case=>p0 e C D F [H1] /D. Qed.

Lemma prog_sup_frame u : frameable (prog_sup u).
Proof.
move=>i j [Hi Vi] Vij.
have J : i \+ j \In pre_sup u.
- move=>e He; move: (Hi _ He)=>{}Hi.
  by case: (fr_st e _ _ (conj Hi Vi) Vij).
exists J=>y m [e][He]Pe.
move: (Hi e He)=>Hi'.
case: (fr_st e _ _ (conj Hi' Vi) Vij)=>pf P; move: Pe.
rewrite (_ : relaxd (single (conj J Vij)) (pre_sup_leq He) = single (conj pf Vij));
  last by congr Ideal; apply: pf_irr.
case/P=>h' [E][V']P'.
exists h'; do!split=>//; exists e, He.
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
by exists J2; rewrite (pf_irr (bound J2) (bound pf1)).
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
- by move=>_ [e][->]; case: e=>e P; case: (P _ _ p Vi).
exists J=>y m /= [e][[[e1 P]]][/= E He1] H; subst e1.
set I' := (X in prog_of e X) in H.
case: (P _ _ p Vi)=>Hi; apply.
by rewrite (_ : single (conj Hi Vi) = I') //; congr Ideal; apply: pf_irr.
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

Definition f' (e : lat) :=
  sup [Pred t : lat | exists e', e' <== e /\ t = f e'].

Lemma f'_mono : monotone f'.
Proof.
move=>x y H; apply: sup_mono=>fz; case=>z [Hz {fz}->].
by exists z; split=>//; apply/poset_trans/H.
Qed.

Definition ffix : tp := tarski_lfp f'.

End Fix.

Lemma vrf_mono A i (e : ST A) (Q1 Q2 : post A) :
        Q1 <== Q2 -> vrf i e Q1 -> vrf i e Q2.
Proof.
move=>H H1 Vi; case: (H1 Vi)=>pf {}H1.
by exists pf=>y m /H1; apply: H.
Qed.

Lemma vrfV A i (e : ST A) (Q : post A) :
       (valid i -> vrf i e Q) -> vrf i e Q.
Proof. by move=>H V; apply: H. Qed.

Lemma vrf_frame A i j (e : ST A) (Q : post A) :
        vrf i e (fun y m => valid (m \+ j) -> Q y (m \+ j)) ->
        vrf (i \+ j) e Q.
Proof.
move=>H Vij; have Vi := validL Vij; case: (H Vi)=>Hi {}H.
case: (fr_st (conj Hi Vi) Vij)=>pf P.
exists pf=>y m.
case/P=>h [{m}->][Vhj {}P].
by apply: H.
Qed.

Lemma frame_star A i (e : ST A) (Q : post A) (r : Pred heap) :
  i \In (fun h => vrf h e Q) # r -> vrf i e (fun v => Q v # r).
Proof.
case=>h1[h2][{i}-> H1 H2].
apply: vrf_frame=>V1; case: (H1 V1)=>Hp Hr.
exists Hp=>y m Pm Vm2.
exists m, h2; split=>//.
by apply: Hr.
Qed.

Lemma vrf_post A i (e : ST A) (Q1 Q2 : post A) :
        (forall y m, valid m -> Q1 y m -> Q2 y m) ->
        vrf i e Q1 -> vrf i e Q2.
Proof.
move=>H H1 Vi; case: (H1 Vi)=>pf {}H1.
exists pf=>y m Hm.
by apply/H/H1=>//; exact: (dstr_valid Hm).
Qed.

Section Return.
Variables (A : Type) (x : A).

Definition ret_pre : pre := PredT.

Definition ret_prog : prog ret_pre A :=
  fun p y m =>
    m \In id_val p /\ y = Val x.

Lemma ret_coherent : coherent ret_prog.
Proof.
move=>p y m; split; first by case=>H {y}->; exists m, H.
by case=>i [Hi][{m}<-{y}->].
Qed.

Lemma ret_dstrict : def_strict ret_prog.
Proof. by case=>p H y /= []; case/H. Qed.

Lemma ret_frame : frameable ret_prog.
Proof.
move=>i j [[] Hv] Vij.
by exists I=>_ _ [<- ->]; exists i.
Qed.

Definition ret := Prog ret_coherent ret_dstrict ret_frame.

Lemma vrf_ret (Q : post A) i :
        Q (Val x) i -> vrf i ret Q.
Proof. by move=>Hi V; exists I=>_ _ [<- ->]. Qed.

End Return.

Section Throw.
Variables (A : Type) (e : exn).

Definition throw_pre : pre := PredT.

Definition throw_prog : prog throw_pre A :=
  fun p y m =>
    m \In id_val p /\ y = @Exn A e.

Lemma throw_coherent : coherent throw_prog.
Proof.
move=>p y m; split; first by case=>H {y}->; exists m, H.
by case=>i [Hi][{m}<-{y}->].
Qed.

Lemma throw_dstrict : def_strict throw_prog.
Proof. by case=>p H y /= []; case/H. Qed.

Lemma throw_frame : frameable throw_prog.
Proof.
move=>i j [[] Hv] Vij.
by exists I=>_ _ [<- ->]; exists i.
Qed.

Definition throw := Prog throw_coherent throw_dstrict throw_frame.

Lemma vrf_throw (Q : post A) i :
        Q (Exn e) i -> vrf i throw Q.
Proof. by move=>Hi V; exists I=>_ _ [<- ->]. Qed.

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
      exists pf : i \In defed (pre_of e1),
        h \In prog_of e1 (single pf) x /\
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
move=>i j [[Hi P] Hv] Vij; case: (fr_st Hi Vij)=>pf H.
have Hij : i \+ j \In bind_pre.
- exists (conj pf Vij)=>x _ /H [h][->][Vhj] /P {}P.
  have Hh : h \In defed (pre_of (e2 x)) by split=>//; apply: (validL Vhj).
  by case: (fr_st Hh Vhj).
exists Hij=>y m; case=>_[x][h][<-][{}Hij][Hh].
rewrite (pf_irr (conj pf Vij) Hij) in H.
case: x Hh=>[x|e] Hh.
- case=>Hh' Pm.
  case/H: Hh=>h1 [Eh][Vh]P1.
  rewrite Eh in Hh' Pm; move: (P _ _ P1)=>Hh1.
  have J1 : h1 \In defed (pre_of (e2 x)) by split=>//; apply: (validL Vh).
  case: (fr_st J1 Vh)=>pf1.
  rewrite (_ : single (conj pf1 Vh) = single Hh'); last by congr Ideal; apply: pf_irr.
  case/(_ _ _ Pm)=>h2[Em][Vm]Ph2.
  exists h2; do!split=>//; exists i, (Val x), h1; split=>//.
  by exists Hi; split=>//; exists J1.
case=>->->.
case/H: Hh=>h1[Eh][Vh]Ph1.
exists h1; do!split=>//; exists i, (Exn e), h1; split=>//.
by exists Hi.
Qed.

Definition bind := Prog bind_coherent bind_dstrict bind_frame.

Lemma vrf_bind (Q : post B) i :
        vrf i e1 (fun x m => match x with
                  | Val x' => vrf m (e2 x') Q
                  | Exn e => Q (Exn e) m
                  end) ->
        vrf i bind Q.
Proof.
move=>H Vi; case: (H Vi)=>Hi {}H /=.
have Hi' : i \In bind_pre.
- exists (conj Hi Vi)=>x m Pm.
  by case: (H _ _ Pm (dstr_valid Pm)).
exists Hi'=>y j /= [_][x][m][<-][{}Hi'][Pm]C.
rewrite (_ : single (conj Hi Vi) = single Hi') in H;
  last by congr Ideal; apply: pf_irr.
have Vm := dstr_valid Pm.
case: x Pm C=>[x|e] Pm.
- case=>Hm2 Pj.
  move: (H _ _ Pm); case/(_ Vm)=>Hm; apply.
  rewrite (_ : single (conj Hm Vm) = single Hm2) //.
  by congr Ideal; apply: pf_irr.
by case=>->->; apply: (H _ _ Pm).
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
      exists pf : i \In defed (pre_of e),
        h \In prog_of e (single pf) x /\
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
move=>i j [[Hi [P1 P2]] Vi] Vij; case: (fr_st Hi Vij)=>pf H.
have J : i \+ j \In try_pre.
- exists (conj pf Vij); split.
  - move=>x _ /H [h][->][Vhj] /P1 {}P1.
    have J' : h \In defed (pre_of (e1 x)) by split=>//; apply: (validL Vhj).
    by case: (fr_st J' Vhj).
  move=>ex _ /H [h][->][Vhj] /P2 {}P2.
  have J' : h \In defed (pre_of (e2 ex)) by split=>//; apply: (validL Vhj).
  by case: (fr_st J' Vhj).
exists J=>y m; case=>_[x][h1][<-][H0][H1].
rewrite (_ : single (conj pf Vij) = single H0) in H;
  last by congr Ideal; apply: pf_irr.
case: x H1=>[x|ex] H1.
- case=>H1' Po.
  case: (H _ _ H1)=>h'[E'][V']P'.
  rewrite E' in H1' Po; move: (P1 _ _ P')=>H1''.
  have J' : h' \In defed (pre_of (e1 x)) by split=>//; apply: (validL V').
  case: (fr_st J' V')=>pf2.
  rewrite (_ : single (conj pf2 V') = single H1');
    last by congr Ideal; apply: pf_irr.
  case/(_ _ _ Po)=>h''[E''][V'']P''.
  exists h''; do!split=>//.
  exists i, (Val x), h'=>/=; split=>//.
  by exists Hi; split=>//; exists J'.
case=>H1' Po.
case: (H _ _ H1)=>h'[E'][V']P'.
rewrite E' in H1' Po; move: (P2 _ _ P')=>H1''.
have J' : h' \In defed (pre_of (e2 ex)) by split=>//; apply: (validL V').
case: (fr_st J' V')=>pf2.
rewrite (_ : single (conj pf2 V') = single H1');
  last by congr Ideal; apply: pf_irr.
case/(_ _ _ Po)=>h''[E''][V'']P''.
exists h''; do!split=>//.
exists i, (Exn ex), h'=>/=; split=>//.
by exists Hi; split=>//; exists J'.
Qed.

Definition try := Prog try_coherent try_dstrict try_frame.

Lemma vrf_try (Q : post B) i :
        vrf i e (fun x m => match x with
                 | Val x' => vrf m (e1 x') Q
                 | Exn ex => vrf m (e2 ex) Q
                 end) ->
        vrf i try Q.
Proof.
move=>H Vi; case: (H Vi)=>pf P /=.
have J : i \In try_pre.
- exists (conj pf Vi); split=>x m Pm;
  by case: (P _ _ Pm (dstr_valid Pm)).
exists J=>y j /= [_][x][m][<-][pf'][Pm]F.
rewrite (_ : single (conj pf Vi) = single pf') in P;
  last by congr Ideal; apply: pf_irr.
have Vm := dstr_valid Pm.
case: x Pm F=>[x|ex] Pm.
- case=>Hm Hj.
  case: (P _ _ Pm Vm)=>pf''; apply.
  rewrite (_ : single (conj pf'' Vm) = single Hm) //.
  by congr Ideal; apply: pf_irr.
case=>Hm Hj.
case: (P _ _ Pm Vm)=>pf''; apply.
rewrite (_ : single (conj pf'' Vm) = single Hm) //.
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
have J : i \+ j \In read_pre.
- split; first by rewrite domUn inE Vij Hx.
  by exists v; rewrite findUnL // Hx.
exists J=>y m [/= <-][w][->]H.
exists i; do!split=>//; exists w; split=>//.
by rewrite findUnL // Hx in H.
Qed.

Definition read := Prog read_coherent read_dstrict read_frame.

Lemma vrf_read (Q : post A) (v : A) j :
       (valid (x :-> v \+ j) -> Q (Val v) (x :-> v \+ j)) ->
       vrf (x :-> v \+ j) read Q.
Proof.
move=>H Vi /=.
have J : x :-> v \+ j \In read_pre.
- split; first by rewrite domPtUnE.
  by exists v; rewrite findPtUn.
exists J=>_ _ [<-][w][->].
rewrite findPtUn //; case=>/inj_pair2 {w}<-.
by apply: H.
Qed.

End Read.


Section Write.
Variable (A : Type) (x : ptr) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition write_pre : pre :=
  fun i => x \in dom i.

Definition write_prog : prog write_pre unit :=
  fun p y m =>
    exists i, [/\ y = Val tt, m = upd x (idyn v) i,
                  i \In id_val p & x \in dom i].

Lemma write_coherent : coherent write_prog.
Proof.
move=>p y m; split.
- by case=>i [{y}-> {m}-> Hi Hx]; exists i, Hi, i.
by case=>i [Hi][_][{y}-> {m}-> <- Hx]; exists i.
Qed.

Lemma write_dstrict : def_strict write_prog.
Proof.
case=>p H y [i] /= [_ E Hi Hx].
suff L: valid (upd x (idyn v) i) by rewrite -E in L.
by rewrite validU (dom_cond Hx) (dom_valid Hx).
Qed.

Lemma write_frame : frameable write_prog.
Proof.
move=>i j [Hi Vi] Vij.
have J : i \+ j \In write_pre.
- by rewrite /write_pre -toPredE /= domUn inE Vij Hi.
exists J=>_ _ [_][->-> <- _]; exists (upd x (idyn v) i).
rewrite updUnL Hi validUUn //; do!split=>//.
by exists i.
Qed.

Definition write := Prog write_coherent write_dstrict write_frame.

Lemma vrf_write (Q : post unit) j B (u : B) :
        (valid (x :-> v \+ j) -> Q (Val tt) (x :-> v \+ j)) ->
        vrf (x :-> u \+ j) write Q.
Proof.
move=>H Vi /=.
have J : x :-> u \+ j \In write_pre.
- by rewrite /write_pre -toPredE /= domPtUnE.
exists J=>_ _ [_][->-> <- _].
rewrite updPtUn; apply: H.
by rewrite (@validPtUnE _ _ _ _ (idyn u)).
Qed.

End Write.


Section Allocation.
Variables (A : Type) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition alloc_pre : pre := PredT.

Definition alloc_prog : prog alloc_pre ptr :=
  fun p y m =>
    exists i l, [/\ y = Val l, m = l :-> v \+ i, i \In id_val p,
                    l != null & l \notin dom i].

Lemma alloc_coherent : coherent alloc_prog.
Proof.
move=>p x m; split.
- case=>i[l][{x}-> {m}-> Hi Hl1 Hl2].
  by exists i, Hi, i, l.
case=>i[Hi][_][l][{x}-> {m}-> <- Hl1 Hl2].
by exists i, l.
Qed.

Lemma alloc_dstrict : def_strict alloc_prog.
Proof.
case=>p H _ [/= i][l][_ Hu Hi Hl1 Hl2]; case/H: Hi=>_ {H}Vi.
suff {Hu}: valid (l :-> v \+ i) by rewrite -Hu.
by rewrite validPtUn; apply/and3P.
Qed.

Lemma alloc_frame : frameable alloc_prog.
Proof.
move=>i j [[]] Vi Vij.
exists I=>_ _ [_][x][-> -> <- Hx1 Hx2].
exists (x :-> v \+ i); rewrite -joinA; do!split=>//.
- rewrite validUnAE validPt domPtK Hx1 Vij /= all_predC.
  apply/hasP=>[[y Hy]]; rewrite !inE=>/eqP E.
  by move: Hy Hx2; rewrite E=>->.
exists i, x; split=>//.
by apply/dom_NNL/Hx2.
Qed.

Definition alloc := Prog alloc_coherent alloc_dstrict alloc_frame.

Lemma vrf_alloc (Q : post ptr) i :
  (forall x, valid (x :-> v \+ i) -> Q (Val x) (x :-> v \+ i)) ->
  vrf i alloc Q.
Proof.
move=>H Vi /=.
exists I=>_ _ [_][x][-> -> <- Hx Hx2].
by apply: H; rewrite validPtUn Hx Vi.
Qed.

End Allocation.


Section BlockAllocation.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_pre : pre := PredT.

Definition allocb_prog : prog allocb_pre ptr :=
  fun p y m =>
    exists i l, [/\ y = Val l, m = updi l (nseq n v) \+ i,
                    i \In id_val p & valid m].

Lemma allocb_coherent : coherent allocb_prog.
Proof.
move=>p x m; split.
- by case=>i [l][{x}-> {m}-> Hi V]; exists i, Hi, i, l.
by case=>i [Hi][_][l][{x}-> {m}-> <- V]; exists i, l.
Qed.

Lemma allocb_dstrict : def_strict allocb_prog.
Proof. by case=>p H y[m][/= l][]. Qed.

Lemma allocb_frame : frameable allocb_prog.
Proof.
move=>i j [[] Vi] Vij.
exists I=>y m [_][l][/= {y}-> {m}-> <- V].
exists (updi l (nseq n v) \+ i); rewrite -joinA; do!split=>//.
exists i, l; do!split=>//.
by rewrite joinA in V; apply: (validL V).
Qed.

Definition allocb := Prog allocb_coherent allocb_dstrict allocb_frame.

Lemma vrf_allocb (Q : post ptr) i :
        (forall x, valid (updi x (nseq n v) \+ i) ->
           Q (Val x) (updi x (nseq n v) \+ i)) ->
        vrf i allocb Q.
Proof.
move=>H Vi /=.
exists I=>y m [_][l][/= {y}-> {m}-> <- V].
by apply: H.
Qed.

End BlockAllocation.


Section Deallocation.
Variable x : ptr.

Definition dealloc_pre : pre :=
  fun i => x \in dom i.

Definition dealloc_prog (p : ideald dealloc_pre) (y : ans unit) m :=
  exists i, [/\ y = Val tt, m = free i x, i \In id_val p & x \in dom i].

Lemma dealloc_coherent : coherent dealloc_prog.
Proof.
move=>p y m; split.
- by case=>i [{y}-> {m}-> Hi Hx]; exists i, Hi, i.
by case=>i [Hi][_][{y}-> {m}-> <- Hx]; exists i.
Qed.

Lemma dealloc_dstrict : def_strict dealloc_prog.
Proof.
case=>p H _ [i][/= _ Hu Hi _]; case/H: Hi=> _ {H}Vi.
suff {Hu}: valid (free i x) by rewrite -Hu.
by rewrite validF.
Qed.

Lemma dealloc_frame : frameable dealloc_prog.
Proof.
move=>i j [Hi Vi] Vij.
have J: i \+ j \In dealloc_pre.
- by rewrite /dealloc_pre -toPredE /= domUn inE Vij Hi.
exists J=>_ _ [_][-> -> <- Hx].
exists (free i x); do!split.
- by apply/freeUnR/dom_inNL/Hi.
- by apply: validFUn.
by exists i.
Qed.

Definition dealloc :=
  Prog dealloc_coherent dealloc_dstrict dealloc_frame.

Lemma vrf_dealloc (Q : post unit) B (v : B) j:
        (x \notin dom j -> valid j -> Q (Val tt) j) ->
        vrf (x :-> v \+ j) dealloc Q.
Proof.
move=>H Vi /=.
have J: x :-> v \+ j \In dealloc_pre.
- by rewrite /dealloc_pre -toPredE /= domPtUnE.
exists J=>_ _ [_][-> -> <- Hx].
rewrite freePtUn //; apply: H; last by exact: (validR Vi).
by move: Hx; rewrite domPtUnE validPtUn; case/and3P.
Qed.

End Deallocation.

End Model.

(****************************************************)
(* Notation to move from binary posts to unary ones *)
(****************************************************)

Notation "'Do' e" := (@STprog _ _ _ e _) (at level 80).

Definition logbase A (p : pre) (q : post A) : spec unit A :=
  fun => (p, q).

Definition logvar {B A} (G : A -> Type) (s : forall x : A, spec (G x) B) :
             spec {x : A & G x} B :=
  fun '(existT x g) => s x g.

Notation "'STsep' ( p , q ) " := (STspec (logbase p q)) (at level 0).

Notation "{ x .. y }, 'STsep' ( p , q ) " :=
  (STspec (logvar (fun x => .. (logvar (fun y => logbase p q)) .. )))
   (at level 0, x binder, y binder, right associativity).

Notation "x '<--' c1 ';' c2" := (Model.bind c1 (fun x => c2))
  (at level 78, right associativity).
Notation "c1 ';;' c2" := (Model.bind c1 (fun _ => c2))
  (at level 78, right associativity).
Notation "'!' x" := (Model.read _ x) (at level 50).
Notation "e1 '::=' e2" := (Model.write e1 e2) (at level 60).
