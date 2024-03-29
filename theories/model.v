From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From pcm Require Import options axioms pred prelude.
From pcm Require Import pcm unionmap heap.
From htt Require Import domain.

(* Exceptions are an equality type *)
Inductive exn : Type := exn_from_nat of nat.

Definition exn_to_nat :=
  fun '(exn_from_nat y) => y.

Definition eqexn :=
  fun '(exn_from_nat m) '(exn_from_nat n) => m == n.

Lemma eqexnP : Equality.axiom eqexn.
Proof. by move=>[x][y]/=; case: eqP=>[->|*]; constructor=>//; case. Qed.

Canonical Structure exn_eqMixin := EqMixin eqexnP.
Canonical Structure exn_eqType := EqType exn exn_eqMixin.

(* Answer type *)
Inductive ans (A : Type) : Type := Val of A | Exn of exn.
Arguments Exn [A].

(* A set of heaps *)
Notation pre := (Pred heap).

(* A set of (ans A * heap) *)
(* This models the fact that programs can hang, returning nothing, *)
(* or produce nondeterministic results (e.g. alloc). *)
Notation post A := (ans A -> heap -> Prop).

Definition spec G A := G -> pre * post A : Type.

(*************************************************************)
(* List of inference rules, with vrf predicate kept abstract *)
(*************************************************************)

Module Type VrfSig.

Parameter ST : Type -> Type.

Parameter ret : forall A, A -> ST A.
Parameter throw : forall A, exn -> ST A.
Parameter bind : forall A B, ST A -> (A -> ST B) -> ST B.
Parameter try : forall A B, ST A -> (A -> ST B) -> (exn -> ST B) -> ST B.
Parameter read : forall A, ptr -> ST A.
Parameter write : forall A, ptr -> A -> ST unit.
Parameter alloc : forall A, A -> ST ptr.
Parameter allocb : forall A, A -> nat -> ST ptr.
Parameter dealloc : ptr -> ST unit.

Arguments throw [A] e.
Arguments read [A] x.

(* we need program to come first in the argument list
   so that automation can match on it *)
Parameter vrf' : forall A, ST A -> heap -> post A -> Prop.

(* recover the usual [pre]prog[post] order with a notation *)
Notation vrf i e Q := (vrf' e i Q).

Parameter vrfV : forall A e i (Q : post A),
            (valid i -> vrf i e Q) -> vrf i e Q.
Parameter vrf_post : forall A e i (Q1 Q2 : post A),
            (forall y m, valid m -> Q1 y m -> Q2 y m) ->
            vrf i e Q1 -> vrf i e Q2.
Parameter vrf_frame : forall A e i j (Q : post A),
            vrf i e (fun y m => valid (m \+ j) -> Q y (m \+ j)) ->
            vrf (i \+ j) e Q.
Parameter vrf_ret : forall A x i (Q : post A),
            (valid i -> Q (Val x) i) -> vrf i (ret x) Q.
Parameter vrf_throw : forall A e i (Q : post A),
            (valid i -> Q (Exn e) i) -> vrf i (throw e) Q.
Parameter vrf_bind : forall A B (e1 : ST A) (e2 : A -> ST B) i (Q : post B),
            vrf i e1 (fun x m =>
                        match x with
                        | Val x' => vrf m (e2 x') Q
                        | Exn e => valid m -> Q (Exn e) m
                        end) ->
            vrf i (bind e1 e2) Q.
Parameter vrf_try : forall A B (e : ST A) (e1 : A -> ST B) (e2 : exn -> ST B) i (Q : post B),
            vrf i e (fun x m =>
                       match x with
                       | Val x' => vrf m (e1 x') Q
                       | Exn ex => vrf m (e2 ex) Q
                       end) ->
            vrf i (try e e1 e2) Q.
Parameter vrf_read : forall A x j (v : A) (Q : post A),
            (valid (x :-> v \+ j) -> Q (Val v) (x :-> v \+ j)) ->
            vrf (x :-> v \+ j) (read x) Q.
Parameter vrf_write : forall A x (v : A) B (u : B) j (Q : post unit),
            (valid (x :-> v \+ j) -> Q (Val tt) (x :-> v \+ j)) ->
            vrf (x :-> u \+ j) (write x v) Q.
Parameter vrf_alloc : forall A (v : A) i (Q : post ptr),
            (forall x, valid (x :-> v \+ i) -> Q (Val x) (x :-> v \+ i)) ->
            vrf i (alloc v) Q.
Parameter vrf_allocb : forall A (v : A) n i (Q : post ptr),
            (forall x, valid (updi x (nseq n v) \+ i) ->
               Q (Val x) (updi x (nseq n v) \+ i)) ->
            vrf i (allocb v n) Q.
Parameter vrf_dealloc : forall x A (v : A) j (Q : post unit),
            (x \notin dom j -> valid j -> Q (Val tt) j) ->
            vrf (x :-> v \+ j) (dealloc x) Q.

Definition has_spec G A (s : spec G A) (e : ST A) :=
  forall g i, (s g).1 i -> vrf i e (s g).2.

Structure STspec G A (s : spec G A) := STprog {
  model :> ST A;
  _ : model \In has_spec s}.

Arguments STspec G [A] s.

Notation "'Do' e" := (@STprog _ _ _ e _) (at level 80).

Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2))
  (at level 81, right associativity).
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2))
  (at level 81, right associativity).
Notation "'!' x" := (read x) (at level 50).
Notation "x '::=' e" := (write x e) (at level 60).

Parameter Fix : forall G A (B : A -> Type) (s : forall x : A, spec G (B x)),
  ((forall x : A, STspec G (s x)) -> forall x : A, STspec G (s x)) ->
  forall x : A, STspec G (s x).

End VrfSig.


(********************************)
(* Definition of the Hoare type *)
(********************************)

Module Vrf : VrfSig.

Section BasePrograms.
Variables (P : pre) (A : Type).

(* we carve out the model out of the following base type *)
Definition prog : Type := forall i : heap, valid i -> i \In P -> post A.

(* we take only preconditions and progs with special properties *)
(* which we define next *)

(* safety monotonicity *)
Definition safe_mono :=
  forall i j, i \In P -> valid (i \+ j) -> i \+ j \In P.

(* defined heaps map to defined heaps *)
Definition def_strict (e : prog) :=
  forall i p v x, Heap.Undef \Notin e i v p x.

(* frame property *)
Definition frameable (e : prog) :=
  forall i j (pf : i \In P) (V : valid (i \+ j)) (pf' : i \+ j \In P) y m,
    e _ V pf' y m ->
    exists h, [/\ m = h \+ j, valid (h \+ j) & e _ (validL V) pf y h].

End BasePrograms.

Section STDef.
Variable (A : Type).

Structure ST' := Prog {
  pre_of : pre;
  prog_of : prog pre_of A;
  _ : safe_mono pre_of;
  _ : def_strict prog_of;
  _ : frameable prog_of}.

(* module field must be a definition, not structure *)
Definition ST := ST'.

Lemma sfm_st e : safe_mono (pre_of e).
Proof. by case: e. Qed.

Arguments prog_of : clear implicits.

Lemma dstr_st e : def_strict (prog_of e).
Proof. by case: e. Qed.

Corollary dstr_valid e i p v x m :
            m \In prog_of e i p v x -> valid m.
Proof. by case: m=>// /dstr_st. Qed.

Lemma fr_st e : frameable (prog_of e).
Proof. by case: e. Qed.

Arguments fr_st [e i j].

(* poset structure on ST *)

Definition st_leq e1 e2 :=
  exists pf : pre_of e2 <== pre_of e1,
  forall i (v : valid i) (p : i \In pre_of e2),
    prog_of e1 _ v (pf _ p) <== prog_of e2 _ v p.

Lemma st_refl e : st_leq e e.
Proof.
exists (poset_refl _)=>i V P y m.
by rewrite (pf_irr (poset_refl (pre_of e) i P) P).
Qed.

Lemma st_asym e1 e2 : st_leq e1 e2 -> st_leq e2 e1 -> e1 = e2.
Proof.
move: e1 e2=>[p1 e1 S1 D1 F1][p2 e2 S2 D2 F2]; rewrite /st_leq /=.
case=>E1 R1 [E2 R2].
move: (poset_asym E1 E2)=>?; subst p2.
have : e1 = e2.
- apply: fext=>i; apply: fext=>Vi; apply: fext=>Pi; apply: fext=>y; apply: fext=>m.
  move: (R2 i Vi Pi y m)=>{}R2; move: (R1 i Vi Pi y m)=>{}R1.
  apply: pext; split.
  - by move=>H1; apply: R1; rewrite (pf_irr (E1 i Pi) Pi).
  by move=>H2; apply: R2; rewrite (pf_irr (E2 i Pi) Pi).
move=>?; subst e2.
by congr Prog; apply: pf_irr.
Qed.

Lemma st_trans e1 e2 e3 : st_leq e1 e2 -> st_leq e2 e3 -> st_leq e1 e3.
Proof.
move: e1 e2 e3=>[p1 e1 S1 D1 F1][p2 e2 S2 D2 F2][p3 e3 S3 D3 F3].
case=>/= E1 R1 [/= E2 R2]; rewrite /st_leq /=.
have E3 := poset_trans E2 E1; exists E3=>i V P y m.
set P' := E2 i P.
move: (R1 i V P' y m)=>{}R1; move: (R2 i V P y m)=>{}R2.
move=>H1; apply/R2/R1.
by rewrite (pf_irr (E1 i P') (E3 i P)).
Qed.

(* bottom is a program that can always run but never returns (an endless loop) *)

Definition pre_bot : pre := top.

Definition prog_bot : prog pre_bot A :=
  fun _ _ _ _ => bot.

Lemma sfmono_bot : safe_mono pre_bot.
Proof. by []. Qed.

Lemma dstrict_bot : def_strict prog_bot.
Proof. by move=>*. Qed.

Lemma frame_bot : frameable prog_bot.
Proof. by []. Qed.

Definition st_bot := Prog sfmono_bot dstrict_bot frame_bot.

Lemma st_botP e : st_leq st_bot e.
Proof. by case: e=>p e S D F; exists (@pred_topP _ _)=>???; apply: botP. Qed.

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
  fun i V P y m => exists e (pf : e \In u),
    prog_of e _ V (pre_sup_leq pf P) y m.

Arguments prog_sup : clear implicits.

Lemma pre_sup_sfmono u : safe_mono (pre_sup u).
Proof.
move=>i j Pi Vij e He.
by apply: sfm_st=>//; apply: Pi.
Qed.

Lemma prog_sup_dstrict u : def_strict (prog_sup u).
Proof. by move=>i P V y; case; case=>p e S D F [H1] /D. Qed.

Lemma prog_sup_frame u : frameable (prog_sup u).
Proof.
move=>i j Pi Vij Pij y m [e][He]Pe.
have Pi' := Pi e He; have Pij' := Pij e He.
move: Pe; rewrite (pf_irr (pre_sup_leq He Pij) Pij').
case/(fr_st Pi' Vij Pij')=>h [{m}-> Vhj Ph].
exists h; split=>//; exists e, He.
by rewrite (pf_irr (pre_sup_leq He Pi) Pi').
Qed.

Definition st_sup u : ST :=
  Prog (@pre_sup_sfmono u) (@prog_sup_dstrict u) (@prog_sup_frame u).

Lemma st_supP u e : e \In u -> e <== st_sup u.
Proof.
case: e=>p e' S D F R.
exists (pre_sup_leq R)=>/=p0 y m H.
by exists (Prog S D F), R.
Qed.

Lemma st_supM u e :
  (forall e1, e1 \In u -> e1 <== e) -> st_sup u <== e.
Proof.
case: e=>p e S D F R.
have J : p <== pre_sup u.
- by move=>/= x Px e' pf; case: (R _ pf)=>/= + _; apply.
exists J=>i V P y m [e0][H0 Hm].
case: (R _ H0)=>/= Hx; apply.
by rewrite (pf_irr (Hx i P) (pre_sup_leq H0 (J i P))).
Qed.

Definition stLatticeMixin := LatticeMixin st_supP st_supM.
Canonical stLattice := Lattice ST stLatticeMixin.

End STDef.

Arguments prog_of [A].
Arguments sfm_st [A e i j].
Arguments dstr_st [A e i].
Arguments fr_st [A e i j].

Section STspecDef.
Variables (G A : Type) (s : spec G A).

(* strongest postcondition predicate transformer *)

Definition vrf' (e : ST A) i (Q : post A) :=
  forall (V : valid i),
    exists (pf : i \In pre_of e), forall y m,
      prog_of e _ V pf y m -> Q y m.

Notation vrf i e Q := (vrf' e i Q).

Definition has_spec (e : ST A) :=
  forall g i, (s g).1 i -> vrf i e (s g).2.

Structure STspec := STprog {
  model :> ST A;
  _ : model \In has_spec}.

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

Lemma st_bot_has_spec : @st_bot A \In has_spec.
Proof. by move=>g i H V /=; exists I. Qed.

Definition stsp_bot := STprog st_bot_has_spec.

Lemma stsp_botP e : stsp_leq stsp_bot e.
Proof. by case: e=>*; apply: botP. Qed.

Definition stspPosetMixin := PosetMixin stsp_botP stsp_refl stsp_asym stsp_trans.
Canonical stspPoset := Eval hnf in Poset STspec stspPosetMixin.

(* lattice structure on STspec *)

Definition st_sup' (u : Pred STspec) : ST A :=
  sup [Pred p | exists e, p = model e /\ e \In u].

Lemma st_sup_has_spec' u : st_sup' u \In has_spec.
Proof.
move=>g i p Vi.
have J : i \In pre_of (st_sup' u).
- by move=>_ [e][->]; case: e=>e P; case: (P _ _ p Vi).
exists J=>y m /= [e][[[e1 P]]][/= E He1] H; subst e1.
case: (P _ _ p Vi)=>Hi; apply.
set I' := (X in prog_of e _ Vi X) in H.
by rewrite (pf_irr Hi I').
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

Notation vrf i e Q := (vrf' e i Q).

(************************************)
(* modeling the language primitives *)
(************************************)

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

Definition Fix : tp := tarski_lfp f'.

(* fixed point constructor which requires explicit proof of monotonicity *)
Definition Fix' (pf : monotone (f : lat -> lat)) : tp :=
  tarski_lfp (f : lat -> lat).

End Fix.

Arguments Fix [G A B s] f x.
Arguments Fix' [G A B s] f pf x.


Section VrfLemmas.
Variables (A : Type) (e : ST A).

Lemma vrfV i (Q : post A) :
        (valid i -> vrf i e Q) -> vrf i e Q.
Proof. by move=>H V; apply: H. Qed.

Lemma vrf_post i (Q1 Q2 : post A) :
        (forall y m, valid m -> Q1 y m -> Q2 y m) ->
        vrf i e Q1 -> vrf i e Q2.
Proof.
move=>H H1 Vi; case: (H1 Vi)=>pf {}H1.
exists pf=>y m Hm.
by apply/H/H1=>//; exact: (dstr_valid Hm).
Qed.

Lemma vrf_frame i j (Q : post A) :
        vrf i e (fun y m => valid (m \+ j) -> Q y (m \+ j)) ->
        vrf (i \+ j) e Q.
Proof.
move=>H Vij; have Vi := validL Vij; case: (H Vi)=>Hi {}H.
have Hij := sfm_st Hi Vij.
exists Hij=>y m.
case/(fr_st Hi Vij Hij)=>h [{m}-> Vhj P].
apply: H=>//.
by rewrite (pf_irr Vi (validL Vij)).
Qed.

Lemma frame_star i (Q : post A) (r : Pred heap) :
        i \In (fun h => vrf h e Q) # r -> vrf i e (fun v => Q v # r).
Proof.
case=>h1[h2][{i}-> H1 H2].
apply: vrf_frame=>V1; case: (H1 V1)=>Hp Hr.
exists Hp=>y m Pm Vm2.
exists m, h2; split=>//.
by apply: Hr.
Qed.

End VrfLemmas.

Section Return.
Variables (A : Type) (x : A).

Definition ret_pre : pre := top.

Definition ret_prog : prog ret_pre A :=
  fun i _ _ y m =>
    m = i /\ y = Val x.

Lemma ret_sfmono : safe_mono ret_pre.
Proof. by []. Qed.

Lemma ret_dstrict : def_strict ret_prog.
Proof. by move=>i [] V _ /= [E _]; rewrite -E in V. Qed.

Lemma ret_frame : frameable ret_prog.
Proof. by move=>i j [Vij []] _ _ [-> ->]; exists i. Qed.

Definition ret := Prog ret_sfmono ret_dstrict ret_frame.

Lemma vrf_ret i (Q : post A) :
        (valid i -> Q (Val x) i) -> vrf i ret Q.
Proof. by move=>H V; exists I=>_ _ [->->]; apply: H. Qed.

End Return.

Section Throw.
Variables (A : Type) (e : exn).

Definition throw_pre : pre := top.

Definition throw_prog : prog throw_pre A :=
  fun i _ _ y m =>
    m = i /\ y = @Exn A e.

Lemma throw_sfmono : safe_mono throw_pre.
Proof. by []. Qed.

Lemma throw_dstrict : def_strict throw_prog.
Proof. by move=>i [] V _ /= [E _]; rewrite -E in V. Qed.

Lemma throw_frame : frameable throw_prog.
Proof. by move=>i j [Vij []] _ _ [-> ->]; exists i. Qed.

Definition throw := Prog throw_sfmono throw_dstrict throw_frame.

Lemma vrf_throw i (Q : post A) :
        (valid i -> Q (Exn e) i) -> vrf i throw Q.
Proof. by move=>H V; exists I=>_ _ [->->]; apply: H. Qed.

End Throw.

Section Bind.
Variables (A B : Type).
Variables (e1 : ST A) (e2 : A -> ST B).

Definition bind_pre : pre :=
  fun i =>
    exists (Vi : valid i) (Pi : i \In pre_of e1),
      forall x m, prog_of e1 _ Vi Pi (Val x) m -> pre_of (e2 x) m.

Definition bind_pre_proj i : i \In bind_pre -> i \In pre_of e1 :=
  fun '(ex_intro _ (ex_intro p _)) => p.

Definition bind_prog : prog bind_pre B :=
  fun i V P y m =>
    exists x h (Ph : h \In prog_of e1 _ V (bind_pre_proj P) x),
      match x with
      | Val x' => exists Ph' : h \In pre_of (e2 x'),
                    m \In prog_of (e2 x') _ (dstr_valid Ph) Ph' y
      | Exn e => y = Exn e /\ m = h
      end.

Lemma bind_sfmono : safe_mono bind_pre.
Proof.
move=>i j [Vi][Pi]P Vij.
have Pij := sfm_st Pi Vij.
exists Vij, Pij=>x m.
case/(fr_st Pi Vij Pij)=>h [{m}-> Vhj].
rewrite (pf_irr (validL Vij) Vi)=>/P Ph.
by apply: sfm_st=>//; apply: (validL Vhj).
Qed.

Lemma bind_dstrict : def_strict bind_prog.
Proof.
move=>i [Vi][Pi P] Vi' y[x][h][/=].
case: x=>[x|e]Ph.
- by case=>Ph' /dstr_st.
by case=>_; move: Ph=>/[swap]<- /dstr_st.
Qed.

Lemma bind_frame : frameable bind_prog.
Proof.
move=>i j [Vi][Pi P] Vij [_ [Pij _]] y m [x][h][/=].
move: (fr_st Pi Vij Pij)=>H.
case: x=>[x|e] Ph.
- case=>Ph'.
  case: (H _ _ Ph)=>h1[Eh V1 Ph1]; subst h.
  rewrite (pf_irr (validL Vij) Vi) in Ph1 *; move: (P _ _  Ph1)=> P21.
  rewrite (pf_irr (dstr_valid Ph) V1).
  case/(fr_st P21 V1 Ph')=>h2[Em Vm Ph2].
  exists h2; split=>//; exists (Val x), h1, Ph1, P21.
  by rewrite (pf_irr (dstr_valid Ph1) (validL V1)).
case=>->->.
case/H: Ph=>h1[Eh Vh Ph1].
by exists h1; split=>//; exists (Exn e), h1, Ph1.
Qed.

Definition bind := Prog bind_sfmono bind_dstrict bind_frame.

Lemma vrf_bind i (Q : post B) :
        vrf i e1 (fun x m =>
                    match x with
                    | Val x' => vrf m (e2 x') Q
                    | Exn e => valid m -> Q (Exn e) m
                    end) ->
        vrf i bind Q.
Proof.
move=>H Vi; case: (H Vi)=>Hi {}H /=.
have Hi' : i \In bind_pre.
- by exists Vi, Hi=>x m Pm; case: (H _ _ Pm (dstr_valid Pm)).
exists Hi'=>y j /= [x][m][Pm] C.
rewrite (pf_irr Hi (bind_pre_proj Hi')) in H.
case: x Pm C=>[x|e] Pm; move: (H _ _ Pm (dstr_valid Pm))=>{}H.
- by case=>Pm2 Pj; case: H=>Pm2'; apply; rewrite (pf_irr Pm2' Pm2).
by case=>->->.
Qed.

End Bind.

Section Try.
Variables (A B : Type).
Variables (e : ST A) (e1 : A -> ST B) (e2 : exn -> ST B).

Definition try_pre : pre :=
  fun i =>
    exists (Vi : valid i) (Pi : i \In pre_of e),
      (forall y  m, prog_of e _ Vi Pi (Val y)  m -> pre_of (e1 y)  m) /\
       forall ex m, prog_of e _ Vi Pi (Exn ex) m -> pre_of (e2 ex) m.

Definition try_pre_proj i : i \In try_pre -> i \In pre_of e :=
  fun '(ex_intro _ (ex_intro p _)) => p.

Definition try_prog : prog try_pre B :=
  fun i V P y m =>
    exists x h (Ph : h \In prog_of e i V (try_pre_proj P) x),
      match x with
      | Val x' => exists (Ph' : h \In pre_of (e1 x')),
                    m \In prog_of (e1 x') _ (dstr_valid Ph) Ph' y
      | Exn ex => exists (Ph' : h \In pre_of (e2 ex)),
                    m \In prog_of (e2 ex) _ (dstr_valid Ph) Ph' y
      end.

Lemma try_sfmono : safe_mono try_pre.
Proof.
move=>i j [Vi [Pi][E1 E2]] Vij.
have Pij := sfm_st Pi Vij.
exists Vij, Pij; split.
- move=>y m.
  case/(fr_st Pi Vij Pij)=>h [{m}-> Vhj].
  rewrite (pf_irr (validL Vij) Vi)=>/E1 Ph.
  by apply: sfm_st=>//; apply: (validL Vhj).
move=>ex m.
case/(fr_st Pi Vij Pij)=>h [{m}-> Vhj].
rewrite (pf_irr (validL Vij) Vi)=>/E2 Ph.
by apply: sfm_st=>//; apply: (validL Vhj).
Qed.

Lemma try_dstrict : def_strict try_prog.
Proof.
move=>i [Vi [Pi][E1 E2]] Vi' y[x][h][/=].
by case: x=>[x|ex] Eh; case=>Ph /dstr_st.
Qed.

Lemma try_frame : frameable try_prog.
Proof.
move=>i j [Vi [Pi][E1 E2]] Vij [_ [Pij _]] y m [x][h][/=].
move: (fr_st Pi Vij Pij)=>H.
case: x=>[x|ex] Ph.
- case=>Ph'.
  case: (H _ _ Ph)=>h1[Eh V1 Ph1]; subst h.
  rewrite (pf_irr (validL Vij) Vi) in Ph1 *; move: (E1 _ _  Ph1)=>P21.
  rewrite (pf_irr (dstr_valid Ph) V1).
  case/(fr_st P21 V1 Ph')=>h2[Em Vm Ph2].
  exists h2; split=>//; exists (Val x), h1, Ph1, P21.
  by rewrite (pf_irr (dstr_valid Ph1) (validL V1)).
case=>Ph'.
case: (H _ _ Ph)=>h1[Eh V1 Ph1]; subst h.
rewrite (pf_irr (validL Vij) Vi) in Ph1 *; move: (E2 _ _  Ph1)=> P21.
rewrite (pf_irr (dstr_valid Ph) V1).
case/(fr_st P21 V1 Ph')=>h2[Em Vm Ph2].
exists h2; split=>//; exists (Exn ex), h1, Ph1, P21.
by rewrite (pf_irr (dstr_valid Ph1) (validL V1)).
Qed.

Definition try := Prog try_sfmono try_dstrict try_frame.

Lemma vrf_try i (Q : post B) :
        vrf i e (fun x m =>
                   match x with
                   | Val x' => vrf m (e1 x') Q
                   | Exn ex => vrf m (e2 ex) Q
                   end) ->
        vrf i try Q.
Proof.
move=>H Vi; case: (H Vi)=>pf {}H /=.
have J : i \In try_pre.
- by exists Vi, pf; split=>x m Pm; case: (H _ _ Pm (dstr_valid Pm)).
exists J=>y j /= [x][m][Pm]F.
rewrite (pf_irr pf (try_pre_proj J)) in H.
case: x Pm F=>[x|ex] Pm [Hm Hj];
case: (H _ _ Pm (dstr_valid Pm))=>pf''; apply;
by rewrite (pf_irr pf'' Hm).
Qed.

End Try.

(* don't export, just for fun *)
Lemma bnd_is_try A B (e1 : ST A) (e2 : A -> ST B) i r :
        vrf i (try e1 e2 (throw B)) r ->
        vrf i (bind e1 e2) r.
Proof.
move=>H Vi; case: (H Vi)=>[[Vi'][P1 /= [E1 E2]]] {}H.
have J : i \In pre_of (bind e1 e2).
- exists Vi, P1=>y m.
  by rewrite (pf_irr Vi Vi')=>/E1.
exists J=>y m /= [x][h][Ph]C.
apply: H; exists x, h=>/=.
rewrite (pf_irr P1 (bind_pre_proj J)) in E2 *; exists Ph.
move: Ph C; case: x=>// e Ph [{y}-> {m}->].
rewrite (pf_irr Vi' Vi) in E2.
by exists (E2 _ _ Ph).
Qed.

Section Read.
Variable (A : Type) (x : ptr).

Local Notation idyn v := (@dyn _ id _ v).

Definition read_pre : pre :=
  fun i => x \in dom i /\ exists v : A, find x i = Some (idyn v).

Definition read_prog : prog read_pre A :=
  fun i _ _ y m =>
    exists w, [/\ m = i, y = Val w & find x m = Some (idyn w)].

Lemma read_sfmono : safe_mono read_pre.
Proof.
move=>i j [Hx [v E]] Vij; split.
- by rewrite domUn inE Vij Hx.
by exists v; rewrite findUnL // Hx.
Qed.

Lemma read_dstrict : def_strict read_prog.
Proof. by move=>i _ Vi _ [_ [E _ _]]; rewrite -E in Vi. Qed.

Lemma read_frame : frameable read_prog.
Proof.
move=>i j [Hx [v E]] Vij _ _ _ [w [-> -> H]].
exists i; split=>//; exists w; split=>{v E}//.
by rewrite findUnL // Hx in H.
Qed.

Definition read := Prog read_sfmono read_dstrict read_frame.

Lemma vrf_read j (v : A) (Q : post A) :
       (valid (x :-> v \+ j) -> Q (Val v) (x :-> v \+ j)) ->
       vrf (x :-> v \+ j) read Q.
Proof.
move=>H Vi /=.
have J : x :-> v \+ j \In read_pre.
- split; first by rewrite domPtUnE.
  by exists v; rewrite findPtUn.
exists J=>_ _ [w [->->]].
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
  fun i _ _ y m =>
    [/\ y = Val tt, m = upd x (idyn v) i & x \in dom i].

Lemma write_sfmono : safe_mono write_pre.
Proof.
move=>i j; rewrite /write_pre -!toPredE /= => Hx Vij.
by rewrite domUn inE Vij Hx.
Qed.

Lemma write_dstrict : def_strict write_prog.
Proof.
move=>i Hx _ _ [_ E _]; rewrite /write_pre -toPredE /= in Hx.
suff {E}: valid (upd x (idyn v) i) by rewrite -E.
by rewrite validU (dom_cond Hx) (dom_valid Hx).
Qed.

Lemma write_frame : frameable write_prog.
Proof.
move=>i j Hx Vij _ _ _ [-> -> _].
exists (upd x (idyn v) i); split=>//;
rewrite /write_pre -toPredE /= in Hx.
- by rewrite updUnL Hx.
by rewrite validUUn.
Qed.

Definition write := Prog write_sfmono write_dstrict write_frame.

Lemma vrf_write B (u : B) j (Q : post unit) :
        (valid (x :-> v \+ j) -> Q (Val tt) (x :-> v \+ j)) ->
        vrf (x :-> u \+ j) write Q.
Proof.
move=>H Vi /=.
have J : x :-> u \+ j \In write_pre.
- by rewrite /write_pre -toPredE /= domPtUnE.
exists J=>_ _ [->-> _].
rewrite updPtUn; apply: H.
by rewrite (@validPtUnE _ _ _ _ (idyn u)).
Qed.

End Write.

Section Allocation.
Variables (A : Type) (v : A).

Local Notation idyn v := (@dyn _ id _ v).

Definition alloc_pre : pre := top.

Definition alloc_prog : prog alloc_pre ptr :=
  fun i _ _ y m =>
    exists l, [/\ y = Val l, m = l :-> v \+ i,
                  l != null & l \notin dom i].

Lemma alloc_sfmono : safe_mono alloc_pre.
Proof. by []. Qed.

Lemma alloc_dstrict : def_strict alloc_prog.
Proof.
move=>i [] Vi _ [l][_ E Hl Hl2].
suff {E}: valid (l :-> v \+ i) by rewrite -E.
by rewrite validPtUn; apply/and3P.
Qed.

Lemma alloc_frame : frameable alloc_prog.
Proof.
move=>i j [] Vij [] _ _ [l][->-> Hl Hl2].
exists (l :-> v \+ i); rewrite -joinA; split=>//.
- rewrite validUnAE validPt domPtK Hl Vij /= all_predC.
  apply/hasP=>[[y Hy]]; rewrite !inE=>/eqP E.
  by move: Hy Hl2; rewrite E=>->.
exists l; split=>//.
by apply/dom_NNL/Hl2.
Qed.

Definition alloc := Prog alloc_sfmono alloc_dstrict alloc_frame.

Lemma vrf_alloc i (Q : post ptr) :
        (forall x, valid (x :-> v \+ i) -> Q (Val x) (x :-> v \+ i)) ->
        vrf i alloc Q.
Proof.
move=>H Vi /=.
exists I=>_ _ [x][-> -> Hx Hx2].
by apply: H; rewrite validPtUn Hx Vi.
Qed.

End Allocation.

Section BlockAllocation.
Variables (A : Type) (v : A) (n : nat).

Definition allocb_pre : pre := top.

Definition allocb_prog : prog allocb_pre ptr :=
  fun i _ _ y m =>
    exists l, [/\ y = Val l, m = updi l (nseq n v) \+ i & valid m].

Lemma allocb_sfmono : safe_mono allocb_pre.
Proof. by []. Qed.

Lemma allocb_dstrict : def_strict allocb_prog.
Proof. by move=>i [] Vi y [l][]. Qed.

Lemma allocb_frame : frameable allocb_prog.
Proof.
move=>i j [] Vij [] _ _ [l][->-> V].
exists (updi l (nseq n v) \+ i); rewrite -joinA; split=>//.
exists l; split=>//.
by rewrite joinA in V; apply: (validL V).
Qed.

Definition allocb := Prog allocb_sfmono allocb_dstrict allocb_frame.

Lemma vrf_allocb i (Q : post ptr) :
        (forall x, valid (updi x (nseq n v) \+ i) ->
           Q (Val x) (updi x (nseq n v) \+ i)) ->
        vrf i allocb Q.
Proof.
move=>H Vi /=.
exists I=>_ _ [l][->-> V].
by apply: H.
Qed.

End BlockAllocation.

Section Deallocation.
Variable x : ptr.

Definition dealloc_pre : pre :=
  fun i => x \in dom i.

Definition dealloc_prog : prog dealloc_pre unit :=
  fun i _ _ y m =>
    [/\ y = Val tt, m = free i x & x \in dom i].

Lemma dealloc_sfmono : safe_mono dealloc_pre.
Proof.
move=>i j; rewrite /dealloc_pre -!toPredE /= => Hx Vij.
by rewrite domUn inE Vij Hx.
Qed.

Lemma dealloc_dstrict : def_strict dealloc_prog.
Proof.
move=>i _ Vi _ [_ E _].
suff {E}: valid (free i x) by rewrite -E.
by rewrite validF.
Qed.

Lemma dealloc_frame : frameable dealloc_prog.
Proof.
move=>i j Hx Vij Hx' _ _ [->-> _].
exists (free i x); split=>//;
rewrite /dealloc_pre -!toPredE /= in Hx Hx'.
- by apply/freeUnR/dom_inNL/Hx.
by apply: validFUn.
Qed.

Definition dealloc :=
  Prog dealloc_sfmono dealloc_dstrict dealloc_frame.

Lemma vrf_dealloc A (v : A) j (Q : post unit) :
        (x \notin dom j -> valid j -> Q (Val tt) j) ->
        vrf (x :-> v \+ j) dealloc Q.
Proof.
move=>H Vi /=.
have J: x :-> v \+ j \In dealloc_pre.
- by rewrite /dealloc_pre -toPredE /= domPtUnE.
exists J=>_ _ [->-> Hx].
rewrite freePtUn //; apply: H; last by exact: (validR Vi).
by move: Hx; rewrite domPtUnE validPtUn; case/and3P.
Qed.

End Deallocation.

(* Monotonicity of the constructors *)

Section Monotonicity.

Variables (A B : Type).

Lemma do_mono G (e1 e2 : ST A) (s : spec G A)
        (pf1 : has_spec s e1) (pf2 : has_spec s e2) :
        e1 <== e2 -> @STprog _ _ _ e1 pf1 <== @STprog _ _ _ e2 pf2.
Proof. by []. Qed.

Lemma bind_mono (e1 e2 : ST A) (k1 k2 : A -> ST B) :
        e1 <== e2 -> k1 <== k2 -> (bind e1 k1 : ST B) <== bind e2 k2.
Proof.
move=>[H1 H2] pf2.
have pf: bind_pre e2 k2 <== bind_pre e1 k1.
- move=>h [Vh][Pi] H.
  exists Vh, (H1 _ Pi)=>x m /H2/H H'.
  by case: (pf2 x)=>+ _; apply.
exists pf=>i Vi /[dup][[Vi'][Pi']P'] Pi x h.
case; case=>[a|e][h0][Ph][Ph'] H.
- exists (Val a), h0.
  move: (H2 i Vi (bind_pre_proj Pi))=>H'.
  rewrite (pf_irr (H1 i (bind_pre_proj Pi)) (bind_pre_proj (pf i Pi))) in H'.
  have Ph0 := (H' _ _ Ph); exists Ph0.
  move: (P' a h0); rewrite (pf_irr Vi' Vi) (pf_irr Pi' (bind_pre_proj Pi))=>H''.
  exists (H'' Ph0); case: (pf2 a)=>Pr; apply.
  by rewrite (pf_irr (dstr_valid Ph0) (dstr_valid Ph)) (pf_irr (Pr h0 (H'' Ph0)) Ph').
rewrite Ph' H; exists (Exn e), h0.
move: (H2 i Vi (bind_pre_proj Pi))=>H'.
rewrite (pf_irr (H1 i (bind_pre_proj Pi)) (bind_pre_proj (pf i Pi))) in H'.
by exists (H' _ _ Ph).
Qed.

Lemma try_mono (e1 e2 : ST A) (k1 k2 : A -> ST B) (h1 h2 : exn -> ST B) :
        e1 <== e2 -> k1 <== k2 -> h1 <== h2 ->
        (try e1 k1 h1 : ST B) <== try e2 k2 h2.
Proof.
move=>[H1 H2] pf2 pf3.
have pf: try_pre e2 k2 h2 <== try_pre e1 k1 h1.
- move=>h [Vh][Pi] [Hk Hn].
  exists Vh, (H1 _ Pi); split.
  - move=>x m /H2/Hk H'.
    by case: (pf2 x)=>+ _; apply.
  move=>ex m /H2/Hn H'.
  by case: (pf3 ex)=>+ _; apply.
exists pf =>i Vi /[dup][[Vi'][Pi'][Pk0 Ph0]] Pi x h.
case; case=>[a|e][h0][Ph][Ph'] H.
- exists (Val a), h0.
  move: (H2 i Vi (try_pre_proj Pi))=>H'.
  rewrite (pf_irr (H1 i (try_pre_proj Pi)) (try_pre_proj (pf i Pi))) in H'.
  have Ph1 := (H' _ _ Ph); exists Ph1.
  move: (Pk0 a h0); rewrite (pf_irr Vi' Vi) (pf_irr Pi' (try_pre_proj Pi))=>H''.
  exists (H'' Ph1); case: (pf2 a)=>Pr; apply.
  by rewrite (pf_irr (dstr_valid Ph1) (dstr_valid Ph)) (pf_irr (Pr h0 (H'' Ph1)) Ph').
exists (Exn e), h0.
move: (H2 i Vi (try_pre_proj Pi))=>H'.
rewrite (pf_irr (H1 i (try_pre_proj Pi)) (try_pre_proj (pf i Pi))) in H'.
have Ph1 := (H' _ _ Ph); exists Ph1.
move: (Ph0 e h0); rewrite (pf_irr Vi' Vi) (pf_irr Pi' (try_pre_proj Pi))=>H''.
exists (H'' Ph1); case: (pf3 e)=>Pr; apply.
by rewrite (pf_irr (dstr_valid Ph1) (dstr_valid Ph)) (pf_irr (Pr h0 (H'' Ph1)) Ph').
Qed.

(* the rest of the  constructors are trivial *)
Lemma ret_mono (v1 v2 : A) :
        v1 = v2 -> (ret v1 : ST A) <== ret v2.
Proof. by move=>->. Qed.

Lemma throw_mono (e1 e2 : exn) :
        e1 = e2 -> (throw A e1 : ST A) <== throw A e2.
Proof. by move=>->. Qed.

Lemma read_mono (p1 p2 : ptr) :
        p1 = p2 -> (read A p1 : ST A) <== read A p2.
Proof. by move=>->. Qed.

Lemma write_mono (p1 p2 : ptr) (x1 x2 : A) :
        p1 = p2 -> x1 = x2 -> (write p1 x1 : ST unit) <== write p2 x2.
Proof. by move=>->->. Qed.

Lemma alloc_mono (x1 x2 : A) :
        x1 = x2 -> (alloc x1 : ST ptr) <== alloc x2.
Proof. by move=>->. Qed.

Lemma allocb_mono (x1 x2 : A) (n1 n2 : nat) :
        x1 = x2 -> n1 = n2 -> (allocb x1 n1 : ST ptr) <== allocb x2 n2.
Proof. by move=>->->. Qed.

Lemma dealloc_mono (p1 p2 : ptr) :
        p1 = p2 -> (dealloc p1 : ST unit) <== dealloc p2.
Proof. by move=>->. Qed.

Variables (G : Type) (C : A -> Type) (s : forall x, spec G (C x)).
Notation lat := (dfunLattice (fun x => [lattice of STspec (s x)])).

Lemma fix_mono (f1 f2 : lat -> lat) : f1 <== f2 -> (Fix f1 : lat) <== Fix f2.
Proof.
move=>Hf; apply: tarski_lfp_mono.
- move=>x1 x2 Hx; apply: supM=>z [x][H ->]; apply: supP; exists x.
  by split=>//; apply: poset_trans H Hx.
move=>y; apply: supM=>_ [x][H1 ->].
by apply: poset_trans (Hf x) _; apply: supP; exists x.
Qed.

End Monotonicity.

Section MonotonicityExamples.

Notation "'Do' e" := (@STprog _ _ _ e _) (at level 80).

Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2))
  (at level 81, right associativity).
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2))
  (at level 81, right associativity).
Notation "'!' x" := (read x) (at level 50).
Notation "x '::=' e" := (write x e) (at level 60).

Fixpoint fact (x : nat) := if x is x'.+1 then x * fact x' else 1.

Definition facttp := forall x : nat, @STspec unit nat
  (fun => (fun i => True, 
   fun v m => if v is Val w then w = fact x else False)).

(* for the example, we need a quick lemma for function calls *)
(* this need not be exported, as it follows from the signature *)
(* will reprove it outside of the module *)

Lemma gE G A (s : spec G A) g i (e : @STspec G A s) (Q : post A) : 
        (s g).1 i ->
        (forall v m, (s g).2 (Val v) m ->
           valid m -> Q (Val v) m) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid m -> Q (Exn x) m) ->
        vrf i e Q.
Proof.
case: e=>e /= /[apply] Hp Hv He; apply: vrfV=>V /=.
by apply/vrf_post/Hp; case=>[v|ex] m Vm H; [apply: Hv | apply: He].
Qed.

(* now we can do the example with monotonicity explicitly *)

Program Definition factx :=
  Fix' (fun (loop : facttp) (x : nat) =>
    Do (if x is x'.+1 then
          t <-- loop x'; 
          ret (x * t)
        else ret 1)) _.
Next Obligation.
case=>i /= _; case: x; first by apply: vrf_ret.
by move=>n; apply: vrf_bind=>//; apply: gE=>// x m -> _; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H; case=>[|n]; first by apply: poset_refl.
by apply: do_mono; apply: bind_mono=>//; apply: H.
Qed.

(* Monotonocity works even if we compute *)
(* with propositions, and deliberately invert the polarity. *)

Definition proptp := unit -> @STspec unit Prop
  (fun => (fun i => True, fun R m => True)).

Program Definition propx := 
  Fix' (fun (loop : proptp) (x : unit) =>
    Do (R <-- loop tt; ret (not R))) _.
Next Obligation.
case=>i _; apply: vrf_bind=>//.
by apply: gE=>//= R m _ C; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H /= n; apply: do_mono; apply: bind_mono=>//. 
by apply: H.
Qed.

Definition proptp2 := Prop -> @STspec unit Prop 
  (fun => (fun i => True, fun (Ro : ans Prop) m => True)).

Program Definition propx2 := 
  Fix' (fun (loop : proptp2) (x : Prop) =>
    Do (R <-- loop (x -> x); ret R)) _ True.
Next Obligation.
case=>i /= _; apply: vrf_bind=>//.
by apply: gE=>//= R m _ _; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H /= n; apply: do_mono. 
by apply: bind_mono=>//; apply: H.
Qed.

Definition proptp3 := forall R : Prop, @STspec unit Prop 
  (fun => (fun i => True, 
           fun (Ro : ans Prop) m => if Ro is Val Ro' then Ro' else False)).

Program Definition propx3 := 
  Fix' (fun (loop : proptp3) (x : Prop) =>
    Do (R <-- loop (x -> x); ret R)) _ True.
Next Obligation.
case=>i /= _; apply: vrf_bind=>//.
by apply: gE=>//= R m X _; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H /= n; apply: do_mono.
by apply: bind_mono=>//; apply: H.
Qed.

(* It seems safe to say that monotonicity is always easy *)
(* to prove for all the programs that we expect to write. *)
(* Thus, we will export Fix over monotone closure, but not Fix'. *)
(* Exporting Fix has the advantage of eliding the always simple *)
(* and syntax-directed proofs of monotonicity, which we just don't *)
(* want to bother with. *)

(* This is in line with the existing proofs of soundness of HTT as a *)
(* standalone theory, where you can show that all functions that can be *)
(* produced using the syntax are monotone in the model. That proof *)
(* relied on a significant subset of Coq, but still a subset. *)

(* The paper is: *)
(* Partiality, State and Dependent Types *)
(* Kasper Svendsen, Lars Birkedal and Aleksandar Nanevski *)
(* International Conference on Typed Lambda Calculi and Applications (TLCA) *)
(* pages 198-212, 2011. *)

(* The model in that paper, and the one we use here, are quite different *)
(* however, and we can't exclude concocting a *)
(* non-monotone program using the syntax we export here, *)
(* based on the results of that other paper. *)
(* That said, we have so far failed to do produce such a non-monotone function. *)
(* But if such a case arises, we should switch to using Fix' *)
(* and ask for explicit proofs of monotonicity. *)
(* For all the examples we did so far, such a proof is easily *)
(* constructed, along the above lines (moreover, such proofs ought to be automatable) *)
(* Perhaps a proof, in the theory of Coq, that all functions are monotone *)
(* can be produced if we worked from parametricity properties of Coq, *)
(* which have been established in the past work, and even internalized *)
(* into Coq by means of parametricity axioms. But that remains future work. *)

End MonotonicityExamples.

End Vrf.

Export Vrf.

Definition skip := ret tt.

Corollary vrf_mono A (e : ST A) i : monotone (vrf' e i).
Proof. by move=>/= Q1 Q2 H; apply: vrf_post=>y m _; apply: H. Qed.


(******************************************)
(* Notation for logical variable postexts *)
(******************************************)

Definition logbase A (p : pre) (q : post A) : spec unit A :=
  fun => (p, q).

Definition logvar {B A} (G : A -> Type) (s : forall x : A, spec (G x) B) :
             spec {x : A & G x} B :=
  fun '(existT x g) => s x g.

Notation "'STsep' ( p , q ) " := (STspec unit (logbase p q)) (at level 0).

Notation "{ x .. y }, 'STsep' ( p , q ) " :=
  (STspec _ (logvar (fun x => .. (logvar (fun y => logbase p q)) .. )))
   (at level 0, x binder, y binder, right associativity).

(************************************************************)
(* Lemmas for pulling out and instantiating ghost variables *)
(************************************************************)

(* Lemmas without framing, i.e. they pass the entire heap to the *)
(* routine being invoked.                                        *)

Lemma gE G A (s : spec G A) g i (e : STspec G s) (Q : post A) :
        (s g).1 i ->
        (forall v m, (s g).2 (Val v) m ->
           valid m -> Q (Val v) m) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid m -> Q (Exn x) m) ->
        vrf i e Q.
Proof.
case: e=>e /= /[apply] Hp Hv He; apply: vrfV=>V /=.
by apply/vrf_post/Hp; case=>[v|ex] m Vm H; [apply: Hv | apply: He].
Qed.

Arguments gE [G A s] g [i e Q] _ _.

Notation "[gE]" := (gE tt) (at level 0).

Notation "[ 'gE' x1 , .. , xn ]" :=
  (gE (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'gE'  x1 ,  .. ,  xn ]").

(* a combination of gE + vrf_bind, for "stepping over" the call *)
Lemma stepE G A B (s : spec G A) g i (e : STspec G s) (e2 : A -> ST B) (Q : post B) :
        (s g).1 i ->
        (forall x m, (s g).2 (Val x) m -> vrf m (e2 x) Q) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid m -> Q (Exn x) m) ->
        vrf i (bind e e2) Q.
Proof.
move=>Hp Hv He.
by apply/vrf_bind/(gE _ Hp)=>[v m P|x m P _] V; [apply: Hv | apply: He].
Qed.

Arguments stepE [G A B s] g [i e e2 Q] _ _.

Notation "[stepE]" := (stepE tt) (at level 0).

Notation "[ 'stepE' x1 , .. , xn ]" :=
  (stepE (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'stepE'  x1 ,  .. ,  xn ]").

(* a combination of gE + vrf_try *)
Lemma tryE G A B (s : spec G A) g i (e : STspec G s) (e1 : A -> ST B) (e2 : exn -> ST B) (Q : post B) :
        (s g).1 i ->
        (forall x m, (s g).2 (Val x) m -> vrf m (e1 x) Q) ->
        (forall x m, (s g).2 (Exn x) m -> vrf m (e2 x) Q) ->
        vrf i (try e e1 e2) Q.
Proof.
move=>Hp Hv Hx.
by apply/vrf_try/(gE _ Hp)=>[x|ex] m Vm P; [apply: Hv | apply: Hx].
Qed.

Arguments tryE [G A B s] g [i e e1 e2 Q] _ _.

Notation "[tryE]" := (tryE tt) (at level 0).

Notation "[ 'tryE' x1 , .. , xn ]" :=
  (tryE (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'tryE'  x1 ,  .. ,  xn ]").

(* Common special case for framing on `Unit`, i.e. passing an *)
(* empty heap to the routine. For more sophisticated framing  *)
(* variants see the `heapauto` module.                        *)

Lemma gU G A (s : spec G A) g i (e : STspec G s) (Q : post A) :
        (s g).1 Unit ->
        (forall v m, (s g).2 (Val v) m ->
           valid (m \+ i) -> Q (Val v) (m \+ i)) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid (m \+ i) -> Q (Exn x) (m \+ i)) ->
        vrf i e Q.
Proof.
case: e=>e /= /[apply] Hp Hv Hx; rewrite -(unitL i).
apply/vrf_frame/vrf_post/Hp.
by case=>[x|ex] n _ =>[/Hv|/Hx].
Qed.

Notation "[gU]" := (gU tt) (at level 0).

Notation "[ 'gU' x1 , .. , xn ]" :=
  (gU (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'gU'  x1 ,  .. ,  xn ]").

(* a combination of gU + vrf_bind *)
Lemma stepU G A B (s : spec G A) g i (e : STspec G s) (e2 : A -> ST B)
             (Q : post B) :
        (s g).1 Unit ->
        (forall x m, (s g).2 (Val x) m -> vrf (m \+ i) (e2 x) Q) ->
        (forall x m, (s g).2 (Exn x) m ->
           valid (m \+ i) -> Q (Exn x) (m \+ i)) ->
        vrf i (bind e e2) Q.
Proof.
move=>Hp Hv Hx.
apply/vrf_bind/(gU _ Hp)=>[x m H V|ex m H V _].
- by apply: Hv H.
by apply: Hx.
Qed.

Arguments stepU [G A B s] g i [e e2 Q] _ _ _.

Notation "[stepU]" := (stepU tt) (at level 0).

Notation "[ 'stepU' x1 , .. , xn ]" :=
  (stepU (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'stepU'  x1 ,  .. ,  xn ]").

(* a combination of gU + vrf_try *)
Lemma tryU G A B (s : spec G A) g i (e : STspec G s)
             (e1 : A -> ST B) (e2 : exn -> ST B) (Q : post B) :
        (s g).1 Unit ->
        (forall x m, (s g).2 (Val x) m -> vrf (m \+ i) (e1 x) Q) ->
        (forall x m, (s g).2 (Exn x) m -> vrf (m \+ i) (e2 x) Q) ->
        vrf i (try e e1 e2) Q.
Proof.
move=>Hi H1 H2.
apply/vrf_try/(gU _ Hi)=>[x|ex] m H V.
- by apply: H1 H.
by apply: H2.
Qed.

Arguments tryU [G A B s] g i [e e1 e2 Q] _ _ _.

Notation "[tryU]" := (tryU tt) (at level 0).

Notation "[ 'tryU' x1 , .. , xn ]" :=
  (tryU (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'tryU'  x1 ,  .. ,  xn ]").

(* some notation for writing posts that signify no exceptions are raised *)

Definition vfun' A (f : A -> heap -> Prop) : post A :=
  fun y i => if y is Val v then f v i else False.

Notation "[ 'vfun' x => p ]" := (vfun' (fun x => p))
  (at level 0, x name, format "[ 'vfun'  x  =>  p ]") : fun_scope.

Notation "[ 'vfun' x : aT => p ]" := (vfun' (fun (x : aT) => p))
  (at level 0, x name, only parsing) : fun_scope.

Notation "[ 'vfun' x i => p ]" := (vfun' (fun x i => p))
  (at level 0, x name, format "[ 'vfun'  x  i  =>  p ]") : fun_scope.

Notation "[ 'vfun' ( x : aT ) i => p ]" := (vfun' (fun (x : aT) i => p))
  (at level 0, x name, only parsing) : fun_scope.
