(*
Copyright 2012 IMDEA Software Institute
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
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From pcm Require Import options axioms pred prelude.
From pcm Require Import pcm unionmap heap.
From htt Require Import domain.

(*********************************************)
(* Denotational model                        *)
(* denoting programs as relations            *)
(* over input/output heaps and output result *)
(*********************************************)

(* Helper definitions *)

(* Exceptions are an equality type *)
Inductive exn : Type := exn_from_nat of nat.

Definition exn_to_nat :=
  fun '(exn_from_nat y) => y.

Definition eqexn :=
  fun '(exn_from_nat m) '(exn_from_nat n) => m == n.

Lemma eqexnP : Equality.axiom eqexn.
Proof. by move=>[x][y]/=; case: eqP=>[->|*]; constructor=>//; case. Qed.

HB.instance Definition _ := hasDecEq.Build exn eqexnP.

(* Answer type *)
Inductive ans (A : Type) : Type := Val of A | Exn of exn.
Arguments Exn [A].

(* precondition is predicate over heaps *)
Definition pre := Pred heap.
(* postcondition is relates return result and output heap *)
(* because it's a relation, it models that programs can produce *)
(* no results (by looping forever) or produce more than one result *)
(* non-deterministically. *)
(* The latter will be used to model the alloc program *)
Definition post A := ans A -> heap -> Prop.
(* specification is a pair of precondition and postcondition *)
(* possibly parameterized by logical variable of type G (ghost) *)
(* (G may have product type, to allow for context of logical variables) *)
Definition spec G A := G -> pre * post A : Type.

(*************************************************************)
(* List of inference rules, with vrf predicate kept abstract *)
(*************************************************************)

Module Type VrfSig.
Parameter ST : Type -> Type.
Parameter ret : forall A, A -> ST A.
Parameter throw : forall A, exn -> ST A.
Parameter bnd : forall A B, ST A -> (A -> ST B) -> ST B.
Parameter try : forall A B, ST A -> (A -> ST B) -> (exn -> ST B) -> ST B.
Parameter read : forall A, ptr -> ST A.
Parameter write : forall A, ptr -> A -> ST unit.
Parameter alloc : forall A, A -> ST ptr.
Parameter allocb : forall A, A -> nat -> ST ptr.
Parameter dealloc : ptr -> ST unit.

Arguments throw {A}.
Arguments read : clear implicits.

(* given program e : ST A, input heap i, postcondition Q *)
(* vrf' judges if running e in i produces output heap and result *)
(* that satisfy Q *)
(* related to predicate transformers *)
(* vrf' has program as its first argument to facilitate automation *)
Parameter vrf' : forall A, ST A -> heap -> post A -> Prop.

(* in practice it's more convenient to order the arguments as *)
(* initial heap, program, postcondition *)
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
Parameter vrf_bnd : forall A B (e1 : ST A) (e2 : A -> ST B) 
    i (Q : post B),
  vrf i e1 (fun x m =>
    match x with
    | Val x' => vrf m (e2 x') Q
    | Exn e => valid m -> Q (Exn e) m
    end) ->
  vrf i (bnd e1 e2) Q.
Parameter vrf_try : forall A B (e : ST A) (e1 : A -> ST B) 
    (e2 : exn -> ST B) i (Q : post B),
  vrf i e (fun x m =>
    match x with
    | Val x' => vrf m (e1 x') Q
    | Exn ex => vrf m (e2 ex) Q
  end) ->
  vrf i (try e e1 e2) Q.
Parameter vrf_read : forall A x j (v : A) (Q : post A),
  (valid (x :-> v \+ j) -> Q (Val v) (x :-> v \+ j)) ->
  vrf (x :-> v \+ j) (read A x) Q.
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

(* some notation *)
Notation "x '<--' c1 ';' c2" := (bnd c1 (fun x => c2))
  (at level 81, right associativity, format
  "'[v' x  '<--'  c1 ';' '//' c2 ']'").
Notation "' x '<--' c1 ';' c2" := (bnd c1 (fun x => c2))
  (at level 81, right associativity, x strict pattern, format
  "'[v' ' x  '<--'  c1 ';' '//' c2 ']'").
Notation "c1 ';;' c2" := (bnd c1 (fun _ => c2))
  (at level 81, right associativity).
Notation "'!' x" := (read _ x) (at level 50).
Notation "x '::=' e" := (write x e) (at level 60).
(* using locked for Do, to make the Do definitions opaque *)
(* otherwise, clients will inline the code of Do, preventing *)
(* the use of the program with the spec that has been verified *)
(* with Do. *)
Notation "'Do' e" := (locked (@STprog _ _ _ e _)) (at level 80).

(* Fixed point constructor *)
(* We shall make fix work over *monotone closure* of argument function. *)
(* This is a mathematical hack to avoid spurious monotonicity proofs *)
(* that's necessary in shallow embedding, as we have no guarantee *)
(* that the argument function is actually monotone. *)
(* We *do* prove later on that all constructors are monotone. *)
(* We also hide model definition so that all functions one can *)
(* apply ffix to will be built out of monotonicity-preserving *)
(* constructors (and hence will be monotone). *)
Parameter ffix : forall G A (B : A -> Type) (s : forall x : A, spec G (B x)),
  ((forall x : A, STspec G (s x)) -> forall x : A, STspec G (s x)) ->
  forall x : A, STspec G (s x).
End VrfSig.

(********************************)
(* Definition of the Hoare type *)
(********************************)

Module Vrf : VrfSig.

Section BasePrograms.
Variables (P : pre) (A : Type).

(* the model is carved out of the following base type *)
Definition prog : Type := 
  forall i : heap, valid i -> i \In P -> post A.

(* we take only preconditions and progs with special properties *)
(* which we define next *)

(* safety monotonicity *)
Definition safe_mono :=
  forall i j, i \In P -> valid (i \+ j) -> i \+ j \In P.

(* defined heaps map to defined heaps *)
Definition def_strict (e : prog) :=
  forall i p v x, undef \Notin e i v p x.

(* frame property *)
Definition frameable (e : prog) :=
  forall i j (pf : i \In P) (V : valid (i \+ j)) (pf' : i \+ j \In P) y m,
    e _ V pf' y m ->
    exists h, [/\ m = h \+ j, valid (h \+ j) & e _ (validL V) pf y h].

End BasePrograms.

(* the model considers programs of base type, given a precondition *)
(* and adds several properties: *)
(* - safety monotonicity *)
(* - strictness of definedness *)
(* - frameability *)

Definition st_axiom A (p : pre) (e : prog p A) := 
  [/\ safe_mono p, def_strict e & frameable e].

Structure ST' (A : Type) := Prog {
  pre_of : pre;
  prog_of : prog pre_of A;
  _ : st_axiom prog_of}.

Arguments prog_of {A}.

(* module field must be a definition, not structure *)
Definition ST := ST'.

(* projections *)

Lemma sfm_st A (e : ST A) : safe_mono (pre_of e).
Proof. by case: e=>?? []. Qed.

Lemma dstr_st A (e : ST A) : def_strict (prog_of e).
Proof. by case: e=>?? []. Qed.

Lemma dstr_valid A (e : ST A) i p v x m :
        m \In prog_of e i p v x -> 
        valid m.
Proof. by case: m=>// /dstr_st. Qed.

Lemma fr_st A (e : ST A) : frameable (prog_of e).
Proof. by case: e=>?? []. Qed.

Arguments sfm_st {A e i j}.
Arguments dstr_st {A e i}.
Arguments fr_st {A e i j}.

Section STDef.
Variable A : Type.
Implicit Type e : ST A.

(* poset structure on ST *)

Definition st_leq e1 e2 :=
  exists pf : pre_of e2 <== pre_of e1,
  forall i (v : valid i) (p : i \In pre_of e2),
    prog_of e1 _ v (pf _ p) <== prog_of e2 _ v p.

Lemma st_is_poset : poset_axiom st_leq.
Proof.
split=>[e|e1 e2|e1 e2 e3].
- exists (poset_refl _)=>i V P y m.
  by rewrite (pf_irr (poset_refl (pre_of e) i P) P).
- case: e1 e2=>p1 e1 [S1 D1 F1][p2 e2 [S2 D2 F2]].
  rewrite /st_leq /=; case=>E1 R1 [E2 R2].
  move: (poset_asym E1 E2)=>?; subst p2.
  have : e1 = e2.
  - apply: fext=>i; apply: fext=>Vi; apply: fext=>Pi.
    apply: fext=>y; apply: fext=>m.
    move: (R2 i Vi Pi y m)=>{}R2; move: (R1 i Vi Pi y m)=>{}R1.
    apply: pext; split.
    - by move=>H1; apply: R1; rewrite (pf_irr (E1 i Pi) Pi).
    by move=>H2; apply: R2; rewrite (pf_irr (E2 i Pi) Pi).
  move=>?; subst e2.
  by congr Prog; apply: pf_irr.
case: e1 e2 e3=>p1 e1 [S1 D1 F1][p2 e2 [S2 D2 F2]][p3 e3 [S3 D3 F3]].
case=>/= E1 R1 [/= E2 R2]; rewrite /st_leq /=.
have E3 := poset_trans E2 E1; exists E3=>i V P y m.
set P' := E2 i P.
move: (R1 i V P' y m)=>{}R1; move: (R2 i V P y m)=>{}R2.
move=>H1; apply/R2/R1.
by rewrite (pf_irr (E1 i P') (E3 i P)).
Qed.

HB.instance Definition _ := isPoset.Build (ST A) st_is_poset.

(* lattice structure on ST *)

(* suprema of programs: *)
(* - precondition is intersection of preconditions of programs *)
(* - denotation is union of denotations of programs *)
                     
(* intersection of preconditions *)
Definition pre_sup (u : Pred (ST A)) : pre :=
  fun h => forall e, e \In u -> h \In pre_of e.

Definition pre_sup_leq u e (pf : e \In u) : pre_sup u <== pre_of e :=
  fun h (pf1 : pre_sup u h) => pf1 e pf.

(* union of postconditions *)
Definition prog_sup (u : Pred (ST A)) : prog (pre_sup u) A :=
  fun i V P y m => exists e (pf : e \In u),
    prog_of e _ V (pre_sup_leq pf P) y m.

Arguments prog_sup : clear implicits.

Lemma progsup_is_st u : st_axiom (prog_sup u).
Proof.
split=>[i j Pi Vij E He|i P V y|i j Pi Vij Pij y m [e][He Pe]].
- by apply: sfm_st=>//; apply: Pi.
- by case; case=>p e [S D F][H1] /D.
have Pi' := Pi e He; have Pij' := Pij e He.
move: Pe; rewrite (pf_irr (pre_sup_leq He Pij) Pij').
case/(fr_st Pi' Vij Pij')=>h [{m}-> Vhj Ph].
exists h; split=>//; exists e, He.
by rewrite (pf_irr (pre_sup_leq He Pi) Pi').
Qed.

Definition st_sup u : ST A := Prog (progsup_is_st u).  

Lemma st_is_lattice : lattice_axiom st_sup.
Proof.
split=>/= u e; case: e=>p e' X R.
- exists (pre_sup_leq R)=>/=p0 y m H.
  by exists (Prog X), R.
have J : p <== pre_sup u.
- by move=>/= x Px ex pf; case: (R _ pf)=>/= + _; apply.
exists J=>i V P y m [e0][H0 Hm].
case: (R _ H0)=>/= Hx; apply.
by rewrite (pf_irr (Hx i P) (pre_sup_leq H0 (J i P))).
Qed.

HB.instance Definition _ := isLattice.Build (ST A) st_is_lattice.
End STDef.

(* types that embed the specs *)

Section STspecDef.
Variables (G A : Type) (s : spec G A).

Definition vrf' (e : ST A) (i : heap) (Q : post A) :=
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

Lemma stspleq_is_poset : poset_axiom stsp_leq.
Proof.
split=>[e|e1 e2|e1 e2 e3].
- by case: e=>e He; apply: poset_refl. 
- case: e1 e2=>e1 H1 [e2 H2]; rewrite /stsp_leq /= =>E1 E2.
  have E := poset_asym E1 E2; subst e2.
  by congr STprog; apply: pf_irr.
case: e1 e2 e3=>e1 H1 [e2 H2][e3 H3].
by apply: poset_trans.
Qed.

HB.instance Definition _ := isPoset.Build STspec stspleq_is_poset.

(* lattice structure on STspec *)

(* denotation of the union of STspec programs is *)
(* the union of their denotations *)
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

Lemma stspsup_is_lattice : lattice_axiom stsp_sup.
Proof.
split=>/= u [p S R].
- by apply: supP; exists (STprog S). 
by apply: supM=>/= y[q][->]; apply: R. 
Qed.

HB.instance Definition _ := isLattice.Build STspec stspsup_is_lattice.

End STspecDef.

Notation vrf i e Q := (vrf' e i Q).

(* required vrf lemmas *)

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

(************************************)
(* modeling the language primitives *)
(************************************)

(* recursion *)

Section Fix.
Variables (G A : Type) (B : A -> Type) (pq : forall x, spec G (B x)).
Notation tp := (forall x, STspec (pq x)).
Notation lat := (dfun_lattice (fun x => STspec (pq x))).
Variable f : tp -> tp.

(* fixed point constructor over monotone closure *)
Definition f' (c : lat) := sup [Pred t : lat | exists c', c' <== c /\ t = f c'].
Definition ffix := tarski_lfp f'.

(* fixed point constructor which requires explicit proof of monotonicity *)
Definition monotone' := monofun_axiom (f : lat -> lat).
Definition ffix2 (pf : monotone') : tp := tarski_lfp (f : lat -> lat).
End Fix.

Arguments ffix {G  A B pq}.
Arguments ffix2 {G A B pq}.

(* monadic unit *)
Section Return.
Variables (A : Type) (x : A).

Definition ret_pre : pre := top.

Definition ret_prog : prog ret_pre A :=
  fun i _ _ y m => m = i /\ y = Val x.

Lemma retprog_is_st : st_axiom ret_prog.
Proof. 
split=>[//|i [] V _ /= [E _]|i j [Vij []] _ _ [->->]].
- by rewrite -E in V.
by exists i.
Qed.

Definition ret := Prog retprog_is_st.

Lemma vrf_ret i (Q : post A) :
        (valid i -> Q (Val x) i) -> vrf i ret Q.
Proof. by move=>H V; exists I=>_ _ [->->]; apply: H. Qed.
End Return.

(* exception throwing *)
Section Throw.
Variables (A : Type) (e : exn).

Definition throw_pre : pre := top.

Definition throw_prog : prog throw_pre A :=
  fun i _ _ y m => m = i /\ y = @Exn A e.

Lemma throwprog_is_st : st_axiom throw_prog.
Proof.
split=>[//|i [V] _ /= [E _]|i j [Vij []] _ _ [->->]].
- by rewrite -E in V.
by exists i.
Qed.

Definition throw := Prog throwprog_is_st.

Lemma vrf_throw i (Q : post A) :
        (valid i -> Q (Exn e) i) -> vrf i throw Q.
Proof. by move=>H V; exists I=>_ _ [->->]; apply: H. Qed.
End Throw.

(* monadic bind *)
Section Bnd.
Variables (A B : Type).
Variables (e1 : ST A) (e2 : A -> ST B).

Definition bnd_pre : pre :=
  fun i =>
    exists (Vi : valid i) (Pi : i \In pre_of e1),
      forall x m, prog_of e1 _ Vi Pi (Val x) m -> pre_of (e2 x) m.

Definition bnd_pre_proj i : i \In bnd_pre -> i \In pre_of e1 :=
  fun '(ex_intro _ (ex_intro p _)) => p.

Definition bnd_prog : prog bnd_pre B :=
  fun i V P y m =>
    exists x h (Ph : h \In prog_of e1 _ V (bnd_pre_proj P) x),
      match x with
      | Val x' => exists Ph' : h \In pre_of (e2 x'),
                    m \In prog_of (e2 x') _ (dstr_valid Ph) Ph' y
      | Exn e => y = Exn e /\ m = h
      end.

Lemma bndprog_is_st : st_axiom bnd_prog.
Proof.
split.
- move=>i j [Vi][Pi] P Vij; have Pij := sfm_st Pi Vij.
  exists Vij, Pij=>x m; case/(fr_st Pi Vij Pij)=>h [{m}-> Vhj].
  rewrite (pf_irr (validL Vij) Vi)=>/P Ph.
  by apply: sfm_st=>//; apply: (validL Vhj).
- move=>i [Vi][Pi P] Vi' y [x][h][/=].
  case: x=>[x|e]Ph; first by case=>Ph' /dstr_st.
  by case=>_; move: Ph=>/[swap]<- /dstr_st.
move=>i j [Vi][Pi P] Vij [_ [Pij _]] y m [x][h][/=].
move: (fr_st Pi Vij Pij)=>H; case: x=>[x|e] Ph.
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

Definition bnd := Prog bndprog_is_st.

Lemma vrf_bnd i (Q : post B) :
        vrf i e1 (fun x m =>
                    match x with
                    | Val x' => vrf m (e2 x') Q
                    | Exn e => valid m -> Q (Exn e) m
                    end) ->
        vrf i bnd Q.
Proof.
move=>H Vi; case: (H Vi)=>Hi {}H /=.
have Hi' : i \In bnd_pre.
- by exists Vi, Hi=>x m Pm; case: (H _ _ Pm (dstr_valid Pm)).
exists Hi'=>y j /= [x][m][Pm] C.
rewrite (pf_irr Hi (bnd_pre_proj Hi')) in H.
case: x Pm C=>[x|e] Pm; move: (H _ _ Pm (dstr_valid Pm))=>{}H.
- by case=>Pm2 Pj; case: H=>Pm2'; apply; rewrite (pf_irr Pm2' Pm2).
by case=>->->.
Qed.

End Bnd.

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

Lemma tryprog_is_st : st_axiom try_prog.
Proof.
split.
- move=>i j [Vi [Pi][E1 E2]] Vij; have Pij := sfm_st Pi Vij.
  exists Vij, Pij; split.
  - move=>y m.
    case/(fr_st Pi Vij Pij)=>h [{m}-> Vhj].
    rewrite (pf_irr (validL Vij) Vi)=>/E1 Ph.
    by apply: sfm_st=>//; apply: (validL Vhj).
  move=>ex m.
  case/(fr_st Pi Vij Pij)=>h [{m}-> Vhj].
  rewrite (pf_irr (validL Vij) Vi)=>/E2 Ph.
  by apply: sfm_st=>//; apply: (validL Vhj).
- move=>i [Vi [Pi][E1 E2]] Vi' y [x][h][/=].
  by case: x=>[x|ex] Eh; case=>Ph /dstr_st.
move=>i j [Vi [Pi][E1 E2]] Vij [_ [Pij _]] y m [x][h][/=].
move: (fr_st Pi Vij Pij)=>H; case: x=>[x|ex] Ph.
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

Definition try := Prog tryprog_is_st.

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

(* bnd follows from try; not to export, just for fun *)
Lemma bnd_is_try A B (e1 : ST A) (e2 : A -> ST B) i r :
        vrf i (try e1 e2 (throw B)) r ->
        vrf i (bnd e1 e2) r.
Proof.
move=>H Vi; case: (H Vi)=>[[Vi'][P1 /= [E1 E2]]] {}H.
have J : i \In pre_of (bnd e1 e2).
- exists Vi, P1=>y m.
  by rewrite (pf_irr Vi Vi')=>/E1.
exists J=>y m /= [x][h][Ph]C.
apply: H; exists x, h=>/=.
rewrite (pf_irr P1 (bnd_pre_proj J)) in E2 *; exists Ph.
move: Ph C; case: x=>// e Ph [{y}-> {m}->].
rewrite (pf_irr Vi' Vi) in E2.
by exists (E2 _ _ Ph).
Qed.

Section Read.
Variable (A : Type) (x : ptr).

Definition read_pre : pre :=
  fun i => x \in dom i /\ exists v : A, find x i = Some (idyn v).

Definition read_prog : prog read_pre A :=
  fun i _ _ y m =>
    exists w, [/\ m = i, y = Val w & find x m = Some (idyn w)].

Lemma readprog_is_st : st_axiom read_prog.
Proof.
split.
- move=>i j [Hx [v E]] Vij; split.
  - by rewrite domUn inE Vij Hx.
  by exists v; rewrite findUnL // Hx.
- by move=>i _ Vi _ [_ [E _ _]]; rewrite -E in Vi. 
move=>i j [Hx [v E]] Vij _ _ _ [w [-> -> H]].
exists i; split=>//; exists w; split=>{v E}//.
by rewrite findUnL // Hx in H.
Qed.

Definition read := Prog readprog_is_st.

Lemma vrf_read j (v : A) (Q : post A) :
       (valid (x :-> v \+ j) -> 
          Q (Val v) (x :-> v \+ j)) ->
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

Definition write_pre : pre := fun i => x \in dom i.

Definition write_prog : prog write_pre unit :=
  fun i _ _ y m =>
    [/\ y = Val tt, m = upd x (idyn v) i & x \in dom i].

Lemma writeprog_is_st : st_axiom write_prog.
Proof.
split.
- move=>i j; rewrite /write_pre -!toPredE /= => Hx Vij.
  by rewrite domUn inE Vij Hx.
- move=>i Hx _ _ [_ E _]; rewrite /write_pre -toPredE /= in Hx.
  suff {E}: valid (upd x (idyn v) i) by rewrite -E.
  by rewrite validU (dom_cond Hx) (dom_valid Hx).
move=>i j Hx Vij _ _ _ [-> -> _].
exists (upd x (idyn v) i); split=>//;
rewrite /write_pre -toPredE /= in Hx.
- by rewrite updUnL Hx.
by rewrite validUUn.
Qed.

Definition write := Prog writeprog_is_st.

Lemma vrf_write B (u : B) j (Q : post unit) :
        (valid (x :-> v \+ j) -> 
           Q (Val tt) (x :-> v \+ j)) ->
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

Definition alloc_pre : pre := top.

Definition alloc_prog : prog alloc_pre ptr :=
  fun i _ _ y m =>
    exists l, [/\ y = Val l, m = l :-> v \+ i,
                  l != null & l \notin dom i].

Lemma allocprog_is_st : st_axiom alloc_prog.
Proof.
split=>//.
- move=>i [] Vi _ [l][_ E Hl Hl2].
  suff {E}: valid (l :-> v \+ i) by rewrite -E.
  by rewrite validPtUn; apply/and3P.
move=>i j [] Vij [] _ _ [l][->-> Hl Hl2].
exists (l :-> v \+ i); rewrite -joinA; split=>//.
- rewrite validUnAE validPt domPtK Hl Vij /= all_predC.
  apply/hasP=>[[y Hy]]; rewrite !inE=>/eqP E.
  by move: Hy Hl2; rewrite E=>->.
exists l; split=>//.
by apply/dom_NNL/Hl2.
Qed.

Definition alloc := Prog allocprog_is_st.

Lemma vrf_alloc i (Q : post ptr) :
        (forall x, valid (x :-> v \+ i) -> 
           Q (Val x) (x :-> v \+ i)) ->
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

Lemma allocbprog_is_st : st_axiom allocb_prog.
Proof.
split=>//.
- by move=>i [] Vi y [l][]. 
move=>i j [] Vij [] _ _ [l][->-> V].
exists (updi l (nseq n v) \+ i); rewrite -joinA; split=>//.
exists l; split=>//.
by rewrite joinA in V; apply: (validL V).
Qed.

Definition allocb := Prog allocbprog_is_st.

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

Lemma deallocprog_is_st : st_axiom dealloc_prog.
Proof.
split.
- move=>i j; rewrite /dealloc_pre -!toPredE /= => Hx Vij.
  by rewrite domUn inE Vij Hx.
- move=>i _ Vi _ [_ E _].
  suff {E}: valid (free i x) by rewrite -E.
  by rewrite validF.
move=>i j Hx Vij Hx' _ _ [->-> _].
exists (free i x); split=>//;
rewrite /dealloc_pre -!toPredE /= in Hx Hx'.
- by apply/freeUnL/dom_inNL/Hx.
by apply: validFUn.
Qed.

Definition dealloc := Prog deallocprog_is_st.

Lemma vrf_dealloc A (v : A) j (Q : post unit) :
        (x \notin dom j -> 
         valid j -> 
         Q (Val tt) j) ->
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
Variables A B : Type.

Lemma do_mono G (e1 e2 : ST A) (s : spec G A)
          (pf1 : has_spec s e1) (pf2 : has_spec s e2) :
        e1 <== e2 -> 
        @STprog _ _ _ e1 pf1 <== @STprog _ _ _ e2 pf2.
Proof. by []. Qed.

Lemma bind_mono (e1 e2 : ST A) (k1 k2 : A -> ST B) :
        e1 <== e2 -> 
        k1 <== k2 -> 
        (bnd e1 k1 : ST B) <== bnd e2 k2.
Proof.
move=>[H1 H2] pf2.
have pf: bnd_pre e2 k2 <== bnd_pre e1 k1.
- move=>h [Vh][Pi] H.
  exists Vh, (H1 _ Pi)=>x m /H2/H H'.
  by case: (pf2 x)=>+ _; apply.
exists pf=>i Vi /[dup][[Vi'][Pi']P'] Pi x h.
case; case=>[a|e][h0][Ph][Ph'] H.
- exists (Val a), h0.
  move: (H2 i Vi (bnd_pre_proj Pi))=>H'.
  rewrite (pf_irr (H1 i (bnd_pre_proj Pi)) (bnd_pre_proj (pf i Pi))) in H'.
  have Ph0 := (H' _ _ Ph); exists Ph0.
  move: (P' a h0); rewrite (pf_irr Vi' Vi) (pf_irr Pi' (bnd_pre_proj Pi))=>H''.
  exists (H'' Ph0); case: (pf2 a)=>Pr; apply.
  rewrite (pf_irr (dstr_valid Ph0) (dstr_valid Ph)).
  by rewrite (pf_irr (Pr h0 (H'' Ph0)) Ph').
rewrite Ph' H; exists (Exn e), h0.
move: (H2 i Vi (bnd_pre_proj Pi))=>H'.
rewrite (pf_irr (H1 i (bnd_pre_proj Pi)) (bnd_pre_proj (pf i Pi))) in H'.
by exists (H' _ _ Ph).
Qed.

Lemma try_mono (e1 e2 : ST A) (k1 k2 : A -> ST B) (h1 h2 : exn -> ST B) :
        e1 <== e2 -> 
        k1 <== k2 -> 
        h1 <== h2 ->
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
  move: (Pk0 a h0); rewrite (pf_irr Vi' Vi). 
  rewrite (pf_irr Pi' (try_pre_proj Pi))=>H''.
  exists (H'' Ph1); case: (pf2 a)=>Pr; apply.
  rewrite (pf_irr (dstr_valid Ph1) (dstr_valid Ph)).
  by rewrite (pf_irr (Pr h0 (H'' Ph1)) Ph').
exists (Exn e), h0.
move: (H2 i Vi (try_pre_proj Pi))=>H'.
rewrite (pf_irr (H1 i (try_pre_proj Pi)) (try_pre_proj (pf i Pi))) in H'.
have Ph1 := (H' _ _ Ph); exists Ph1.
move: (Ph0 e h0); rewrite (pf_irr Vi' Vi) (pf_irr Pi' (try_pre_proj Pi))=>H''.
exists (H'' Ph1); case: (pf3 e)=>Pr; apply.
rewrite (pf_irr (dstr_valid Ph1) (dstr_valid Ph)).
by rewrite (pf_irr (Pr h0 (H'' Ph1)) Ph').
Qed.

(* the rest of the  constructors are trivial *)
Lemma ret_mono (v1 v2 : A) :
        v1 = v2 -> 
        (ret v1 : ST A) <== ret v2.
Proof. by move=>->. Qed.

Lemma throw_mono (e1 e2 : exn) :
        e1 = e2 -> 
        (throw A e1 : ST A) <== throw A e2.
Proof. by move=>->. Qed.

Lemma read_mono (p1 p2 : ptr) :
        p1 = p2 -> 
        (read A p1 : ST A) <== read A p2.
Proof. by move=>->. Qed.

Lemma write_mono (p1 p2 : ptr) (x1 x2 : A) :
        p1 = p2 -> 
        x1 = x2 -> 
        (write p1 x1 : ST unit) <== write p2 x2.
Proof. by move=>->->. Qed.

Lemma alloc_mono (x1 x2 : A) :
        x1 = x2 -> 
        (alloc x1 : ST ptr) <== alloc x2.
Proof. by move=>->. Qed.

Lemma allocb_mono (x1 x2 : A) (n1 n2 : nat) :
        x1 = x2 -> 
        n1 = n2 -> 
        (allocb x1 n1 : ST ptr) <== allocb x2 n2.
Proof. by move=>->->. Qed.

Lemma dealloc_mono (p1 p2 : ptr) :
        p1 = p2 -> 
        (dealloc p1 : ST unit) <== dealloc p2.
Proof. by move=>->. Qed.

Variables (G : Type) (C : A -> Type) (pq : forall x, spec G (C x)).
Notation lat := (dfun_lattice (fun x => STspec (pq x))).

Lemma fix_mono (f1 f2 : lat -> lat) : 
        f1 <== f2 -> 
        (ffix f1 : lat) <== ffix f2.
Proof.
move=>Hf; rewrite /ffix.
(* f' f2 is monotone closure of f2; hence it's monotone *)
have M : monofun_axiom (f' f2).
- move=>x1 x2 Hx; apply: supM=>z [x][H ->]; apply: supP; exists x. 
  by split=>//; apply: poset_trans H Hx.
set ff := MonoFun.pack_ (isMonoFun.Build _ _ (f' f2) M).
apply: (tarski_lfp_mono (f2:=ff)).
move=>y; apply: supM=>_ [x][H1 ->].
by apply: poset_trans (Hf x) _; apply: supP; exists x.
Qed.

End Monotonicity.

Notation "'Do' e" := (@STprog _ _ _ e _) (at level 80).
Notation "x '<--' c1 ';' c2" := (bnd c1 (fun x => c2))
  (at level 81, right associativity).
Notation "c1 ';;' c2" := (bnd c1 (fun _ => c2))
  (at level 81, right associativity).
Notation "'!' x" := (read x) (at level 50).
Notation "x '::=' e" := (write x e) (at level 60).

(* Some examples *)

(* the examples require a lemma for instantiating ghosts *)
(* when doing function calls *)
(* this need not be exported, as it follows from the signature *)
(* and will be reproven outside of the Vrf module *)

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

(* factorial *)

Fixpoint fact (x : nat) := if x is x'.+1 then x * fact x' else 1.
Definition facttp := forall x : nat, @STspec unit nat
  (fun => (fun i => True, 
   fun v m => if v is Val w then w = fact x else False)).

(* proof using ffix2, with monotonicity proved explicitly *)
Program Definition factx :=
  ffix2 (fun (loop : facttp) (x : nat) =>
    Do (if x is x'.+1 then
          t <-- loop x'; 
          ret (x * t)
        else ret 1)) _.
Next Obligation.
case=>i /= _; case: x; first by apply: vrf_ret.
by move=>n; apply: vrf_bnd=>//; apply: gE=>// x m -> _; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H; case=>[|n]; first by apply: poset_refl.
by apply: do_mono; apply: bind_mono=>//; apply: H.
Qed.

(* monotonocity can be proved even if we compute *)
(* with propositions, and deliberately invert the polarity. *)

Definition proptp := unit -> @STspec unit Prop
  (fun => (fun i => True, fun R m => True)).

Program Definition propx := 
  ffix2 (fun (loop : proptp) (x : unit) =>
    Do (R <-- loop tt; ret (not R))) _.
Next Obligation.
case=>i _; apply: vrf_bnd=>//.
by apply: gE=>//= R m _ C; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H /= n; apply: do_mono; apply: bind_mono=>//. 
by apply: H.
Qed.

Definition proptp2 := Prop -> @STspec unit Prop 
  (fun => (fun i => True, fun (Ro : ans Prop) m => True)).

Program Definition propx2 := 
  ffix2 (fun (loop : proptp2) (x : Prop) =>
    Do (R <-- loop (x -> x); ret R)) _ True.
Next Obligation.
case=>i /= _; apply: vrf_bnd=>//.
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
  ffix2 (fun (loop : proptp3) (x : Prop) =>
    Do (R <-- loop (x -> x); ret R)) _ True.
Next Obligation.
case=>i /= _; apply: vrf_bnd=>//.
by apply: gE=>//= R m X _; apply: vrf_ret.
Qed.
Next Obligation.
move=>x1 x2 H /= n; apply: do_mono.
by apply: bind_mono=>//; apply: H.
Qed.

(* It seems safe to say that monotonicity is always easy *)
(* to prove for all the programs that we expect to write. *)
(* Thus, the module will export ffix over monotone closure, but not ffix2. *)
(* Exporting ffix has the advantage of eliding the always simple *)
(* and syntax-directed proofs of monotonicity. *)

(* This is in line with the existing proofs of soundness of HTT as a *)
(* standalone theory, which shows that all functions that can be *)
(* produced using the declared syntax are monotone in the model. *)
(* The paper is: *)
(* Partiality, State and Dependent Types *)
(* Kasper Svendsen, Lars Birkedal and Aleksandar Nanevski *)
(* International Conference on Typed Lambda Calculi and Applications (TLCA) *)
(* pages 198-212, 2011. *)

(* The model in that paper, and the one we use here, are quite different *)
(* however, and one can't exclude concocting a *)
(* non-monotone program using the syntax exported here, *)
(* based on the results of that other paper. *)
(* That said, so far there we failed to produce such a non-monotone function. *)
(* But if such a case arises, we should switch to using ffix2 *)
(* and ask for explicit proofs of monotonicity. *)
(* For all the examples done so far, such a proof is easily *)
(* constructed, along the above lines (moreover, such proofs ought to be automatable) *)
(* Perhaps a proof, in the theory of Coq, that all functions are monotone *)
(* can be produced if one worked from parametricity properties of Coq, *)
(* which have been established in the past work, and even internalized *)
(* into Coq by means of parametricity axioms. But that remains future work. *)

End Vrf.
Export Vrf.

(* some helpers *)
Definition skip := ret tt.

Lemma vrf_mono A (e : ST A) i : monofun_axiom (vrf' e i).
Proof. by move=>/= Q1 Q2 H; apply: vrf_post=>y m _; apply: H. Qed.

(******************************************)
(* Notation for logical variable postexts *)
(******************************************)

Definition logbase A (p : pre) (q : post A) : spec unit A :=
  fun => (p, q).

Definition logvar {B A} (G : A -> Type) (s : forall x : A, spec (G x) B) :
             spec {x : A & G x} B :=
  fun '(existT x g) => s x g.

Notation "'STsep' ( p , q ) " :=
  (STspec unit (fun => (p, q))) (at level 0,
   format "'[hv ' STsep   ( '[' p , '/' q ']' ) ']'").

Notation "'STsep' { x .. y } ( p , q )" :=
  (STspec _ (logvar (fun x => .. (logvar (fun y => logbase p q)) .. )))
   (at level 0, x binder, y binder, right associativity,
    format "'[hv ' STsep  { x .. y }  '/ '  ( '[' p , '/' q ']' ) ']'").

Notation "[>  h1 , .. , hn <]" :=
  (existT _ h1 .. (existT _ hn tt) .. ) (at level 0).

(************************************************************)
(* Lemmas for pulling out and instantiating ghost variables *)
(************************************************************)

(* Lemmas without framing, i.e. they pass the entire heap to the *)
(* routine being invoked.                                        *)

Lemma gE G A (pq : spec G A) (e : STspec G pq) g (Q : post A) i :
        (pq g).1 i ->
        (forall v m, (pq g).2 (Val v) m ->
           valid m -> Q (Val v) m) ->
        (forall x m, (pq g).2 (Exn x) m ->
           valid m -> Q (Exn x) m) ->
        vrf i e Q.
Proof.
case: e=>e /= /[apply] Hp Hv He; apply: vrfV=>V /=.
by apply/vrf_post/Hp; case=>[v|ex] m Vm H; [apply: Hv | apply: He].
Qed.

Arguments gE {G A pq e} g {Q}.

Notation "[gE]" := (gE tt) (at level 0). 
Notation "[ 'gE' x1 , .. , xn ]" :=
  (gE (existT _ x1 .. (existT _ xn tt) ..))
(at level 0, format "[ 'gE'  x1 ,  .. ,  xn ]").

(* combination of gE + vrf_bind, for "stepping over" the call *)
Lemma stepE G A B (pq : spec G A) (e : STspec G pq) 
          (e2 : A -> ST B) i (Q : post B) (g : G) :
        (pq g).1 i ->
        (forall x m, (pq g).2 (Val x) m -> vrf m (e2 x) Q) ->
        (forall x m, (pq g).2 (Exn x) m ->
           valid m -> Q (Exn x) m) ->
        vrf i (bnd e e2) Q.
Proof.
move=>Hp Hv He; apply/vrf_bnd/(gE _ _ Hp).
- by move=>v m P V; apply: Hv.
by move=>x m P _ V; apply: He.
Qed.

Arguments stepE {G A B pq e e2 i Q}.

Notation "[stepE]" := (stepE tt) (at level 0).
Notation "[ 'stepE' x1 , .. , xn ]" :=
  (stepE (existT _ x1 .. (existT _ xn tt) ..))
(at level 0, format "[ 'stepE'  x1 ,  .. ,  xn ]").

(* combination of gE + vrf_try *)
Lemma tryE G A B (pq : spec G A) (e : STspec G pq) (e1 : A -> ST B) 
          (e2 : exn -> ST B) i (Q : post B) (g : G) :
        (pq g).1 i ->
        (forall x m, (pq g).2 (Val x) m -> vrf m (e1 x) Q) ->
        (forall x m, (pq g).2 (Exn x) m -> vrf m (e2 x) Q) ->
        vrf i (try e e1 e2) Q.
Proof.
move=>Hp Hv Hx; apply/vrf_try/(gE _ _ Hp).
- by move=>x m Vm P; apply: Hv.
by move=>ex m Vm P; apply: Hx.
Qed.

Arguments tryE {G A B pq e e1 e2 i Q}.

Notation "[tryE]" := (tryE tt) (at level 0).
Notation "[ 'tryE' x1 , .. , xn ]" :=
  (tryE (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'tryE'  x1 ,  .. ,  xn ]").

(* backward symbolic execution by one step *)
Lemma bnd_vrf G A B (pq : A -> spec G B) (g : G) (e1 : ST A) 
          (e2 : forall x, STspec G (pq x)) (Q : post B) i :
        vrf i e1 (fun x m => 
          match x with 
            Val v => (pq v g).1 m
          | Exn e => valid m -> Q (Exn e) m
          end) ->
        (forall v y m, (pq v g).2 y m -> valid m -> Q y m) ->
        vrf i (bnd e1 e2) Q.
Proof.
move=>H1 H2; apply/vrf_bnd/vrf_post/H1=>/= y m V.
by case: y=>// y H; apply: gE H _ _ => v h; apply: H2. 
Qed.

Arguments bnd_vrf {G A B pq} g {e1 e2 Q}.

Notation "[bnd_vrf]" := (bnd_vrf tt) (at level 0). 
Notation "[ 'bnd_vrf' x1 , .. , xn ]" :=
  (bnd_vrf (existT _ x1 .. (existT _ xn tt) ..))
(at level 0, format "[ 'bnd_vrf'  x1 ,  .. ,  xn ]").


(* Common special case for framing on `Unit`, i.e. passing an *)
(* empty heap to the routine. For more sophisticated framing  *)
(* variants see the `heapauto` module.                        *)

Lemma gU G A (pq : spec G A) (e : STspec G pq) i (Q : post A) g :
        (pq g).1 Unit ->
        (forall v m, (pq g).2 (Val v) m ->
           valid (m \+ i) -> Q (Val v) (m \+ i)) ->
        (forall x m, (pq g).2 (Exn x) m ->
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

(* combination of gU + vrf_bind *)
Lemma stepU G A B (pq : spec G A) (e : STspec G pq) (e2 : A -> ST B)
             i (Q : post B) g :
        (pq g).1 Unit ->
        (forall x m, (pq g).2 (Val x) m -> vrf (m \+ i) (e2 x) Q) ->
        (forall x m, (pq g).2 (Exn x) m ->
           valid (m \+ i) -> Q (Exn x) (m \+ i)) ->
        vrf i (bnd e e2) Q.
Proof.
move=>Hp Hv Hx; apply/vrf_bnd/(gU _ Hp). 
- by move=>x m H V; apply: Hv H.
by move=>ex m H V _; apply: Hx.
Qed.

Arguments stepU {G A B pq e e2 i Q}. 

Notation "[stepU]" := (stepU tt) (at level 0).
Notation "[ 'stepU' x1 , .. , xn ]" :=
  (stepU (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'stepU'  x1 ,  .. ,  xn ]").

(* combination of gU + vrf_try *)
Lemma tryU G A B (pq : spec G A) (e : STspec G pq)
             (e1 : A -> ST B) (e2 : exn -> ST B) i (Q : post B) g :
        (pq g).1 Unit ->
        (forall x m, (pq g).2 (Val x) m -> vrf (m \+ i) (e1 x) Q) ->
        (forall x m, (pq g).2 (Exn x) m -> vrf (m \+ i) (e2 x) Q) ->
        vrf i (try e e1 e2) Q.
Proof.
move=>Hi H1 H2; apply/vrf_try/(gU _ Hi). 
- by move=>x m H V; apply: H1 H.
by move=>ex m H V; apply: H2.
Qed.

Arguments tryU {G A B pq e e1 e2 i Q}.

Notation "[tryU]" := (tryU tt) (at level 0).
Notation "[ 'tryU' x1 , .. , xn ]" :=
  (tryU (existT _ x1 .. (existT _ xn tt) ..))
  (at level 0, format "[ 'tryU'  x1 ,  .. ,  xn ]").

(* notation for writing posts that signify *)
(* that no exception is raised *)

Definition vfun' A (f : A -> heap -> Prop) : post A :=
  fun y i => if y is Val v then f v i else False.

Notation "[ 'vfun' x => p ]" := (vfun' (fun x => p))
  (at level 0, x name, format "[ 'vfun'  x  =>  p ]") : function_scope.
Notation "[ 'vfun' x : aT => p ]" := (vfun' (fun (x : aT) => p))
  (at level 0, x name, only parsing) : function_scope.
Notation "[ 'vfun' x i => p ]" := (vfun' (fun x i => p))
  (at level 0, x name, format "[ 'vfun'  x  i  =>  p ]") : function_scope.
Notation "[ 'vfun' ( x : aT ) i => p ]" := (vfun' (fun (x : aT) i => p))
  (at level 0, x name, only parsing) : function_scope.
