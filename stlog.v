Set Automatic Coercions Import.
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import pred pcm unionmap heap stmod stsep. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Lemma bnd_is_try (A B : Type) (e1 : ST A) (e2 : A -> ST B) i r : 
        verify i (ttry e1 e2 (throw B)) r ->
        verify i (bind e1 e2) r.
Proof.
move=>H; apply: frame0=>D.
case: {H D} (H D) (D)=>[[i1]][i2][->][[H1 [H2 H3]]] _ T D.
split=>[|y m].
- split=>[|x m]; first by apply: fr_pre H1.
  by case/(locality D H1)=>m1 [->][_]; move/H2; apply: fr_pre.
move=>{D} H; apply: T=>h1 h2 E.
rewrite {i1 i2 H1 H2 H3}E in H * => D1 [H1][H2] H3.
case: H=>[[x][h][]|[e][->]]; move/(locality D1 H1);
case=>[m1][->][D2] T1; move: (T1); [move/H2 | move/H3]=>H4.
- move=>T2; case/(locality D2 H4): (T2)=>m3 [->][D3].
  by exists m3; do !split=>//; left; exists x; exists m1.
exists m1; do !split=>//; right; exists e; exists m1; split=>//. 
move=>j1 j2 E D _; rewrite {m1 D2}E in T1 D H4 *.
by exists j1; do !split=>//; move=>k1 k2 -> D2 ->.
Qed. 

Local Notation cont A := (ans A -> heap -> Prop).


(* The duplication of the lemmas for the bnd and try cases is spurious!!! *)
(* All are a simple composition of Hoare rule for sequential composition *)
(* with the rule for the specific command being stepped *)
(* But I can't bother now with optimizing *)

Section EvalDo.
Variables (A B : Type).

Lemma val_do (e : ST A) i j (r : cont A) :
        (valid i -> pre_of e i) -> 
        (forall x m, post_of e (Val x) i m -> 
                       valid (m \+ j) -> r (Val x) (m \+ j)) ->
        (forall x m, post_of e (Exn x) i m -> 
                       valid (m \+ j) -> r (Exn x) (m \+ j)) ->
        verify (i \+ j) e r.
Proof.
move=>H1 H2 H3; apply: frame; apply: frame0=>D; split; first by apply: H1.
by case=>x m H4 D1 D2; [apply: H2 | apply: H3].
Qed.

Lemma try_do (e : ST A) e1 e2 i j (r : cont B) : 
        (valid i -> pre_of e i) -> 
        (forall x m, post_of e (Val x) i m -> verify (m \+ j) (e1 x) r) ->
        (forall x m, post_of e (Exn x) i m -> verify (m \+ j) (e2 x) r) ->
        verify (i \+ j) (ttry e e1 e2) r.
Proof.
move=>H1 H2 H3; apply: frame0=>D; split=>[|y m]; move: (H1 (validL D))=>H.
- split; first by apply: fr_pre; exists i, Unit; rewrite unitR.
  by split=>y m /(_ i j (erefl _) D H) [m1][->][D2]; [case/H2 | case/H3].
by case=>[[x]|[x]][h][] /(_ i j (erefl _) D H) [m1][->][D2];
   [case/H2 | case/H3]=>// _; apply.
Qed.

Lemma bnd_do (e : ST A) e2 i j (r : cont B) : 
        (valid i -> pre_of e i) -> 
        (forall x m, post_of e (Val x) i m -> verify (m \+ j) (e2 x) r) -> 
        (forall x m, post_of e (Exn x) i m -> 
                       valid (m \+ j) -> r (Exn x) (m \+ j)) ->
        verify (i \+ j) (bind e e2) r.
Proof.
move=>H1 H2 H3; apply: bnd_is_try; apply: try_do=>// x m H4. 
by apply: frame1; split=>// y m1 [->->] _; rewrite unitL; apply: H3. 
Qed.

End EvalDo.


Section EvalReturn.
Variables (A B : Type). 

Lemma val_ret v i (r : cont A) : 
       (valid i -> r (Val v) i) -> verify i (ret v) r. 
Proof.
by rewrite -[i]unitL=>H; apply: val_do=>// x m [->] // [->].
Qed.

Lemma try_ret e1 e2 (v : A) i (r : cont B) :
        verify i (e1 v) r -> verify i (ttry (ret v) e1 e2) r.
Proof. 
by rewrite -[i]unitL=>H; apply: try_do=>// x m [->] // [->].
Qed. 

Lemma bnd_ret e (v : A) i (r : cont B) : 
        verify i (e v) r -> verify i (bind (ret v) e) r.
Proof. by move=>H; apply: bnd_is_try; apply: try_ret. Qed.

End EvalReturn.


Section EvalRead.
Variables (A B : Type).

Lemma val_read v x i (r : cont A) : 
        (valid (x :-> v \+ i) -> r (Val v) (x :-> v \+ i)) -> 
        verify (x :-> v \+ i) (read A x) r.
Proof.
move=>*; apply: val_do; first by [exists v];
by move=>y m [<-]; move/(_ v (erefl _))=>// [->].
Qed.
 
Lemma try_read e1 e2 v x i (r : cont B) : 
        verify (x :-> v \+ i) (e1 v) r -> 
        verify (x :-> v \+ i) (ttry (read A x) e1 e2) r. 
Proof.
move=>*; apply: try_do; first by [exists v];
by move=>y m [<-]; move/(_ v (erefl _))=>// [->].
Qed.

Lemma bnd_read e v x i (r : cont B) : 
        verify (x :-> v \+ i) (e v) r -> 
        verify (x :-> v \+ i) (bind (read A x) e) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_read. Qed.

End EvalRead.


Section EvalWrite. 
Variables (A B C : Type).

Lemma val_write (v : A) (w : B) x i (r : cont unit) : 
        (valid (x :-> v \+ i) -> r (Val tt) (x :-> v \+ i)) -> 
        verify (x :-> w \+ i) (write x v) r.
Proof.
move=>*; apply: val_do; first by [exists B; exists w];
by move=>y m [// [->] ->].
Qed.

Lemma try_write e1 e2 (v: A) (w : C) x i (r : cont B) : 
        verify (x :-> v \+ i) (e1 tt) r -> 
        verify (x :-> w \+ i) (ttry (write x v) e1 e2) r. 
Proof.
move=>*; apply: try_do; first by [exists C; exists w];
by move=>y m [// [->] ->].
Qed.

Lemma bnd_write e (v : A) (w : C) x i (r : cont B) : 
        verify (x :-> v \+ i) (e tt) r -> 
        verify (x :-> w \+ i) (bind (write x v) e) r. 
Proof. by move=>*; apply: bnd_is_try; apply: try_write. Qed.

End EvalWrite.


Section EvalAlloc.
Variables (A B : Type).

Lemma val_alloc (v : A) i (r : cont ptr) : 
        (forall x, valid (x :-> v \+ i) -> r (Val x) (x :-> v \+ i)) -> 
        verify i (alloc v) r.
Proof.
move=>H; rewrite -[i]unitL; apply: val_do=>//; 
by move=>y m [x][//][-> ->]; apply: H.
Qed.

Lemma try_alloc e1 e2 (v : A) i (r : cont B) : 
        (forall x, verify (x :-> v \+ i) (e1 x) r) ->
        verify i (ttry (alloc v) e1 e2) r.
Proof.
move=>H; rewrite -[i]unitL; apply: try_do=>//;
by move=>y m [x][//][-> ->]; apply: H.
Qed.

Lemma bnd_alloc e (v : A) i (r : cont B) : 
        (forall x, verify (x :-> v \+ i) (e x) r) ->
        verify i (bind (alloc v) e) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_alloc. Qed.

End EvalAlloc.


Section EvalBlockAlloc.
Variables (A B : Type).

Lemma val_allocb (v : A) n i (r : cont ptr) : 
        (forall x, valid (updi x (nseq n v) \+ i) -> 
           r (Val x) (updi x (nseq n v) \+ i)) -> 
        verify i (allocb v n) r.
Proof.
move=>H; rewrite -[i]unitL; apply: val_do=>//;
by move=>y m [x][//][->->]; apply: H.
Qed.

Lemma try_allocb e1 e2 (v : A) n i (r : cont B) : 
        (forall x, verify (updi x (nseq n v) \+ i) (e1 x) r) ->
        verify i (ttry (allocb v n) e1 e2) r.
Proof.
move=>H; rewrite -[i]unitL; apply: try_do=>//;
by move=>y m [x][//][->->]; apply: H.
Qed.

Lemma bnd_allocb e (v : A) n i (r : cont B) : 
        (forall x, verify (updi x (nseq n v) \+ i) (e x) r) ->
        verify i (bind (allocb v n) e) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_allocb. Qed.

End EvalBlockAlloc.

Section EvalDealloc.
Variables (A B : Type).

Lemma val_dealloc (v : A) x i (r : cont unit) : 
        (valid i -> r (Val tt) i) -> 
        verify (x :-> v \+ i) (dealloc x) r.
Proof.
move=>H; apply: val_do; first by [exists A; exists v];
by move=>y m [//][->] ->; rewrite unitL.
Qed.

Lemma try_dealloc e1 e2 (v : B) x i (r : cont A) :
        verify i (e1 tt) r -> 
        verify (x :-> v \+ i) (ttry (dealloc x) e1 e2) r.
Proof.
move=>H; apply: try_do; first by [exists B; exists v];
by move=>y m [//][->] ->; rewrite unitL.
Qed.

Lemma bnd_dealloc e (v : B) x i (r : cont A) : 
        verify i (e tt) r -> 
        verify (x :-> v \+ i) (bind (dealloc x) e) r.
Proof. by move=>*; apply: bnd_is_try; apply: try_dealloc. Qed.

End EvalDealloc.


Section EvalThrow.

Lemma val_throw A x i (r : cont A) : 
        (valid i -> r (Exn x) i) -> verify i (throw A x) r.
Proof.
move=>H; rewrite -[i]unitL; apply: val_do=>//;
by move=>y m [->] // [->]; rewrite unitL.
Qed.

Lemma try_throw A B e1 e2 x i (r : cont B) : 
        verify i (e2 x) r -> 
        verify i (ttry (throw A x) e1 e2) r.
Proof.
move=>H; rewrite -[i]unitL; apply: try_do=>//;
by move=>y m [->] // [->]; rewrite unitL.
Qed.
 
Lemma bnd_throw A B e x i (r : cont B) : 
        (valid i -> r (Exn x) i) -> 
        verify i (bind (throw A x) e) r.
Proof.
by move=>H; apply: bnd_is_try; apply: try_throw; apply: val_throw.
Qed.

End EvalThrow.


(* specialized versions of do lemmas, to handle ghost variables. *)

Section EvalGhost.
Variables (A B C : Type) (t : C) (p : C -> Pred heap) (q : C -> post A).
Variables (i j : heap) (P : Pred heap).

Lemma val_gh {e} (r : cont A) : 
        let: s := (fun i => exists x, i \In p x, 
                   fun y i m => forall x, i \In p x -> q x y i m) in
        (forall x m, q t (Val x) i m -> valid (m \+ j) -> r (Val x) (m \+ j)) ->
        (forall x m, q t (Exn x) i m -> valid (m \+ j) -> r (Exn x) (m \+ j)) ->            
        i \In p t -> 
        verify (i \+ j) (with_spec s e) r.
Proof. by move=>*; apply: val_do=>/=; eauto. Qed.

Lemma val_gh1 {e} (r : cont A) : 
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in 
        (i \In p t -> P i) -> 
        (forall x m, q t (Val x) i m -> valid (m \+ j) -> r (Val x) (m \+ j)) -> 
        (forall x m, q t (Exn x) i m -> valid (m \+ j) -> r (Exn x) (m \+ j)) ->            
        i \In p t ->
        verify (i \+ j) (with_spec (P, Q) e) r.
Proof. by move=>*; apply: val_do=>/=; eauto. Qed.

Lemma try_gh {e e1 e2} (r : cont B) : 
        let: s := (fun i => exists x, i \In p x, 
                   fun y i m => forall x, i \In p x -> q x y i m) in 
        (forall x m, q t (Val x) i m -> verify (m \+ j) (e1 x) r) ->
        (forall x m, q t (Exn x) i m -> verify (m \+ j) (e2 x) r) ->
        i \In p t -> 
        verify (i \+ j) (ttry (with_spec s e) e1 e2) r.
Proof. by move=>*; apply: try_do=>/=; eauto. Qed.

Lemma try_gh1 {e e1 e2} (r : cont B) : 
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in 
        (i \In p t -> P i) -> 
        (forall x m, q t (Val x) i m -> verify (m \+ j) (e1 x) r) ->
        (forall x m, q t (Exn x) i m -> verify (m \+ j) (e2 x) r) ->
        i \In p t -> 
        verify (i \+ j) (ttry (with_spec (P, Q) e) e1 e2) r.
Proof. by move=>*; apply: try_do=>/=; eauto. Qed.

Lemma bnd_gh {e e1} (r : cont B) : 
        let: s := (fun i => exists x, i \In p x, 
                   fun y i m => forall x, i \In p x -> q x y i m) in 
        (forall x m, q t (Val x) i m -> verify (m \+ j) (e1 x) r) -> 
        (forall x m, q t (Exn x) i m -> valid (m \+ j) -> r (Exn x) (m \+ j)) ->
        i \In p t ->
        verify (i \+ j) (bind (with_spec s e) e1) r.
Proof. by move=>*; apply: bnd_do=>/=; eauto. Qed.

Lemma bnd_gh1 {e e1} (r : cont B) : 
        let: Q := fun y i m => forall x, i \In p x -> q x y i m in 
        (i \In p t -> P i) ->
        (forall x m, q t (Val x) i m -> verify (m \+ j) (e1 x) r) -> 
        (forall x m, q t (Exn x) i m -> valid (m \+ j) -> r (Exn x) (m \+ j)) ->
        i \In p t -> 
        verify (i \+ j) (bind (with_spec (P, Q) e) e1) r.
Proof. by move=>*; apply: bnd_do=>/=; eauto. Qed.


End EvalGhost.


Definition pull (A : Type) x (v:A) := (joinC (x :-> v), joinCA (x :-> v)).
Definition push (A : Type) x (v:A) := (joinCA (x :-> v), joinC (x :-> v)).


