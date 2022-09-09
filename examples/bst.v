From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq path.
From fcsl Require Import axioms pred ordtype.
From fcsl Require Import pcm unionmap heap autopcm automap.
From HTT Require Import model heapauto.
From HTT Require Import bintree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Obligation Tactic := auto.

Section BST.
Context {T : ordType}.

(* Helper lemmas *)

Lemma iffPb (b1 b2 : bool) : reflect (b1 <-> b2) (b1 == b2).
Proof.
case: eqP=>[->|N]; constructor=>//.
case: b1 b2 N; case=>//= _.
- by case=>/(_ erefl).
by case=>_ /(_ erefl).
Qed.

Lemma iffE (b1 b2 : bool) : b1 = b2 <-> (b1 <-> b2).
Proof. by split=>[->|] //; move/iffPb/eqP. Qed.
Lemma ord_neq (x y : T) : ord x y -> x != y.
Proof.
move=>H; apply/negP=>/eqP E.
by rewrite E irr in H.
Qed.

Lemma all_notin {A : eqType} (p : pred A) xs y :
  all p xs -> ~~ p y -> y \notin xs.
Proof. by move/allP=>Ha; apply/contra/Ha. Qed.

Lemma sorted_rconsE (xs : seq T) x :
  sorted ord (rcons xs x) = all (ord^~ x) xs && sorted ord xs.
Proof.
rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /= path_sortedE; last first.
- by move=>a b c Hab /trans; apply.
by rewrite all_rev rev_sorted.
Qed.

Lemma sorted_cat_cons_cat (l r : seq T) x :
  sorted ord (l ++ x :: r) = sorted ord (l ++ [::x]) && sorted ord (x::r).
Proof.
apply/iffE; split.
- by move/[dup]/cat_sorted2=>->; rewrite -cat1s catA =>/cat_sorted2 ->.
case/andP=>/= + H; rewrite cats1.
case: l=>//=a l; rewrite rcons_path=>/andP [H1 H2].
by rewrite cat_path /= H1 H2.
Qed.

(* bst operations *)

Fixpoint insert x (t : tree T) : tree T :=
  if t is Node l a r
    then
      if x == a then Node l a r
        else if ord x a then Node (insert x l) a r
                        else Node l a (insert x r)
  else Node leaf x leaf.

Fixpoint search (t : tree T) x : bool :=
  if t is Node l a r
    then
      if x == a then true
        else if ord x a then search l x
                        else search r x
  else false.

(* invariant *)

Fixpoint bst (t : tree T) : bool :=
  if t is Node l a r
    then [&& all (ord^~ a) (inorder l), all (ord a) (inorder r), bst l & bst r]
    else true.

Lemma bst_to_sorted (t : tree T) :
  bst t <-> sorted ord (inorder t).
Proof.
elim: t=>//=l IHl a r IHr.
rewrite sorted_cat_cons_cat /= cats1 (sorted_rconsE) (path_sortedE (@trans T)) -andbA.
split; case/and4P.
- by move=>->->/IHl->/IHr->.
by move=>->/IHl->->/IHr->.
Qed.

Lemma inorder_insert x (t : tree T) :
  bst t ->
  perm_eq (inorder (insert x t))
          (if x \in inorder t then inorder t else x :: inorder t).
Proof.
elim: t=>//=l IHl a r IHr /and4P [Hal Har /IHl Hl /IHr Hr] {IHl IHr}.
rewrite mem_cat inE; case: (ifP [|| _, _ | _]).
- case/or3P=>H.
  - rewrite H in Hl.
    move/allP: Hal=>/(_ x H) /[dup] Hxa /ord_neq/negbTE ->; rewrite Hxa /=.
    by apply/permEl/perm_catr.
  - by rewrite H.
  rewrite H in Hr.
  move/allP: Har=>/(_ x H) /[dup] /nsym/negP/negbTE ->.
  move/ord_neq; rewrite eq_sym =>/negbTE -> /=.
  by apply/permEl/perm_catl; rewrite perm_cons.
move/negbT; rewrite !negb_or; case/and3P=>/negbTE Hxl /negbTE Hx /negbTE Hxr.
rewrite {}Hxl in Hl; rewrite {}Hxr in Hr; case: (ordP x a)=>/= H.
- by rewrite -cat_cons; apply/permEl/perm_catr.
- by rewrite H in Hx.
rewrite -(cat1s x) -(cat1s a) -(cat1s a (inorder r)).
rewrite perm_sym perm_catC -!catA catA perm_sym catA.
apply/permEl/perm_catl; apply: (perm_trans Hr).
by rewrite cats1 -perm_rcons.
Qed.

Lemma bst_insert x (t : tree T) : bst t -> bst (insert x t).
Proof.
elim: t=>//=l IHl a r IHr /and4P [Hal Har Hl Hr].
case: ifP; first by move=>_ /=; rewrite Hal Har Hl Hr.
move=>Hx; case: ifP=>Ho /=.
- rewrite Har (IHl Hl) Hr /= andbT (perm_all _ (@inorder_insert x _ Hl)).
  by case: ifP=>//= _; rewrite Ho.
rewrite Hal Hl (IHr Hr) /= andbT (perm_all _ (@inorder_insert x _ Hr)).
case: ifP=>//= _; rewrite Har andbT.
by case: ordP=>//; [rewrite Ho| rewrite Hx].
Qed.

Lemma insert_insert x1 x2 (t : tree T) :
  bst t ->
  perm_eq (inorder (insert x1 (insert x2 t)))
          (inorder (insert x2 (insert x1 t))).
Proof.
move=>H.
have H1: (bst (insert x1 t)) by apply: bst_insert.
have H2: (bst (insert x2 t)) by apply: bst_insert.
apply: (perm_trans (inorder_insert x1 H2)); rewrite perm_sym.
apply: (perm_trans (inorder_insert x2 H1)).
rewrite (perm_mem (inorder_insert x1 H) x2) (perm_mem (inorder_insert x2 H) x1).
case: (ifP (x1 \in _))=>Hx1.
- case: (ifP (x2 \in _))=>Hx2.
  - apply: (perm_trans (inorder_insert x1 H)); rewrite Hx1 perm_sym.
    by apply: (perm_trans (inorder_insert x2 H)); rewrite Hx2.
  - rewrite inE Hx1 orbT perm_sym.
    apply: (perm_trans (inorder_insert x2 H)); rewrite Hx2 perm_cons perm_sym.
    by apply: (perm_trans (inorder_insert x1 H)); rewrite Hx1.
rewrite inE; case: ifP.
- case/orP.
  - by move/eqP=>->; rewrite Hx1 inE eq_refl /=.
  move=>Hx2; rewrite Hx2 Hx1.
  apply: (perm_trans (inorder_insert x1 H)); rewrite Hx1 perm_cons perm_sym.
  by apply: (perm_trans (inorder_insert x2 H)); rewrite Hx2.
move/negbT; rewrite negb_or; case/andP=>/negbTE HE /negbTE Hx2.
rewrite Hx2 inE Hx1 orbF eq_sym HE.
move: (inorder_insert x1 H); rewrite -(perm_cons x2) Hx1=>H'; apply: (perm_trans H').
rewrite -cat1s -(cat1s x1) perm_catCA /= perm_cons perm_sym.
by apply: (perm_trans (inorder_insert x2 H)); rewrite Hx2.
Qed.

Lemma inorder_search (t : tree T) :
  bst t ->
  search t =i inorder t.
Proof.
move=>+ x; elim: t=>//=l IHl a r IHr /and4P [Hal Har /IHl Hl /IHr Hr] {IHl IHr}.
rewrite -topredE /= in Hl; rewrite -topredE /= in Hr.
rewrite -topredE /= mem_cat inE.
case: ifP=>_ /=; first by rewrite orbT.
case: ifP=>Hx.
- rewrite Hl.
  suff: x \notin inorder r by move/negbTE=>->/=; rewrite orbF.
  by apply: (all_notin Har); apply/negP/nsym.
rewrite Hr.
suff: x \notin inorder l by move/negbTE=>->.
by apply: (all_notin Hal)=>/=; rewrite Hx.
Qed.

(* Procedures *)

Opaque mknode.

Definition inserttreeT x : Type :=
  forall p, {t : tree T}, STsep (treep p t, [vfun p' => treep p' (insert x t)]).

Program Definition inserttree x : inserttreeT x :=
  Fix (fun (go : inserttreeT x) p =>
       Do (if p == null
             then n <-- mknode x;
                  ret n
             else a <-- !(p.+ 1);
                  if x == a then ret p
                    else if ord x a then l <-- !p;
                                         l' <-- go l;
                                         p ::= l';;
                                         ret p
                                    else r <-- !(p.+ 2);
                                         r' <-- go r;
                                         p.+ 2 ::= r';;
                                         ret p)).
Next Obligation.
move=>x go p [t][] i /= H.
case: eqP H=>[{p}->|/eqP E] H.
- apply: vrfV=>V; case: (treep_null V H)=>{t H}->{i V}->.
  by apply: [stepE]=>//=; case=>//= n m H; step.
case: (treep_cont E H)=>l[z][r][pl][pr][_][{t H}->{i}->][hl][hr][-> Hl Hr].
step; case: eqP.
- move=>_; step=>_.
  by exists pl, pr, (hl \+ hr); split=>//; exists hl, hr.
move=>Exz; case: ifP=>Ho; step.
- apply: [stepX l]@hl=>//= p' h' H'.
  do 2![step]=>{pl Hl} _.
  by exists p', pr, (h' \+ hr); split=>//; exists h', hr.
apply: [stepX r]@hr=>//= p' h' H'.
do 2![step]=>{pr Hr} _.
by exists pl, p', (hl \+ h'); split=>//; exists hl, h'.
Qed.

Definition searchtreeT x : Type :=
  forall p, {t : tree T}, STsep (treep p t, [vfun b h => treep p t h /\ b == search t x]).

Program Definition searchtree x : searchtreeT x :=
  Fix (fun (go : searchtreeT x) p =>
       Do (if p == null
             then ret false
             else a <-- !(p.+ 1);
                  if x == a then ret true
                    else if ord x a then l <-- !p;
                                         go l
                                    else r <-- !(p.+ 2);
                                         go r)).
Next Obligation.
move=>x go p [t][] i /= H.
case: eqP H=>[{p}->|/eqP E] H.
- apply: vrfV=>V; case: (treep_null V H)=>{t H}->{i V}->.
  by step.
case: (treep_cont E H)=>l[z][r][pl][pr][_][{t H}->{i}->][hl][hr][-> Hl Hr].
step; case: eqP.
- move=>_; step=>_; split=>//.
  by exists pl, pr, (hl \+ hr); split=>//; exists hl, hr.
move=>Exz; case: ifP=>Ho; step.
- apply: [gX l]@hl=>//= b h' [H' E'] _; split=>{b E' hl Hl}//.
  by exists pl, pr, (h' \+ hr); split=>//; exists h', hr.
apply: [gX r]@hr=>//= b h' [H' E'] _; split=>{b E' hr Hr}//.
by exists pl, pr, (hl \+ h'); split=>//; exists hl, h'.
Qed.

Program Definition test p x1 x2 :
  {t : tree T}, STsep (fun h => treep p t h /\ bst t,
                      [vfun (pb : ptr * bool) h =>
                       let t' := insert x2 (insert x1 t) in
                       [/\ treep pb.1 t' h, bst t' & pb.2]]) :=
  Do (p1 <-- inserttree x1 p;
      p2 <-- inserttree x2 p1;
      r <-- searchtree x1 p2;
      ret (p2, r)).
Next Obligation.
move=>p x1 x2 [t][] i /= [Ht Hi].
apply: [stepE t]=>//=; case=>//= p1 h1 H1.
apply: [stepE (insert x1 t)]=>//=; case=>//= p2 h2 H2.
apply: [stepE (insert x2 (insert x1 t))]=>//=; case=>//= b h3 [H3 Hb].
step=>_.
have Hr2: bst (insert x2 t) by apply: bst_insert.
have Hr21: bst (insert x2 (insert x1 t)) by do 2![apply: bst_insert].
split=>//; rewrite (eqP Hb).
move: (inorder_search Hr21 x1); rewrite -topredE /= =>->.
rewrite (perm_mem (insert_insert _ _ Hi)) (perm_mem (inorder_insert x1 Hr2) x1).
by case: ifP=>// _; rewrite inE eq_refl.
Qed.

End BST.
