From Coq Require Import ssreflect ssrbool ssrfun Eqdep.
From mathcomp Require Import ssrnat seq eqtype path.
From fcsl Require Import axioms ordtype.
From fcsl Require Import options.

Lemma filter_predC1 (A : eqType) (x : A) (s : seq A) :
        x \notin s -> filter (predC1 x) s = s.
Proof.
by move=>H; apply/all_filterP/allP=>y /=; case: eqP=>// ->; apply/contraL.
Qed.

Lemma has_takedrop {A : Type} (p : pred A) (s : seq A) x :
        has p s ->
          s = take (find p s) s ++ [::nth x s (find p s)] ++ drop (find p s).+1 s.
Proof.
move=>H.
set i := find p s.
have L1 : i < size s by rewrite /i -has_find.
rewrite -{1}(cat_take_drop i s).
by rewrite (drop_nth x).
Qed.

Lemma has_psplit (A : Type) (p : pred A) (s : seq A) (x : A) :
        has p s ->
          s = take (find p s) s ++ [::nth x s (find p s)] ++ drop (find p s).+1 s.
Proof.
move=>H.
set i := find p s.
have L1 : i < size s by rewrite /i -has_find.
rewrite -{1}(cat_take_drop i s).
by rewrite (drop_nth x).
Qed.

Lemma has_split (A : eqType) (x : A) (s : seq A) :
        x \in s -> exists s1 s2, s = s1 ++ [:: x] ++ s2.
Proof.
move=>H.
have L : has (pred1 x) s.
- by case: hasP=>//; elim; exists x=>/=.
move: (has_psplit x L).
set i := find (pred1 x) s.
rewrite (_ : nth x s i = x); last first.
- suff : pred1 x (nth x s i) by move/eqP.
  by apply: nth_find.
by move=>->; exists (take i s), (drop i.+1 s).
Qed.

Lemma has_split_uniq (A : eqType) (x : A) (s : seq A) :
       x \in s -> uniq s ->
         exists s1 s2, s = s1 ++ [:: x] ++ s2 /\
           uniq (s1 ++ s2) /\ x \notin (s1 ++ s2).
Proof.
move=>H1 H2; move: (has_split H1)=>[s1 [s2 H3]].
exists s1; exists s2; move: H2.
rewrite H3 uniq_catCA cons_uniq.
by move/andP=>[].
Qed.

Lemma mem_split {T : eqType} (x : T) (s : seq T) :
        x \in s -> exists s1, exists s2, s = s1 ++ [:: x] ++ s2.
Proof.
move=>H.
have L : has (pred1 x) s.
- by case: hasP=>//; elim; exists x=>/=.
move: (has_takedrop x L).
set i := find (pred1 x) s.
rewrite (_ : nth x s i = x); last first.
- suff : pred1 x (nth x s i) by move/eqP.
  by apply: nth_find.
eauto.
Qed.

(* TODO this should be expressible directly *)
Lemma path_relax {K : ordType} (k k' : K) ks : ord k k' -> path ord k' ks -> path ord k ks.
Proof.
move=>O; case: ks=>//= a l /andP [O2 P2].
apply/andP; split=>//.
by apply/trans/O2.
Qed.
