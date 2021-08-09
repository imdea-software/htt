From Coq Require Import ssreflect ssrbool ssrfun Eqdep.
From mathcomp Require Import ssrnat seq eqtype.
From fcsl Require Import axioms.
From fcsl Require Import options.

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
