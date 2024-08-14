(*
Copyright 2020 IMDEA Software Institute
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

(******************)
(* Key-Value maps *)
(******************)

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq path ssrnat.
From pcm Require Import options axioms pred ordtype finmap seqext.
From pcm Require Import pcm unionmap heap autopcm automap.
From htt Require Import options model heapauto.

(***********************)
(* stateful KV map ADT *)
(***********************)

(* Dynamic KV map is determined by its root pointer(s). *)
(* Functions such insert and remove may modify *)
(* the root, and will correspondingly return the new one. *)
(* Tp is abstracted to facilitate structures that may *)
(* have more than one root pointers. Also, it enables *)
(* passing K and V to methods thus reducing annotations *)
(* There's no deep reason to make tp : Set, except that *)
(* it should be thought of a collection of pointers, hence small. *)
Module DynKVmap.
Record Sig (K : ordType) (V : Type) : Type :=
  make {tp :> Set;
        default : tp;
        shape : tp -> {finMap K -> V} -> Pred heap;
        new : STsep (emp, [vfun x => shape x (nil K V)]);
        free : forall x, STsep {s} (shape x s,
                                   [vfun _ : unit => emp]);
        insert : forall x k v,
                   STsep {s} (shape x s,
                             [vfun y => shape y (ins k v s)]);
        remove : forall x k,
                   STsep {s} (shape x s,
                             [vfun y => shape y (rem k s)]);
        lookup : forall x k,
                   STsep {s} (shape x s,
                             [vfun y m => m \In shape x s /\ y = fnd k s])}.
End DynKVmap.

(* Static KV map (or just KV map) are those that *)
(* don't need to modify the root pointer. *)
(* Typical example will be hash tables *)
(* Another example is a structure obtained by packaing *)
(* the root pointer along with the dynamic KV map that the *)
(*  root points to. *)

Module KVmap.
Record Sig (K : ordType) (V : Type) : Type :=
  make {tp :> Set;
        default : tp;
        shape : tp -> {finMap K -> V} -> Pred heap;
        (* allocate root pointer and empty structure *)
        new : STsep (emp, [vfun x => shape x (nil K V)]);
        (* remove the struture, and the root pointer *)
        free : forall x, STsep {s} (shape x s,
                                   [vfun _ : unit => emp]);
        (* insert, keeping the root pointer unchanged *)
        insert : forall x k v,
                   STsep {s} (shape x s,
                             [vfun _ : unit => shape x (ins k v s)]);
        (* remove, keeping the root pointer unchanged *)
        remove : forall x k,
                   STsep {s} (shape x s,
                             [vfun _ : unit => shape x (rem k s)]);
        lookup : forall x k,
                   STsep {s} (shape x s,
                             [vfun y m => m \In shape x s /\ y = fnd k s])}.
End KVmap.

(**********************************************************)
(* KV map implemented as a sorted association linked list *)
(**********************************************************)

Module DynAssocList.
Section AssocList.
Variables (K : ordType) (V : Set).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

(* single entry of the map as a triple of heap cells *)
Definition entry (p q : ptr) (k : K) (v : V) : heap :=
  p :-> k \+ p.+1 :-> v \+ p.+2 :-> q.

(* similarly to plain linked list *)
(* development starts with generic definition of list segment *)
(* and then specializes to self-contained lists specified *)
(* by finMap structure *)
Fixpoint shape_seg' (x y : ptr) (xs : seq (K * V)) : Pred heap :=
  if xs is (k,v) :: tl then
     [Pred h | exists q h',
       h = entry x q k v \+ h'
     /\ h' \In shape_seg' q y tl]
  else [Pred h | x = y /\ h = Unit].

Definition shape_seg (x y : ptr) (s : fmap) : Pred heap :=
  shape_seg' x y (seq_of s).

Definition shape (x : ptr) (s : fmap) : Pred heap :=
  shape_seg x null s.

(* null pointer represents empty map *)
Lemma shape_null (s : fmap) h :
        valid h -> 
        h \In shape null s ->
        s = nil /\ h = Unit.
Proof.
move=>D; case: s; case=>/=.
- by move=>? [_ ->] //; rewrite fmapE.
move=>[??]??[?][?][H].
by rewrite H -!joinA validPtUn in D.
Qed.

(* non-empty well-formed region represents a non-empty map such that *)
(* a head entry respecting the key order can be pulled out of the map *)
Lemma shape_cont (s : fmap) p h :
        p != null -> 
        h \In shape p s ->
        exists k v q h',
          [/\ s = ins k v (behd s),   (* k:->v is the head entry *)
              all (ord k) (supp (behd s)),
              h = entry p q k v \+ h' &
              h' \In shape q (behd s)].
Proof.
move=>E; case: s=>xs srt /=.
elim: xs srt=>/=; first by move=>? [E0]; rewrite E0 in E.
move=>[k v] /= l IH srt [q][h'][-> H].
exists k, v, q, h'; split=>//; last by apply: order_path_min.
by rewrite fmapE /= last_ins'.
Qed.

(* inserting an entry with minimal key is prepending to the list *)
Lemma shape_cons (s : fmap) p q h k v :
        all (ord k) (supp s) -> 
        h \In shape q s ->
        entry p q k v \+ h \In shape p (ins k v s).
Proof.
move/all_path_supp=>S H.
suff: ins k v s = @FinMap _ _ ((k,v)::seq_of s) S by move=>->; exists q,h.
rewrite fmapE /=; case: s {H}S=>/= xs ??.
by rewrite last_ins'.
Qed.

(* inserting an entry with maximal key is appending to the list *)
Lemma shape_seg_rcons (s : fmap) x p q h k v :
        (* conceptually last s < k *)
        all (ord^~ k) (supp s) ->
        h \In shape_seg x p s ->
        (h \+ entry p q k v) \In shape_seg x q (ins k v s).
Proof.
case: s=>xs; elim: xs h x=>/=.
- move=>??? _ [->->]; rewrite unitL.
  by exists q, Unit; rewrite unitR.
move=>[k' v'] /= xs IH _ x S /andP [O Os] [x0][h'][-> H'].
rewrite /shape_seg /=; move/nsym/negP/negbTE: (O)=>->.
case: ordP O=>//= _ _.
exists x0, (h' \+ entry p q k v); rewrite -!joinA; split=>//.
by apply: IH=>//; apply: (path_sorted S).
Qed.

(* disjoint maps can be concatenated if the order is respected *)
Lemma shape_fcat s1 s2 h1 h2 x y :
        (* conceptually last s1 < head s2 *)
        allrel ord (supp s1) (supp s2) ->
        h1 \In shape_seg x y s1 -> 
        h2 \In shape y s2 ->
        h1 \+ h2 \In shape x (fcat s1 s2).
Proof.
move=>O1 H1.
case: s2 O1=>xs; elim: xs h1 y h2 s1 H1=>/=.
- by move=>???? H1 ? _ [Eq ->]; rewrite Eq in H1; rewrite unitR.
move=>[k' v'] xs; rewrite /fcat /= => IH /= h1 y h2 s1 H1 srt O2 H2.
case: H2=>z[h'][-> H']; rewrite joinA; apply: IH; first 1 last.
- by apply/path_sorted/srt.
- move=>H0; rewrite (allrel_in_l (xs':=k'::supp s1) _); last by apply: supp_ins.
  rewrite allrel_consl order_path_min //=.
  by apply/allrel_sub_r/O2=>?; rewrite inE orbC=>->.
- by move=>?; apply: H'.
apply: shape_seg_rcons=>//.
by move: O2; rewrite allrel_consr =>/andP [].
Qed.

(* main procedures *)

(* new map is just a null pointer *)
Program Definition new : STsep (emp, [vfun x => shape x nil]) :=
  Do (ret null).
Next Obligation. by case=>_ /= ->; step. Qed.

(* freeing a map is deallocating all its elements *)
(* and the root pointer *)
Definition freeT : Type :=
  forall p, STsep {fm} (shape p fm, [vfun _ : unit => emp]).

Program Definition free : freeT :=
  ffix (fun (loop : freeT) p =>
    Do (if p == null then ret tt
        else pnext <-- !p.+2;
             dealloc p;;
             dealloc p.+1;;
             dealloc p.+2;;
             loop pnext)).
Next Obligation.
(* pull out ghost var, precondition, branch *)
move=>loop p [fm][] i /= H; case: eqP=>[|/eqP] E.
(* reached the end, heap must be empty *)
- by apply: vrfV=>D; step=>_; rewrite E in H; case: (shape_null D H).
(* pull out the head entry *)
case: (shape_cont E H)=>k[v][q][h][_ _ {i H}-> H].
(* deallocate it *)
do 4!step; rewrite !unitL.
(* invoke the loop on the tail *)
by apply: [gE (behd fm)].
Qed.

(* looking up an element in the map *)


Definition lookupT k : Type :=
  forall p, STsep {fm} (shape p fm,
                       [vfun y m => m \In shape p fm /\ y = fnd k fm]).

Program Definition lookup x (k : K) :
  STsep {fm} (shape x fm,
             [vfun y m => m \In shape x fm /\ y = fnd k fm]) :=
  ffix (fun (loop : lookupT k) (cur : ptr) =>
       Do (if cur == null then ret None
           else
             k' <-- !cur;
             if k == k'
             then v <-- !cur.+1;
                  ret (Some v)
             else if ord k' k
                  then next <-- !cur.+2;
                       loop next
                  else ret None)) x.
Next Obligation.
(* pull out ghost var+precondition, branch on cur being null *)
move=>_ k go cur [fm][] h /= H; case: eqP=>[|/eqP] Ec.
(* reached the end, heap and spec must be empty, element not found *)
- by apply: vrfV=>Vh; step=>_; rewrite Ec in H; case: (shape_null Vh H)=>->.
(* pull out head entry *)
case: (shape_cont Ec H)=>k'[v][next][h'][Ef O' Ei H']; rewrite {h}Ei in H *.
(* read the head key, branch on equality comparison *)
step; case: eqP=>[|/eqP] Ek.
(* the key matches, return the head value *)
- by do 2![step]=>_; split=>//; rewrite Ef fnd_ins Ek eq_refl.
(* branch on comparison *)
case: ifP=>Ho'.
(* head key is less than the needed one, loop on tail *)
(* (fall back to gR to preserve associativity) *)
- step; apply/[gR (behd fm)] @ h'=>//= v0 h0' [H0 E0] _.
  by rewrite Ef fnd_ins (negbTE Ek); split=>//; exact: shape_cons.
(* head key is bigger than the needed one, abort *)
move: (connex Ek); rewrite {}Ho' orbC /= =>Ho'; step=>_; split=>//.
(* k is not in the head entry *)
apply/esym/fnd_supp; rewrite Ef supp_ins inE negb_or; apply/andP; split=>//.
(* nor it is in the tail *)
by apply/notin_path/path_le/all_path_supp/O'.
Qed.

(* removing element by key from the map, return the pointer to the new map *)

(* loop invariant: *)
(* 1. split the list into a zipper-like structure `fml ++ [k'->v'] ++ fmr` *)
(* 2. ordering is respected *)
(* 3. k is not in fml nor in the focus entry k'->v' *)
(* the focus is needed to connect the remainder of the map to it after removal *)
Definition removeT p k : Type :=
  forall (prevcur : ptr * ptr),
    STsep {fm} (fun h => exists fml fmr k' v',
                  [/\ fm = fcat (ins k' v' fml) fmr,
                      all (ord^~ k') (supp fml) /\ all (ord k') (supp fmr),
                      k \notin supp fml /\ k != k' &
                      h \In
                       (shape_seg p prevcur.1 fml #
                       (fun h => h = entry prevcur.1 prevcur.2 k' v') #
                       shape prevcur.2 fmr)],
               [vfun _ : unit => shape p (rem k fm)]).

Program Definition remove x (k : K) :
  STsep {fm} (shape x fm,
             [vfun y => shape y (rem k fm)]) :=
  Do (let go := ffix (fun (loop : removeT x k) '(prev, cur) =>
                     Do (if cur == null then ret tt
                         else k' <-- !cur;
                              if k == k'
                                then next <-- !cur.+2;
                                     dealloc cur;;
                                     dealloc cur.+1;;
                                     dealloc cur.+2;;
                                     prev.+2 ::= (next : ptr);;
                                     ret tt
                                else if ord k' k
                                     then next <-- !cur.+2;
                                          loop (cur, next)
                                     else ret tt))
      in
      if x == null then ret null
        else k' <-- !x;
             if k == k'
                then next <-- !x.+2;
                     dealloc x;;
                     dealloc x.+1;;
                     dealloc x.+2;;
                     ret next
                else if ord k' k
                     then next <-- !x.+2;
                          go (x, next);;
                          ret x
                     else ret x).
(* first the loop *)
(* don't return the pointer because it cannot change *)
(* as the head is fixed by fml *)
Next Obligation.
(* pull out ghost var, preconditions and heap validity *)
move=>x k0 go _ prev cur [_][] _ /= [fml][fmr][k][v][-> [Ol Or]
[El E]][hl][_][-> Hl [_][hr][->->Hr]].
(* branch on cur *)
case: eqP=>[|/eqP] Ec.
  (* cur = null - nothing to left to process, i.e., fmr = [] *)
- apply: vrfV=>Vh; step=>_; rewrite {}Ec in Hr *.
  (* k is not in fml ++ (k->v) *)
  case: (shape_null (validX Vh) Hr)=>/=->->.
  rewrite fcats0 unitR rem_ins (negbTE E) (rem_supp El).
  exact: shape_seg_rcons.
(* cur <> null, pull out the head entry from fmr *)
case: (shape_cont Ec Hr)=>k'[v'][next][hr']
[Efr /all_path_supp Or' {hr Hr Ec}-> Hr']; rewrite joinA joinC.
(* derive ordering facts *)
move/all_path_supp: (Or); rewrite {1}Efr; 
case/(path_supp_ins_inv Or')/andP=>Ho' Or''.
(* get head key, branch on comparing it to needed one *)
step; case: eqP=>[|/eqP] Ek.
  (* k = k' - element is found, run the deallocations *)
- do 4!step; rewrite !unitL; do 2![step]=>_.
  (* pull out fml ++ (k->v) *)
  rewrite Efr -fcat_srem; last by rewrite supp_ins inE negb_or E.
  (* drop the element in the spec *)
  rewrite rem_ins {1}Ek eq_refl rem_supp; 
    last by rewrite Ek; apply: notin_path.
  (* heap shape is respected *)
  rewrite joinC; apply/shape_fcat/Hr'; last by apply: shape_seg_rcons.
  (* the ordering is respected as well *)
  rewrite (allrel_in_l (xs':=k::supp fml) _); last by apply: supp_ins.
  rewrite allrel_consl order_path_min //=.
  by apply/(allrel_trans (z:=k))/order_path_min=>//=.
(* k <> k', now branch on order comparison *)
case: ifP=>Ho0.
(* k' is less than k, invoke the loop, shifting the focus to the right *)
- step; apply: [gE (fcat (ins k' v' (ins k v fml)) (behd fmr))]=>//=.
  (* prove that all conditions are respected *)
  - exists (ins k v fml), (behd fmr), k', v'; do!split=>//.
      (* new focus comes after fml ++ old focus *)
    - rewrite (eq_all_r (s2:=k::supp fml)) /= ?Ho' /=; 
        last by apply: supp_ins.
      by apply/sub_all/Ol=>? /trans; apply.
      (* new focus comes before the new suffix *)
    - by apply: order_path_min.
      (* the needed key is not in fml ++ old focus *)
    - by rewrite supp_ins inE negb_or E.
    (* heap shape is respected *)
    exists (hl \+ entry prev cur k v), (entry cur next k' v' \+ hr').
    rewrite joinC; split=>//; last by vauto.
    by apply: shape_seg_rcons.
  (* reassemble the spec, as insertions of old and new foci commute *)
  move=>_ m Hm Vm; rewrite Efr.
  by rewrite fcat_inss // -?fcat_sins // in Hm; apply: notin_path.
(* k' is bigger than k, abort *)
move: (connex Ek); rewrite {}Ho0 orbC /= =>Ho0.
step=>_; rewrite rem_supp.
- (* the shape is preserved *)
  rewrite joinC; apply: shape_fcat; first 1 last.
  - by apply: shape_seg_rcons.
  - by rewrite Efr; apply: shape_cons=>//; apply: order_path_min.
  (* ordering is preserved *)
  rewrite (allrel_in_l (xs':=k::supp fml) _); last by apply: supp_ins.
  rewrite allrel_consl Or /=.
  by apply/(allrel_trans (z:=k))=>//; exact: trans.
(* the element wasn't found *)
rewrite Efr supp_fcat !inE negb_or; apply/andP; split;
  rewrite supp_ins !inE negb_or; apply/andP; split=>//.
by apply/notin_path/path_le/Or'.
Qed.
(* now the outer function, which mostly repeats the loop *)
(* the first iteration is special because we don't yet have a left prefix *)
(* to connect to the remainder if the head is removed *)
Next Obligation.
(* pull out ghost+precondition, branch on x *)
move=>/= x k0 [fm][]i /= H; case: eqP=>[|/eqP] Ex.
- (* x is null, nothing to process *)
  by apply: vrfV=>Vh; move: H; rewrite Ex =>/(shape_null Vh) [->->]; step=>_.
(* x <> null, pull out the head entry *)
case: (shape_cont Ex H)=>{Ex}k[v][next][h'][Ef Of Eh H']; rewrite Eh.
(* read the key, branch on equality comparison *)
step; case: eqP=>[->|/eqP Ek].
- (* k = k', element found in head position, run deallocations, return new head *)
  do 5![step]=>_; rewrite !unitL Ef rem_ins eq_refl rem_supp //.
  by apply/notin_path/all_path_supp.
(* k <> k', now branch on order comparison *)
case: ifP=>Ho0.
(* k' is less than k, start the loop with the head entry as the focus *)
- step; apply: [stepE fm]=>//=; last by move=>_ ??; step.
  (* invariants and shape are satisfied *)
  exists nil, (behd fm), k, v; do!split=>//.
  - by rewrite fcat_inss; [rewrite fcat0s|apply/notin_path/all_path_supp].
  by exists Unit, (entry x next k v \+ h'); split=>//; [rewrite unitL | vauto].
(* k' is bigger than k, abort *)
move: (connex Ek); rewrite {}Ho0 orbC /= =>Ho0.
(* return the old head, invariants are preserved *)
step=>_; rewrite -Eh rem_supp // Ef supp_ins !inE negb_or Ek /=.
by apply/notin_path/path_le/all_path_supp/Of.
Qed.

(* upserting (inserting or updating if the key is found) *)
(* an entry into the map, return the pointer to the new map *)

(* loop invariant, essentially identical to remove: *)
(* 1. as in remove, split the list into a zipper-like structure *)
(*    `fml ++ [k'->v'] ++ fmr` *)
(* 2. the ordering is respected *)
(* 3. k is not in fml and is less than the key k' of focus entry *)
(* the focus is needed to connect the new element after insertion *)
Definition insertT p k v : Type :=
  forall (prevcur : ptr * ptr),
    STsep {fm} (fun h => exists fml fmr k' v',
                  [/\ fm = fcat (ins k' v' fml) fmr,
                      all (ord^~ k') (supp fml) /\ all (ord k') (supp fmr),
                      k \notin supp fml /\ ord k' k &
                      h \In
                       (shape_seg p prevcur.1 fml #
                       (fun h => h = entry prevcur.1 prevcur.2 k' v') #
                       shape prevcur.2 fmr)],
               [vfun _ : unit => shape p (ins k v fm)]).

Program Definition insert x (k : K) (v : V) :
  STsep {fm} (shape x fm,
             [vfun y => shape y (ins k v fm)]) :=
  Do (let go := ffix (fun (loop : insertT x k v) '(prev, cur) =>
                     Do (if cur == null
                           then new <-- allocb k 3;
                                new.+1 ::= v;;
                                new.+2 ::= null;;
                                prev.+2 ::= new;;
                                ret tt
                           else k' <-- !cur;
                                if k == k'
                                  then cur.+1 ::= v;;
                                       ret tt
                                  else if ord k' k
                                       then next <-- !cur.+2;
                                            loop (cur, next)
                                       else new <-- allocb k 3;
                                            new.+1 ::= v;;
                                            new.+2 ::= cur;;
                                            prev.+2 ::= new;;
                                            ret tt))
      in
      if x == null
        then new <-- allocb k 3;
             new.+1 ::= v;;
             new.+2 ::= null;;
             ret new
        else k' <-- !x;
             if k == k'
               then x.+1 ::= v;;
                    ret x
               else if ord k' k
                    then next <-- !x.+2;
                         go (x, next);;
                         ret x
                    else new <-- allocb k 3;
                         new.+1 ::= v;;
                         new.+2 ::= x;;
                         ret new).
(* first the loop *)
(* don't return the pointer because it cannot change *)
(* as the head is fixed by fml *)
Next Obligation.
(* pull out ghost var+preconditions *)
move=>x k0 v0 loop _ prev cur [_][] _ /= [fml][fmr][k][v]
[-> [Ol Or][El Ho0]][hl][_][-> Hl [_][hr][->-> Hr]].
(* branch on cur *)
case: eqP=>[|/eqP] Ec.
(* cur = null, insert as the last element *)
- rewrite {}Ec in Hr; apply: vrfV=>Vh.
  step=>p; rewrite unitR; do 2!step; rewrite joinC; do 2![step]=>_.
  (* fmr is empty *)
  case: (shape_null (validX Vh) Hr)=>/=->->.
  rewrite fcats0 unitR [X in _ \+ entry _ _ _ _ \+ X]joinA.
  (* shape and ordering invariants are satisfied *)
  apply/shape_seg_rcons/shape_seg_rcons=>//.
  rewrite (eq_all_r (s2:=k::supp fml)) /= ?Ho0 /=; last by apply: supp_ins.
  by apply/sub_all/Ol=>? /trans; apply.
(* cur <> null, pull out the head entry from fmr *)
case: (shape_cont Ec Hr)=>k'[v'][next][hr'][Efr Or' {hr Hr Ec}-> Hr']. 
rewrite joinA joinC.
(* derive ordering facts *)
move/all_path_supp: (Or); rewrite {1}Efr.
case/(path_supp_ins_inv (all_path_supp Or'))/andP=>Ho'.
move/(order_path_min (@trans _))=>Or''.
(* get new key, branch on equality comparison *)
step; case: eqP=>[|/eqP] Ek.
(* k = k', update the value at this position *)
- do 2![step]=>_; rewrite Efr -fcat_sins ins_ins -Ek eq_refl joinC.
  (* invariants are preserved as the key didn't change *)
  apply: shape_fcat; first 1 last.
  - by apply: shape_seg_rcons.
  - by apply: shape_cons=>//; rewrite Ek.
  rewrite (allrel_in_l (xs':=k::supp fml) _); last by apply: supp_ins.
  rewrite (allrel_in_r (ys':=k0::supp (behd fmr)) _ _); last by apply: supp_ins.
  rewrite allrel_consl allrel_consr /= Ho0 Or'' /=; apply/andP; split.
  - by apply/sub_all/Ol=>? /trans; apply.
  by apply: (allrel_trans (z:=k))=>//; exact: trans.
(* k <> k', now branch on order comparison *)
case: ifP=>Ho'0.
(* k' is less than k, invoke the loop, shifting the focus to the right *)
- step; apply/[gE (fcat (ins k' v' (ins k v fml)) (behd fmr))]=>//=.
  (* prove that all conditions are respected *)
  - exists (ins k v fml), (behd fmr), k', v'; do!split=>//.
    (* new focus comes after fml ++ old focus *)
    - rewrite (eq_all_r (s2:=k::supp fml)) /= ?Ho' /=; last by apply: supp_ins.
      by apply/sub_all/Ol=>? /trans; apply.
    (* the needed key is not in fml ++ old focus *)
    - rewrite supp_ins inE negb_or andbC El /=.
      by case: ordP Ho0.
    (* heap shape is respected *)
    exists (hl \+ entry prev cur k v), (entry cur next k' v' \+ hr').
    by rewrite joinC; split=>//; [apply: shape_seg_rcons | vauto].
  (* reassemble the spec, as insertions of old and new foci commute *)
  move=>_ m Hm _; rewrite Efr.
  rewrite fcat_inss // in Hm; first by rewrite -fcat_sins in Hm.
  by apply/notin_path/all_path_supp.
(* k' is bigger than k, insert at this position *)
move: (connex Ek); rewrite {}Ho'0 orbC /= =>Ho0'.
(* run the allocation and assignments *)
step=>new; rewrite unitR; do 2!step; rewrite joinA joinC; do 2![step]=>_.
rewrite Efr -fcat_sins; apply: shape_fcat; first 1 last.
(* shape is respected for the prefix fml ++ old focus *)
- by apply: shape_seg_rcons.
(* shape is satisfed for new element + suffix *)
- rewrite [X in X \+ (entry _ _ _ _ \+ _)]joinA.
  apply/shape_cons/shape_cons=>//.
  apply/order_path_min=>//; apply/path_supp_ins=>//.
  by apply/path_le/all_path_supp/Or'.
(* ordering is respected *)
rewrite (allrel_in_l (xs':=k::supp fml) _); last by apply: supp_ins.
rewrite (allrel_in_r (ys':=k0::k'::supp (behd fmr)) _ _); last first.
- by move=>?; rewrite ?(supp_ins,inE).
rewrite allrel_consl !allrel_consr /= Ho0 Ho' Or'' /=; apply/and3P; split.
- by apply/sub_all/Ol=>? /trans; apply.
- by apply/sub_all/Ol=>? /trans; apply.
by apply: (allrel_trans (z:=k))=>//; apply: trans.
Qed.
(* now the outer function, which mostly repeats the loop *)
(* the first iteration is special because we don't yet have a left prefix *)
(* to connect to the new element if it inserted at the head position *)
Next Obligation.
(* pull out ghost+precondition, branch on x *)
move=>/= x k0 v0 [fm][]h /= H; case: eqP=>[|/eqP] Ex.
(* x = null, insert as the only element, heap and spec are empty *)
- apply: vrfV=>Vh; move: H; rewrite Ex=>/(shape_null Vh) [->->].
  (* run *)
  step=>p; rewrite !unitR; do 3![step]=>_.
  by exists null, Unit; rewrite unitR joinA.
(* x <> null, pull out the head entry *)
case: (shape_cont Ex H)=>{Ex}k[v][next][h'][Ef Of {h H}-> H].
(* read the head key, branch on equality comparison *)
step; case: eqP=>[->|/eqP Ek].
(* k = k', exact key found in head position, update the head value *)
- do 2![step]=>_; rewrite Ef ins_ins eq_refl.
  by apply: shape_cons.
(* k <> k', now branch on order comparison *)
case: ifP=>Ho0.
(* k' is less than k, run the loop with the head entry as the focus *)
- step; apply: [stepE fm]=>//=; last by move=>_ ??; step.
  (* invariants are respected *)
  exists nil, (behd fm), k, v; do!split=>//.
  - by rewrite fcat_inss; [rewrite fcat0s|apply/notin_path/all_path_supp].
  by exists Unit, (entry x next k v \+ h'); split=>//; [rewrite unitL|vauto].
(* k' is bigger than k, insert after the head *)
move: (connex Ek); rewrite {}Ho0 orbC /= =>Ho0.
(* run allocation and assignments, return the old head *)
step=>q; rewrite unitR; do 3![step]=>_.
(* invariants are preserved *)
rewrite Ef [X in X \+ (entry _ _ _ _ \+ _)]joinA.
apply/shape_cons/shape_cons=>//.
apply/order_path_min=>//.
apply/path_supp_ins=>//.
by apply/path_le/all_path_supp/Of.
Qed.

(* ordered association list is a dynamic KV map *)

Definition AssocList := DynKVmap.make null new free insert remove lookup.
End AssocList.
End DynAssocList.

(* static variant packages the root pointer *)
(* with the dynamic part of the structure *)

Module AssocList.
Section AssocList.
Variables (K : ordType) (V : Set).
Notation fmap := (finMap K V).
Notation nil := (nil K V).

Definition shape (x : ptr) (f : fmap) : Pred heap := 
  [Pred h | exists (a : ptr) h', 
     h = x :-> a \+ h' /\ @DynAssocList.shape K V a f h'].

(* new structure, but the root pointer is given *)
Program Definition new0 (x : ptr) : 
    STsep {a : ptr} (fun h => h = x :-> a, 
                    [vfun _ : unit => shape x nil]) := 
  Do (a <-- @DynAssocList.new K V;
      x ::= a).
Next Obligation.
move=>x [a][/= _ ->]; apply: [stepU]=>//= b h H.
by step; exists b, h; rewrite joinC. 
Qed.

Program Definition new : 
    STsep (emp, [vfun x => shape x nil]) := 
  Do (a <-- @DynAssocList.new K V;
      alloc a).
Next Obligation.
case=>_ /= ->; apply: [stepU]=>//= a h H.
by step=>x; exists a, h; rewrite unitR. 
Qed.

(* free structure, keep the root pointer *)
Program Definition free0 x : 
    STsep {s} (shape x s,
              [vfun (_ : unit) h => exists a : ptr, h = x :-> a]) := 
  Do (a <-- !x;
      DynAssocList.free K V a).
Next Obligation.
move=>x [fm][/= _ [a][h][-> H]]; step.
by apply: [gX fm]@h=>//= _ _ -> _; rewrite unitR; eauto.
Qed.

Program Definition free x : 
    STsep {s} (shape x s,
              [vfun _ : unit => emp]) := 
  Do (a <-- !x;
      dealloc x;;
      DynAssocList.free K V a).
Next Obligation.
by move=>x [fm][/= _ [a][h][-> H]]; step; step; apply: [gX fm]@h.
Qed.

Program Definition insert x k v :
    STsep {s} (shape x s,
              [vfun _ : unit => shape x (ins k v s)]) := 
  Do (a <-- !x; 
      y <-- DynAssocList.insert a k v;
      x ::= y).
Next Obligation.
move=>x k v [fm][/= _ [a][h][-> H]]; step.
by apply: [stepX fm]@h=>//= y {}h {}H; step; hhauto.
Qed.

Program Definition remove x k : 
    STsep {s} (shape x s,
              [vfun _ : unit => shape x (rem k s)]) := 
  Do (a <-- !x;
      y <-- DynAssocList.remove V a k;
      x ::= y).
Next Obligation.
move=>x k [fm][/= _ [a][h][-> H]]; step.
by apply: [stepX fm]@h=>//= y {}h {}H; step; hhauto.
Qed.

Program Definition lookup x k : 
    STsep {s} (shape x s,
              [vfun y m => m \In shape x s /\ y = fnd k s]) := 
  Do (a <-- !x;
      DynAssocList.lookup V a k).
Next Obligation.
move=>x k [fm][/= _ [a][h][-> H]]; step.
by apply: [gX fm]@h=>//= y {}h {H}[]; hhauto.
Qed.

(* ordered association list is a KV map *)
Definition AssocList := KVmap.make null new free insert remove lookup.
End AssocList.
End AssocList.
