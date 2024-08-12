(*
Copyright 2021 IMDEA Software Institute
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

From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq ssrnat.
From pcm Require Import options axioms pred seqext.
From pcm Require Import pcm unionmap heap auto automap autopcm.
From htt Require Import options model heapauto.
From htt Require Import llist.

(* queue variant with fixed capacity *)
(* that overwrites data in a circular way *)

(* the structure is a pair of pointers: *)
(* a mutable length and immutable capacity *)
Record buffer (T : Type) : Type :=
  Buf {active: ptr; inactive: ptr; len: ptr; capacity: nat}.

Definition BufferFull : exn := exn_from_nat 10.
Definition BufferEmpty : exn := exn_from_nat 20.

Module Buffer.
Section Buffer.
Variable T : Type.
Notation buffer := (buffer T).

(* the active part of the buffer is specified by a given list *)
(* the inactive part by another arbitrary list *)
(* length is the size of the active part, capacity is the sum *)
(* the two parts are joined head-to-tail forming the titular cycle *)
Definition is_buffer (a i : ptr) (m n : nat) (xs : seq T) :=
  [Pred h | exists (ys : seq T) ha hi,
            [/\ h = ha \+ hi,
                n = size xs + size ys,
                m = size xs,
                ha \In lseg a i xs &
                hi \In lseg i a ys]].

(* the structure itself requires three extra memory cells *)
Definition shape (b : buffer) (xs : seq T) :=
  [Pred h | exists a i m h',
    [/\ valid (active b :-> a \+ (inactive b :-> i \+ (len b :-> m \+ h'))),
        h = active b :-> a \+ (inactive b :-> i \+ (len b :-> m \+ h')) &
        h' \In is_buffer a i m (capacity b) xs]].

(* main methods *)

(* initializing a new buffer *)

(* loop invariant for allocating the inner structure *)
Definition new_loopT (n : nat) (init : T) : Type :=
  forall (pk : ptr * nat),
  STsep {q} (fun h => pk.2 < n /\ h \In lseg pk.1 q (nseq pk.2 init),
             [vfun p' => lseg p' q (nseq n.-1 init)]).

(* allocate the buffer with capacity n prefilled by init *)
Program Definition new (n : nat) (init : T) :
          STsep (emp, [vfun v => shape v [::]]) :=
  (* allocate the buffer in a loop *)
  Do (let run := ffix (fun (go : new_loopT n init) '(r,k) =>
                      Do (if k < n.-1 then
                            p' <-- allocb r 2;
                            p' ::= init;;
                            go (p', k.+1)
                          else ret r)) in
      if 0 < n then
        (* we allocate the initial node separately *)
        (* so we have something to "tie" the cycle to *)
        p <-- allocb null 2;
        p ::= init;;
        (* allocate the remaining n-1 nodes by prepending to it *)
        q <-- run (p, 0);
        (* form the cycle *)
        p.+1 ::= q;;
        (* allocate the structure *)
        m <-- alloc 0;
        pi <-- alloc q;
        pa <-- alloc q;
        ret (Buf T pa pi m n)
      else m <-- alloc 0;
           pi <-- alloc null;
           pa <-- alloc null;
           ret (Buf T pa pi m 0)).
(* first the loop *)
Next Obligation.
(* pull out the ghost (the initial node) + preconditions, match on k *)
move=>n init go _ r k [q][] i /= [Hk H]; case: ltnP=>Hk1.
- (* k < n.-1, allocate new node *)
  step=>p'; step; rewrite unitR.
  (* do the recursive call, both preconditions hold *)
  apply: [gE q]=>//=; split; first by rewrite -ltn_predRL.
  by exists r, i; rewrite joinA.
(* deduce k = n.-1 from n.-1 <= k < n *)
move: Hk=>/[dup]/ltn_predK=>{1}<-; rewrite ltnS=>Hk.
by step=>_; have/eqP <-: (k == n.-1) by rewrite eqn_leq Hk1 Hk.
Qed.
(* now the outer program *)
Next Obligation.
(* simplify, match on n *)
move=>n init [] _ /= ->; case: ifP=>[N0|_].
- (* 0 < n, allocate the initial node *)
  step=>p; step; rewrite !unitR.
  (* run the loop by framing on an empty heap *)
  apply: [stepU p]=>//= q h H.
  (* run the rest of the program *)
  step; step=>m; step=>pi; step=>pa; step=>V.
  (* the structure is well-formed if the buffer is *)
  exists q, q, 0, (h \+ (p :-> init \+ p.+1 :-> q)); split=>//.
  (* most of the conditions hold trivially or by simple arithmetics *)
  exists (nseq n init), Unit, (h \+ (p :-> init \+ p.+1 :-> q)); split=>//=.
  - by rewrite unitL.
  - by rewrite add0n size_nseq.
  (* the cycle is well-formed *)
  by rewrite -(ltn_predK N0) -rcons_nseq; apply/lseg_rcons; exists p, h.
(* n = 0, allocate a trivial structure with a null buffer *)
step=>m; step=>pi; step=>pa; step=>V.
(* it is well-formed *)
exists null, null, 0, Unit=>/=; split=>//.
by exists [::], Unit, Unit; split=>//; rewrite unitR.
Qed.

(* "polite" write, checks the buffer length, throws an exception on overflow *)
Program Definition write (x : T) (b : buffer) :
  STsep {xs} (shape b xs,
              fun y h => match y with
                         | Val _ => h \In shape b (rcons xs x)
                         | Exn e => e = BufferFull /\ h \In shape b xs
                         end) :=
  Do (m <-- !len b;
      if m < capacity b then
        i <-- !inactive b;
        i ::= x;;
        r <-- !i.+1;
        inactive b ::= (r : ptr);;
        len b ::= m.+1
      else throw BufferFull).
Next Obligation.
(* pull out ghost, destructure the precondition *)
move=>x b [xs []] _ /= [a][i][_][h][_ -> [ys][ha][hi][E Ec -> Ha Hi]].
(* read length, match on it *)
rewrite Ec; step; case: ltnP.
- (* buffer is not full, so the inactive part is non-empty *)
  rewrite {h}E -{1}(addn0 (size xs)) ltn_add2l => Hys.
  (* read the inactive pointer, unroll the inactive heap so that we can proceed *)
  step; case/(lseg_lt0n Hys): Hi=>y [r][h][_ {hi}-> H]; do 4![step]=>{y}V.
  (* the new structure is well-formed if the buffer is *)
  exists a, r, (size xs).+1, (ha \+ (i :-> x \+ (i.+1 :-> r \+ h))); split=>//.
  (* most of the conditions hold trivially or by simple arithmetics *)
  exists (behead ys), (ha \+ (i :-> x \+ i.+1 :-> r)), h; split=>//.
  - by rewrite !joinA.
  - by rewrite Ec size_rcons size_behead -subn1 addnABC // subn1.
  - by rewrite size_rcons.
  (* the new segment is well-formed *)
  by apply/lseg_rcons; exists i, ha.
(* the buffer is full and the inactive part is empty *)
rewrite -{2}(addn0 (size xs)) leq_add2l leqn0 => /nilP Eys.
(* throw the exception *)
step=>V; split=>//.
(* the buffer is unchanged *)
exists a, i, (size xs), h; split=>//.
by exists [::], ha, hi; rewrite Eys in Ec Hi.
Qed.

(* version that overwrites data in a cyclic fashion *)
(* checking that capacity != 0 is the client's problem *)
(* so it can be dealt with globally *)
Program Definition overwrite (x : T) (b : buffer) :
  STsep {xs} (fun h => 0 < capacity b /\ h \In shape b xs,
             [vfun _ => shape b (drop ((size xs).+1 - capacity b) 
                                (rcons xs x))]) :=
  Do (i <-- !inactive b;
      i ::= x;;
      r <-- !i.+1;
      inactive b ::= (r : ptr);;
      m <-- !len b;
      if m < capacity b then
         len b ::= m.+1
      else
         active b ::= r).
Next Obligation.
(* pull out ghost, destructure the preconditions *)
move=>x b [xs []] _ /= [Hc][a][i][_][_][_ -> [ys][ha][hi][-> Ec -> Ha Hi]].
(* read the inactive pointer, case split on inactive part *)
(* we do this early on because we need to unroll the heap to proceed *)
rewrite Ec in Hc *; step; case: ys Ec Hi Hc=>/=.
(* inactive part is empty, so the buffer is full *)
(* and the active part is the whole cycle *)
- rewrite addn0=>Ec [Ei {hi}->] Hxs; rewrite unitR; rewrite {i}Ei in Ha *.
(* unroll the (active) heap *)
  case/(lseg_lt0n Hxs): Ha=>z[r][h'][Exs {ha}-> H'].
(* run the rest of the program *)
(* the postcondition simplifies to beheading the extended xs *)
  do 4!step; rewrite ltnn subSnn drop1; step=>V.
(* the new structure is well-formed if the buffer is *)
  exists r, r, (size xs), (a :-> x \+ (a.+1 :-> r \+ h')); split=>//.
(* most of the conditions hold trivially or by simple arithmetics *)
  exists [::], (a :-> x \+ (a.+1 :-> r \+ h')), Unit; split=>//=.
  - by rewrite unitR.
  - by rewrite addn0 size_behead size_rcons.
  - by rewrite size_behead size_rcons.
(* xs is non-empty so behead commutes with rcons *)
  rewrite behead_rcons //; apply/lseg_rcons.
(* the segment is well-formed *)
  by exists a, h'; split=>//; rewrite [in RHS]joinC joinA.
(* inactive part is non-empty, unroll the inactive heap *)
move=>y ys Ec [r][h'][{hi}-> H'] _.
(* run the rest of the program *)
(* the postcondition simplifies to just the extended xs *)
do 4![step]=>{y}; rewrite -{1}(addn0 (size xs)) ltn_add2l /=; step=>V.
rewrite addnS subSS subnDA subnn sub0n drop0.
(* the new structure is well-formed if the buffer is *)
exists a, r, (size xs).+1, (ha \+ (i :-> x \+ (i.+1 :-> r \+ h'))); split=>//.
(* the buffer is well-formed by simple arithmetics *)
exists ys, (ha \+ (i :-> x \+ i.+1 :-> r)), h'; split=>//.
- by rewrite !joinA.
- by rewrite Ec size_rcons addnS addSn.
- by rewrite size_rcons.
by apply/lseg_rcons; exists i, ha.
Qed.

(* reading (popping) a value from the buffer *)
Program Definition read (b : buffer) :
  STsep {xs} (shape b xs,
    fun y h => match y with
               | Val x => h \In shape b (behead xs) /\ ohead xs = Some x
               | Exn e => e = BufferEmpty /\ xs = [::]
               end) :=
  Do (m <-- !len b;
      if 0 < m then
        a <-- !active b;
        x <-- !a;
        r <-- !a.+1;
        active b ::= (r : ptr);;
        len b ::= m.-1;;
        ret x
      else throw BufferEmpty).
Next Obligation.
(* pull out ghost, destructure precondition *)
move=>b [xs []] _ /= [a][i][_][_][_ -> [ys][ha][hi][-> Hc -> Ha Hi]].
(* read the length, match on it *)
step; case: ltnP.
(* buffer is non-empty, read the active pointer *)
- move=>Hxs; step.
(* unroll the active heap to proceed *)
  case/(lseg_lt0n Hxs): Ha=>x[r][h'][Exs {ha}-> H'].
(* run the rest of the program *)
  do 5![step]=>V; split; last by rewrite Exs.
(* the new structure is well-formed if the buffer is *)
  exists r, i, (size xs).-1, (a :-> x \+ (a.+1 :-> r \+ h') \+ hi); split=>//.
(* the buffer is well-formed by simple arithmetics *)
  exists (rcons ys x), h', (hi \+ (a :-> x \+ a.+1 :-> r)); split=>//.
  - by rewrite [LHS](pullX (h' \+ hi)) !joinA.
  - by rewrite size_rcons Hc {1}Exs /= addnS addSn.
  - by rewrite size_behead.
  by apply/lseg_rcons; exists a, hi.
(* throw the exception, buffer is empty and so is the spec *)
by rewrite leqn0=>/nilP->; step.
Qed.

(* deallocating the buffer *)
(* check that capacity = 0 here, since this should be a rare operation *)
(* of course, it could also be moved into the precondition as for overwrite *)

(* loop invariant for deallocating the inner structure *)
Definition free_loopT (n : nat) : Type :=
  forall (pk : ptr * nat),
  STsep {q (xs : seq T)} (fun h => h \In lseg pk.1 q xs /\ size xs = n - pk.2,
                         [vfun _ : unit => emp]).

Program Definition free (b : buffer) :
  STsep {xs} (fun h => h \In shape b xs,
             [vfun _ => emp]) :=
  Do (let run := ffix (fun (go : free_loopT (capacity b)) '(r,k) =>
                      Do (if k < capacity b then
                            p' <-- !r.+1;
                            dealloc r;;
                            dealloc r.+1;;
                            go (p', k.+1)
                          else ret tt)) in
      (if 0 < capacity b then
        a <-- !active b;
        run (a, 0);;
        skip
      else skip);;
      dealloc (active b);;
      dealloc (inactive b);;
      dealloc (len b)).
(* first the loop *)
Next Obligation.
(* pull out ghosts, destructure the preconditions, match on k *)
move=>b go _ r k [q][xs][] h /= [H Hs]; case: ltnP.
(* k < capacity, so the spec is still non-empty *)
- move=>Hk; have {Hk}Hxs: 0 < size xs by rewrite Hs subn_gt0.
(* unroll the heap *)
  case/(lseg_lt0n Hxs): H=>x[p][h'][E {h}-> H'].
(* save the next node pointer and deallocate the node *)
  do 3!step; rewrite !unitL.
(* run the recursive call, simplify *)
  apply: [gE q, behead xs]=>//=; split=>//.
  by rewrite subnS; move: Hs; rewrite {1}E /= =><-.
(* k = capacity, so the spec is empty *)
rewrite -subn_eq0=>/eqP Hc; rewrite {}Hc in Hs.
(* this means the heap is empty *)
by step=>_; move: H; move/eqP/nilP: Hs=>->/=; case.
Qed.
(* now the program *)
Next Obligation.
(* pull out ghost, destructure the precondition, match on capacity *)
move=>b [xs][] _ /= [a][i][m][_][_ -> [ys][ha][hi][-> Hc -> Ha Hi]]; case: ltnP.
(* 0 < capacity, first apply vrf_bind to "step into" the `if` block *)
(* run the loop starting from the active part, frame the corresponding heaps *)
- move=>_; apply/vrf_bnd; step; apply: [stepX a, xs++ys]@(ha \+ hi)=>//=.
(* concatenate the active and inactive parts to satisfy the loop precondition *)
  - move=>_; split; last by rewrite size_cat subn0.
    by apply/lseg_cat; exists i, ha, hi.
(* by deallocating the structure, the heap is emptied *)
  by move=>_ _ ->; rewrite unitR; step=>V; do 3![step]=>_; rewrite !unitR.
(* capacity = 0, so just deallocate the structure *)
rewrite leqn0=>/eqP E; do 4!step; rewrite !unitL=>_.
(* both parts of the spec are empty and so are the corresponding heaps *)
move: Hc; rewrite E =>/eqP; rewrite eq_sym addn_eq0=>/andP [/nilP Ex /nilP Ey].
move: Ha; rewrite Ex /=; case=>_->; move: Hi; rewrite Ey /=; case=>_->.
by rewrite unitR.
Qed.

End Buffer.
End Buffer.
