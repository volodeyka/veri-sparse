From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import tuple finfun finset path fintype tuple ssralg countalg.
From mathcomp Require Import zify fintype choice eqtype bigop matrix order.
From pcm Require Import ordtype.
From Equations Require Import Equations.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint intersect s1 :=
  if s1 is x1 :: s1' then
    let fix intersect_s1 s2 :=
      if s2 is x2 :: s2' then
        if x1 == x2 then 
          x1 :: intersect s1' s2' 
        else if x1 < x2 then
          intersect s1' s2
        else  intersect_s1 s2'
      else [::] in
    intersect_s1
  else fun=> [::].

Lemma intersects0 s: 
  intersect [::] s = [::].
Proof. by []. Qed.

Lemma intersect0s s: 
  intersect s [::] = [::].
Proof. by case: s. Qed.

Lemma intersectSS a b s1 s2:
  intersect (a :: s1) (b :: s2) = 
    if a == b then 
      a :: intersect s1 s2 
    else if a < b then 
      intersect s1 (b :: s2)
    else intersect (a :: s1) s2.
Proof. by []. Qed.

Arguments intersect : simpl never.

Notation "x '[' n ']'" := (nth 0 x n) (at level 2).

Definition nth_mat N K (Mat : 'M[nat]_(N, K)) i j := 
  if i < N =P true is ReflectT iLN then 
    if j < K =P true is ReflectT jLK then
      Mat (Ordinal iLN) (Ordinal jLK)
    else 0 
  else 0.

Notation "M '[' i ',' j ']' " := (nth_mat M i j) (at level 2).

Definition slice T (s : seq T) k n := drop k (take n s).

Lemma nth_slice s n k i : 
  k + i < n ->
  (slice s k n)[i] = s[k + i].
Proof. by move=> ?; rewrite /slice nth_drop nth_take. Qed.

Arguments nth_slice {_} _.

Lemma size_slice T (s : seq T) n k : 
  size (slice s k n) = minn n (size s) - k.
Proof. rewrite /slice size_drop size_take; case: ltngtP; lia. Qed.

Variant inh (T : Type) : Prop := Inh (p : T).

Section DSpMSpV.

Definition CSR N K M 
  (X : 'M_(N, K))
  (X_val X_crd : M.-tuple nat)
  (X_pos : N.+1.-tuple nat) := 
  [/\
    forall i, i < N -> 
      forall j, X_pos[i] <= j < X_pos[i.+1] -> 
        X_val[j] = X[i, X_crd[j]],
    forall i j, X[i, j] != 0 ->
        [/\ exists2 k, X_pos[i] <= k < X_pos[i.+1] & j = X_crd[k], i < N & j < K],
    forall i, i < N ->
      sorted ltn (slice X_crd X_pos[i] X_pos[i.+1]),
    forall i, X_crd[i] < K &
    forall i, X_pos[i] <= M
  ].

Definition DCSR N K M P
  (X : 'M_(N, K))
  (X_val X_crd : M.-tuple nat)
  (X_pos : N.+1.-tuple nat) 
  (X_pos1 : 2.-tuple nat)
  (X_crd1 : P.-tuple nat)
  := 
  [/\
    forall i, i < P -> 
      forall j, X_pos[i] <= j < X_pos[i.+1] -> 
        X_val[j] = X[X_crd1[i], X_crd[j]],
    forall i j, X[i, j] != 0 ->
        [/\ exists l k, 
          [/\ X_pos[l] <= k < X_pos[l.+1],
              i = X_crd1[l],
              j = X_crd[k] & 
              l < P], i < M & j < K],
    forall i, i < P ->
      sorted ltn (slice X_crd X_pos[i] X_pos[i.+1]),
    forall i, X_crd[i] < K &
    [/\ forall i, X_crd1[i] <= N,
        forall i, X_pos[i] <= M &
        sorted ltn X_crd1]
  ].

Definition SV := @CSR 1.

Context N K M L P 
  (X : 'M[nat]_(N, K))
  (X_val X_crd : M.-tuple nat)
  (X_pos : N.+1.-tuple nat)
  (X_pos1 : 2.-tuple nat)
  (X_crd1 : P.-tuple nat)
  (V : 'rV[nat]_K)
  (V_pos : 2.-tuple nat)
  (V_crd V_val : L.-tuple nat).

Hypothesis DCSRX : DCSR X X_val X_crd X_pos X_pos1 X_crd1.
Hypothesis SVV   : SV   V V_val V_crd V_pos.

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a erefl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Obligation Tactic := lia.
Equations sum (kX kV pX_end pV_end : nat) : nat by wf ((pX_end + pV_end) - (kV + kX)) lt := 
sum kX kV pX_end pV_end with inspect ((pV_end <= kV) || (pX_end <= kX)) := {
  | false eqn: P => 
  if X_crd[kX] == V_crd[kV] then 
    sum kX.+1 kV.+1 pX_end pV_end + X_val[kX] * V_val[kV]
  else if X_crd[kX] < V_crd[kV] then 
    sum kX.+1 kV pX_end pV_end
  else sum kX kV.+1 pX_end pV_end
  | _  eqn: _ => 0
}.
Fail Next Obligation.

Definition intersect_slice x1 s1 y1 x2 s2 y2 := 
    intersect (slice s1 x1 y1) (slice s2 x2 y2).

Arguments intersect_slice /.

Lemma slice0 T (s : seq T) k n : 
  k >= n -> 
  slice s k n = [::].
Proof. move=>*; rewrite /slice drop_oversize // size_take; case: ifP; lia. Qed.

Lemma sliceS s k n : 
  k < n -> 
  k < size s ->
  slice s k n = s[k] :: slice s k.+1 n.
Proof.
move=>*; rewrite /slice (@drop_nth _ 0) ?nth_take // size_take; case: ifP; lia.
Qed.


Definition intersectE := (intersect0s, intersects0, intersectSS).

Lemma sumE i kX kV: 
  X_pos[i] <= kX ->
  V_pos[0] <= kV ->
  i < P ->
  sum kX kV X_pos[i.+1] V_pos[1] = 
  \sum_(j <- intersect_slice kX X_crd X_pos[i.+1] kV V_crd V_pos[1]) X[X_crd1[i], j] * V[0, j].
Proof.
move=> kXL kVL ?.
have [n] := ubnP ((X_pos[i.+1] + V_pos[1]) - (kV + kX)).
elim: n=> // n IHn in kV kX kVL kXL *.
move=> /ltnSE-leGn; simp sum=> /=.
case e: ((V_pos [1] <= kV) || (X_pos[i.+1] <= kX)).
{ by case/orP: e=> /slice0-> /[! (intersectE, big_nil)]. }
case: DCSRX=> E1 ??? []? /(_ i.+1)??.
case: SVV => E2 ??? /(_ 1)?.
rewrite [slice _ kX _]sliceS ?[slice _ kV _]sliceS ?size_tuple; try lia. 
rewrite intersectSS; do ?case: ifP; try lia.
{ move=> /eqP E.
  rewrite big_cons IHn /=; try lia.
  rewrite -E1 ?E -?E2; lia. }
all: rewrite -sliceS ?size_tuple ?IHn /=; lia.
Qed.

Lemma in_intersect s1 s2 x:
  sorted ltn s1 ->
  sorted ltn s2 -> 
  x \in intersect s1 s2 = 
  (x \in s1) && (x \in s2).
Proof.
have [n] := ubnP (size s1 + size s2).
elim: n=> // n IHn in s1 s2 *.
case: s1=> /= [*|??].
{ by rewrite intersectE. }
case: s2=> /= [*|??? /[dup]?/[swap]/[dup]?].
{ by rewrite intersectE andbC. }
rewrite /= ?path_sortedE; try exact/trans.
case/andP=> /allP A1 ? /andP-[/allP A2 ?].
rewrite ?inE intersectE.
do ? case: ifP.
{ move/eqP->; rewrite inE IHn //; last lia.
  by case: (_ == _). }
{ rewrite IHn // ?inE.
  case: (x =P _)=> //= [-> ?|].
  { by rewrite eq_sym=> ->. }
  case: (x =P _)=> //= -> *.
  case: (boolP (_ \in _))=> //= ?.
  case: (boolP (_ \in _))=> //= /A1. lia. }
rewrite IHn // ?inE /=; try lia.
case: (x =P _)=> //= [-> ?|].
{ by rewrite eq_sym=> ->. }
case: (x =P _)=> //= -> *; rewrite andbT.
case: (boolP (_ \in _))=> //= /A2; lia.
Qed.

Lemma intersect_sorted s1 s2 :
  sorted ltn s1 ->
  sorted ltn s2 -> 
  sorted ltn (intersect s1 s2).
Proof.
have [n] := ubnP (size s1 + size s2).
elim: n=> // n IHn in s1 s2 *.
case: s1=> /= [*|??] //.
case: s2=> /= [*|??? /[dup]?/[swap]/[dup]?] //.
rewrite /= ?path_sortedE; try exact/trans.
case/andP=> /allP A1 ? /andP-[/allP A2 ?].
rewrite ?inE intersectE.
do ? case: ifP.
{ move=> /eqP E /=; rewrite path_sortedE; last exact/trans.
  apply/andP; split; last (apply/IHn=> //; lia).
  apply/allP=> ?; rewrite in_intersect //.
  by case/andP=> /A2->. }
all: move=> *; apply/IHn=> //=; lia.
Qed.

Lemma in_slice s k l n :
  n <= size s ->
  k <= l < n -> s[l] \in slice s k n.
Proof.
move=> nL ?.
apply/(nthP 0); exists (l - k).
{ rewrite size_slice (minn_idPl nL); lia. }
rewrite nth_drop nth_take; first congr nth; lia.
Qed.

Lemma slice_in (s : seq nat) k n x:
  x \in slice s k n -> x \in s.
Proof. by move/mem_drop/mem_take. Qed.

Theorem DSpMSpV i : i < N ->
  let ind := index i X_crd1 in
  (if ind < P then 
    sum X_pos[ind] V_pos[0] X_pos[ind.+1] V_pos[1]
  else 0) = 
  \sum_(j < K) X[i, j] * V[0, j].
Proof.
move=> iL /=; have: P = size X_crd1 by rewrite size_tuple.
move=> /[dup] sE {2}->.
rewrite index_mem; case: ifP.
{ move=> /[dup] II; rewrite -{4}(nth_index 0 II).
  rewrite -index_mem -sE; move: {i iL II} (index _ _)=> i iL.
  case: DCSRX=> _ NZ1 /(_ _ iL) S1 C [] ? /(_ i.+1)?; case: SVV=> _ NZ2 /(_ 0 erefl) S2 ? /(_ 1)?.
  rewrite sumE //.
  have <-: \sum_(0 <= j < K) X[X_crd1[i], j] * V[0, j] =\sum_(j < K) X[X_crd1[i], j] * V[0, j] by apply/big_mkord.
  set intr := intersect_slice _ _ _ _ _ _.
  move=> /sorted_uniq-/(_ (@trans _) (@irr _)) /nth_uniq uE.
  have ->: \sum_(0 <= j < K) X[X_crd1[i], j] * V[0, j] =
    \sum_(0 <= j < K | j \in intr) X[X_crd1[i], j] * V[0, j].
  { apply/esym/big_rmcond_in=> ?? IN.
    apply/eqP; move: IN; apply/contraNT.
    rewrite muln_eq0 negb_or=> /andP-[/[swap]].
    case/NZ2=> -[j1 ? -> _ ?].
    case/NZ1=> -[j2 [? [? /eqP ++ ?]]].
    rewrite uE ?size_tuple // => /eqP iE E ??.
    rewrite in_intersect ? (S1, S2) // {1}E.
    by rewrite ?in_slice ?size_tuple // iE. }
  apply/esym; rewrite -big_filter; apply/perm_big.
  apply/uniq_perm.
  { exact/filter_uniq/iota_uniq. }
  { apply/sorted_uniq/intersect_sorted=> //; [exact/trans|exact/irr]. }
  move=>>; rewrite mem_filter mem_index_iota /intr /= in_intersect //.
  apply/idP/idP=> [/andP-[->] //|/[dup]{2}-> /andP-[/slice_in]].
  by move/nthP=> /(_ 0)-[??<- ]; rewrite C. }
move=> /negbT IN.
have <-: \sum_(0 <= j < K) X[i, j] * V[0, j] =\sum_(j < K) X[i, j] * V[0, j] by apply/big_mkord.
suff ->: \sum_(0 <= j < K) X[i, j] * V[0, j] =
    \sum_(0 <= j < K | pred0 j) X[i, j] * V[0, j].
{ by rewrite -big_filter filter_pred0 big_nil. }
apply/esym/big_rmcond_in=> *.
case: DCSRX=> _ NZ *.
apply/eqP/(contraNT _ IN). 
rewrite muln_eq0 negb_or=> /andP-[/NZ][][]?[]? [? -> *].
exact/memt_nth.
Qed.


End DSpMSpV.