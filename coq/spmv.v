From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import tuple finfun finset path fintype tuple.
From mathcomp Require Import zify fintype choice eqtype bigop matrix order.
From pcm Require Import ordtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "x '`_' n" := (nth 0 x n).

Definition nth_mat N K (Mat : 'M[nat]_(N, K)) i j := 
  if i < N =P true is ReflectT iLN then 
    if j < K =P true is ReflectT jLK then
      Mat (Ordinal iLN) (Ordinal jLK)
    else 0 
  else 0.

Notation "M '`_[' i ',' j ']' " := (nth_mat M i j) (at level 2).

Definition slice T (s : seq T) k n := drop k (take n s).

Lemma nth_slice s n k i : 
  k + i < n ->
  (slice s k n)`_i = s`_(k + i).
Proof. by move=> ?; rewrite /slice nth_drop nth_take. Qed.

Arguments nth_slice {_} _.

Lemma size_slice T (s : seq T) n k : 
  size (slice s k n) = minn n (size s) - k.
Proof. rewrite /slice size_drop size_take; case: ltngtP; lia. Qed.

Variant inh (T : Type) : Prop := Inh (p : T).

Section CSR.

Context N K M 
  (X : 'M[nat]_(N, K))
  (X_val X_crd : M.-tuple nat)
  (X_pos : N.+1.-tuple nat)
  (V : K.-tuple nat).

Hypothesis CSR :
  [/\
    forall i, i < N -> 
      forall j, X_pos`_i <= j < X_pos`_i.+1 -> 
        X_val`_j = X`_[i, X_crd`_j],
    forall i j, i < N -> j < K -> 
      inh (reflect
        (exists2 k, X_pos`_i <= k < X_pos`_i.+1 & j = X_crd`_k) 
        (X`_[i, j] != 0)),
    forall i, i < N ->
      sorted ltn (slice X_crd X_pos`_i X_pos`_i.+1),
    forall i, X_crd`_i < K &
    forall i, X_pos`_i <= M
  ].

Theorem SpMV i : i < N ->
  \sum_(X_pos`_i <= k < X_pos`_i.+1) V`_(X_crd`_k) * X_val`_k = 
  \sum_(j < K) V`_j * X`_[i, j].
Proof.
  case: CSR=> XE Xn0 Col_chunk_sorted colLK rowLK ?.
  under eq_big_seq=> ?. 
  { rewrite mem_index_iota=> ? /[! (@XE i)] //; over. }
  have: forall x y, index_iota x y = map (addn x) (index_iota 0 (y - x)).
  { move=>>; by rewrite /index_iota -iotaDl addn0 subn0. }
  move=>-> /=. rewrite big_map.
  set D := X_pos`_i.+1 - X_pos`_i.
  rewrite big_seq_cond.
  under congr_big. 
  { over. }
  { move=>?. over. }
  { move=> j. rewrite mem_index_iota andbT=> ?.
    rewrite -(nth_slice X_pos`_i.+1); last lia.
    over. }
  move=> /=. rewrite -big_seq_cond.
  set X_crd' := slice _ _ _.
  have: size X_crd' = D. 
  { rewrite /X_crd' size_slice /D size_tuple.
    move: (rowLK i.+1). lia. }
  move=> /[dup] scrd'E <-.
  have<-:
    \sum_(j  <- X_crd') V`_j * X`_[i, j] =
    \sum_(i0 <- index_iota 0 (size X_crd')) V`_(X_crd'`_i0) * X `_[ i, X_crd'`_i0].
  { exact/big_nth. }
  have->: 
    \sum_(j < K) V`_j * X `_[ i, j] = 
    \sum_(0 <= j < K) V`_j * X `_[ i, j].
  { exact/esym/big_mkord. }
  have P: perm_eq (filter (mem X_crd') (index_iota 0 K)) X_crd'.
  { apply/uniq_perm.
    { exact/filter_uniq/iota_uniq. }
    { apply/sorted_uniq/Col_chunk_sorted=> //; [exact/trans|exact/irr]. }
    move=> ?. rewrite mem_filter mem_index_iota /=.
    apply/idP/idP=> [/andP[]|] // /[dup]{-1}-> /= /mem_drop/mem_take/(nthP 0).
    by case=> ? _ <-. }
  rewrite -(perm_big _ P) /= big_filter.
  apply/big_rmcond_in=> j /= /[! mem_index_iota].
  rewrite /X_crd'=> ? /nthP Xn0'.
  apply/eqP; rewrite muln_eq0; apply/orP; right.
  case: (@Xn0 i j)=> // H; apply/H=> [[k ? Eq]]; apply/(Xn0' 0).
  exists (k - X_pos`_i).
  { rewrite scrd'E /D; lia. }
  rewrite nth_slice ?Eq; last lia.
  congr nth; lia.
Qed.

End CSR.



