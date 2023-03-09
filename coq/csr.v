From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import tuple finfun finset path fintype tuple.
From mathcomp Require Import zify fintype choice eqtype bigop matrix.

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
  \sum_(X_pos`_i <= k < X_pos`_i.+1) V`_(X_crd`_k) * X`_[i, X_crd`_k] = 
  \sum_(j < K) V`_j * X`_[i, j].
Proof.
Admitted.

End CSR.



