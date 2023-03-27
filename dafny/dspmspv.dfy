function sum(X_val : array<int>, X_crd : array<nat>,
             v_val : array<int>, v_crd : array<nat>, kX : nat, kV : nat, pX_end : nat, pV_end : nat) : (s : int) 
  reads X_val, X_crd
  requires X_val.Length == X_crd.Length
  requires pX_end <= X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < X_val.Length
  requires 0 <= kX <= X_crd.Length

  reads v_crd, v_val
  requires v_val.Length == v_crd.Length
  requires pV_end <= v_crd.Length
  requires forall i :: 0 <= i < v_crd.Length ==> v_crd[i] < v_val.Length
  requires 0 <= kV <= v_crd.Length

  decreases pX_end + pV_end - (kX + kV)
  {
    if pV_end <= kV || pX_end <= kX then 
      0
    else if X_crd[kX] == v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV] * X_val[kX]
    else if X_crd[kX] < v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    else sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
  }

function min(x : nat, y : nat) : nat {
  if x <= y then x else y
}

predicate notin(y: nat, x : array<nat>) 
  reads x
{
  forall i :: 0 <= i < x.Length ==> y != x[i]
}

function index(x : nat, y: array<nat>) : (i : nat)
  reads y
  ensures i >= y.Length ==> notin(x, y)
  ensures i <  y.Length ==> y[i] == x

method SpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
                                  X_crd1 : array<nat>, X_pos1 : array<nat>,
              v_val : array<int>, v_crd : array<nat>, v_pos : array<nat>) returns (y : array<int>)
  // X requirments 
  requires X_pos.Length >= 1
  requires X_val.Length == X_crd.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < X_val.Length
  requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length
  requires X_pos1.Length == 2
  requires forall i :: 0 <= i < 2 ==> X_pos1[i] <= X_crd1.Length
  requires X_crd1.Length < X_pos.Length
  requires forall i :: 0 <= i < X_crd1.Length ==> X_crd1[i] < X_pos.Length - 1
  requires forall i, j :: 0 <= i < j < X_crd1.Length ==> X_crd1[i] < X_crd1[j]

  // v requirments 
  requires v_pos.Length == 2
  requires v_val.Length == v_crd.Length
  requires forall i, j :: 0 <= i < j < v_pos.Length ==> v_pos[i] < v_pos[j];
  requires forall i :: 0 <= i < v_crd.Length ==> v_crd[i] < v_val.Length
  requires forall i :: 0 <= i < 2            ==> 0 <= v_pos[i] <= v_val.Length

  ensures y.Length + 1 == X_pos.Length
  ensures 
    forall i :: X_pos1[0] <= i < X_pos1[1] ==>
      y[X_crd1[i]] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], v_pos[0], X_pos[i+1], v_pos[1])
  ensures forall i :: 0 <= i < y.Length ==> notin(i, X_crd1) ==> y[i] == 0
  {
    var N : nat := X_pos.Length - 1;
    y := new int[N](i => 0);

    var n : nat := X_pos1[0];
    var kX , pX_end : nat;
    var kV , pV_end : nat;
    var kX0, kV0    : nat;
    var k : nat;
    var pX_end1 := X_pos1[1];


    while n < pX_end1
      invariant n <= X_crd1.Length
      invariant forall i :: X_pos1[0] <= i < n ==> y[X_crd1[i]] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], v_pos[0], X_pos[i+1], v_pos[1])
      invariant forall i :: 0 <= i < y.Length ==> notin(i, X_crd1) ==> y[i] == 0
      {
        y[X_crd1[n]] := 0;
        kX     := X_pos[n];
        pX_end := X_pos[n + 1];
        kV     := v_pos[0];
        pV_end := v_pos[1];

        while (kX < pX_end && kV < pV_end) 
          invariant X_pos[n] <= kX <= pX_end
          invariant v_pos[0] <= kV <= pV_end
          invariant forall i :: 0 <= i < y.Length ==> notin(i, X_crd1) ==> y[i] == 0
          invariant forall i :: X_pos1[0] <= i < n ==> y[X_crd1[i]] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], v_pos[0], X_pos[i+1], v_pos[1])
          invariant y[X_crd1[n]] + sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == sum(X_val, X_crd, v_val, v_crd, X_pos[n], v_pos[0], pX_end, pV_end)
          decreases pX_end + pV_end - (kX + kV)
          {
            kX0 := X_crd[kX];
            kV0 := v_crd[kV];
            k := min(kV0, kX0);
            if (kX0 == k && kV0 == k) {
              assert (kX0 == kV0);
              y[X_crd1[n]] := y[X_crd1[n]] + X_val[kX] * v_val[kV];
              kX := kX + 1;
              kV := kV + 1;
            } else if (kX0 == k) {
              assert(kX0 < kV0);
              kX := kX + 1;
            } else if (kV0 == k) {
              assert(kV0 < kX0);
              kV := kV + 1;
            }
          }
        n := n + 1;
      }
  }