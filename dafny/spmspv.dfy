<<<<<<< HEAD
predicate contains(arr: array<nat>, target: nat)
  reads arr
{
  exists i :: 0 <= i < arr.Length && arr[i] == target
}

function findIndexOf(arr: array<nat>, target: nat) : (index: nat)
  reads arr
  requires contains(arr, target)
  ensures 0 <= index < arr.Length && arr[index] == target
{
  findIndexHelper(arr, target, 0)
}

function findIndexHelper(arr: array<nat>, target: nat, index: nat) : (result: nat)
  reads arr
  requires contains(arr, target)
  requires 0 <= index <= arr.Length
  requires forall i | 0 <= i < index :: arr[i] != target
  ensures 0 <= result < arr.Length && arr[result] == target
  decreases arr.Length - index
{
  if arr[index] == target then {
    index
  } else {
    findIndexHelper(arr, target, index + 1)
  }
}

predicate sorted(arr: array<nat>)
  reads arr
{
  forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
}

function sum(X_val: array<int>, X_crd: array<nat>, v_pos: array<nat>, v_val: array<int>, b: int, k: int) : (s: int)
  reads X_val, X_crd, v_pos, v_val
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires v_pos.Length == v_val.Length
  // requires sorted(v_pos)
  // requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v_pos[v_pos.Length - 1]
  ensures k <= b ==> s == 0
  ensures b < k ==> (contains(v_pos, X_crd[b]) ==> s == sum(X_val, X_crd, v_pos, v_val, b + 1, k) + X_val[b] * v_val[findIndexOf(v_pos, X_crd[b])])
  decreases k - b
{
  if k <= b then 
    0
  else if contains(v_pos, X_crd[b]) then
    sum(X_val, X_crd, v_pos, v_val, b + 1, k) + X_val[b] * v_val[findIndexOf(v_pos, X_crd[b])]
  else
    sum(X_val, X_crd, v_pos, v_val, b + 1, k)
}

method SpMSpV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v_pos: array<nat>, v_val : array<int>) returns (y : array<int>)
  requires X_crd.Length >= 1 
  requires X_crd.Length == X_val.Length
  requires X_pos.Length >= 1
  requires v_pos.Length == v_val.Length
  // requires sorted(v_pos) - since both are compressed, not needed
  // requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v_pos[v_pos.Length - 1]
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j]
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v_pos, v_val, X_pos[i], X_pos[i + 1])
{
  var N: nat := X_pos.Length - 1;
  y := new int[N];
  var n: nat := 0;
  while n < N
    invariant n <= y.Length
    invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v_pos, v_val, X_pos[i], X_pos[i + 1])
  { 
    y[n] := 0;
    var k: nat := X_pos[n];
    while k < X_pos[n + 1]
      invariant k <= X_pos[n + 1]
      invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v_pos, v_val, X_pos[i], X_pos[i + 1])
      invariant y[n] + sum(X_val, X_crd, v_pos, v_val, k, X_pos[n+1]) == sum(X_val, X_crd, v_pos, v_val, X_pos[n], X_pos[n+1]) 
    {
      if contains(v_pos, X_crd[k]) 
      {
        y[n] := y[n] + X_val[k] * v_val[findIndexOf(v_pos, X_crd[k])];
      }
      k := k + 1;
    }
    n := n + 1;
  }
}



=======
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

  ensures (pV_end <= kV || pX_end <= kX) ==> s == 0
  ensures 
    kX < pX_end && kV < pV_end ==>
    X_crd[kX] == v_crd[kV] ==> 
    s == sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[v_crd[kV]] * X_val[X_crd[kX]]
  decreases pX_end + pV_end - (kX + kV)
  {
    if pV_end <= kV || pX_end <= kX then 
      0
    else if X_crd[kX] == v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[v_crd[kV]] * X_val[X_crd[kX]]
    else if X_crd[kX] < v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    else sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
  }

function min(x : nat, y : nat) : nat {
  if x <= y then x else y
}

method SpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
              v_val : array<int>, v_crd : array<nat>, v_pos : array<nat>) returns (y : array<int>)
  // X requirments 
  requires X_pos.Length >= 1
  requires X_val.Length == X_crd.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < X_val.Length
  requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length

  // v requirments 
  requires v_pos.Length == 2
  requires v_val.Length == v_crd.Length
  requires forall i, j :: 0 <= i < j < v_pos.Length ==> v_pos[i] < v_pos[j];
  requires forall i :: 0 <= i < v_crd.Length ==> v_crd[i] < v_val.Length
  requires forall i :: 0 <= i < 2            ==> 0 <= v_pos[i] <= v_val.Length

  ensures y.Length + 1 == X_pos.Length
  ensures 
    forall i :: 0 <= i < y.Length ==>
      y[i] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], v_pos[0], X_pos[i+1], v_pos[1])
  {
    var N : nat := X_pos.Length - 1;
    y := new int[N];

    var n : nat := 0;
    var kX , pX_end : nat;
    var kV , pV_end : nat;
    var kX0, kV0    : nat;
    var k : nat;

    while n < N
      invariant n <= y.Length
      invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], v_pos[0], X_pos[i+1], v_pos[1])
      { 
        y[n]   := 0;
        kX     := X_pos[n];
        pX_end := X_pos[n + 1];
        kV     := v_pos[0];
        pV_end := v_pos[1];

        while (kX < pX_end && kV < pV_end) 
        invariant X_pos[n] <= kX <= pX_end
        invariant v_pos[0] <= kV <= pV_end
        invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], v_pos[0], X_pos[i+1], v_pos[1])
        invariant y[n] + sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == sum(X_val, X_crd, v_val, v_crd, X_pos[n], v_pos[0], pX_end, pV_end)
        decreases pX_end + pV_end - (kX + kV)
          {
            kX0 := X_crd[kX];
            kV0 := v_crd[kV];
            k := min(kV0, kX0);
            if (kX0 == k && kV0 == k) {
              assert (kX0 == kV0);
              y[n] := y[n] + X_val[kX0] * v_val[kX0];
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
>>>>>>> c51f6ee (add SpMSpV dafny)
