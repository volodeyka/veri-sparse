function sum(X_val: array<int>, X_crd: array<nat>, v : array<int>, b : int, k : int) : (s : int)
  reads X_val, X_crd, v
  requires X_val.Length >= b >= 0
  requires k <= X_val.Length
  requires X_val.Length == X_crd.Length
  requires forall i :: 0 <= i < X_crd.Length ==> 0 <= X_crd[i] < v.Length
  ensures k <= b ==> s == 0
  ensures b < k ==> s ==  sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
  decreases k - b
  {
    if k <= b then 
      0
    else  sum(X_val, X_crd, v, b + 1, k) + X_val[b] * v[X_crd[b]]
  }


method SpMV(X_val: array<int>, X_crd: array<nat>, X_pos: array<nat>, v : array<int>) returns (y : array<int>)
  requires X_crd.Length >= 1 
  requires X_crd.Length == X_val.Length;
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_crd.Length ==> X_crd[i] < v.Length
  requires forall i :: 0 <= i < X_pos.Length ==> X_pos[i] <= X_val.Length
  requires X_pos.Length >= 1
  ensures y.Length + 1 == X_pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
  {
    var N: nat := X_pos.Length - 1;
    y := new int[N];
    var n: nat := 0;
    while n < N
      invariant n <= y.Length
      invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
      { 
        y[n] := 0;
        var k: nat := X_pos[n];
        while k < X_pos[n + 1]
          invariant k <= X_pos[n + 1]
          invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v, X_pos[i], X_pos[i + 1])
          invariant y[n] + sum(X_val, X_crd, v, k, X_pos[n+1]) == sum(X_val, X_crd, v, X_pos[n], X_pos[n+1]) 
          {
            y[n] := y[n] + X_val[k] * v[X_crd[k]];
            k := k + 1;
          }
        n := n + 1;
      }
  }