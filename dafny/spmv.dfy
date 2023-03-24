function sum(vals: array<int>, crd: array<nat>, x : array<int>, b : int, k : int) : (s : int)
  reads vals, crd, x
  requires b >= 0
  requires 0 <= k <= vals.Length
  requires vals.Length == crd.Length
  requires forall i :: 0 <= i < crd.Length ==> 0 <= crd[i] < x.Length
  ensures s == sumL(vals, crd, x, b, k)
  ensures k <= b ==> s == 0
  ensures b <= k < vals.Length ==> sumL(vals, crd, x, b, k + 1) == s + vals[k] * x[crd[k]]
  // {
  //   if k <= b then 
  //     0
  //   else  sum(vals, crd, x, b, k - 1) + vals[k - 1] * x[crd[k - 1]]
  // }

function sumL(vals: array<int>, crd: array<nat>, x : array<int>, b : int, k : int) : (s : int)


method SpMV(vals: array<int>, crd: array<nat>, pos: array<nat>, x : array<int>) returns (y : array<int>)
  requires crd.Length >= 1 
  requires crd.Length == vals.Length;
  requires forall i, j :: 0 <= i < j < pos.Length ==> pos[i] <= pos[j];
  requires forall i :: 0 <= i < crd.Length ==> crd[i] < x.Length
  requires forall i :: 0 <= i < pos.Length ==> pos[i] < vals.Length
  requires pos.Length >= 1
  ensures y.Length + 1 == pos.Length
  ensures forall i :: 0 <= i < y.Length ==> y[i] == sum(vals, crd, x, pos[i], pos[i + 1])
  {
    var numRows: nat := pos.Length - 1;
    y := new int[numRows];
    var row: nat := 0;
    while row < numRows
      invariant row <= y.Length
      invariant forall i :: 0 <= i < row ==> y[i] == sum(vals, crd, x, pos[i], pos[i + 1])
      { 
        y[row] := 0;
        var idx: nat := pos[row];
        while idx < pos[row + 1]
          invariant idx <= pos[row + 1]
          invariant forall i :: 0 <= i < row ==> y[i] == sum(vals, crd, x, pos[i], pos[i + 1])
          invariant y[row] == sum(vals, crd, x, pos[row], idx) 
          {
            y[row] := y[row] + vals[idx] * x[crd[idx]];
            idx := idx + 1;
          }
        row := row + 1;
      }
  }