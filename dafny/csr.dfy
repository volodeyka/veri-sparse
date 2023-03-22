method SparseMatrixVectorMultiply(vals: array<int>, columns: array<nat>, rowStarts: array<nat>, x: array<int>) returns (y: array<int>)
  requires columns.Length >= 1 && columns.Length == vals.Length;
  requires forall i, j :: 0 <= i < j < rowStarts.Length ==> rowStarts[i] <= rowStarts[j];
  requires forall i :: 0 <= i < columns.Length ==> columns[i] < x.Length
  requires rowStarts.Length >= 2 && rowStarts[0] == 0
  ensures rowStarts.Length-1 == y.Length
  // verification of results ensure statement goes here
{
  var numRows: nat := rowStarts.Length - 1;
  y := new int[numRows];
  var row: nat := 0;
  while row < numRows
    invariant 0 <= row <= numRows
    decreases numRows - row
    { 
      y[row] := 0;
      var idx: nat := rowStarts[row];
      while idx < rowStarts[row + 1]
        invariant idx < vals.Length
        decreases rowStarts[row + 1] - idx
        {
            y[row] := y[row] + vals[idx] * x[columns[idx]];
            idx := idx + 1;
        }
      row := row + 1;
    }
}