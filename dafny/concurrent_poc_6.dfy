class Process {
    var row: nat;
    var curColumn: nat;
    var opsLeft: nat;

    constructor (init_row: nat, initOpsLeft: nat) {
        row := init_row;
        curColumn := 0;
        opsLeft := initOpsLeft;
    }
}

function sum(s : seq<nat>) : nat
{
    if s == [] then 0 else s[0] + sum(s[1..])
}

lemma sum0(s : seq<nat>)
  ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
  
  {
    if s == [] {
    } else {
      sum0(s[1..]);
    }
  }

lemma sum_const(s : seq<nat>, x : nat)
  ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x 
  {
  }

lemma sum_eq(s1 : seq<nat>, s2 : seq<nat>)
  requires |s1| == |s2|
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
  ensures sum(s1) == sum(s2)
  {

  }

lemma sum_exept(s1 : seq<nat>, s2 : seq<nat>, x : nat, j : nat)
requires |s1| == |s2|
requires j < |s1|
requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
requires s1[j] == s2[j] + x
ensures sum(s1) == sum(s2) + x
{
    if s1 == [] {
        assert(j >= |s1|);
    } else {
        if j == 0 {
            assert (sum(s1) == s1[0] + sum(s1[1..]));
            assert (sum(s2) == s2[0] + sum(s2[1..]));
            sum_eq(s1[1..], s2[1..]);
            assert sum(s1[1..]) == sum(s2[1..]);
        } else {
            sum_exept(s1[1..], s2[1..], x, j - 1);
        }
    }
}


function calcRow(M : array2<int>, x : seq<int>, row: nat, start_index: nat) : (product: int)
    reads M
    requires M.Length1 == |x|
    requires row < M.Length0
    requires start_index <= M.Length1
    decreases M.Length1 - start_index
{
    if start_index == M.Length1 then
        0
    else
        M[row, start_index] * x[start_index] + calcRow(M, x, row, start_index+1)
}

class MatrixVectorMultiplier
{
    var P: set<Process>

    // var M: array2<int>
    // var x: seq<int>
    // var y: array<int>
    // ghost var len0 : nat
    // ghost var len1 : nat

    var totalOps: nat

    var numRows: nat

    var leftOvers : array<nat>
    

    ghost predicate Valid(M: array2<int>, x: seq<int>, y: array<int>)
        reads this, y, P, M, leftOvers
    {
        M.Length0 == y.Length &&
        M.Length1 == |x| &&
        numRows == y.Length &&
        |P| == numRows &&
        // 0 <= totalOps <= M.Length0 * M.Length1 &&
        |P| == leftOvers.Length &&

        (forall p, q :: p in P && q in P && p != q ==> p.row !=  q.row) &&
        (forall p :: p in P ==> 0 <= p.row < numRows) &&
        (forall p :: p in P ==> 0 <= p.curColumn <= M.Length1) &&
        (forall p :: p in P ==> 0 <= p.opsLeft <= M.Length1) && 
        (forall p :: p in P ==> y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)) &&
        (forall p :: p in P ==> leftOvers[p.row] == p.opsLeft) &&
        (forall p :: p in P ==> p.opsLeft == M.Length1 - p.curColumn) &&
        (sum(leftOvers[..]) == totalOps)
    }

    constructor (processes: set<Process>, M_: array2<int>, x_: seq<int>, y_: array<int>)
        // Idea here is that we already have a set of processes such that each one is assigned one row.
        // Daphny makes it a ginormous pain in the ass to actually create such a set, so we just assume
        // we already have one.

        //this states that the number of rows and processes are the same, and that there is one process
        //for every row
        requires |processes| == M_.Length0
        requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
        requires (forall p :: p in processes ==> 0 <= p.row < M_.Length0)

        //initializes process start
        requires (forall p :: p in processes ==> 0 == p.curColumn)
        requires (forall p :: p in processes ==> p.opsLeft == M_.Length1)

        requires (forall i :: 0 <= i < y_.Length ==> y_[i] == 0)
        requires y_.Length == M_.Length0

        requires |x_| == M_.Length1
        requires M_.Length0 > 0
        requires |x_| > 0
        ensures (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1)
        ensures totalOps ==  M_.Length0 * M_.Length1
        // ensures (forall s :: (forall i :: 0 <= i < |s| ==> s[i] == M_.Length1) ==> sum(s) == |s| * M_.Length1)
        ensures Valid(M_, x_, y_)
    {
        numRows := M_.Length0;
        P := processes;
        // M := M_;
        // x := x_;
        // y := y_;

        new;
        leftOvers := new nat[M_.Length0](i => M_.Length1);

        assert (forall i :: 0 <= i < leftOvers.Length ==> leftOvers[i] == M_.Length1);
        sum_const(leftOvers[..], M_.Length1);
        totalOps := M_.Length0 * M_.Length1;
        
    }

    method processNext(M: array2<int>, x: seq<int>, y: array<int>)
        requires Valid(M, x, y)
        // requires p in P
        // requires p.opsLeft > 0
        // requires p.curColumn < M.Length1
        requires sum(leftOvers[..]) > 0
        requires totalOps > 0
        // requires y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)
        modifies this, y, `P
        ensures Valid(M, x, y)
        // ensures p.opsLeft == old(p.opsLeft) - 1
        // ensures p.curColumn == old(p.curColumn) + 1
        // ensures p.curColumn <= M.Length1
        // ensures p.row == old(p.row)
        // ensures p.row < y.Length
        ensures totalOps == old(totalOps) - 1
        // ensures sum(leftOvers[..]) < sum(old(leftOvers[..]))
        // ensures y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)
    {
        var p :| p in P && p.opsLeft > 0;
        y[p.row] := y[p.row] + M[p.row, p.curColumn] * x[p.curColumn];
        p.opsLeft := p.opsLeft - 1;
        p.curColumn := p.curColumn + 1;
        leftOvers[p.row] := leftOvers[p.row] - 1;
        assert (forall i :: 0 <= i < leftOvers.Length ==> i != p.row ==> leftOvers[i] == old(leftOvers[i]));
        assert (leftOvers[p.row] + 1 == old(leftOvers[p.row]));
        sum_exept(old(leftOvers[..]), leftOvers[..], 1, p.row);
        totalOps := totalOps - 1;
    }

}

method Run(processes: set<Process>, M: array2<int>, x: array<int>) returns (y: array<int>)
    requires |processes| == M.Length0
    requires (forall p, q :: p in processes && q in processes && p != q ==> p.row !=  q.row)
    requires (forall p :: p in processes ==> 0 <= p.row < M.Length0)

    requires (forall p :: p in processes ==> 0 == p.curColumn)
    requires (forall p :: p in processes ==> p.opsLeft == M.Length1)

    requires x.Length > 0
    requires M.Length0 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
    modifies processes, M, x
{
    var i := 0;
    y := new int[M.Length0](i => 0);

    var mv := new MatrixVectorMultiplier(processes, M, x[..], y);
    while sum(mv.leftOvers[..]) > 0 && exists p :: (p in mv.P && p.opsLeft > 0)
        invariant mv.Valid(M, x[..], y)
        invariant (forall p :: p in mv.P ==> y[p.row] + calcRow(M, x[..], p.row, p.curColumn) == calcRow(M, x[..], p.row, 0))
        invariant sum(mv.leftOvers[..]) >= 0
        invariant mv.totalOps >= 0
        // invariant mv.P
        decreases mv.totalOps
    {
        mv.processNext(M, x[..], y);
    }
    assert(sum(mv.leftOvers[..]) == 0);
    assert(forall p :: p in mv.P ==> y[p.row] == calcRow(M, x[..], p.row, 0));


}


// method Main() {
    
//     var M: array2<int> := new int[3, 3];


//     M[0,0] := 1;
//     M[0,1] := 2;
//     M[0,2] := 3;

//     M[1,0] := 1;
//     M[1,1] := 2;
//     M[1,2] := 3;

//     M[2,0] := 1;
//     M[2,1] := 20;
//     M[2,2] := 3;

//     var x := new int[3];
//     x[0] := 1;
//     x[1] := -3;
//     x[2] := 3;

//     var y := calcRow(M, x, 0, 3);
//     print "output: ", y, "\n";
// }
