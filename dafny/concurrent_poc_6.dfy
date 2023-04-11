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

class MatrixVectorMultiplier
{
    var P: set<Process>

    var finished_calc: set<Process>

    var M: array2<int>
    var x: seq<int>
    var y: array<int>

    var totalOps: nat

    var numRows: nat
    

    ghost predicate Valid 
        reads this, P
    {
        M.Length0 == y.Length &&
        M.Length1 == |x| &&
        numRows == y.Length &&
        |P| == numRows &&
        0 <= totalOps <= M.Length0 * M.Length1 &&

        (forall p :: p in finished_calc ==> p in P) &&
        (forall p, q :: p in P && q in P && p != q ==> p.row !=  q.row) &&
        (forall p :: p in P ==> 0 <= p.row < numRows) &&
        (forall p :: p in P ==> 0 <= p.curColumn <= M.Length1) &&
        (forall p :: p in P ==> 0 <= p.opsLeft <= M.Length1)
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
        ensures Valid()
    {
        numRows := M_.Length0;
        P := processes;
        M := M_;
        x := x_;
        y := y_;

        totalOps := M_.Length0 * M_.Length1;

        finished_calc := {};
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

    method processNext(p: Process)
        requires Valid()
        requires p in P
        requires p.opsLeft > 0
        requires p.curColumn < M.Length1
        requires totalOps > 0
        requires y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)
        modifies this, y, p
        ensures unchanged(`x)
        ensures Valid()
        ensures p.opsLeft == old(p.opsLeft) - 1
        ensures p.curColumn == old(p.curColumn) + 1
        ensures p.curColumn <= M.Length1
        ensures p.row == old(p.row)
        ensures p.row < y.Length
        ensures y[p.row] + calcRow(M, x, p.row, p.curColumn) == calcRow(M, x, p.row, 0)
    {
        y[p.row] := y[p.row] + M[p.row, p.curColumn] * x[p.curColumn];
        p.opsLeft := p.opsLeft - 1;
        p.curColumn := p.curColumn + 1;
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
    modifies processes
    decreases *
{
    var i := 0;
    y := new int[M.Length0];
    while i < y.Length
        invariant 0 <= i <= y.Length
        invariant forall j :: 0 <= j < i ==> y[j] == 0
    {
        y[i] := 0;
        i := i + 1;
    }

    var mv := new MatrixVectorMultiplier(processes, M, x[..], y);
    while mv.totalOps > 0
    {
        var p :| p in mv.P && p.opsLeft > 0;
        mv.processNext(p);
    }


}


function calcRow(M: array2<int>, x: array<int>, row: nat, start_index: nat) : (product: int)
    reads M, x
    requires M.Length1 == x.Length
    requires row < M.Length0
    requires start_index <= M.Length1
    decreases M.Length1 - start_index
{
    if start_index == M.Length1 then
        0
    else
        M[row, start_index] * x[start_index] + calcRow(M, x, row, start_index+1)
}

method Main() {
    
    var M: array2<int> := new int[3, 3];


    M[0,0] := 1;
    M[0,1] := 2;
    M[0,2] := 3;

    M[1,0] := 1;
    M[1,1] := 2;
    M[1,2] := 3;

    M[2,0] := 1;
    M[2,1] := 20;
    M[2,2] := 3;

    var x := new int[3];
    x[0] := 1;
    x[1] := -3;
    x[2] := 3;

    var y := calcRow(M, x, 0, 3);
    print "output: ", y, "\n";
}
