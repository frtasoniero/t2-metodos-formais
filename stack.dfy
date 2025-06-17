class Stack {
    var arr: array<int>
    var count: int
    ghost var abs: seq<int> // Abstract representation (top at end)

    ghost predicate Valid()
        reads this, arr
    {
        0 <= count <= arr.Length &&
        abs == arr[..count]
    }

    constructor(cap: nat)
        requires cap > 0
        ensures Valid()
        ensures abs == []
    {
        arr := new int[cap];
        count := 0;
        abs := [];
    }

    method Push(x: int)
        requires Valid()
        requires count < arr.Length
        modifies this, arr
        ensures Valid()
        ensures abs == old(abs) + [x]
    {
        arr[count] := x;
        count := count + 1;
        abs := old(abs) + [x];
    }

    method Pop() returns (x: int)
        requires Valid()
        requires count > 0
        modifies this
        ensures Valid()
        ensures abs == old(abs)[..|old(abs)|-1]
        ensures x == old(abs)[|old(abs)|-1]
    {
        count := count - 1;
        x := arr[count];
        abs := old(abs)[..|old(abs)|-1];
    }

    method Top() returns (x: int)
        requires Valid()
        requires count > 0
        ensures x == abs[|abs|-1]
        ensures abs == old(abs)
    {
        x := arr[count-1];
    }

    function IsEmpty(): bool
        requires Valid()
        reads this, arr
        ensures IsEmpty() <==> |abs| == 0
    {
        count == 0
    }

    function Size(): int
        requires Valid()
        reads this, arr
        ensures Size() == count
    {
        count
    }
}

method Main() {
    var s := new Stack(4);
    assert s.IsEmpty();
}