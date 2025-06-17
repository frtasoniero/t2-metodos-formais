class Stack {
    var arr: array<int>
    var count: int

    ghost var abs: seq<int> // Abstract representation (top at end)

    ghost predicate Valid()
        reads this, arr
    {
        0 <= count <= arr.Length
        && abs == arr[..count] // abs matches concrete prefix
    }

    constructor()
        ensures Valid()
        ensures abs == []
    {
        arr := new int[4]; // Start with small array, can resize later
        count := 0;
        abs := [];
    }

    method Push(x: int)
        requires Valid()
        modifies this, arr
        ensures Valid()
        ensures abs == old(abs) + [x]
    {
        if count == arr.Length {
            var newArr := new int[arr.Length * 2];
            var i := 0;
            while i < count
                invariant 0 <= i <= count
                invariant count == arr.Length
                invariant newArr.Length == arr.Length * 2
                invariant forall j :: 0 <= j < i ==> newArr[j] == arr[j]
            {
                newArr[i] := arr[i];
                i := i + 1;
            }
            arr := newArr;
        }
        arr[count] := x;
        count := count + 1;
        abs := old(abs) + [x];
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
    var s := new Stack();
    assert s.IsEmpty();
    assert s.Size() == 0;
    s.Push(1);
}