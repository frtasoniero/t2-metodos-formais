class {:autocontracts} Stack {
    var arr: array<int>
    var count: int

    ghost var abs: seq<int> // Abstract representation (top at end)

    ghost predicate Valid()
    {
        arr.Length != 0 // Ensure the array is not empty
        && 0 <= count <= arr.Length
        && abs == arr[..count] // abs matches concrete prefix
    }

    constructor()
        ensures Valid()
        ensures abs == []
    {
        arr := new int[5]; // Start with small array, can resize later
        count := 0;
        abs := [];
    }

    method Push(x: int)
        ensures abs == old(abs) + [x]
    {
        if (count == arr.Length)
        {
            var b := new int[2 * arr.Length];
            forall i | 0 <= i < arr.Length
            {
                b[i] := arr[i];
            }
            arr := b;
        }
        arr[count] := x;
        count := count + 1;
        abs := abs + [x];
    }

    function IsEmpty(): bool
        ensures IsEmpty() <==> |abs| == 0
    {
        count == 0
    }

    function Size(): int
        ensures Size() == |abs|
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