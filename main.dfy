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

    method Pop() returns (x: int)
        requires |abs| > 0
        ensures x == old(abs)[|old(abs)| - 1]
        ensures abs == old(abs)[..|old(abs)| - 1]
    {
        x := arr[count - 1];
        count := count - 1;
        forall i | 0 <= i < count
        {
            arr[i] := arr[i];
        }
        abs := arr[..count];
    }

    method Peek() returns (x: int)
        requires |abs| > 0
        ensures x == abs[|abs| - 1]
    {
        x := arr[count - 1];
    }

    method ConcatenateStacks(other: Stack) returns (result: Stack)
        requires Valid()
        requires other.Valid()
        ensures result.Valid()
        ensures result.abs == abs + other.abs
    {
        result := new Stack();

        var i:= 0;

        while i < count
            invariant 0 <= i <= count
            invariant 0 <= i <= result.count
            invariant fresh(result.Repr)
            invariant result.Valid()
            invariant result.abs == abs[0..i]
        {
            var value := arr[i];
            result.Push(value);
            i := i + 1;
        }

        var j := 0;
        while j < other.count
            invariant 0 <= j <= other.count
            invariant 0 <= j <= result.count
            invariant fresh(result.Repr)
            invariant result.Valid()
            invariant result.abs == abs + other.abs[0..j]
        {
            var value := other.arr[j];
            result.Push(value);
            j := j + 1;
        }
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
    
    // Test initial state
    assert s.IsEmpty();
    assert s.Size() == 0;
    
    // Test Push method
    s.Push(1);
    assert !s.IsEmpty();
    assert s.Size() == 1;
    
    // Test Peek method (should return top element without removing it)
    var peekValue := s.Peek();
    assert peekValue == 1;
    assert s.Size() == 1; // Size should remain the same after Peek
    assert !s.IsEmpty();
    
    // Test Push with multiple elements
    s.Push(2);
    s.Push(3);
    assert s.Size() == 3;
    
    // Test Peek with multiple elements (should return last pushed element)
    peekValue := s.Peek();
    assert peekValue == 3;
    assert s.Size() == 3; // Size should remain the same
    
    // Test Pop method - LIFO (Last-In-First-Out)
    var popValue := s.Pop();
    assert popValue == 3; // Should return the last element pushed
    assert s.Size() == 2; // Size should decrease after Pop
    
    // Test another Pop
    popValue := s.Pop();
    assert popValue == 2;
    assert s.Size() == 1;
    
    // Test Peek after Pop operations
    peekValue := s.Peek();
    assert peekValue == 1; // Should be the first element we pushed
    assert s.Size() == 1;
    
    // Test final Pop
    popValue := s.Pop();
    assert popValue == 1;
    assert s.Size() == 0;
    assert s.IsEmpty();
    
    // Test Push after emptying the stack
    s.Push(10);
    s.Push(20);
    assert s.Size() == 2;
    assert !s.IsEmpty();
    
    // Test final Peek and Pop
    peekValue := s.Peek();
    assert peekValue == 20;
    
    popValue := s.Pop();
    assert popValue == 20;
    assert s.Size() == 1;
    
    popValue := s.Pop();
    assert popValue == 10;
    assert s.IsEmpty();
    assert s.Size() == 0;

    // Add this to your Main method for testing
    // Test ConcatenateStacks
    var s1 := new Stack();
    s1.Push(2);
    s1.Push(3);

    var s2 := new Stack();
    s2.Push(1);
    s2.Push(7);

    var combined := s1.ConcatenateStacks(s2);
    assert combined.Size() == 4;
    assert s1.Size() == 2; // Original stack unchanged
    assert s2.Size() == 2; // Original stack unchanged

    // Verify the concatenation order by popping elements
    var val := combined.Pop();
    assert val == 7; // Last element from s2
    val := combined.Pop();
    assert val == 1;
    val := combined.Pop();
    assert val == 3;
    val := combined.Pop();
    assert val == 2; // First element from s1
}