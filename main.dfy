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
    
    // Test Pop method
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

}