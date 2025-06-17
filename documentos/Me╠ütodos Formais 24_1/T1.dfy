
class {:autocontracts} DequeCircular {
  var capacity: int // Tamanho do array
  var arrElements: array<int> // array de elementos
  var front: int // Indíce do primeiro elemento do array
  var rear: int // Indíce do primeiro elemento do array
  var size: int // Números de elementos no array


  ghost var Elements: seq<int> // Elementos do Array
  ghost var Capacity: int

  ghost predicate Valid()
  {
    0 <= front <= capacity &&
    0 <= rear < capacity &&
    0 <= size <= capacity &&
    capacity == arrElements.Length
    Capacity == capacity &&
    Elements == if head + size <= elements.Length
                then elements[head..head + size]
                else elements[head..] + elements[..size - (elements.Length - head)]
  }

  /*
    Constructor.
  */
  constructor EmptyQueue(maxSize: nat)
    requires maxSize > 0
    ensures Elements == []
    ensures capacity == maxSize
  {
    elements := new int[maxSize];
    head := 0;
    size := 0;
    capacity := maxSize;
    Elements := [];
  }

  /*
    Enqueue Method
  */
  method Enqueue(e: int)
    requires !IsFull()
    ensures Elements == old(Elements) + [e]
  {
    elements[(head + size) % elements.Length] := e;
    size := size + 1;
    Elements := Elements + [e];
  }

  /*
    Dequeue method.
  */
  method Dequeue() returns (e: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
  {
    e := elements[head];
    if head + 1 < elements.Length {
      head := head + 1;
    }
    else {
      head := 0;
    }
    size := size - 1;
    Elements := Elements[1..];
  }

  /*
    Contains predicate.
  */
  predicate Contains(e: int)
    ensures Contains(e) == (e in Elements)
  {
    if head + size < elements.Length then
      e in elements[head..head + size]
    else
      e in elements[head..] + elements[..size - (elements.Length - head)]
  }

  /*
    Size function.
  */
  function Size(): nat
    ensures Size() == |Elements|
  {
    size
  }

  /*
    IsEmpty predicate.
  */
  predicate IsEmpty()
    ensures IsEmpty() <==> (|Elements| == 0)
  {
    size == 0
  }

  /*
    IsFull predicate.
  */
  predicate IsFull()
    ensures IsFull() <==> |Elements| == capacity
  {
    size == elements.Length
  }

  /*
    GetAt method.
    (Not requested in the assignment, but useful).
  */
  method GetAt(i: nat) returns (e: int)
    requires i < size
    ensures e == Elements[i]
  {
    e := elements[(head + i) % elements.Length];
  }

  /*
    AsSequence method.
    (Auxiliary method for the Concatenate method)
  */
  method AsSequence() returns (s: seq<int>)
    ensures s == Elements
    {
      s := if head + size <= elements.Length
           then elements[head..head + size]
           else elements[head..] + elements[..size - (elements.Length - head)];
    }

  /*
    Concatenate method.
  */
  method Concatenate(q1: DequeCircular) returns(q2: DequeCircular)
    requires q1.Valid()
    requires q1 != this
    ensures fresh(q2)
    ensures q2.capacity == capacity + q1.capacity
    ensures q2.Elements == Elements + q1.Elements
  {
    q2 := new DequeCircular.EmptyQueue(elements.Length + q1.elements.Length);
    var s1 := AsSequence();
    var s2 := q1.AsSequence();
    var both := s1 + s2;
    forall i | 0 <= i < size
    {
      q2.elements[i] := both[i];
    }
    q2.size := size + q1.size;
    q2.head := 0;
    q2.Elements := Elements + q1.Elements;
    
    print q2.elements.Length;
    print q2.size;
  }
}

/*
  Main method.
  Here the the CircularArray class is demonstrated.
*/
method Main()
{
  var q := new DequeCircular.EmptyQueue(10); // Create a new queue.
  assert q.IsEmpty(); // The queue must be empty.

  q.Enqueue(1); // Enqueue the element 1.
  assert !q.IsEmpty(); // The queue must now not be empty.
  assert q.Size() == 1; // The queue must have size 1 after the enqueue.
  assert q.Contains(1); // The queue must contain the element 1.
  var e1 := q.GetAt(0); // Get the element at index 0.
  assert e1 == 1; // The element at index 0 must be 1.

  q.Enqueue(2); // Enqueue the element 2.
  assert q.Size() == 2; // The queue must have size 2 after the enqueue.
  assert q.Contains(2); // The queue must contain the element 2.
  var e2 := q.GetAt(1); // Get the element at index 1.
  assert e2 == 2; // The element at index 1 must be 2.

  var e := q.Dequeue(); // Dequeue the element 1.
  assert e == 1; // The dequeued element must be 1.
  assert q.Size() == 1; // The queue must have size 1 after the dequeue.
  assert !q.Contains(1); // The queue must NOT contain the element 1 anymore.

  q.Enqueue(3); // Enqueue the element 3.
  assert q.Size() == 2; // The queue must have size 2 after the enqueue.
  assert q.Contains(3); // The queue must contain the element 3.

  e := q.Dequeue(); // Dequeue the element 2.
  assert e == 2; // The dequeued element must be 2.
  assert q.Size() == 1; // The queue must have size 1 after the dequeue.
  assert !q.Contains(2); // The queue must NOT contain the element 2 anymore.

  e := q.Dequeue(); // Dequeue the element 3.
  assert e == 3; // The dequeued element must be 3.
  assert q.Size() == 0; // The queue must have size 0 after the dequeue.
  assert !q.Contains(3); // The queue must NOT contain the element 3 anymore.

  assert q.IsEmpty(); // The queue must now be empty.
  assert q.Size() == 0; // The queue must now have size 0.
}