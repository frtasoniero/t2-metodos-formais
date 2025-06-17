type T = int // for demonstration, but could be any type

class {:autocontracts} Deque
{
    // Abstraction
    ghost var Content: seq<T>
    ghost const Capacity: nat

    // Implementation 
    const arr: array<T> 
    const cap: nat
    var tail: nat

    ghost predicate Valid()
    {
      cap > 0 &&
      arr.Length == cap &&
      0 <= tail <= cap &&
      Content == arr[0..tail] &&
      Capacity == cap
    }
 
    constructor (c: nat)
      requires c > 0
      ensures Content == []
      ensures Capacity == c
    {
      arr := new T[c];
      cap := c;
      tail := 0;
      Content := [];
      Capacity := c;
    }

    //Predicate that can be used as a method, generating executable code
    predicate isEmpty()
      ensures isEmpty() <==> Content == []
    {
      tail == 0
    }
    
    //Predicate that can be used as a method, generating executable code
    predicate isFull()
      ensures isFull() <==> |Content| == Capacity
    {
      tail == cap
    }

    //Function that can be used as a method, generating executable code
    function front() : T
      requires !isEmpty()
      ensures front() == Content[0]
    {
      arr[0]
    }

    //Function that can be used as a method, generating executable code
    function back() : T
      requires !isEmpty()
      ensures back() == Content[|Content| - 1]
    {
      arr[tail-1]
    }

    method push_back(e : T)
      requires !isFull()
      ensures Content == old(Content) + [e]
    {
      arr[tail] := e;
      tail := tail + 1;
      Content := Content + [e];
    }

    method pop_back() returns (e:T)
      requires !isEmpty()
      ensures e == old(Content[|Content| - 1])
      ensures Content == old(Content[..|Content|-1])
    {
      tail := tail - 1;
      e := arr[tail];
      Content := Content[..tail];
    }

    method push_front(e : T)
      requires !isFull()
      ensures Content == [e] + old(Content) 
    {
      forall i | 0 <= i < tail
      {
        arr[tail - i] := arr[tail - i - 1];
      }
      arr[0] := e;
      tail := tail + 1;
      Content := [e] + Content;
    }

    method pop_front() returns (e:T)
      requires !isEmpty()
      ensures e == old(Content[0])
      ensures Content == old(Content[1..])
    {
      e := arr[0];
      tail := tail - 1;
      forall i | 0 <= i < tail
      {
        arr[i] := arr[i+1];
      }
      Content := arr[0..tail];
    }
}

method Main()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    var e := q.pop_back();
    assert e == 3;
    assert q.front() == 2;
    assert q.back() == 1;
    e := q.pop_front();
    assert e == 2;
    assert q.front() == 1;
    assert q.back() == 1;
    e := q.pop_front();
    assert e == 1;
    assert q.isEmpty();
}
