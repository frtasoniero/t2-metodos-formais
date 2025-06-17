// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class {:autocontracts} UnlimitedQueue
    {
      // public view of the class:
  ghost var Contents: seq<int>  // the contents of the ring buffer
  ghost var maxSize: nat  // the capacity of the ring buffer

  // private implementation:
  var data: array<int>
  var head: nat
  var len: nat

  // Valid encodes the consistency of RingBuffer objects (think, invariant)
  ghost predicate Valid()
    {
                        data.Length == maxSize &&
    len == |Contents| &&
    (maxSize == 0 ==> len == head == 0 && Contents == []) &&
    (maxSize != 0 ==> len <= maxSize && head < maxSize) &&
    Contents == if head + len <= maxSize then data[head..head+len]
    else data[head..] + data[..head+len-maxSize]
    }

    constructor(n: nat)
      ensures Contents == [] && maxSize == n
    {
    data := new int[n];
    head, len := 0, 0;
    Contents, maxSize := [], n;
    }

  function isEmpty() : bool 
    ensures isEmpty() <==> (Contents == []) && (len == 0)
  {
    len == 0
  }

  method contains(x: int) returns (result: bool)
    ensures result <==> (x in Contents) {
    var i := head;
    result := false;

    if head + len <= data.Length {
      while i < head+len
        invariant head <= i < head+len+1
        invariant result == (x in data[head..i]) {
        if data[i] == x {
          result := true;
    }
        i := (i + 1);
    }
    } else {
      while i < data.Length
        invariant head <= i < data.Length + 1
        invariant result == (x in data[head..i])
    {
        if data[i] == x {
          result := true;
    }
        i := (i + 1);
    }

      var j:= 0;
      while j < head+len-data.Length
        invariant 0 <= j <= head+len-data.Length
        invariant if (x in data[head..i]) then result == true else result == (x in data[0..j]) {
        if data[j] == x {
          result:=true;
    }
        j:= (j + 1);
    }

    }}


  method Enqueue(x: int)
    // requires |Contents| != maxSize
    ensures Contents == old(Contents) + [x]
            && if(old(maxSize) == old(len)) then maxSize == old(maxSize) * 2 + 1 else maxSize == old(maxSize)
    {
    if data.Length == len {
      var more := data.Length + 1;
      var d := new int[data.Length + more];
      forall i | 0 <= i < data.Length {
        d[if i < head then i else i + more] := data[i];
    }
      maxSize, data, head := maxSize + more, d, if len == 0 then 0 else head + more;
    }
    var nextEmpty := if head + len < data.Length
    then head + len else head + len - data.Length;
    data[nextEmpty] := x;
    len := len + 1;
    Contents := Contents + [x];
    }

  method Dequeue() returns (x: int)
    requires Contents != []
    ensures x == old(Contents)[0] && Contents == old(Contents)[1..] && maxSize == old(maxSize)
    {
    x := data[head];  assert x == Contents[0];
    head, len := if head + 1 == data.Length then 0 else head + 1, len - 1;
    Contents := Contents[1..];
    }

  method Append(q: UnlimitedQueue) returns (newQueue: UnlimitedQueue)
    requires q.Valid()
    ensures q.data == old(q.data)
    ensures data == old(data)
    ensures |Contents| == old(|Contents|)
    ensures |q.Contents| == old(|q.Contents|)
    ensures newQueue.Contents == Contents + q.Contents
    ensures newQueue.head == 0
    ensures |newQueue.Contents| == newQueue.len
    ensures newQueue.len == len + q.len
    ensures newQueue.Contents[..len] == Contents
    ensures newQueue.Contents[len..(len+q.len)] == q.Contents
    // ensures newQueue.Valid()
    ensures newQueue.data.Length == newQueue.maxSize
    ensures newQueue.len == |newQueue.Contents|
    ensures (newQueue.maxSize == 0 ==> newQueue.len == newQueue.head == 0 && newQueue.Contents == [])
    ensures (newQueue.maxSize != 0 ==> newQueue.len <= newQueue.maxSize && newQueue.head < newQueue.maxSize)
    ensures newQueue.head + newQueue.len <= newQueue.maxSize ==> newQueue.Contents ==
                                                                 newQueue.data[newQueue.head..newQueue.head+newQueue.len]
    ensures newQueue.head + newQueue.len > newQueue.maxSize ==> newQueue.Contents == newQueue.data[newQueue.head..] + newQueue.data[..newQueue.head+newQueue.len - newQueue.maxSize]
  {
    newQueue := new UnlimitedQueue(len + q.len);
    var aux := new int[len + q.len];

    forall i | 0 <= i < len + q.len {
      aux[i] := if i < len then data[i] else q.data[i - len];
    }
    assert aux.Length == len + q.len;
    newQueue.data := aux;
    newQueue.len := len + q.len;
    newQueue.head := 0;
    newQueue.maxSize := aux.Length;
    newQueue.Contents := Contents + q.Contents;
  }
}

method main()
{
  var b := new UnlimitedQueue(2);

  assert b.isEmpty() == true;

  var c := new UnlimitedQueue(3);
  var qq := b.Append(c); assert qq.len == 0;
  var rr := qq.contains(4); assert rr == false;
  b.Enqueue(1);
  assert |b.Contents| == 1;
  b.Enqueue(2);
  assert |b.Contents| == 2;
  b.Enqueue(3);
  assert |b.Contents| == 3;
  var r:= b.contains(2); assert r == true;
  var h := b.Dequeue(); assert h == 1;
  assert |b.Contents| == 2;
  var r1:= b.contains(1); assert r1 == false;
  c.Enqueue(10);
  c.Enqueue(20);
  c.Enqueue(30);
  c.Enqueue(40);
  var q := b.Append(c);
  assert |q.Contents| == 6;
  // var rq := q.contains(40); assert rq == true;
}