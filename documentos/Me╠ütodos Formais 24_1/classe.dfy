//usado como ref https://www.javatpoint.com/implementation-of-deque-by-circular-array
//

class {:autocontracts} DequeCircular {
  var arrElements: array<int> // Array de elementos
  var front: int 
  var rear: int 
  var qty: int //quantos elementos no deque

  ghost var Elements: seq<int> // Elementos do Array
  ghost const Capacity: nat

  ghost predicate Valid()
  {
    0 <= qty <= arrElements.Length &&
    -1 <= front < arrElements.Length &&
    0 <= rear < arrElements.Length &&
    0 <= qty == |Elements| &&
    Capacity == arrElements.Length &&
    Elements == if front == -1
                  then []
                else if rear < front
                  then arrElements[front..] + arrElements[..rear+1]
                else arrElements[front..rear + 1]

  }

  constructor BuildDeque(capacity : int)
    requires capacity > 0
    ensures Elements == []
    ensures Capacity == capacity
  {
    arrElements := new int[capacity];
    front := -1;
    rear:= 0;
    Elements := [];
    qty := 0;
    Capacity := capacity;
  }

  predicate IsFull()
    ensures IsFull() <==> |Elements| == Capacity {
    qty == arrElements.Length
  }

  function Size(): int
    ensures Size() == |Elements|
  {
    qty
  }

  predicate IsEmpty()
    ensures IsEmpty() <==> (|Elements| == 0)
  {
    front == -1
  }

  function DeckSize(): int
    ensures DeckSize() == arrElements.Length
  {
    arrElements.Length
  }

  method AddElementFront(x : int)
    requires !IsFull()
    ensures Elements == [x] + old(Elements)
  {
    qty := qty +1;

    if(front == -1){
      front := 0;
      rear := 0;
    }
    else if(front == 0){
      front := arrElements.Length - 1;
    } else {
      front := (front - 1 + arrElements.Length) % arrElements.Length;
    }
    arrElements[front] := x;
    Elements := [x] + Elements;

  }

  method AddElementRear(x : int)
    requires !IsFull()
    ensures Elements == old(Elements) + [x] 
  {
    if(front == -1){
      front := 0;
      rear := 0;
    }
    else if(rear == arrElements.Length - 1){
      rear := 0;
    }
    else{
      rear := (rear + 1) % arrElements.Length;
    }
    arrElements[rear] := x;
    Elements := Elements + [x];
    qty := qty + 1;

  }

  method DeleteElementFront() returns (x: int)
    requires !IsEmpty()
    ensures Elements == old(Elements)[1..]
    ensures x == old(Elements[0])
  {
    x := arrElements[front];
    if (rear == front){
      front := -1;
      rear := 0;
    }
    else if(front == arrElements.Length-1){
      front := 0;
    }
    else{
      front := front +1;
    }
    Elements := Elements[1..];
    qty := qty -1;
  }

  method DeleteElementRear() returns (x: int)
    requires !IsEmpty()
    ensures x == old(Elements[|Elements| -1])
    ensures Elements == old(Elements[..|Elements| -1])
  {
    x := arrElements[rear];
    if (rear == front){
      front := -1;
      rear := 0;
    }
    else if(rear == 0){
      rear := arrElements.Length - 1;
    }else{
      rear := rear - 1;
    }
    Elements := Elements[..|Elements| -1];
    qty := qty -1;
  }

  method Resize(oldDeq : DequeCircular) returns (deq: DequeCircular)
    requires oldDeq.Valid()
    requires Valid()
    ensures deq.Elements == Elements + oldDeq.Elements
  {
    deq := new DequeCircular.BuildDeque(oldDeq.arrElements.Length * 2);
    var size := deq.DeckSize();
    var arr1 := Sort();
    var arr2 := oldDeq.Sort();
    var arrSumed := arr1 + arr2;
    forall i | 0 <= i < |arrSumed| {
      deq.arrElements[i] := arrSumed[i];
    }
    deq.qty := qty + oldDeq.qty;
    deq.Elements := Elements + oldDeq.Elements;
    deq.rear := rear;
    deq.front := front;
  } 



   method Sort() returns (sorted: seq<int>)
    ensures |sorted| == qty
  {
    if front == -1 && qty == 0 {
      return [];
    }

    if rear >= front {
      return arrElements[front..rear + 1];
    } else {
      return arrElements[front..] + arrElements[..rear + 1];
    }
  }

  predicate Contains(x : int)
  ensures Contains(x) == (x in Elements)
  requires !IsEmpty(){
    if rear >= front then 
      x in arrElements[front..rear + 1]
    else 
      x in arrElements[front..] + arrElements[..rear + 1]

  }

}
method Main()
{
  var deq := new DequeCircular.BuildDeque(2);
  assert deq.DeckSize() == 2;
  assert deq.IsEmpty();
  deq.AddElementFront(1);
  assert !deq.IsEmpty();
  assert deq.Size() == 1;
  assert deq.Contains(1);
  
  deq.AddElementRear(2);
  assert !deq.IsEmpty();
  assert deq.Size() == 2;
  assert deq.Contains(2);

  assert deq.IsFull();

  var e1 := deq.DeleteElementFront();
  assert deq.Size() == 1;
  assert e1 == 1;
  assert !deq.Contains(1);


  var e2 := deq.DeleteElementRear();
  assert deq.Size() == 0;
  assert deq.IsEmpty();
  assert e2 == 2;

}