// queue implemented with circular array to have infinite size

const initialValue := 10

class{:autocontracts} UnlimitedQueue {

  var a: array<int>;
  var head: nat;
  var tail: nat;
  var max: nat;

  var numberOfElements: nat;
  //Abstração
  ghost var content: seq<int>;

  ghost predicate Valid() {
    max > 0
    && a.Length == max
    && 0 <= head < max
    && 0 <= tail < max
    && ((head > tail ==> content == a[head..] + a[0..tail]) || (tail >= head ==> content ==  a[head..tail])) // substituir por uma verificação que valide que content é o mesmo que a[head..tail] ou a[tail..head] em qualquer ordem
    && numberOfElements == |content|
    }

    constructor ()
      ensures content == []
      ensures a.Length == initialValue
    {
    a := new int[initialValue];
    head := 0;
    tail := 0;
    max := initialValue;
    content := [];
    numberOfElements := 0;
  }

  function size():nat
    ensures size() == |content|
  {
    numberOfElements
  }

  function isEmpty():bool
    ensures isEmpty() == (size() == 0)
  {
    numberOfElements == 0
  }

  method contains (x: nat) returns (r: bool)
    requires Valid()
    ensures Valid()
    ensures r == (x in content)
  {
    var i: nat := head;

    r := false;
    while i != tail
      invariant 0 <= i < a.Length
      invariant Valid()
    {
      if a[i] == x {
        r := true;
      }
      i := (i + 1) % a.Length;
    }
  }

    // insert in circular array
    method enqueue (x: nat)
        requires Valid()
        ensures Valid()
        ensures content == old(content) + [x] {
          a[tail] := x;
          tail := (tail + 1) % a.Length;

          if(tail == head) {
            tail := a.Length;
            var aux := new int[2 * a.Length];
            forall i | 0 <= i < a.Length
            {
                aux[i] := a[i];
            }
            a := aux;
            max := a.Length;
          }
          
          numberOfElements := numberOfElements + 1;
          content := content + [x];
        }

    // remove element from circular array
    method dequeue () returns (r: int)
        requires Valid()
        requires size() > 0
        requires numberOfElements < |content|
        ensures Valid()
        ensures r == old(content)[0]
        ensures content == old(content)[..numberOfElements] {
            r := a[head];
            a[head] := -1;
            head := (head + 1) % a.Length;
            numberOfElements := numberOfElements - 1;

            content := content[..numberOfElements];
          
        }

    // add all elements from one queue to another
    method append (q: UnlimitedQueue)
        requires Valid()
        requires q.Valid()
        ensures Valid()
        ensures content == old(content) + q.content
}