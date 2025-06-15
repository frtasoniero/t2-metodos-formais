// Trabalho T2 - Métodos Formais - PUCRS
// Grupo: [INTEGRANTES AQUI]

method Main() 
{
    var s := new Stack(5);
    var empty := s.isEmpty();
    assert empty;
    var sSize := s.size();
    assert sSize == 0;

    assert s.Valid();
}

class Stack {
    var data: array<int>
    var count: int

    ghost var abs: seq<int> // Represents the abstract state of the stack

    ghost predicate Valid()
        reads this, data
    {
        0 <= count <= data.Length && abs == data[..count]
    }

    constructor (capacity: int)
        requires capacity >= 0
        ensures Valid()
        ensures abs == []
    {
        data := new int[capacity];
        count := 0;
        abs := [];
    }

    method push(x: int)
        requires Valid() && count < data.Length
        modifies this, data
        ensures Valid()
        ensures abs == old(abs) + [x]
    {
        data[count] := x;
        count := count + 1;
        abs := abs + [x];
    }

    method size() returns (s: int)
        requires Valid()
        ensures s == |abs|
        ensures s == count
    {
        return count;
    }

    method isEmpty() returns (empty: bool)
        requires Valid()
        ensures empty == (|abs| == 0)
        ensures empty == (count == 0)
    {
        return count == 0;
    }
}