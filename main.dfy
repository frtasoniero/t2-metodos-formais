/*
 * Grupo: Felipe Tasoniero, Lucas Wolschick
 * Trabalho T2 - Métodos Formais
 * Dafny Version: 4.10.0
 * 
 * Verificação formal em Dafny da implementação de uma pilha (Stack) com as seguintes características:
    * - Implementação de pilha com array dinâmico
    * - Métodos: Push, Pop, Peek, ConcatenateStacks, IsEmpty, Size
 */

class {:autocontracts} Stack {
    // Representação concreta da pilha
    var arr: array<int>
    var count: int

    ghost var abs: seq<int> // Representação abstrata (topo no final)

    // Representação do estado da pilha
    ghost predicate Valid()
    {
        arr.Length != 0 // Garante que o array não está vazio
        && 0 <= count <= arr.Length
        && abs == arr[..count] // abs corresponde ao prefixo concreto
    }

    // Construtor da pilha
    constructor()
        ensures Valid()
        ensures abs == []
    {
        arr := new int[5]; // Inicia com array pequeno, duplica o tamanho ao atingir o limite
        count := 0;
        abs := [];
    }

    // Adiciona um elemento ao topo da pilha
    // Se o array estiver cheio, duplica seu tamanho
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

    // Remove o elemento do topo da pilha e o retorna
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

    // Lê o elemento do topo da pilha sem removê-lo
    method Peek() returns (x: int)
        requires |abs| > 0
        ensures x == abs[|abs| - 1]
    {
        x := arr[count - 1];
    }

    // Combina duas pilhas, mantendo a ordem dos elementos
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

    // Inverte a ordem dos elementos na pilha
    method Reverse()
        requires |abs| > 0
        ensures |abs| == |old(abs)|
        ensures forall i | 0 <= i < |abs| :: abs[i] == old(abs[|abs| - i - 1])
    {
        var b := new int[count];

        forall i | 0 <= i < count
        {
            b[i] := arr[count - i - 1];
        }

        arr := b;
        abs := arr[..count];
    }

    // Verifica se a pilha está vazia
    function IsEmpty(): bool
        ensures IsEmpty() <==> |abs| == 0
    {
        count == 0
    }

    // Consulta o numero de elementos na pilha
    function Size(): int
        ensures Size() == |abs|
    {
        count
    }
}

method Main()
{
    var s := new Stack();
    
    // Teste estado inicial (verifica se a pilha está vazia)
    assert s.IsEmpty();
    assert s.Size() == 0;
    
    // Teste Push
    s.Push(1);
    s.Push(2);
    assert s.Size() == 2;
    assert !s.IsEmpty();
    
    // Teste Peek (leitura do elemento do topo)
    var peekValue := s.Peek();
    assert peekValue == 2; // Último elemento adicionado
    assert s.Size() == 2;  // Tamanho não deve mudar
    
    // Teste Pop (remoção do último elemento)
    var popValue := s.Pop();
    assert popValue == 2;  // Remoção e retorno do último elemento adicionado
    assert s.Size() == 1;  // Tamanho deve diminuir

    // Teste ConcatenateStacks (combinação de duas pilhas)
    var s1 := new Stack();
    s1.Push(2);
    s1.Push(3);

    var s2 := new Stack();
    s2.Push(1);
    s2.Push(7);

    assert s1.abs == [2, 3];
    assert s2.abs == [1, 7];

    var combined := s1.ConcatenateStacks(s2);

    assert combined.Size() == 4;
    assert s1.Size() == 2; // Pilha original s1 não deve ser alterada
    assert s2.Size() == 2; // Pilha original s2 não deve ser alterada

    assert combined.abs == [2, 3, 1, 7]; // Combinação correta dos elementos

    // Teste Reverse (inversão da ordem dos elementos)
    var s3 := new Stack();
    s3.Push(1);
    s3.Push(3);
    s3.Push(6);
    assert s3.abs == [1, 3, 6];

    s3.Reverse();
    assert s3.abs == [6, 3, 1]; // Ordem invertida
    assert s3.Size() == 3; // Tamanho deve permanecer o mesmo
}