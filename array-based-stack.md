https://dafny.org/blog/2023/08/14/clear-specification-and-implementation/

Implementing an array-based stack
Now let’s look at how a common implementation of this data type might be structured. This approach uses a consecutive array to store elements, which we look at first because it’s somewhat simpler than the linked-list implementation we’ll consider next.

Before digging into the implementation, there’s one subtlety we need to discuss. The array-based approach sometimes requires allocating more space than is currently used, making it necessary to have a value available to fill unused entries. Many Dafny types have default values that can be used for this purpose, but not all types do. It is possible to constrain type parameters to those that do have default values by, for instance, using the declaration `class Stack<T(0)>`, to insist that `T` have type characteristic `0`, the notation for having a default value.

However, doing this would make the array-based stack have different constraints on its type parameter than other stack implementations, which isn’t ideal. An alternative is to make use of the fact that Dafny can define datatypes with ghost alternatives, and that datatypes with only one non-ghost alternative with only one argument have no runtime overhead. Therefore, the array-based stack implementation uses an (internal) datatype called `GhostOption` that makes it possible for `Stack` to be parameterized by an arbitrary type because the `GhostOption` type always has a default value.

    module ArrayStackImplementation {
      import opened StackSpecification`Private

      datatype GhostOption<T> = ghost None | Some(value: T)

      class Stack<T> {

The elements of the are stored in an array, using `GhostOption` to allow uninitialized values.

    var elts : array<GhostOption<T>>
We need a separate size tracker to know how much of the array is being used, because the size of elts itself will always be a power of two, and some entries will usually be unused.

    var size : nat
A ghost variable keeps track of the correspondence between the concrete storage in the array and the model used by the specification. This could also be used as a (slightly less efficient) implementation, as is done in a later example. As a ghost variable, it has no impact on performance.

    ghost var model : StackModel<T>
A stack agrees with its model if `size` matches the size of the model, the array has at least that much room, and all of the elements within the size of the model match the model. Note, however, that the model prepends to the beginning and the array adds at the end! Finally, the array always needs to have room for some elements, even if they’re all unused.

    ghost predicate ValidModel()
      reads this, elts
    {
      && elts.Length > 0
      && elts.Length >= |model|
      && size == |model|
      && forall i :: 0 <= i < |model| ==>
           elts[i] == Some(model[size - (i + 1)])
    }
An initial stack has room for a few elements (the exact number was chosen arbitrarily) but none of them are used. It is empty and valid.

    constructor InitStack()
      ensures ValidModel()
      ensures IsEmpty()
    {
      elts := new GhostOption<T>[4];
      size := 0;
      model := EmptyModel();
    }
To push an element on the stack, write to the first unused element of the array and increment the size. If there’s not room, however, it’s necessary to allocate a new array and copy the old elements over. Like all operations except `InitStack`, it requires a valid model. Like all operations that modify the stack, it ensures a valid model.

    method Push(val : T)
      requires ValidModel()
      modifies this, elts
      ensures old(size) >= old(elts.Length) ==> fresh(elts)
      ensures ValidModel()
      ensures !IsEmpty()
      ensures model == PushModel(old(model), val)
    {
      if size >= elts.Length {
        var newElts : array<GhostOption<T>> := new [elts.Length * 2];
        for i := 0 to size
          modifies newElts
          invariant forall j :: 0 <= j < i ==>
            newElts[j] == Some(model[size - (j + 1)])
        {
          newElts[i] := elts[i];
        }
        elts := newElts;
      }
      model := PushModel(model, val);
      elts[size] := Some(val);
      size := size + 1;
    }
To pop an element, return the last used element of the array and decrement the size. Ensures that both the return value and the internal changes match the stack specification.

    method Pop() returns (result : T)
      requires ValidModel()
      requires !IsEmpty()
      modifies this
      ensures ValidModel()
      ensures model == PopModel(old(model)).1
      ensures result == PopModel(old(model)).0
    {
      model := PopModel(model).1;
      size := size - 1;
      result := elts[size].value;
    }
The size variable alone is sufficient to tell us whether the stack is empty very efficiently.

        predicate IsEmpty()
          reads this, elts
          requires ValidModel()
          ensures IsEmpty() <==> IsEmptyModel(model)
        {
          size == 0
        }
      }
    }