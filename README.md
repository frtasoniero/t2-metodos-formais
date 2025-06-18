# Assignment 2

The grade for this assignment consists of the work specified here, whose objective is to build formal specifications and verifications in the Dafny language for algorithms on data structures. The assignment will be carried out in groups of up to 5 students. The work must be submitted via Moodle by the date indicated in the submission area according to the course schedule. The group must submit a (.dfy) file containing all the source code in Dafny and the names of all group members.

## Instructions

We are interested in implementing the abstract data type Stack (with no size limit) through a concrete implementation using arrays. Note that the use of arrays is mandatory in all operations of the concrete implementation!

To do this, you will need to create a Stack class in Dafny and represent the attributes, methods, functions, and predicates according to the following instructions. For simplification, consider the declaration of Stacks containing integers and do not worry about implementing a generic collection.

Abstract representation (via ghost):

- Represent the collection of stack elements.
- Represent any other information relevant for the correct verification of the implementation.

Class invariant (via predicate):

- Use an appropriate Valid() predicate for the invariant of the abstract representation associated with the stack collection.

Operations:

- Constructor must instantiate an empty stack.
- Add a new element to the top of the stack.
- Remove an element from the top of the stack, if it is not empty.
- Read the value at the top of the stack, without removing it, if the stack is not empty.
- Check whether the stack is empty or not.
- Query the number of elements stored in the stack.
- Reverse the order of the elements in the stack.
- Stack one stack on top of another, returning a new stack, without changing the stacks provided as arguments.

All preconditions, postconditions, invariants, and variants must be correctly specified. Part of the evaluation of the assignment is the complete understanding of which assertions should be part of the specification of the requested operations on the data structure.

Finally, build a small “Main” method demonstrating the use of the implemented operations and verifying assertions (in the style of unit tests) for a number of cases that ensure