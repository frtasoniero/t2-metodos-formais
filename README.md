# Formal Methods – Project 2

## 📝 Project Title

> **Formal Specification and Verification of the Stack Data Structure in Dafny**

## 🎯 Objective

Develop **formal specifications** and **verifications** in **Dafny** for algorithms using data structures.
You must implement and formally verify the abstract data type **Stack** using **arrays** in all concrete implementations.

## 📥 Submission Guidelines

* **What to Submit:**

  * `.dfy` file containing all Dafny source code
  * Names of all group members

## 📋 Problem Statement

You are to implement the **Stack** abstract data type (without size limit), using a concrete implementation with **arrays** (arrays are required for all operations!).

Your Dafny implementation should include:

### 1️⃣ Abstract Representation (using `ghost`)

* Represent the stack's elements collection
* Represent any other information necessary for correct verification

### 2️⃣ Class Invariant (using `predicate`)

* Use a suitable `Valid()` predicate for the class invariant, associated with the stack's abstract representation

### 3️⃣ Required Operations

Implement the following methods:

* **Constructor:** Create an empty stack
* **Push:** Add a new element at the top
* **Pop:** Remove the top element (if not empty)
* **Peek:** View the top element without removing (if not empty)
* **IsEmpty:** Check if the stack is empty
* **Size:** Return the number of elements in the stack
* **Reverse:** Reverse the stack elements order
* **Stack Over Another:** Combine two stacks (returns a new stack, does not alter originals)

> ⚡️ **Tip:** Every operation must have correct preconditions, postconditions, invariants, and variants!

## 🧪 Main Method Requirement

* Implement a `Main` method demonstrating all operations above
* Use **assertions** (unit test style) to guarantee coverage for typical and edge cases

## 🗒️ Notes After Project Review

  - **Model/Invariant:** self-contract

  - **Constructor:**

     * **Implementation:** ok
     * **Validation:** ok

  - **Add (Push):**

     * **Implementation:** ok
     * **Validation:** ok

  - **Remove (Pop):**

     * **Implementation:** ok
     * **Validation:** ok

  - **Top (Peek):** does not guarantee stack immutability

     * **Implementation:** ok
     * **Validation:** ok

  - **IsEmpty:**

     * **Implementation:** ok
     * **Validation:** ok

  - **Size:**

     * **Implementation:** ok
     * **Validation:** ok

  - **Reverse:**

     * **Implementation:** ok
     * **Validation:** ok

  - **Stack Over Another:** does not guarantee immutability of argument stacks

     * **Implementation:** ok
     * **Validation:** ok

  - **Main:** ok
