# Agda formalization of Li and Zhang's flow and path-sensitive information flow analysis
## 
Agda formalization of a static information flow analysis presented in the "Towards a Flow- and Path-Sensitive Information Flow Analysis: Technical Report" paper by Peixuan Li and Danfeng Zhang, which uses a fixed-label type system with dependent types.

## Installation
This formalization has been tested using 
<a href="https://agda.readthedocs.io/en/v2.7.0/getting-started/installation.html"> Agda 2.7.0 </a> and the Agda standard library v2.2. 

## Code Structure
The Agda modules are organized according to the following structure:

* src
    * Examples
        * Example1
        * Example2
        * Example3
        * Example4
    * Semantic
        * Correctness
        * CorrectnessLemmas
        * Memory
        * Semantic
        * WellFormed
    * Transformation
        * ActiveSet
        * AST
        * Transformation
        * VariableSet
    * TypeSystem
        * AssignmentId
        * Liveness
        * Predicates
        * SecurityLabels
        * TypeSystem

## Module Content

**Transformation**

* **AST.agda**: Definition of the syntax trees for both the bracketed and non-bracketed versions of the source language. _(Section 3)_

* **ActiveSet.agda**: Definition of active sets and operations for them. _(Section 4.2)_

* **Transformation.agda**: Transformation between bracketed and non-bracketed programs. _(Section 4.2)_

* **VariableSet.agda**: Utility module defining finite sets of program variables.

**Semantic**

* **Memory.agda**: Definition of memory for bracketed and non-bracketed programs. _(Section 4.3)_

* **Semantic.agda**: Big step semantics for both languages.

* **WellFormed.agda**: Well-formedness definition and properties for memories relative to active sets.

* **CorrectnessLemmas.agda**: Formalization of Lemmas 3 and 4 of the transformation correctness proof. _(Appendix A)_ 

* **Correctness.agda**: Formalization of the proof of correctness of the transformation. _(Appendix A)_

**TypeSystem**

* **SecurityLabels.agda**: Definition of the type system's security labels. _(Section 5.3)_

* **AssignmentId.agda**: Assignment of unique IDs to each assignment statement of a program. _(Section 5.4)_

* **Liveness.agda**: Variable liveness analysis, which is later used in the typing rules. _(Section 5.4)_

* **Predicates.agda**: Generation of program state predicates that are true for each assignment statement, also used in the typing rules. _(Section 5.4)_

* **TypeSystem.agda**: Definition of the type system for transformed programs. _(Section 5.5)_

**Examples**

Set of example programs used to test some aspects of the type system.