# Agda formalization of Li and Zhang's flow and path-sensitive information flow analysis
## 
Agda formalization of a static information flow analysis presented in the "Towards a Flow- and Path-Sensitive Information Flow Analysis: Technical Report" paper by Peixuan Li and Danfeng Zhang, which uses a fixed-label type system with dependent types.

## Installation
This formalization has been tested using 
<a href="https://agda.readthedocs.io/en/v2.7.0/getting-started/installation.html"> Agda 2.7.0 </a> and the Agda standard library v2.2. 

## Code Structure
The Agda modules are organized according to the following structure:

* Base 
    * AST
    * AssignmentId
    * Liveness
    * Predicates
    * SecurityLabels
    * Semantic
    * Transformation
    * TypeSystem
    * VariableSet

## Module Content

**Base**

* **AST.agda**: Definition of the syntax trees for both the bracketed and non-bracketed versions of the source language. _(Section 3)_

* **Transformation.agda**: Transformation between bracketed and non-bracketed programs. _(Section 4.2)_

* **Semantic.agda**: Proof of correctness of the transformation. _(Section 4.3)_

* **SecurityLabels.agda**: Definition of the type system's security labels. _(Section 5.3)_

* **AssignmentId.agda**: Assignment of unique IDs to each assignment statement of a program. _(Section 5.4)_

* **Liveness.agda**: Variable liveness analysis, which is later used in the typing rules. _(Section 5.4)_

* **Predicates.agda**: Generation of program state predicates that are true for each assignment statement, also used in the typing rules. _(Section 5.4)_

* **TypeSystem.agda**: Definition of the type system for transformed programs. _(Section 5.5)_

* **VariableSet.agda**: Utility module defining finite sets of program variables.