# Agda formalization of Li and Zhang's flow and path-sensitive information flow analysis
## 
Agda formalization of a static information flow analysis presented in the "Towards a Flow- and Path-Sensitive Information Flow Analysis: Technical Report" paper by Peixuan Li and Danfeng Zhang, which uses a fixed-label type system with dependent types.

## Installation
This formalization has been tested using 
<a href="https://agda.readthedocs.io/en/v2.6.3/getting-started/installation.html"> Agda 2.6.3 </a> and the Agda standard library v1.7.2. 

## Code Structure
The Agda modules are organized according to the following structure:

* Base 
    * AST 
    * Transformation      
    * AssignmentId 

## Module Content

**Base**

* **AST.agda**: Definition of the syntax trees for both the bracketed and non-bracketed versions of the source language. _(Section 3)_

* **Transformation.agda**: Transformation between bracketed and non-bracketed programs. _(Section 4)_

* **AssignmentId.agda**: Assignment of unique IDs to each assignment statement of a program. _(Section 5)_