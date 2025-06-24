module Examples.Example1 where

open import Agda.Builtin.List
open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.Product 
open import Data.Vec

n : ℕ
n = 3

open import TypeSystem.AssignmentId {n}
open import Transformation.ActiveSet {n}
open import Transformation.AST {n}
open import TypeSystem.Liveness {n}
open import TypeSystem.Predicates {n}
open import TypeSystem.SecurityLabels {n}
open import Transformation.Transformation {n}
open import TypeSystem.TypeSystem {n}
open import Transformation.VariableSet {n}

x : Fin n
x = (fromℕ 0) ↑ˡ 2

h : Fin n
h = (fromℕ 1) ↑ˡ 1

l : Fin n
l = fromℕ 2

-- EXAMPLE 1: This program is considered insecure by the type system 
-- due to not using the bracketed assignments to gain flow-sensitivity.
example1 : ASTStmS
example1 = Seq (x := Var h)
          (Seq (x := IntVal 0)
               (l := Var x))

typeEnv : TypingEnvironment
typeEnv = (toList [ Label Low ]) ∷ 
          (toList [ Label High ]) ∷ 
          (toList [ Label Low ]) ∷ 
          [] 

typed : Maybe TypingProof
typed = typeProgram example1 typeEnv
