module Examples.Example3 where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.Vec

n : ℕ
n = 5

open import Transformation.AST {n}
open import TypeSystem.SecurityLabels {n}
open import TypeSystem.TypeSystem {n}

x : Fin n
x = (fromℕ 0) ↑ˡ 4

y : Fin n
y = (fromℕ 1) ↑ˡ 3

h : Fin n
h = (fromℕ 2) ↑ˡ 2

l1 : Fin n
l1 = (fromℕ 3) ↑ˡ 1

l2 : Fin n
l2 = fromℕ 4

-- EXAMPLE 3: The type system accepts this program if a dependent
-- value is used in the security label of variable y, thus accepting
-- a program that requires path-sensitivity to be considered secure.
example3 : ASTStmS
example3 = Seq (x := IntVal 0)
          (Seq (y := IntVal 0)
          (Seq (If (Var l1) (y := Var h) Skip)
          (Seq (If (Var l1) Skip (x := Var y))
               (l2 := Var x))))

typeEnv : TypingEnvironment
typeEnv = (toList [ Label Low ]) ∷  
          (toList [ ExpTest (VAR (l1 , zero)) (Label High) (Label Low) ]) ∷ 
          (toList [ Label High ]) ∷ 
          (toList [ Label Low ]) ∷ 
          (toList [ Label Low ]) ∷
          [] 

typed : Maybe TypingProof
typed = typeProgram example3 typeEnv
