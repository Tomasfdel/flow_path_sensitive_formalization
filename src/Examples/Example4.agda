module Examples.Example4 where

open import Data.Fin.Base
open import Data.Maybe.Base
open import Data.Nat
open import Data.Product
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

-- EXAMPLE 4: This program has an implicit declassification problem
-- when changing the value of l1 in the fourth instruction, so it
-- is rejected by our type system due to it being insecure.
example4 : ASTStmS
example4 = Seq (x := IntVal 0)
          (Seq (y := IntVal 0)
          (Seq (If (Var l1) Skip (y := Var h))
          (Seq (l1 := IntVal 1)
          (Seq (If (Var l1) (x := Var y) Skip)
               (l2 := Var x)))))

typeEnv : TypingEnvironment
typeEnv = (toList [ Label Low ]) ∷  
          (toList [ ExpTest (VAR (l1 , zero)) (Label Low) (Label High) ]) ∷ 
          (toList [ Label High ]) ∷ 
          (toList [ Label Low ]) ∷ 
          (toList [ Label Low ]) ∷
          [] 

typed : Maybe TypingProof
typed = typeProgram example4 typeEnv
