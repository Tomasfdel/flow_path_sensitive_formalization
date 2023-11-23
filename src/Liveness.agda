module Liveness {n} where

-- open import Data.Nat 
-- open import Data.Product
-- open import Function.Base

-- open import AST {n}



-- La idea es que tomo un programa y el active set final. 
-- Tengo que devolver un array de largo = cantidad de asignaciones en el programa. 
-- Capaz que para eso necesito como argumento también ese número, que sale del AssignmentId.
-- EL valor de cada elemento sería el LiveOut del statement que corresponda a ese Id.
-- Tengo que hacer una recursión con una primera función que funcione de una manera para el último statement y una distinta para todos los demás.
-- Cómo específicamente hago eso? No tengo la menor idea. 
-- Después, también necesito saber cuáles son los GEN y KILL de cada statement. Capaz que puedo encontrar una referencia de esto en internet,
-- o lo voy a tener que pensar y consultarlo con Ceci.
-- Sería útil también buscar una implementación de Sets porque si no me voy a volver bastante estúpido.
livenessAnalysis : ASTStmId → 𝒜 → Vec n (...)
