{-# OPTIONS -Wall -fwarn-tabs #-}

module ProverTypecheckerInterface where

------------------------------------------------------------
------------------------- Imports --------------------------
------------------------------------------------------------

import Data.List (nub)

import Core
import Prover
import Parser
import Typechecker
import Types
import Data.Maybe
import Eval
------------------------------------------------------------
--------------- Prover-Typechecker Interface ---------------
------------------------------------------------------------

propositionToExps :: Proposition -> [Exp]
propositionToExps p = map snd $ deriveCompleteIDDFS (Sequent [] [] p) 2

propositionToExpsUnique :: Proposition -> [Exp]
propositionToExpsUnique = nub . propositionToExps

typeToExps :: Type -> [Exp]
typeToExps = propositionToExps . toProposition

headMaybe :: [a] -> Maybe a
headMaybe (x:_) = Just x
headMaybe []    = Nothing

unMaybe :: [Maybe a] -> [a]
unMaybe = map fromJust . filter isJust

typeToExp :: Type -> Maybe Exp
typeToExp = headMaybe . typeToExps

parseTypeToExp :: String -> Maybe Exp
parseTypeToExp str = result typeParser str >>= typeToExp

typeToExpsUnique :: Type -> [Exp]
typeToExpsUnique = propositionToExpsUnique . toProposition

typesToProve :: [String]
typesToProve = 
 [  
  "1 -> 1",
  "(A x B) -> ((T -> 1) -> A)",
  "A -> (B -> (B x A))",
  "A -> ((!(A -> B)) -> ((!(A -> C)) -> (B & C)))",
  "((A + B) + (C + D)) -> (A + (B + (C + D)))", 
  "A -> (B + A)",
  "A -> (A + B)", 
  "(A & B) -> A",
  "(A & B) -> B"
 ]
 {-[
  "A -> A", 
  "1",
  "T",
  "1 -> 1",
  "!1",
  "1 x 1",
  "(A x B) -> ((T -> 1) -> A)",
  "A -> (B -> (B (*) A))",
  "!(1x1)",
  "!(A -> A)",
  "(!A)->((!(A -> B)) -> (!B))",
  "(A + B) -> (((A -> C) & (B -> C)) -> C)",
  "((A x B) -> C) -> (A -> (B -> C))", 
  "A -> (A + B)", 
  "A -> ((!(A -> B)) -> ((!(A -> C)) -> (B & C)))",
  "(A & B) -> A",
  "(A & B) -> B",          
  "(A -> B) -> ((B -> C) -> (A -> C))",
  "(A x B) -> (B x A)",
  "A -> (A x 1)",
  "(!(1 -> A)) -> (!A)",                  
  "(T -> 1) -> ((A x B) -> A)",             
  "(A -> (B -> C)) -> ((A x B) -> C)",
  "0 -> (A -> (B -> (C -> D)))",
  "(T -> 1) -> (A -> (B -> (C -> A)))",
  "!(A & B) -> !(A x B)",
  "(A x (B + C)) -> ((A x B) + (A x C))",
  "(!(!A)) -> (!A)", 
  "(!A) -> (!(!A))",
  "((A x B) x C) ->  (A x (B x C))",
  "(A + (B + C)) -> ((A + B) + C)",
  "(A + (B + (C + D))) -> ((A + B) + (C + D))",
  "((A + B) + (C + D)) -> (A + (B + (C + D)))"
 ]-}

printExps :: [Exp] -> IO ()
printExps = mapM_ putStrLn . map showNumberedExp . zip [1..]
  where
    showNumberedExp :: (Int, Exp) -> String
    showNumberedExp (i, e) = "Expression " ++ show i ++ "\n" ++ show e ++ "\n"

printThings :: Show a => [a] -> IO ()
printThings = mapM_ putStrLn . map ((++ "\n") . show)

main :: IO()
main = printExps $ unMaybe $ map parseTypeToExp typesToProve

checks :: [Exp]
checks =  unMaybe $ map parseTypeToExp typesToProve

check2 :: [Maybe Exp]
check2 = map (\x -> result finalExpParser (show x)) $ unMaybe $ map parseTypeToExp typesToProve


------------------------------------------------------------
------------------ Adventure Game Example ------------------
------------------------------------------------------------

adventureProposition :: Proposition
adventureProposition = foldr Implies k [Bang s, Implies s h,
  Implies (Times l h) One, Implies s (Times l c), With p g,
  Implies c (Plus r e), With (Implies (Times r p) k) (Implies (Times e g) k)]
  where
    [s, h, l, c, k, p, g, r, e] = map Atom ["Shovel", "Hole", "Lava", "Chest",
      "Key", "Pink", "Green", "Ruby", "Emerald"]

adventureType :: Type
adventureType = toType adventureProposition

adventureExp :: Exp
adventureExp = head . map snd
             $ deriveComplete (Sequent [] [] adventureProposition) 2
