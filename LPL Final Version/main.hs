{-# OPTIONS -Wall -fwarn-tabs #-}

{- Adam Freilich
CIS 670 Final Project
4.28.14 Final Version -}

module Main where

import Eval
import Types
import Typechecker
import Parser
import Data.Maybe

main :: IO()
main = main' []

main' :: [(String, Exp)] -> IO()
main' exps = do
             x <- putStrLn "Add expressions? (or quit?)" >> getLine
             if      x == "Y" then do 
                                   y  <- getExpr exps
                                   main' (y : exps)
             else if x == "N" then evalMode exps
             else if x == "Q" then putStr "" 
             else (putStrLn "Y/N/Q?" >>  main' exps)

getExpr :: [(String, Exp)] -> IO((String, Exp))
getExpr exps = do 
  x <- putStrLn "Please put in an expression:" >> getLine
  if isJust $ result (expParser $ nameParser exps) x >>= typeCheck
  then do 
    y <- putStrLn "The expression has type" >> 
         (print $ fromJust $ (result (expParser $ nameParser exps) x) >>= typeCheck) >>
         putStrLn "Is this ok?" >> getLine
    if y == "Y" then do 
       name <- putStrLn "What should we call this expression?" >> getLine
       return (name, fromJust $ result (expParser $ nameParser exps) x)
    else if y == "N" then getExpr exps
    else putStrLn "Answer unrecognized, interpreted as N" >> getExpr exps
  else putStrLn "Expression didn't parse/typecheck, try again." >> getExpr exps

evalMode :: [(String, Exp)] -> IO()
evalMode exps = (do
       x  <- putStrLn "Defined expressions:" >> putStr (print' exps) >> 
             putStrLn "Enter expression to evaluate" >> getLine
       if isJust $ result (expParser $ nameParser exps) x  >>= typeCheck
       then print $ fromJust $ result (expParser $ nameParser exps) x >>= eval
       else putStrLn "Something went wrong, try again")
       >> main' exps

print' :: Show a => [a] -> String
print' (x:xs) = show x ++ "\n" ++ print' xs
print' []     = ""