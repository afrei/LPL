{-# OPTIONS -Wall -fwarn-tabs #-}

{- Adam Freilich
CIS 670 Final Project
4.28.14 Final Version -}

module Types where
import Data.List

-- The inductive definitions for Type and Exp
-- Should correspond obviously to those of Prop and Proof terms

data Type = Atomic String
            | ZeroT            
            | OneT
            | TopT             
            | LimpT Type Type  
            | TensT Type Type  
            | BangT Type       
            | OplusT Type Type 
            | WithT Type Type  
              deriving Eq  

instance Show Type where 
    show (Atomic str)   = str
    show ZeroT          = "0"
    show OneT           = "1"
    show TopT           = "T"
    show (LimpT t1 t2)  =  show' t1 ++ " -> "  ++ show' t2
    show (TensT t1 t2)  =  show' t1 ++ " x " ++ show' t2
    show (BangT t)      = "!" ++ show' t
    show (OplusT t1 t2) =  show' t1 ++ " + " ++ show' t2
    show (WithT t1 t2)  =  show' t1 ++ " & "   ++ show' t2

show' :: Type -> String
show' (Atomic str)   = str
show' ZeroT          = "0"
show' OneT           = "1"
show' TopT           = "T"
show' (LimpT t1 t2)  =  "(" ++ show' t1 ++ " -> "  ++ show' t2 ++ ")"
show' (TensT t1 t2)  =  "(" ++ show' t1 ++ " x " ++ show' t2 ++ ")"
show' (BangT t)      =  "!" ++ show' t
show' (OplusT t1 t2) =  "(" ++ show' t1 ++ " + " ++ show' t2 ++ ")"
show' (WithT t1 t2)  =  "(" ++ show' t1 ++ " & "   ++ show' t2 ++ ")"

appe :: Type -> Type -> Maybe Type
appe (LimpT a b) c = if (a == c) then Just b else Nothing
appe _ _           = Nothing

inj1, inj2, prj1, prj2 :: Type -> Maybe Type
inj1 (TensT a _) = Just a
inj1 _           = Nothing

inj2 (TensT _ b) = Just b
inj2 _           = Nothing

prj1 (WithT a _) = Just a
prj1 _           = Nothing

prj2 (WithT _ b) = Just b
prj2 _           = Nothing

data LinVar =  LinVar Integer Type
               deriving Eq  

instance Show LinVar where
    show (LinVar n t) = "{x" ++ show n ++ " : " ++ show t ++"}"

getLType :: LinVar -> Type
getLType (LinVar _ ty) = ty

getLName :: LinVar -> Integer
getLName (LinVar n _) = n

incLVar :: LinVar -> Integer -> LinVar
incLVar (LinVar n ty) m = (LinVar (m+n) ty)

data PerVar =  PerVar Integer Type
               deriving Eq  

instance Show PerVar where
    show (PerVar n t) = "{u" ++ show n ++ " : " ++ show t ++ "}"

getPType :: PerVar -> Type
getPType (PerVar _ ty) = ty

getPName :: PerVar -> Integer
getPName (PerVar n _) = n

incPVar :: PerVar -> Integer -> PerVar
incPVar (PerVar n ty) m = (PerVar (m+n) ty)

data Exp =  LinVarE LinVar
          | PerVarE PerVar
          | AbortE Exp Type [LinVar] -- We require a type of the abort exp and 
                                     -- a list of discarded variables for ease 
                                     -- of typechecking
          | Inj1E Exp Type
          | Inj2E Type Exp
          | CaseE Exp LinVar Exp LinVar Exp
          | TopE [LinVar]            -- We similarly require a list of vars 
          | WithE Exp Exp
          | Prj1E Exp
          | Prj2E Exp
          | UnitE
          | LetUE Exp Exp
          | TensE Exp Exp
          | LetTensE LinVar LinVar Exp Exp
          | LambdaE LinVar Exp
          | AppE Exp Exp
          | BangE Exp
          | LetBangE PerVar Exp Exp
            deriving Eq  

instance Show Exp where
   show (LinVarE x)           = show x
   show (PerVarE u)           = show u
   show (AbortE e t lvs)      = "abort " ++ show e ++ ": " ++ show t ++ 
                                " discarding:"      ++ 
                                (concat $ intersperse " " $ map show lvs)
   show (Inj1E e typ)         = "inj1 (" ++ show e ++ ") + " ++ show typ
   show (Inj2E typ e)         = "inj2 " ++ show typ ++ " + (" ++ show e ++ ")"
   show (CaseE e x1 e1 x2 e2) = "case " ++ show e ++ " of" ++ 
                                "\n| inj1 " ++ show x1 ++ ".(" ++ show e1 ++
                               ")\n| inj2 " ++ show x2 ++ ".(" ++ show e2 ++ ")"
   show (TopE lvs)            = "[] " ++ 
                                " discarding :"      ++ 
                                (concat $ intersperse " " $ map show lvs)
   show (WithE e1 e2)         = "[(" ++ show e1 ++ ") & (" ++ show e2 ++ ")]"
   show (Prj1E e)             = "prj1 (" ++ show e ++ ")"
   show (Prj2E e)             = "prj2 (" ++ show e ++ ")"
   show UnitE                 = "<>"
   show (LetUE e1 e2)         = "let <> = (" ++ show e1 ++ ") in" ++ 
                                "\n(" ++ show e2 ++ ")"
   show (TensE e1 e2)         = "<" ++ show e1 ++ " x " ++ show e2 ++ ">"
   show (LetTensE x y e1 e2)  = "let " ++ show x ++ " x " ++ show y ++ 
                                 " = (" ++ show e1  ++ ") in" ++ 
                                 "\n(" ++ show e2 ++ ")"
   show (LambdaE x e)         = "fun " ++ show x ++ ".\n(" ++ show e ++ ")"
   show (AppE e1 e2)          = "(" ++ show e1 ++ ") $ (" ++ show e2 ++")"
   show (BangE e)             = "!(" ++ show e ++ ")"
   show (LetBangE x e1 e2)    = "let !" ++ show x ++ " = (" ++ 
                                  show e1 ++ ") in\n(" ++ show e2 ++ ")"

-- This display function uses the indent function defined below and
-- produces a more readable version of an expression and is especially
-- useful when there are nested case statements, but doesn't always play
-- well with the parser. Therefore, I don't make it the show, but keep
-- it in since it is sometimes useful to have. 

display :: Exp -> String
display (LinVarE x)           = show x
display (PerVarE u)           = show u
display (AbortE e t lvs)      = "abort " ++ display e ++ ": " ++ show t ++ 
                                " discarding:"      ++ 
                                (concat $ intersperse " " $ map show lvs)
display (Inj1E e typ)         = "inj1 (" ++ display e ++ ") + " ++ show typ
display (Inj2E typ e)         = "inj2 " ++ show typ ++ " + (" 
                                        ++ display e ++ ")"
display (CaseE e x1 e1 x2 e2) = "case " ++ display e ++ " of" ++ (indent $
                                "\n| inj1 " ++ show x1 ++ ".(" ++ 
                                               display e1 ++
                               ")\n| inj2 " ++ show x2 ++ ".(" ++ 
                                               display e2 ++ ")")
display (TopE lvs)            = "[] " ++ 
                                " discarding :"      ++ 
                                (concat $ intersperse " " $ map show lvs)
display (WithE e1 e2)         = "[(" ++ display e1 ++ ") & (" 
                                     ++ display e2 ++ ")]"
display (Prj1E e)             = "prj1 (" ++ display e ++ ")"
display (Prj2E e)             = "prj2 (" ++ display e ++ ")"
display UnitE                 = "<>"
display (LetUE e1 e2)         = "let <> = (" ++ display e1 ++ ") in (" ++ 
                                (indent $ "\n(" ++ display e2) ++ ")"
display (TensE e1 e2)         = "<" ++ display e1 ++ " x " ++ display e2 ++ ">"
display (LetTensE x y e1 e2)  = "let " ++ show x ++ " x " ++ show y ++ 
                                " = (" ++ display e1  ++ ") in (" ++
                                (indent $ "\n(" ++ display e2) ++ ")"
display (LambdaE x e)         = "fun " ++ show x ++ ".(" ++ 
                                (indent $ "\n" ++ display e) ++ ")"
display (AppE e1 e2)          = "(" ++ display e1 ++ ") $ (" ++ display e2 ++")"
display (BangE e)             = "!(" ++ display e ++ ")"
display (LetBangE x e1 e2)    = "let !" ++ show x ++ " = (" ++ 
                                 display e1 ++ ") in (" ++ 
                                 (indent $ "\n" ++ display e2) ++ ")"

indent :: String -> String
indent = unlines . map ((++) "  ") . lines