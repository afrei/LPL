{-# OPTIONS -Wall -fwarn-tabs #-}

{- Adam Freilich
CIS 670 Final Project
4.28.14 Final Version -}

module Eval where

import Types
import Control.Applicative
import Data.List

-- eval reduces until it no longer can
eval :: Exp -> Maybe Exp
eval = limit ((=<<) reduce) . Just
     where limit f x = if (x == f x) then x else limit f (f x)

linSub :: Exp -> LinVar -> Exp -> Maybe Exp
linSub e1 x e2 = linSub' (cleanNames e1 e2) x e2

perSub :: Exp -> PerVar -> Exp -> Exp
perSub e1 x e2 = perSub' (cleanNames e1 e2) x e2

-- Takes exprsions a b and returns a' with names distinct from those in b
cleanNames :: Exp -> Exp -> Exp
cleanNames a b = incNames a (maxName b + 1)

maxName :: Exp -> Integer
maxName (LinVarE x)            = getLName x
maxName (PerVarE v)            = getPName v
maxName (AbortE e1 _ lvs)      = maximum (maxName e1 : map getLName lvs)
maxName (Inj1E e1 _)           = maxName e1
maxName (Inj2E _ e1)           = maxName e1
maxName (CaseE e' x1 e1 x2 e2) = maximum [maxName e', getLName x1, maxName e1,
                                                      getLName x2, maxName e2]
maxName (TopE lvs)             = maximum (map getLName lvs)
maxName (WithE e1 e2)          = max (maxName e1) (maxName e2)
maxName (Prj1E e1)             = maxName e1
maxName (Prj2E e1)             = maxName e1
maxName (UnitE)                = 0
maxName (LetUE e1 e2)          = max (maxName e1) (maxName e2)
maxName (TensE e1 e2)          = max (maxName e1) (maxName e2)
maxName (LetTensE x1 x2 e1 e2) = maximum [getLName x1, maxName e1, 
                                          getLName x2, maxName e2] 
maxName (LambdaE x e')         = max (getLName x) (maxName e')
maxName (AppE e1 e2)           = max (maxName e1) (maxName e2)
maxName (BangE e1)             = maxName e1
maxName (LetBangE v e1 e2)     = maximum [getPName v, maxName e1, maxName e2]

-- incNames increments all of the integer names given to linear/persistent
-- variables by the same given integer n
incNames :: Exp -> Integer -> Exp
incNames (LinVarE x) n             = LinVarE  (incLVar x n)
incNames (PerVarE v) n             = PerVarE  (incPVar v n)
incNames (AbortE e1 ty lvs) n      = AbortE   (incNames e1 n) ty 
                                              (map (flip incLVar n) lvs)
incNames (Inj1E e1 ty) n           = Inj1E    (incNames e1 n) ty
incNames (Inj2E ty e1) n           = Inj2E    ty (incNames e1 n)
incNames (CaseE e' x1 e1 x2 e2) n  = CaseE    (incNames e' n) 
                                              (incLVar x1 n) (incNames e1 n) 
                                              (incLVar x2 n) (incNames e2 n)
incNames (TopE lvs ) n             = TopE     (map (flip incLVar n) lvs)
incNames (WithE e1 e2) n           = WithE    (incNames e1 n) (incNames e2 n)
incNames (Prj1E e1) n              = Prj1E    (incNames e1 n)
incNames (Prj2E e1) n              = Prj2E    (incNames e1 n)
incNames (UnitE) _                 = UnitE
incNames (LetUE e1 e2) n           = LetUE    (incNames e1 n) (incNames e2 n)
incNames (TensE e1 e2) n           = TensE    (incNames e1 n) (incNames e2 n)
incNames (LetTensE x1 x2 e1 e2) n  = LetTensE (incLVar x1 n)  (incLVar x2 n) 
                                              (incNames e1 n) (incNames e2 n)
incNames (LambdaE x e') n          = LambdaE  (incLVar x n)   (incNames e' n)
incNames (AppE e1 e2) n            = AppE     (incNames e1 n) (incNames e2 n)
incNames (BangE e1) n              = BangE    (incNames e1 n)
incNames (LetBangE u e1 e2) n      = LetBangE (incPVar u n)   (incNames e1 n) 
                                                              (incNames e2 n)

linSub' :: Exp -> LinVar -> Exp -> Maybe Exp
linSub' e x (LinVarE v)            = if x == v then Just e else Nothing
linSub' _ _ (PerVarE _)            = Nothing
linSub' e x (AbortE e1 t1 lvs)     = (do
                                       e1' <- linSub' e x e1
                                       return $ AbortE e1' t1 lvs) <|>
                                     (if x `elem` lvs
                                      then Just $ AbortE e1 t1 (delete x lvs)
                                      else Nothing)
linSub' e x (Inj1E e1 ty)          =  do 
                                       e1' <- (linSub' e x e1) 
                                       return $ Inj1E e1' ty
linSub' e x (Inj2E ty e1)          =  do 
                                       e1' <- (linSub' e x e1) 
                                       return $ Inj2E ty e1'
linSub' e x (CaseE e0 y1 e1 y2 e2) = (do 
                                       e0' <- linSub' e x e0
                                       return $ CaseE e0' y1 e1 y2 e2) <|>
                                     (if x /= y1 && x /= y2 
                                      then do 
                                            e1' <- linSub' e x e1
                                            e2' <- linSub' e x e2
                                            return $ CaseE e0 y1 e1' y2 e2'
                                      else Nothing)
linSub' e x (WithE e1 e2)          =  do
                                       e1' <- (linSub' e x e1) 
                                       e2' <- (linSub' e x e2)
                                       return $ WithE e1' e2'
linSub' e x (Prj1E e1)             =  fmap Prj1E (linSub' e x e1) 
linSub' e x (Prj2E e1)             =  fmap Prj2E (linSub' e x e1) 
linSub' _ _ (UnitE)                =  Nothing
linSub' _ x (TopE lvs)             =  if x `elem` lvs 
                                      then Just $ TopE (delete x lvs)
                                      else Nothing  
linSub' e x (LetUE e1 e2)          = (do 
                                       e1' <- (linSub' e x e1)
                                       return $ LetUE e1' e2) <|> 
                                     (do 
                                       e2' <- (linSub' e x e2)
                                       return $ LetUE e1 e2')
linSub' e x (TensE e1 e2)          = (do
                                       e1' <- (linSub' e x e1)
                                       return $ TensE e1' e2) <|> 
                                     (do 
                                       e2' <- (linSub' e x e2)
                                       return $ TensE e1 e2')
linSub' e x (LetTensE v1 v2 e1 e2) = (do
                                       e1' <- (linSub' e x e1)
                                       return $ LetTensE v1 v2 e1' e2) <|> 
                                     (do 
                                       e2' <- (linSub' e x e2)
                                       return $ LetTensE v1 v2 e1 e2')
linSub' e x (LambdaE v e1)         =  do 
                                        e1' <- if x /= v 
                                               then linSub' e x e1
                                               else Nothing
                                        return $ LambdaE v e1'
linSub' e x (AppE e1 e2)           = (do
                                       e1' <- (linSub' e x e1)
                                       return $ AppE e1' e2) <|> 
                                     (do 
                                       e2' <- (linSub' e x e2)
                                       return $ AppE e1 e2')
linSub' _ _ (BangE _)              =  Nothing
linSub' e x (LetBangE v e1 e2)     = (do
                                       e1' <- (linSub' e x e1)
                                       return $ LetBangE v e1' e2) <|> 
                                     (do 
                                       e2' <- (linSub' e x e2)
                                       return $ LetBangE v e1 e2') 

perSub' :: Exp -> PerVar -> Exp -> Exp
perSub' _ _ (LinVarE x)            = LinVarE x
perSub' e u (PerVarE v)            = if u == v then e else PerVarE v
perSub' e u (AbortE e1 ty lvs)     = AbortE (perSub' e u e1) ty lvs
perSub' e u (Inj1E e1 ty)          = Inj1E (perSub' e u e1) ty
perSub' e u (Inj2E ty e1)          = Inj2E ty (perSub' e u e1)
perSub' e u (CaseE e' x1 e1 x2 e2) = CaseE (perSub' e u e') 
                                             x1 (perSub' e u e1) 
                                             x2 (perSub' e u e2)
perSub' _ _ (TopE lvs)             = TopE lvs
perSub' e u (WithE e1 e2)          = WithE (perSub' e u e1) (perSub' e u e2)
perSub' e u (Prj1E e1)             = Prj1E (perSub' e u e1) 
perSub' e u (Prj2E e1)             = Prj2E (perSub' e u e1) 
perSub' _ _ (UnitE)                = UnitE
perSub' e u (LetUE e1 e2)          = LetUE (perSub' e u e1) (perSub' e u e2)
perSub' e u (TensE e1 e2)          = TensE (perSub' e u e1) (perSub' e u e2)
perSub' e u (LetTensE x1 x2 e1 e2) = LetTensE x1 x2 
                                        (perSub' e u e1) (perSub' e u e2)
perSub' e u (LambdaE x e')         = LambdaE x (perSub' e u e')
perSub' e u (AppE e1 e2)           = AppE (perSub' e u e1) (perSub' e u e2) 
perSub' e u (BangE e1)             = BangE (perSub' e u e1)
perSub' e u (LetBangE v e1 e2)     = if u /= v 
                                       then LetBangE v (perSub' e u e1) 
                                                       (perSub' e u e2)
                                       else LetBangE v e1 e2

-- Because it relies on linSubst, we can't just define it Exp -> Exp
-- The first cases are local reduction rules and the latter are 
-- context filling based.
reduce :: Exp -> Maybe Exp
reduce (CaseE (Inj1E x _) x1 e1 _ _)  = linSub x x1 e1
reduce (CaseE (Inj2E _ x) _ _ x2 e2)  = linSub x x2 e2
reduce (Prj1E (WithE e _))            = Just e
reduce (Prj2E (WithE _ e))            = Just e
reduce (LetUE UnitE e)                = Just e
reduce (LetTensE x y (TensE x1 y1) e) = linSub x1 x =<< linSub y1 y =<< Just e
reduce (AppE (LambdaE x e) x1)        = linSub x1 x e
reduce (LetBangE u (BangE e1) e2)     = Just $ perSub e1 u e2
reduce (Inj1E e ty)                   = do
                                         e' <- reduce e 
                                         return $ Inj1E e' ty
reduce (Inj2E ty e)                   = do
                                         e' <- reduce e 
                                         return $ Inj2E ty e'
reduce (CaseE e x1 e1 x2 e2)          = do
                                         e' <- reduce e 
                                         return $ CaseE e' x1 e1 x2 e2
reduce (WithE e1 e2)                  = do
                                         e1' <- reduce e1
                                         e2' <- reduce e2
                                         return $ WithE e1' e2'
reduce (Prj1E e)                      = fmap Prj1E (reduce e)
reduce (Prj2E e)                      = fmap Prj2E (reduce e)
reduce (LetUE e1 e2)                  = do
                                         e1' <- reduce e1
                                         e2' <- reduce e2
                                         return $ LetUE e1' e2'
reduce (TensE e1 e2)                  = do
                                         e1' <- reduce e1
                                         e2' <- reduce e2
                                         return $ TensE e1' e2'
reduce (AppE e1 e2)                   = do
                                         e1' <- reduce e1
                                         e2' <- reduce e2
                                         return $ AppE e1' e2'
reduce (LetBangE u e1 e2)             = do
                                         e1' <- reduce e1
                                         e2' <- reduce e2
                                         return $ LetBangE u e1' e2'
reduce (BangE e)                      = fmap BangE (reduce e)
reduce x                              = Just x