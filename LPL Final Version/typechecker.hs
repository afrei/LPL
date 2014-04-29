{-# OPTIONS -Wall -fwarn-tabs #-}

{- Adam Freilich
CIS 670 Final Project
4.28.14 Final Version -}

module Typechecker where

import Types
import Data.List

data Context = C ([PerVar], [LinVar])
               deriving (Eq, Show)

persistent :: Context -> Context
persistent (C(pvs, _)) = C(pvs, [])

linearVars :: Context -> [LinVar]
linearVars (C(_, lvs)) = lvs

typeCheck :: Exp -> Maybe Type
typeCheck = flip (>>=) getCheckedType . checkWith emptyContext

emptyContext :: Context
emptyContext = C ([], [])

getCheckedType :: (Type, Context) -> Maybe Type
getCheckedType (t, ctxt) = if (linearVars ctxt) == [] 
                           then Just t 
                           else Nothing

linDel :: LinVar -> Context -> Maybe Context
linDel lv (C(pvs, lvs)) = if (lv `elem` lvs) 
                        then Just $ C(pvs, delete lv lvs)
                        else Nothing

delLinVars :: [LinVar] -> Context -> Maybe Context
delLinVars lvs ctxt =  foldr (flip (>>=)) (Just ctxt) (map linDel lvs)

perCont :: PerVar -> Context -> Bool
perCont pv (C(pvs, _)) = pv `elem` pvs

addLin :: LinVar -> Context -> Context
addLin lv (C(pvs, lvs)) = C(pvs, lv:lvs)

addPer :: PerVar -> Context -> Context
addPer pv (C(pvs, lvs)) = C(pv:pvs, lvs)

-- This begins the checkWith function. It derives a type
-- and uses the given context and passes on the remainder.
-- This remainder enables us to deterministically divide
-- The linear context. 

checkWith :: Context -> Exp -> Maybe (Type, Context)
checkWith ctxt (TopE lvs)  = do
 ctxt' <- delLinVars lvs ctxt
 return $ (TopT, ctxt')

checkWith ctxt UnitE = Just (OneT, ctxt)

checkWith ctxt (LinVarE x) = do 
 ctxt' <- linDel x ctxt
 return (getLType x, ctxt')

checkWith ctxt (PerVarE x) = if perCont x ctxt 
                             then Just (getPType x, ctxt) 
                             else Nothing

checkWith ctxt (AbortE e t lvs) = do
 (t1, ctxt1) <-  checkWith ctxt e
 ctxt' <- delLinVars lvs ctxt1
 (t2, ctxt2) <- if (t1 == ZeroT)
                then Just (t, ctxt') 
                else Nothing
 return (t2, ctxt2)

checkWith ctxt (Inj1E e ty) = do 
 (t, ctxt') <- checkWith ctxt e
 return (OplusT t ty , ctxt')

checkWith ctxt (Inj2E ty e) = do 
 (t, ctxt') <- checkWith ctxt e
 return (OplusT ty t, ctxt')

checkWith ctxt (Prj1E e) = do 
 (t, ctxt') <- checkWith ctxt e
 t' <- prj1 t
 return (t', ctxt')

checkWith ctxt (Prj2E e) = do 
 (t, ctxt') <- checkWith ctxt e
 t' <- prj2 t
 return (t', ctxt')

checkWith ctxt (BangE e) = do
 (t, _) <- checkWith (persistent ctxt) e
 return (BangT t, ctxt)

checkWith ctxt (WithE e1 e2) = do 
 (t1, ctxt1) <- checkWith ctxt e1
 (t2, ctxt2) <- checkWith ctxt e2
 ctxt' <- if ctxt1 == ctxt2
          then Just ctxt1
          else Nothing
 return (WithT t1 t2, ctxt')

checkWith ctxt (LetUE e1 e2) = do 
 (t1, ctxt1) <- checkWith ctxt e1
 (t2, ctxt2) <- if (t1 == OneT) 
                then checkWith ctxt1 e2
                else Nothing
 return (t2, ctxt2)

checkWith ctxt (TensE e1 e2) = do
 (t1, ctxt1) <- checkWith ctxt e1
 (t2, ctxt2) <- checkWith ctxt1 e2
 return (TensT t1 t2, ctxt2)

checkWith ctxt (LambdaE x e) = do
 (t1, ctxt1) <- checkWith (addLin x ctxt) e
 if  (x `elem` linearVars ctxt1) then Nothing
                                 else Just (LimpT (getLType x) (t1), ctxt1)

checkWith ctxt (AppE e1 e2) = do
 (t1, ctxt1) <- checkWith ctxt e1
 (t2, ctxt2) <- checkWith ctxt1 e2
 t3 <- appe t1 t2
 return (t3, ctxt2)

checkWith ctxt (LetBangE u e1 e2) = do
 (t1, ctxt1) <- checkWith ctxt e1
 (t2, ctxt2) <- if t1 == BangT (getPType u)
                then checkWith (addPer u ctxt1) e2
                else Nothing
 return (t2, ctxt2)

checkWith ctxt (LetTensE x1 x2 e1 e2) = do 
  (t1, ctxt1) <- checkWith ctxt e1
  (t2, ctxt2) <- if (t1 == TensT (getLType x1) (getLType x2))
                 then checkWith (addLin x1 $ addLin x2 $ ctxt1) e2
                 else Nothing
  if (x1 `elem` (linearVars ctxt2)) || 
     (x2 `elem` (linearVars ctxt2)) 
  then Nothing 
  else Just (t2, ctxt2)

checkWith ctxt (CaseE e x1 e1 x2 e2) = do 
  (t', ctxt') <- checkWith ctxt e
  (t1, ctxt1) <- checkWith (addLin x1 ctxt') e1
  (t2, ctxt2) <- checkWith (addLin x2 ctxt') e2
  t3          <- if t1 == t2 
                    && t' == OplusT (getLType x1) (getLType x2)
                    && ctxt1 == ctxt2
                    && not (x1 `elem` (linearVars ctxt1))
                    && not (x2 `elem` (linearVars ctxt2))
                 then Just t1
                 else Nothing
  return (t3, ctxt1)