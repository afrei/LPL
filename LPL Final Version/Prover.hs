{-# OPTIONS -Wall -fwarn-tabs #-}

module Prover where

------------------------------------------------------------
------------------------- Imports --------------------------
------------------------------------------------------------

import Control.Monad (guard)
import Data.Maybe (catMaybes)

import Core
import Zippers

import Types

------------------------------------------------------------
-------------------- Proof Derivations ---------------------
------------------------------------------------------------

-- Definition of proof derivations

-- General format:
--   (Left)  Rule Index Evidence1 ... EvidenceN OriginalSequent UpdatedSequent
--   (Right) Rule       Evidence1 ... EvidenceN OriginalSequent UpdatedSequent

-- Note that all of the left rules are indexed to refer to a specific
-- proposition in the context. This information is used for proof verification.
-- Additionally, the updated sequent reflects which linear hypotheses were used,
-- or is omitted if the linear context remains the same.

data Derivation
  = Hyp      Int                       Sequent Sequent
  | CopyL    Int Derivation            Sequent Sequent
  | TimesL   Int Derivation            Sequent Sequent
  | TimesR       Derivation Derivation Sequent Sequent
  | OneL     Int Derivation            Sequent Sequent
  | OneR                               Sequent
  | ImpliesL Int Derivation Derivation Sequent Sequent
  | ImpliesR     Derivation            Sequent Sequent
  | WithL1   Int Derivation            Sequent Sequent
  | WithL2   Int Derivation            Sequent Sequent
  | WithR        Derivation Derivation Sequent Sequent
  | TopR                               Sequent Sequent
  | PlusL    Int Derivation Derivation Sequent Sequent
  | PlusR1       Derivation            Sequent Sequent
  | PlusR2       Derivation            Sequent Sequent
  | ZeroL    Int                       Sequent Sequent
  | BangL    Int Derivation            Sequent Sequent
  | BangR        Derivation            Sequent
  deriving (Show)

-- Convenience functions for proof derivations

-- Extracts the original sequent from a proof derivation.
originalSequent :: Derivation -> Sequent
originalSequent (Hyp      _     sOriginal _) = sOriginal
originalSequent (CopyL    _ _   sOriginal _) = sOriginal
originalSequent (TimesL   _ _   sOriginal _) = sOriginal
originalSequent (TimesR     _ _ sOriginal _) = sOriginal
originalSequent (OneL     _ _   sOriginal _) = sOriginal
originalSequent (OneR           sOriginal  ) = sOriginal
originalSequent (ImpliesL _ _ _ sOriginal _) = sOriginal
originalSequent (ImpliesR   _   sOriginal _) = sOriginal
originalSequent (WithL1   _ _   sOriginal _) = sOriginal
originalSequent (WithL2   _ _   sOriginal _) = sOriginal
originalSequent (WithR      _ _ sOriginal _) = sOriginal
originalSequent (TopR           sOriginal _) = sOriginal
originalSequent (PlusL    _ _ _ sOriginal _) = sOriginal
originalSequent (PlusR1     _   sOriginal _) = sOriginal
originalSequent (PlusR2     _   sOriginal _) = sOriginal
originalSequent (ZeroL    _     sOriginal _) = sOriginal
originalSequent (BangL    _ _   sOriginal _) = sOriginal
originalSequent (BangR      _   sOriginal  ) = sOriginal

-- Extracts the updated sequent from a proof derivation, or the original sequent
-- if no changes were made to the linear context.
updatedSequent :: Derivation -> Sequent
updatedSequent (Hyp      _     _         sUpdated) = sUpdated
updatedSequent (CopyL    _ _   _         sUpdated) = sUpdated
updatedSequent (TimesL   _ _   _         sUpdated) = sUpdated
updatedSequent (TimesR     _ _ _         sUpdated) = sUpdated
updatedSequent (OneL     _ _   _         sUpdated) = sUpdated
updatedSequent (OneR           sOriginal         ) = sOriginal
updatedSequent (ImpliesL _ _ _ _         sUpdated) = sUpdated
updatedSequent (ImpliesR   _   _         sUpdated) = sUpdated
updatedSequent (WithL1   _ _   _         sUpdated) = sUpdated
updatedSequent (WithL2   _ _   _         sUpdated) = sUpdated
updatedSequent (WithR      _ _ _         sUpdated) = sUpdated
updatedSequent (TopR           _         sUpdated) = sUpdated
updatedSequent (PlusL    _ _ _ _         sUpdated) = sUpdated
updatedSequent (PlusR1     _   _         sUpdated) = sUpdated
updatedSequent (PlusR2     _   _         sUpdated) = sUpdated
updatedSequent (ZeroL    _     _         sUpdated) = sUpdated
updatedSequent (BangL    _ _   _         sUpdated) = sUpdated
updatedSequent (BangR      _   sOriginal         ) = sOriginal

-- Extracts the persistent context from a sequent.
getPContext :: Sequent -> PersistentContext
getPContext (Sequent pContext _ _) = pContext

-- Extracts the linear context from a sequent.
getLContext :: Sequent -> LinearContext
getLContext (Sequent _ lContext _) = lContext

-- Substitutes the given list of replacement propositions for the current
-- proposition in the context zipper, and returns the context as a list of
-- propositions. This is used when a specific proposition is modified as part of
-- a left inference rule.
updateContext :: [(Int, a)] -> [a] -> [(Int, a)] -> [a]
updateContext ls ps rs = zipperToList (Zipper (map snd ls) (ps ++ (map snd rs)))

-- Replaces the ith to (i + n)th elements of as with as'.
replaceWith :: [a] -> Int -> [a] -> Int -> [a]
replaceWith as i as' n = take i as ++ as' ++ drop (i + n) as

-- Functions for proof search

-- Convenience function which filters the results of derive, retaining only
-- complete proof derivations in which all linear hypotheses have been used.
deriveComplete :: Sequent -> Int -> [(Derivation, Exp)]
deriveComplete = filter (and . map isUsed . getLContext . updatedSequent . fst) `compose2` derive
  where compose2 = (.) . (.)

-- Convenience function which runs deriveComplete with successively larger
-- limits on the number of applications of the CopyL rule, up to the given
-- limit.
deriveCompleteIDDFS :: Sequent -> Int -> [(Derivation, Exp)]
deriveCompleteIDDFS s pLimit = deriveCompleteIDDFSHelper 0
  where
    deriveCompleteIDDFSHelper currentPLimit
      | currentPLimit == 0 || currentPLimit <= pLimit
      = let ds = deriveComplete s currentPLimit in
          case ds of
            [] -> deriveCompleteIDDFSHelper (currentPLimit + 1)
            _  -> ds
    deriveCompleteIDDFSHelper _ = []

-- Generates (possibly incomplete) proof derivations according to the above
-- inference rules, in which some of the linear hypotheses may not have been
-- used.
derive :: Sequent -> Int -> [(Derivation, Exp)]
derive s pLimit = map (\(d, _, e) -> (d, e)) $ deriveLimited s pLimit 0 1

-- Convenience function which runs deriveLimited, extracts the updated linear
-- context from each derivation, and returns tuples of derivations and their
-- associated updated linear contexts.
deriveAndGetLContext :: Sequent -> Int -> Int -> Integer -> [(Derivation, LinearContext, Integer, Exp)]
deriveAndGetLContext = map (\(d, nextId, e) -> (d, getLContext $ updatedSequent d, nextId, e)) `compose4` deriveLimited
  where compose2 = (.) . (.)
        compose3 = (.) . compose2
        compose4 = (.) . compose3

-- Attempts to derive the given sequent, using no more than pLimit hypotheses
-- from the persistent context.
deriveLimited :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveLimited s pLimit pUsed nextId =
  concatMap (\f -> f s pLimit pUsed nextId)
    [ deriveHyp
    , deriveCopyL
    , deriveBangL
    , deriveBangR
    , deriveTimesL
    , deriveTimesR
    , deriveOneL
    , deriveOneR
    , deriveImpliesL
    , deriveImpliesR
    , deriveWithL1
    , deriveWithL2
    , deriveWithR
    , deriveTopR
    , derivePlusL
    , derivePlusR1
    , derivePlusR2
    , deriveZeroL
    ]

deriveHyp :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveHyp s@(Sequent pContext lContext goal) _ _ nextId = do
  Zipper ls ((i, (Unused p, pExp)) : rs) <- indexedZippers lContext
  guard $ p == goal
  return (Hyp i s (Sequent pContext (updateContext ls [(Used p, pExp)] rs) goal), nextId, pExp)

deriveCopyL :: Sequent  -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveCopyL s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  guard $ pUsed < pLimit
  Zipper _ ((i, (p, pExp)) : _) <- indexedZippers pContext
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext ((Unused p, pExp) : lContext) goal) pLimit (pUsed + 1) nextId
  guard $ isUsed (head dLContext)
  return (CopyL i d s (Sequent pContext (tail dLContext) goal), dNextId, dExp)

deriveTimesL :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveTimesL s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused (Times p q), timesExp)) : rs) <- indexedZippers lContext
  let (pVar, qVar) = (LinVar nextId (toType p), LinVar (nextId + 1) (toType q))
  let (pExp, qExp) = (LinVarE pVar, LinVarE qVar)
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [(Unused p, pExp), (Unused q, qExp)] rs) goal) pLimit pUsed (nextId + 2)
  guard $ isUsed (dLContext !! i)
  guard $ isUsed (dLContext !! (i + 1))
  return (TimesL i d s (Sequent pContext (replaceWith dLContext i [(Used (Times p q), timesExp)] 2) goal), dNextId, LetTensE pVar qVar timesExp dExp)

deriveTimesR :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveTimesR s@(Sequent pContext lContext (Times p q)) pLimit pUsed nextId = do
  (d1, d1LContext, d1NextId, d1Exp) <- deriveAndGetLContext (Sequent pContext lContext p) pLimit pUsed nextId
  (d2, d2LContext, d2NextId, d2Exp) <- deriveAndGetLContext (Sequent pContext d1LContext q) pLimit pUsed d1NextId
  return (TimesR d1 d2 s (Sequent pContext d2LContext (Times p q)), d2NextId, TensE d1Exp d2Exp)
deriveTimesR _ _ _ _ = []

deriveOneL :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveOneL s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused One, oneExp)) : rs) <- indexedZippers lContext
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [] rs) goal) pLimit pUsed nextId
  return (OneL i d s (Sequent pContext (replaceWith dLContext i [(Used One, oneExp)] 0) goal), dNextId, LetUE oneExp dExp)

deriveOneR :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveOneR s@(Sequent _ _ One) _ _ nextId = do
  return (OneR s, nextId, UnitE)
deriveOneR _ _ _ _ = []

deriveImpliesL :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveImpliesL s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused (Implies p q), impliesExp)) : rs) <- indexedZippers lContext
  (d1, d1LContext, d1NextId, d1Exp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [] rs) p) pLimit pUsed nextId
  (d2, d2LContext, d2NextId, d2Exp) <- deriveAndGetLContext (Sequent pContext (replaceWith d1LContext i [(Unused q, AppE impliesExp d1Exp)] 0) goal) pLimit pUsed d1NextId
  guard $ isUsed (d2LContext !! i)
  return (ImpliesL i d1 d2 s (Sequent pContext (replaceWith d2LContext i [(Used (Implies p q), impliesExp)] 1) goal), d2NextId, d2Exp)

deriveImpliesR :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveImpliesR s@(Sequent pContext lContext (Implies p q)) pLimit pUsed nextId = do
  let pVar = LinVar nextId (toType p)
  let pExp = LinVarE pVar
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext (lContext ++ [(Unused p, pExp)]) q) pLimit pUsed (nextId + 1)
  guard $ isUsed (last dLContext)
  return (ImpliesR d s (Sequent pContext (init dLContext) (Implies p q)), dNextId, LambdaE pVar dExp)
deriveImpliesR _ _ _ _ = []

deriveWithL1 :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveWithL1 s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused (With p q), withExp)) : rs) <- indexedZippers lContext
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [(Unused p, Prj1E withExp)] rs) goal) pLimit pUsed nextId
  guard $ isUsed (dLContext !! i)
  return (WithL1 i d s (Sequent pContext (replaceWith dLContext i [(Used (With p q), withExp)] 1) goal), dNextId, dExp)

deriveWithL2 :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveWithL2 s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused (With p q), withExp)) : rs) <- indexedZippers lContext
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [(Unused q, Prj2E withExp)] rs) goal) pLimit pUsed nextId
  guard $ isUsed (dLContext !! i)
  return (WithL1 i d s (Sequent pContext (replaceWith dLContext i [(Used (With p q), withExp)] 1) goal), dNextId, dExp)

deriveWithR :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveWithR s@(Sequent pContext lContext (With p q)) pLimit pUsed nextId = do
  (d1, d1LContext, d1NextId, d1Exp) <- deriveAndGetLContext (Sequent pContext lContext p) pLimit pUsed nextId
  (d2, d2LContext, d2NextId, d2Exp) <- deriveAndGetLContext (Sequent pContext lContext q) pLimit pUsed d1NextId
  guard $ d1LContext == d2LContext
  return (WithR d1 d2 s (Sequent pContext d1LContext (With p q)), d2NextId, WithE d1Exp d2Exp)
deriveWithR _ _ _ _ = []

deriveTopR :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveTopR s@(Sequent pContext lContext Top) _ _ nextId = do
  updatedLContext <- mapM maybeConsume lContext
  let consumed = map (snd . snd) $ filter (uncurry (/=)) (zip lContext updatedLContext)
  return (TopR s (Sequent pContext updatedLContext Top), nextId, TopE (catMaybes $ map getLinVar consumed))
  where
    maybeConsume (Used   p, pExp) = [(Used p, pExp)]
    maybeConsume (Unused p, pExp) = [(Unused p, pExp), (Used p, pExp)]
    getLinVar (LinVarE linVar) = Just linVar
    getLinVar _                = Nothing
deriveTopR _ _ _ _ = []

derivePlusL :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
derivePlusL s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused (Plus p q), plusExp)) : rs) <- indexedZippers lContext
  let pVar = LinVar nextId (toType p)
  let pExp = LinVarE pVar
  (d1, d1LContext, d1NextId, d1Exp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [(Unused p, pExp)] rs) goal) pLimit pUsed (nextId + 1)
  let qVar = LinVar d1NextId (toType q)
  let qExp = LinVarE qVar
  (d2, d2LContext, d2NextId, d2Exp) <- deriveAndGetLContext (Sequent pContext (updateContext ls [(Unused q, qExp)] rs) goal) pLimit pUsed (d1NextId + 1)
  guard $ replaceWith d1LContext i [] 1 == replaceWith d2LContext i [] 1
  guard $ isUsed (d1LContext !! i)
  guard $ isUsed (d2LContext !! i)
  return (PlusL i d1 d2 s (Sequent pContext (replaceWith d1LContext i [(Used (Plus p q), plusExp)] 1) goal), d2NextId, CaseE plusExp pVar d1Exp qVar d2Exp)

derivePlusR1 :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
derivePlusR1 s@(Sequent pContext lContext (Plus p q)) pLimit pUsed nextId = do
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext lContext p) pLimit pUsed nextId
  return (PlusR1 d s (Sequent pContext dLContext (Plus p q)), dNextId, Inj1E dExp (toType q))
derivePlusR1 _ _ _ _ = []

derivePlusR2 :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
derivePlusR2 s@(Sequent pContext lContext (Plus p q)) pLimit pUsed nextId = do
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext lContext q) pLimit pUsed nextId
  return (PlusR2 d s (Sequent pContext dLContext (Plus p q)), dNextId, Inj2E (toType p) dExp)
derivePlusR2 _ _ _ _ = []

deriveZeroL :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveZeroL s@(Sequent pContext lContext goal) _ _ nextId = do
  Zipper ls ((i, (Unused Zero, zeroExp)) : rs) <- indexedZippers lContext
  updatedLContext <- mapM maybeConsume (updateContext ls [(Used Zero, zeroExp)] rs)
  let consumed = map (snd . snd) $ filter (uncurry (/=)) (zip (replaceWith lContext i [] 1) (replaceWith updatedLContext i [] 1))
  return (ZeroL i s (Sequent pContext updatedLContext goal), nextId, AbortE zeroExp (toType goal) (catMaybes $ map getLinVar consumed))
  where
    maybeConsume (Used   p, pExp) = [(Used p, pExp)]
    maybeConsume (Unused p, pExp) = [(Unused p, pExp), (Used p, pExp)]
    getLinVar (LinVarE linVar) = Just linVar
    getLinVar _                = Nothing

deriveBangL :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveBangL s@(Sequent pContext lContext goal) pLimit pUsed nextId = do
  Zipper ls ((i, (Unused (Bang p), bangExp)) : rs) <- indexedZippers lContext
  let pVar = PerVar nextId (toType p)
  let pExp = PerVarE pVar
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent (pContext ++ [(p, pExp)]) (updateContext ls [] rs) goal) pLimit pUsed (nextId + 1)
  return (BangL i d s (Sequent pContext (replaceWith dLContext i [(Used (Bang p), bangExp)] 0) goal), dNextId, LetBangE pVar bangExp dExp)

deriveBangR :: Sequent -> Int -> Int -> Integer -> [(Derivation, Integer, Exp)]
deriveBangR s@(Sequent pContext lContext (Bang p)) pLimit pUsed nextId = do
  (d, dLContext, dNextId, dExp) <- deriveAndGetLContext (Sequent pContext lContext p) pLimit pUsed nextId
  guard $ lContext == dLContext
  return (BangR d s, dNextId, BangE dExp)
deriveBangR _ _ _ _ = []
