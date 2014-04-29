{-# OPTIONS -Wall -fwarn-tabs #-}

module Core where

------------------------------------------------------------
------------------------- Imports --------------------------
------------------------------------------------------------

import Types

------------------------------------------------------------
--------------------- Core Definitions ---------------------
------------------------------------------------------------

-- Definition of propositions

data Proposition
  =    Atom String                         -- A
  |   Times Proposition Proposition | One  -- A x B | 1
  | Implies Proposition Proposition        -- A --o B
  |    With Proposition Proposition | Top  -- A & B | Top
  |    Plus Proposition Proposition | Zero -- A + B | 0
  |    Bang Proposition                    -- !A
  deriving (Eq, Show)

data LinearProposition = Used Proposition | Unused Proposition
  deriving (Eq, Show)

-- Convenience functions for propositions

-- Returns whether a linear proposition has been used during proof search.
isUsed :: (LinearProposition, Exp) -> Bool
isUsed (Used   _, _) = True
isUsed (Unused _, _) = False

-- Converts from Proposition to Type.
toType :: Proposition -> Type
toType (Atom s)      = Atomic s
toType One           = OneT
toType Top           = TopT
toType Zero          = ZeroT
toType (Times p q)   = TensT (toType p) (toType q)
toType (Implies p q) = LimpT (toType p) (toType q)
toType (With p q)    = WithT (toType p) (toType q)
toType (Plus p q)    = OplusT (toType p) (toType q)
toType (Bang p)      = BangT (toType p)

-- Converts from Type to Proposition.
toProposition :: Type -> Proposition
toProposition (Atomic s)   = Atom s
toProposition OneT         = One
toProposition TopT         = Top
toProposition ZeroT        = Zero
toProposition (TensT p q)  = Times (toProposition p) (toProposition q)
toProposition (LimpT p q)  = Implies (toProposition p) (toProposition q)
toProposition (WithT p q)  = With (toProposition p) (toProposition q)
toProposition (OplusT p q) = Plus (toProposition p) (toProposition q)
toProposition (BangT p)    = Bang (toProposition p)

-- Definition of sequents

-- The persistent context consists of a list of propositions, and their
-- associated expressions.
type PersistentContext = [(Proposition, Exp)]

-- The linear context consists of a list of linear propositions, and their
-- associated expressions.
type LinearContext = [(LinearProposition, Exp)]

-- A sequent consists of the persistent context, the linear context, and the
-- goal proposition. Hypotheses in the linear context are tagged with a data
-- constructor indicating whether they have been used. All linear propositions
-- are initially unused, and must all be used at the end of a valid proof.
data Sequent = Sequent PersistentContext LinearContext Proposition
  deriving (Eq, Show)
