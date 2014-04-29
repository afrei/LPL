{-# OPTIONS -Wall -fwarn-tabs #-}

module Zippers where

------------------------------------------------------------
------------------------- Imports --------------------------
------------------------------------------------------------

import Data.Maybe (isJust, fromJust)

------------------------------------------------------------
------------------------- Zippers --------------------------
------------------------------------------------------------

-- Definition of zippers (inspired by http://hackage.haskell.org/package/ListZipper-1.1.1.0/docs/src/Data-List-Zipper.html)

-- Zippers provide linear-time traversal through lists while allowing for
-- constant-time access to intermediate elements.

-- The ith zipper of a list consists of two sublists: the reverse of the first
-- i elements of the list, and the remaining (n-i) elements in the list. With
-- this structure, constant-time access is available for the ith element, and
-- the (i-1)th or (i+1)th zipper can be generated in constant time as well.

data Zipper a = Zipper [a] [a]
  deriving (Eq, Show)

-- Convenience functions for zippers

-- Returns the first zipper of a list.
zipperFromList :: [a] -> Zipper a
zipperFromList = Zipper []

-- Converts a zipper into a list.
zipperToList :: Zipper a -> [a]
zipperToList (Zipper ls rs) = reverse ls ++ rs

-- Returns Just the next zipper of a list, or Nothing if no zippers remain.
zipperRight :: Zipper a -> Maybe (Zipper a)
zipperRight (Zipper _  []      ) = Nothing
zipperRight (Zipper ls (a : rs)) = Just (Zipper (a : ls) rs)

-- Returns all zippers of a list, in order.
zippers :: [a] -> [Zipper a]
zippers = map fromJust
        . takeWhile isJust
        . iterate (>>= zipperRight)
        . Just . zipperFromList

-- Returns all zippers of a list, in order, with elements being paired with
-- their indices.
indexedZippers :: [a] -> [Zipper (Int, a)]
indexedZippers = zippers . zip [0..]
