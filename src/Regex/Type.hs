{-
This module implements an efficient regular expression type.

Some aspects of note:

  1) Literals are represented as character sets ('CharSet') instead of just
     single characters ('Char'). This enables efficient and succinct
     representation of character classes (e.g., @[a-z]@ in POSIX syntax).
  
  2) Smart pattern synonyms ensure that 'Regex' instances are
     efficient-by-construction and uphold certain invariants, while still
     allowing natural deconstruction via pattern matching. The invariants are
     based on the standardisation rules from Kahrs and Runciman (2022).

References:

  * Kahrs, Stefan and Colin Runciman. 2022. "Simplifying Regular Expressions
    Further." Journal of Symbolic Computation 109 (2022): 124–143.
    https://doi.org/10.1016/j.jsc.2021.08.003

-}
module Regex.Type
  ( Regex(One,Lit)
  , pattern Zero
  , pattern AnyChar
  , pattern All
  , pattern Times
  , pattern Plus
  , pattern Star
  , pattern Opt
  , nullable
  , pretty
  ) where

import Data.List qualified as List
import Data.Semigroup (stimes)
import Data.Set qualified as Set
import Data.String
import Regex.CharSet (CharSet)
import Regex.CharSet qualified as CS

-------------------------------------------------------------------------------

-- | The 'Regex' type defines regular expressions over Unicode characters.
data Regex  
  = One           -- ^ identitity element (1), empty string (ε)
  | Lit CharSet   -- ^ set of literal symbols, character class
  
  -- internal constructors; use pattern synonyms below
  | Plus_ [Regex]
  | Times_ [Regex] 
  | Star_ Regex
  | Opt_ Regex

  deriving stock 
    ( Eq   -- ^ structural equivalence
    , Ord  -- ^ structural ordering
    )

-- | zero element (0), empty set (∅), bottom (⊥)
pattern Zero :: Regex
pattern Zero <- Lit (CS.null -> True) where
  Zero = Lit CS.empty

-- | set of all singleton words (Σ), class of all characters
pattern AnyChar :: Regex
pattern AnyChar <- Lit (CS.isFull -> True) where
  AnyChar = Lit CS.full

-- | set of all words (Σ*), top (⊤)
pattern All :: Regex
pattern All = Star AnyChar

-- | sequence (r₁ ⋅ r₂), concatenation (r₁ <> r₂)
--
-- Invariants:
--    1) Every sequence consists of at least two elements.
--    2) Sequences do not immediately contain other sequences.
--    3) Sequences do not immediately contain 'Zero' or 'One'.
--
pattern Times :: [Regex] -> Regex
pattern Times xs <- Times_ xs where
  Times xs | elem Zero xs' = Zero
           | null xs'      = One
           | [r] <- xs'    = r
           | otherwise     = Times_ xs'
   where
    xs' = concatMap flatTimes xs
    flatTimes = \case
      Times ys -> ys
      One      -> []
      y        -> [y]

-- | choice (r₁ + r₂), alternation (r₁ | r₂), join (r₁ ∨ r₂)
--
-- Invariants:
--    1) Every choice consists of at least two elements.
--    2) Choices do not immediately contain other choices.
--    3) Choices do not immediately contain 'Zero' or 'One' or 'Opt'.
--    4) Choices do not immediately contain more than one set of literals.
--    5) Choices do not contain duplicates.
--    6) Choices are ordered (via 'Ord').
--
pattern Plus :: [Regex] -> Regex
pattern Plus xs <- Plus_ xs where
  Plus xs | any nullable xs && not (any nullable xs') = Opt $ mkPlus xs'
          | otherwise                                 =       mkPlus xs'
   where
    xs' = Set.toAscList $ Set.fromList $ concatMap flatPlus xs
    flatPlus = \case
      Plus ys -> ys
      Zero    -> []
      One     -> []
      Opt y   -> flatPlus y
      y       -> [y]
    mkPlus = \case
      []  -> Zero
      [y] -> y
      (Lit a : Lit b : ys) -> mkPlus $ Lit (a <> b) : ys
      ys  -> Plus_ ys

-- | iteration, Kleene closure (r*)
--
-- Invariants:
--    1) Iterations do not immediately contain other iterations.
--    2) Iterations do not immediately contain 'Zero' or 'One' or 'Opt'.
--
pattern Star :: Regex -> Regex
pattern Star x <- Star_ x where
  Star Zero     = One
  Star One      = One
  Star (Star x) = Star_ x
  Star (Opt x)  = Star_ x
  Star x        = Star_ x

-- | option (r?)
--
-- Invariants:
--    1) Options do not immediately contain nullable expressions.
--    2) Options do not immediately contain 'Zero'
--
pattern Opt :: Regex -> Regex
pattern Opt x <- Opt_ x where
  Opt Zero           = One
  Opt x | nullable x = x
        | otherwise  = Opt_ x

{-# COMPLETE One, Lit, Plus, Times, Star, Opt #-}

-------------------------------------------------------------------------------

instance IsString Regex where
  fromString = Times . map (Lit . CS.singleton)

instance Semigroup Regex where
  Times xs <> Times ys = Times (xs ++ ys)
  Times xs <> r        = Times (xs ++ [r])
  r        <> Times xs = Times (r:xs)
  r1       <> r2       = Times [r1,r2]

  stimes 0 _ = One
  stimes 1 r = r
  stimes n r = foldr1 (<>) $ replicate (fromIntegral n) r

instance Monoid Regex where
  mempty = One

-------------------------------------------------------------------------------

-- | A regex is /nullable/ if it accepts the empty string.
nullable :: Regex -> Bool
nullable = \case
  One      -> True
  Lit _    -> False
  Plus rs  -> or $ map nullable rs
  Times rs -> and $ map nullable rs
  Star _   -> True
  Opt _    -> True

-------------------------------------------------------------------------------

instance Show Regex where 
  show = pretty

pretty :: Regex -> String
pretty = go (7 :: Int)
 where
  go p = \case
    Zero     -> "∅"
    One      -> "ε"
    Lit c    -> CS.pretty c
    Plus rs  -> parensIf (p >= 7) $ List.intercalate " + " $ map (go 7) rs
    Times rs -> parensIf (p >= 8) $ mconcat $ map (go 8) rs
    Star r   -> parensIf (p >= 9) $ go 9 r <> "*" 
    Opt r    -> parensIf (p >= 9) $ go 9 r <> "?"
  
  parensIf True  s = "(" <> s <> ")"
  parensIf False s = s
