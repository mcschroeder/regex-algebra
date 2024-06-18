-- | An efficient implementation of Unicode character sets/classes, in
-- particular with respect to 'complement'.
--
-- This module is largely based on Edward Kmett's "charset" package
-- (https://hackage.haskell.org/package/charset), which unfortunately is too
-- slow for our use case (probably because it stores an extra set of head bytes
-- that need to be re-constructed anytime charsets are joined/meeted).
-- 
module Regex.CharSet
  ( CharSet(..)
  , empty
  , full
  , singleton
  , complement
  , union
  , unions
  , intersection
  , null
  , isFull
  , isSubsetOf
  , size
  , toList
  , fromList
  , member
  , choose
  , fromCharSet
  , intSetToCharList
  , pretty
  ) where

import Data.Foldable qualified
import Data.IntSet (IntSet)
import Data.IntSet qualified as I
import Data.List qualified as List
import Prelude hiding (null)

-------------------------------------------------------------------------------

-- | A set of Unicode characters.
data CharSet = CharSet !Bool !IntSet

instance Semigroup CharSet where (<>)   = union
instance Monoid    CharSet where mempty = empty

-- | Extensional equality; different internal representations of the same set of
-- characters will be seen as equal.
instance Eq CharSet where 
  a == b = a `isSubsetOf` b && b `isSubsetOf` a

-- | A linear extension of the subset partial order using lexicographic ordering.
instance Ord CharSet where
  a <= b | a `isSubsetOf` b = True
         | b `isSubsetOf` a = False
         | otherwise        = toList a <= toList b  

-------------------------------------------------------------------------------

instance Show CharSet where
  show = pretty

pretty :: CharSet -> String
pretty = \case
  CharSet True  s -> case intSetToCharList s of
    []  -> "∅"
    [x] -> [x]
    xs  -> prettySet xs
  CharSet False s -> case intSetToCharList s of
    []  -> "Σ"
    [x] -> "(Σ∖" <> [x] <> ")" 
    xs  -> "(Σ∖" <> prettySet xs <> ")"
 where
  prettySet xs = "{" <> List.intercalate "," (map pure xs) <> "}"

-------------------------------------------------------------------------------

-- | The empty character set (∅).
empty :: CharSet
empty = CharSet True mempty

-- | The set of all characters (Σ).
full :: CharSet
full = CharSet False mempty

-- | A set consisting of a single character.
singleton :: Char -> CharSet
singleton = CharSet True . I.singleton . fromEnum

-- | The complement of a character set.
complement :: CharSet -> CharSet
complement (CharSet b xs) = CharSet (not b) xs

-- | The union of two character sets.
union :: CharSet -> CharSet -> CharSet
union (CharSet True  xs) (CharSet True  ys) = CharSet True  (I.union        xs ys)
union (CharSet False xs) (CharSet False ys) = CharSet False (I.intersection xs ys)
union (CharSet True  xs) (CharSet False ys) = CharSet False (I.difference   ys xs)
union (CharSet False xs) (CharSet True  ys) = CharSet False (I.difference   xs ys)

-- | The union of the character sets in a foldable structure.
unions :: Foldable f => f CharSet -> CharSet
unions = Data.Foldable.foldl' union empty

-- | The intersection of two character sets.
intersection :: CharSet -> CharSet -> CharSet
intersection (CharSet True  xs) (CharSet True  ys) = CharSet True  (I.intersection xs ys)
intersection (CharSet False xs) (CharSet False ys) = CharSet False (I.union        xs ys)
intersection (CharSet True  xs) (CharSet False ys) = CharSet True  (I.difference   xs ys)
intersection (CharSet False xs) (CharSet True  ys) = CharSet True  (I.difference   ys xs)

-- | Whether the set is empty.
null :: CharSet -> Bool
null (CharSet True  xs) = I.null xs
null (CharSet False xs) = fromEnum @Char maxBound + 1 == I.size xs

-- | Whether the set is full.
isFull :: CharSet -> Bool
isFull (CharSet True  xs) = fromEnum @Char maxBound + 1 == I.size xs
isFull (CharSet False xs) = I.null xs

isSubsetOf :: CharSet -> CharSet -> Bool
isSubsetOf (CharSet True  xs) (CharSet True  ys) = I.isSubsetOf xs ys
isSubsetOf (CharSet False xs) (CharSet False ys) = I.isSubsetOf ys xs
isSubsetOf (CharSet True  xs) (CharSet False ys) = I.null $ I.intersection xs ys
isSubsetOf (CharSet False xs) (CharSet True  ys) = 
  -- all (\c -> I.member c xs || I.member c ys) [0 .. fromEnum $ maxBound @Char]
  fromEnum @Char maxBound + 1 == I.size (I.union xs ys)

-- | The number of characters in the set.
size :: CharSet -> Int
size (CharSet True  cs) = I.size cs
size (CharSet False cs) = fromEnum @Char maxBound + 1 - I.size cs

-- | The characters in the set, in lexicographic order.
toList :: CharSet -> [Char]
toList (CharSet True  cs) = intSetToCharList cs
toList (CharSet False cs) = 
  filter (\x -> fromEnum x `I.notMember` cs) $ enumFromTo minBound maxBound

fromList :: [Char] -> CharSet
fromList = CharSet True . charListToIntSet

-- | Whether a given character is in the set.
member :: Char -> CharSet -> Bool
member c (CharSet True  cs) = I.member    (fromEnum @Char c) cs
member c (CharSet False cs) = I.notMember (fromEnum @Char c) cs

-- | Choose a random character from the set, or 'Nothing' if it is empty.
choose :: CharSet -> Maybe Char
choose cs = case toList cs of
  []  -> Nothing
  x:_ -> Just x

-------------------------------------------------------------------------------

fromCharSet :: CharSet -> (Bool, IntSet)
fromCharSet (CharSet b xs) = (b,xs)

intSetToCharList :: IntSet -> [Char]
intSetToCharList = map (toEnum @Char) . I.toAscList

charListToIntSet :: [Char] -> IntSet
charListToIntSet = I.fromList . map (fromEnum @Char)
