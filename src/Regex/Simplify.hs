{-
This module implements regular expression simplifications based on the
transformations from Kahrs and Runcimcan (2022).

References:

  * Kahrs, Stefan and Colin Runciman. 2022. "Simplifying Regular Expressions
    Further." Journal of Symbolic Computation 109 (2022): 124–143.
    https://doi.org/10.1016/j.jsc.2021.08.003

-}
module Regex.Simplify (simplify) where

import Data.Function
import Data.List.Extra (partition, sortBy, uncons, splitAtEnd, breakEnd)
import Prelude
import Regex.CharSet (CharSet)
import Regex.CharSet qualified as CS
import Regex.Operations
import Regex.Type

-------------------------------------------------------------------------------

simplify :: Regex -> Regex
simplify = goFree
 where
  goFree r = case r of
    Plus  xs | r' <- factorPrefixes xs     , r' /= r -> goFree r'
             | r' <- factorSuffixes xs     , r' /= r -> goFree r'
             | r' <- liftChoices xs        , r' /= r -> goFree r'
             | r' <- lookupChoices xs      , r' /= r -> goFree r'
             | r' <- Plus (map goFree xs)  , r' /= r -> goFree r'
    Times xs | r' <- fuseSequence xs       , r' /= r -> goFree r'
             | r' <- liftSequence xs       , r' /= r -> goFree r'
             | r' <- pressSequence xs      , r' /= r -> goFree r'
             | r' <- lookupSequence xs     , r' /= r -> goFree r'
             | r' <- Times (map goFree xs) , r' /= r -> goFree r'
    Star  x  | r' <- Star (goStar x)       , r' /= r -> goFree r'    
    Opt   x  | r' <- lookupOpt x           , r' /= r -> goFree r' 
             | r' <- Opt (goOpt x)         , r' /= r -> goFree r'
    _                                                -> r  
  
  goOpt r = case r of
    Plus xs  | r' <- fuseOptChoices xs     , r' /= r -> goOpt r'
    Times xs | r' <- fuseOptSequence xs    , r' /= r -> goOpt r'             
    x                                                -> goFree x
  
  goStar r = case r of
    Plus  xs | r' <- fuseStarChoices xs    , r' /= r -> goStar r'
             | r' <- liftStarChoices xs    , r' /= r -> goStar r'
    Times xs | r' <- fuseStarSequence xs   , r' /= r -> goStar r'
    Lit   x                                          -> Lit x
    _        | r' <- liftStar r            , r' /= r -> goStar r'
    _                                                -> goOpt r

-------------------------------------------------------------------------------

-- | Apply the free fusion law on a sequence of regular expressions.
--
--    x* ⋅ x* = x* ⋅ x? = x? ⋅ x* = x*
--
fuseSequence :: [Regex] -> Regex
fuseSequence = Times . go
 where
  go (Star x1 : Star x2 : ys) | x1 == x2 = go (Star x1 : ys)
  go (Star x1 : Opt  x2 : ys) | x1 == x2 = go (Star x1 : ys)
  go (Opt  x1 : Star x2 : ys) | x1 == x2 = go (Star x1 : ys)
  go (y:ys) = y : go ys
  go [] = []

-- | Apply the starred fusion law on a sequence of regular expressions.
--
--    (x? ⋅ y?)* = (x + y)*
--
fuseStarSequence :: [Regex] -> Regex
fuseStarSequence xs
  | all nullable xs = Plus $ map flatNullable xs
  | otherwise       = Times xs

-- | Apply the starred fusion law on a list of choices.
--
--    (x + y?)* = (x + y*)* = (x + y)*
--
fuseStarChoices :: [Regex] -> Regex
fuseStarChoices = Plus . map flatNullable

flatNullable :: Regex -> Regex
flatNullable = \case
    Star r -> r
    Opt  r -> r
    r      -> r

-- | Apply fusion rules on an optional sequence of expression.
--
--    (xx*)? = (x*)?
--    (x*x)? = (x*)?
--
fuseOptSequence :: [Regex] -> Regex
fuseOptSequence = \case
  [x1, Star x2] | x1 == x2 -> Star x2
  [Star x1, x2] | x1 == x2 -> Star x1
  xs -> Times xs

-- | Apply fusion rules within an optional list of choices.
--
--    (x + yy*)? = (x + y*)?
--    (x + y*y)? = (x + y*)?
--
fuseOptChoices :: [Regex] -> Regex
fuseOptChoices xs = Plus $ map go xs
 where
  go (Times ys) = fuseOptSequence ys
  go y          = y

-------------------------------------------------------------------------------

-- | Factorize an ordered list of choices by pairwise application of the
-- left-distributive law and its special cases.
factorPrefixes :: [Regex] -> Regex
factorPrefixes xs = Plus $ go xs
 where
  go (x:y:zs) 
    | z <- factorPrefix      x y, size z < size (Plus [x,y]) =     go (z:zs)
    | z <- factorPrefixOpt   x y, size z < size (Plus [x,y]) =     go (z:zs)
    | z <- factorPrefixStar1 x y, size z < size (Plus [x,y]) =     go (z:zs)
    | z <- factorPrefixStar2 x y, size z < size (Plus [x,y]) =     go (z:zs)
    | otherwise                                              = x : go (y:zs)
  go [x]                                                     = [x]
  go []                                                      = []

-- | Factorize two choices using the left-distributive law.
--
--    a⋅x + a⋅y = a⋅(x+y)
--
factorPrefix :: Regex -> Regex -> Regex
factorPrefix r1 r2
  -----------------------------------------------------------------------
  | ax      <- flatTimes r1
  , ay      <- flatTimes r2
  , axy     <- splitPrefix ax ay
  , (a,x,y) <- map3 Times axy
  , a /= One                                  = a <> Plus [x,y]
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------

-- | Factorize two choices using a special case of the left-distributive law.
--
--    a?⋅x + a⋅y = x + a⋅(x+y)
--    a⋅x + a?⋅y = y + a⋅(x+y)
--
factorPrefixOpt :: Regex -> Regex -> Regex
factorPrefixOpt r1 r2
  -----------------------------------------------------------------------
  | Opt a1 : x1 <- flatTimes r1
  , ax          <- flatTimes a1 ++ x1
  , ay          <- flatTimes r2
  , axy         <- splitPrefix ax ay
  , (a,x,y)     <- map3 Times axy
  , a /= One
  , x /= One
  , size a + 1 >= size x                      = Plus [x, a <> Plus [x,y]]
  -----------------------------------------------------------------------
  | Opt a1 : y1 <- flatTimes r2
  , ay          <- flatTimes a1 ++ y1
  , ax          <- flatTimes r1
  , axy         <- splitPrefix ax ay
  , (a,x,y)     <- map3 Times axy
  , a /= One
  , y /= One
  , size a + 1 >= size y                      = Plus [y, a <> Plus [x,y]]
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------

-- | Factorize two choices using a special case of the left-distributive law.
--
--    a*⋅a⋅x + a⋅y = a⋅(a*⋅x + y)
--    a⋅x + a*⋅a⋅y = a⋅(x + a*⋅y)
--
factorPrefixStar1 :: Regex -> Regex -> Regex
factorPrefixStar1 r1 r2
  -----------------------------------------------------------------------
  | Star a1 : ax1 <- flatTimes r1
  , a2            <- flatTimes a1
  , (a3,x1)       <- splitAt (length a2) ax1
  , a2 == a3
  , ax            <- a3 ++ Star a1 : x1
  , ay            <- flatTimes r2
  , axy           <- splitPrefix ax ay
  , (a,x,y)       <- map3 Times axy
  , a /= One                                  = a <> Plus [x,y]
  -----------------------------------------------------------------------
  | Star a1 : ay1 <- flatTimes r2
  , a2            <- flatTimes a1
  , (a3,y1)       <- splitAt (length a2) ay1
  , a2 == a3
  , ay            <- a3 ++ Star a1 : y1
  , ax            <- flatTimes r1
  , axy           <- splitPrefix ax ay
  , (a,x,y)       <- map3 Times axy
  , a /= One                                  = a <> Plus [x,y]
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------

-- | Factorize two choices using a special case of the left-distributive law.
--
--    a⋅a*⋅x + a*⋅y = a*⋅(a⋅x + y)
--    a*⋅x + a⋅a*⋅y = a*⋅(x + a⋅y)
--
factorPrefixStar2 :: Regex -> Regex -> Regex
factorPrefixStar2 r1 r2
  -----------------------------------------------------------------------
  | ax1                <- flatTimes r1
  , (a1, Star a2 : x1) <- break isStar ax1
  , a1 == flatTimes a2
  , ax                 <- Star a2 : a1 ++ x1
  , ay                 <- flatTimes r2
  , axy                <- splitPrefix ax ay
  , (a,x,y)            <- map3 Times axy
  , a /= One                                  = a <> Plus [x,y]
  -----------------------------------------------------------------------
  | ay1                <- flatTimes r2
  , (a1, Star a2 : y1) <- break isStar ay1
  , a1 == flatTimes a2  
  , ay                 <- Star a2 : a1 ++ y1
  , ax                 <- flatTimes r2
  , axy                <- splitPrefix ax ay
  , (a,x,y)            <- map3 Times axy
  , a /= One                                  = a <> Plus [x,y]
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------

-------------------------------------------------------------------------------

-- | Factorize an ordered list of choices by pairwise application of the
-- right-distributive law and its special cases.
factorSuffixes :: [Regex] -> Regex
factorSuffixes xs = Plus $ go $ sortBy (compare `on` (reverse . flatTimes)) xs
 where
  go (x:y:zs)
    | z <- factorSuffix      x y, size z < size (Plus [x,y]) =     go (z:zs)
    | z <- factorSuffixOpt   x y, size z < size (Plus [x,y]) =     go (z:zs)
    | z <- factorSuffixStar1 x y, size z < size (Plus [x,y]) =     go (z:zs)
    | z <- factorSuffixStar2 x y, size z < size (Plus [x,y]) =     go (z:zs)
    | otherwise                                              = x : go (y:zs)
  go [x]                                                     = [x]
  go []                                                      = []

-- | Factorize two choices using the right-distributive law.
--
--    x⋅b + y⋅b = (x+y)⋅b
--
factorSuffix :: Regex -> Regex -> Regex
factorSuffix r1 r2
  -----------------------------------------------------------------------
  | xb      <- flatTimes r1
  , yb      <- flatTimes r2
  , xyb     <- splitSuffix xb yb
  , (x,y,b) <- map3 Times xyb
  , b /= One                                  = Plus [x,y] <> b
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------

-- | Factorize two choices using a special case of the right-distributive law.
--
--    x⋅b? + y⋅b = x + (x+y)⋅b
--    x⋅b + y⋅b? = y + (x+y)⋅b
--
factorSuffixOpt :: Regex -> Regex -> Regex
factorSuffixOpt r1 r2
  -----------------------------------------------------------------------
  | xb1               <- flatTimes r1
  , Just (x1, Opt b1) <- unsnoc xb1
  , xb                <- x1 ++ flatTimes b1
  , yb                <- flatTimes r2
  , xyb               <- splitSuffix xb yb
  , (x,y,b)           <- map3 Times xyb
  , b /= One
  , x /= One  
  , size b + 1 >= size x                      = Plus [x, Plus [x,y] <> b]
  -----------------------------------------------------------------------
  | yb1               <- flatTimes r2
  , Just (y1, Opt b1) <- unsnoc yb1
  , yb                <- y1 ++ flatTimes b1
  , xb                <- flatTimes r1
  , xyb               <- splitSuffix xb yb
  , (x,y,b)           <- map3 Times xyb
  , b /= One
  , y /= One
  , size b + 1 >= size y                      = Plus [y, Plus [x,y] <> b]
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------

-- | Factorize two choices using a special case of the right-distributive law.
--
--    x⋅b⋅b* + y⋅b = (x⋅b* + y)⋅b
--    x⋅b + y⋅b⋅b* = (x + y⋅b*)⋅b
--
factorSuffixStar1 :: Regex -> Regex -> Regex
factorSuffixStar1 r1 r2
  -----------------------------------------------------------------------
  | xb1                 <- flatTimes r1
  , Just (xb2, Star b1) <- unsnoc xb1
  , b2                  <- flatTimes b1
  , (x1,b3)             <- splitAtEnd (length b2) xb2
  , b2 == b3
  , xb                  <- x1 ++ Star b1 : b3
  , yb                  <- flatTimes r2
  , xyb                 <- splitSuffix xb yb
  , (x,y,b)             <- map3 Times xyb
  , b /= One                                  = Plus [x,y] <> b
  -----------------------------------------------------------------------
  | yb1                 <- flatTimes r2
  , Just (yb2, Star b1) <- unsnoc yb1
  , b2                  <- flatTimes b1
  , (y1,b3)             <- splitAtEnd (length b2) yb2
  , b2 == b3
  , yb                  <- y1 ++ Star b1 : b3
  , xb                  <- flatTimes r1
  , xyb                 <- splitSuffix xb yb
  , (x,y,b)             <- map3 Times xyb
  , b /= One                                  = Plus [x,y] <> b
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]
  -----------------------------------------------------------------------


-- | Factorize two choices using a special case of the right-distributive law.
--
--    x⋅b*⋅b + y⋅b* = (x⋅b + y)⋅b*
--    x⋅b* + y⋅b*⋅b = (x + y⋅b)⋅b*
--
factorSuffixStar2 :: Regex -> Regex -> Regex
factorSuffixStar2 r1 r2
  -----------------------------------------------------------------------
  | xb1                 <- flatTimes r1
  , (xb2, b1)           <- breakEnd isStar xb1
  , Just (x1, Star b2)  <- unsnoc xb2
  , b1 == flatTimes b2
  , xb                  <- x1 ++ b1 ++ [Star b2]
  , yb                  <- flatTimes r2
  , xyb                 <- splitSuffix xb yb
  , (x,y,b)             <- map3 Times xyb
  , b /= One                                  = Plus [x,y] <> b
  -----------------------------------------------------------------------
  | yb1                 <- flatTimes r2
  , (yb2, b1)           <- breakEnd isStar yb1
  , Just (y1, Star b2)  <- unsnoc yb2
  , b1 == flatTimes b2
  , yb                  <- y1 ++ b1 ++ [Star b2]
  , xb                  <- flatTimes r1
  , xyb                 <- splitSuffix xb yb
  , (x,y,b)             <- map3 Times xyb
  , b /= One                                  = Plus [x,y] <> b
  -----------------------------------------------------------------------
  | otherwise                                 = Plus [r1,r2]

-------------------------------------------------------------------------------

flatTimes :: Regex -> [Regex]
flatTimes = \case
  Times xs -> xs
  x        -> [x]

isStar :: Regex -> Bool
isStar (Star _) = True
isStar _        = False

-- | Split two lists at the longest common prefix.
--
-- >>> splitPrefix "mouse" "moose"
-- ("mo", "use", "ose")
--
splitPrefix :: Eq a => [a] -> [a] -> ([a], [a], [a])
splitPrefix = go []
 where
  go zs (x:xs) (y:ys) | x == y = go (x:zs) xs ys
  go zs xs ys = (reverse zs, xs, ys)

-- | Split two lists at the longest common suffix.
--
-- >>> splitSuffix "mouse" "moose"
-- ("mou", "moo", "se")
--
splitSuffix :: Eq a => [a] -> [a] -> ([a], [a], [a])
splitSuffix xs0 ys0 = go [] (reverse xs0) (reverse ys0)
 where
  go zs (x:xs) (y:ys) | x == y = go (x:zs) xs ys
  go zs xs ys = (reverse xs, reverse ys, zs)

-- TODO: replace by Data.List.unsnoc once we depend on base-4.19
unsnoc :: [a] -> Maybe ([a], a)
unsnoc xs = (\(hd, tl) -> (reverse tl, hd)) <$> uncons (reverse xs)

map3 :: (a -> b) -> (a,a,a) -> (b,b,b)
map3 f (x,y,z) = (f x, f y, f z)

-------------------------------------------------------------------------------

-- | Apply the basic lifting law to a starred expression.
--
--    x* = α̂₁(x)*  if α(x) = α₁(x)
--
liftStar :: Regex -> Regex
liftStar r | alpha r == a1 = Lit a1 where a1 = alpha1 r
liftStar r                 = r

-- | Apply the generalized lifting law on a starred list of choices.
--
--     (x + y)* = (α̂₁(x) + y)*  if α(x) ⊆ α₁(x + y)
--
liftStarChoices :: [Regex] -> Regex
liftStarChoices xs = case partition (\x -> alpha x `CS.isSubsetOf` a1) xs of
  ([], _ ) -> Plus xs
  (ys, zs) -> Plus $ map (Lit . alpha1) ys ++ zs
 where
  a1 = alpha1 (Plus xs)

-- | Apply lifting to adjacent subsequences.
--
--    x* ⋅ y? = x*  if α(y) ⊆ α₁(x)
--
liftSequence :: [Regex] -> Regex
liftSequence = Times . go
 where
  go (Star x : Star y : zs) | alpha y `CS.isSubsetOf` alpha1 x = go (Star x : zs)
  go (Star x : Opt  y : zs) | alpha y `CS.isSubsetOf` alpha1 x = go (Star x : zs)
  go (x:xs) = x : go xs
  go [] = []


-- | Apply lifting to subsume choices.
--
--    x* + y = x*  if α(y) ⊆ α₁(x)
  --
liftChoices :: [Regex] -> Regex
liftChoices = Plus . go
 where
  go (x:xs) = go1 x xs []
  go [] = []

  go1 (Star x) (y:ys) zs | alpha y `CS.isSubsetOf` alpha1 x = go1 (Star x) ys zs
  go1 x (Star y : ys) zs | alpha x `CS.isSubsetOf` alpha1 y = go (Star y : ys ++ zs)
  go1 x (y:ys) zs = go1 x ys (y:zs)
  go1 x [] zs = x : go zs

-------------------------------------------------------------------------------

-- | Replace self-star-equivalent nullable subsequences with starred choices.
--
--     x?⋅y? = (x + y)*  if L(x?⋅y?) = L ((x?⋅y?)*)
---
pressSequence :: [Regex] -> Regex
pressSequence = Times . go []
 where
  go ys (x:xs)
    | nullable x = go (x:ys) xs
    | otherwise  = tryPress (reverse ys) ++ x : go [] xs
  go ys []       = tryPress (reverse ys)

  tryPress []               = []
  tryPress [y]              = [y]
  tryPress ys
    | selfStarEq (Times ys) = [Star (Plus $ map flatNullable ys)]
    | otherwise             = ys

-- | Checks whether L(r) = L(r*).
selfStarEq :: Regex -> Bool
selfStarEq r = equivalence r (Star r)
-- TODO: can we somehow exploit this special case of equivalence checking?

-------------------------------------------------------------------------------

-- | Apply known syntactic replacements of sequences.
--
--     (1)  x* ⋅ y ⋅ (x* ⋅ y)* = (x + y)* ⋅ y
--
lookupSequence :: [Regex] -> Regex
lookupSequence = Times . go
 where
  go (Star x1 : y1 : Star (Times [Star x2, y2]) : zs)  -- (1)
    | x1 == x2, y1 == y2 
    = go $ Star (Plus [x1,y1]) <> y1 : zs
  
  go (y:ys) = y : go ys
  go [] = []

-- | Apply known syntactic replacements of choices.
-- 
--     (1)  x⋅Σ* + x* = (x⋅Σ*)?
--     (2)  [ab] + ab = a?b?
--
lookupChoices :: [Regex] -> Regex
lookupChoices = (Plus .) $ go $ \case
  (Times [x1, All], Star x2) | x1 == x2 -> Just $ Opt (Times [x1, All])  -- (1)
  (Lit cs, Times [Lit a, Lit b]) 
    | cs == CS.union a b -> Just $ Opt (Lit a) <> Opt (Lit b) -- (2)
  _ -> Nothing 
 where
  go _ []     = []
  go f (x:xs) = go1 xs []
   where
    go1 []     zs                      = x : go f zs
    go1 (y:ys) zs | Just x' <- f (x,y) = go f (x' : ys ++ zs)
    go1 (y:ys) zs                      = go1 ys (y:zs)

-- | Apply known syntactic replacements of optionals.
--
--    (1)  (x + x?y)? = x?y?
--    (2)  (y + xy?)? = x?y?
--
lookupOpt :: Regex -> Regex
lookupOpt = \case
  Plus [x1, Times [Opt x2, y]] | x1 == x2 -> Opt x1 <> Opt y  -- (1)
  Plus [y1, Times [x, Opt y2]] | y1 == y2 -> Opt x <> Opt y1  -- (2)
  x                                       -> Opt x

-------------------------------------------------------------------------------

-- | The size of a regular expression, following Kahrs and Runciman (2021).
size :: Regex -> Int
size = \case
  Zero     -> 0
  One      -> 0
  Lit _    -> 1
  Plus xs  -> sum (map size xs) + (length xs - 1)
  Times xs -> sum (map size xs) + (length xs - 1)
  Star x   -> size x + 1
  Opt x    -> size x + 1

-------------------------------------------------------------------------------

-- | The alphabet α(r) of characters that appear in the language L(r) of the
-- regular expression r.
alpha :: Regex -> CharSet
alpha = \case
  One      -> mempty
  Lit c    -> c
  Plus rs  -> mconcat $ map alpha rs
  Times rs -> mconcat $ map alpha rs
  Star r   -> alpha r
  Opt r    -> alpha r

-- | The alphabet α₁(r) of characters that appear as singleton words in the
-- language L(r) of the regular expression r.
alpha1 :: Regex -> CharSet
alpha1 = \case
  One      -> mempty
  Lit c    -> c
  Plus rs  -> mconcat $ map alpha1 rs
  Times rs -> timesAlpha1 rs
  Star r   -> alpha1 r
  Opt r    -> alpha1 r

-- | The alphabet α₁(r) of characters that appear as singleton words in the
-- language L(r) of the concatenation r = r₁⋅r₂⋯rₙ of the regular expressions
-- r₁,r₂,…,rₙ.
timesAlpha1 :: [Regex] -> CharSet
timesAlpha1 = fst . foldr go (mempty, True)
 where
  -- the bool indicates whether the tail of the concatenation is nullable
  go r (a, True ) | nullable r = (a <> alpha1 r, True  )
                  | otherwise  = (     alpha1 r, False )
  go r (a, False) | nullable r = (a            , False )
                  | otherwise  = (mempty       , False )

