{-|
This module implements 'intersection' and 'complement' of regular expressions
based on the equation-solving approach by Acay (unpublished manuscript, 2018),
which works entirely algebraically, without intermediate translation into
automata.

References:

  * Acay, Josh. "A Regular Expression Library for Haskell." Unpublished
    manuscript, dated May 22, 2018. LaTeX files and Haskell source code.
    https://github.com/cacay/regexp

  * Antimirov, Valentin. 1996. "Partial derivatives of regular expressions and
    finite automaton constructions." Theoretical Computer Science 155 (1996):
    291-319. https://doi.org/10.1016/0304-3975(95)00182-4

  * Arden, Dean N. 1961. "Delayed Logic and Finite State Machines." Proceedings
    of the 2nd Annual Symposium on Switching Circuit Theory and Logical Design
    (SWCT 1961), 133-151. https://doi.org/10.1109/FOCS.1961.13

  * Brzozowski, Janusz A. 1964. "Derivatives of Regular Expressions." Journal of
    the ACM 11, no. 4 (October 1964): 481-494.
    https://doi.org/10.1145/321239.321249

  * Keil, Matthias and Peter Thiemann. 2014. "Symbolic Solving of Extended
    Regular Expression Inequalities." https://arxiv.org/abs/1410.3227
    
  * Liang Tianyi, Nestan Tsiskaridze, Andrew Reynolds, Cesare Tinelli, and Clark
    Barrett. 2015. "A decision procedure for regular membership and length
    constraints over unbounded strings." Frontiers of Combining Systems (FroCoS
    2015), LNAI 9322, 135–150. https://doi.org/10.1007/978-3-319-24246-0_9
-}
module Regex.Operations where

import Control.Exception
import Control.Monad.Trans.State.Strict
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Semigroup hiding (All)
import Data.Set (Set)
import Data.Set qualified as Set
import Prelude
import Regex.CharSet (CharSet)
import Regex.CharSet qualified as CS
import Regex.Type

-------------------------------------------------------------------------------

-- | The derivative c⁻¹r of a regex r with respect to a character c is a new
-- regex that accepts all words that would be accepted by r if they were
-- prefixed by c, i.e., ℒ(c⁻¹r) = { w | cw ∈ ℒ(r) } (Brzozowski 1964).
derivative :: Char -> Regex -> Regex
derivative c = \case
  One               -> Zero
  Lit d 
    | CS.member c d -> One
    | otherwise     -> Zero
  Plus rs           -> Plus $ map (derivative c) rs
  Times []          -> Zero  -- impossible case; to avoid warnings
  Times (r:rs) 
    | nullable r    -> Plus [Times (derivative c r : rs), derivative c (Times rs)]
    | otherwise     -> derivative c r <> Times rs
  Star r            -> derivative c r <> Star r
  Opt r             -> derivative c r
  
-------------------------------------------------------------------------------

-- | Compute the intersection of two regexes.
--
-- The implementation works purely algebraically, without going through a DFA.
-- It is based on a definition of intersection via derivatives,
--
--     r₁ ∩ r₂ = c₀ + c₁⋅(c₁⁻¹r₁ ∩ c₁⁻¹r₂) + … + cₙ⋅(cₙ⁻¹r₁ ∩ cₙ⁻¹r₂),
--
-- where c₀ is ε if both r₁ and r₂ are nullable and otherwise ∅, and cᵢ
-- enumerates all characters of the alphabet Σ. Unfolding this definition gives
-- a system of linear equations
--
--     X₀ = c₀₀ + c₁₀⋅X₀ + c₂₀⋅X₁ + … + cₙ₀⋅Xₙ
--     X₁ = c₀₁ + c₁₁⋅X₀ + c₂₁⋅X₁ + … + cₙ₁⋅Xₙ
--        ⋮
--     Xₘ = c₀ₘ + c₁ₘ⋅X₀ + c₂ₘ⋅X₁ + … + cₙₘ⋅Xₙ
-- 
-- where each Xᵢ is an intersection of regex derivatives (cᵢₖ⁻¹r₁ ∩ cᵢₖ⁻¹r₂).
-- Using Arden's lemma (1961) and Gaussian elimination, we can solve this system
-- to arrive at a closed-form solution for X₀ = r₁ ∩ r₂.
--
-- To avoid actually enumerating the whole alphabet, we use local mintermization
-- (Keil and Thiemann 2014) to partition the alphabet into equivalence classes;
-- see the 'next' function below.
intersection :: Regex -> Regex -> Regex
intersection = curry $ solve $ \(x1,x2) ->
  let
    c0 | nullable x1, nullable x2 = One
       | otherwise                = Zero

    cx = [ (x, Lit p) | p <- Set.toList $ next x1 ⋈ next x2
                      , Just c <- [CS.choose p]
                      , let x = (derivative c x1, derivative c x2)
         ]

  in (c0, Map.fromListWith (\a b -> Plus [a,b]) cx)

-- | Compute the complement of a regex.
--
-- The implementation works in the same way as 'intersection' and is based
-- on the definition
--
--     ¬r = c₀ + c₁⋅¬(c₁⁻¹r) + … + cₙ⋅¬(cₙ⁻¹r),
--
-- where c₀ is ε if r is not nullable and otherwise ε.
complement :: Regex -> Regex
complement = solve $ \x ->
  let 
    c0 | nullable x = Zero 
       | otherwise  = One
    
    c1 = Lit (CS.complement $ CS.unions $ next x) <> All
    
    cx = [ (derivative c x, Lit p) | p <- Set.toList $ next x
                                   , Just c <- [CS.choose p]
         ]

  in (Plus [c0,c1], Map.fromListWith (\a b -> Plus [a,b]) cx)

-- | Semantic equivalence of two regular expressions, i.e., language equality.
equivalence :: Regex -> Regex -> Bool
equivalence r1 r2 = Zero == Plus [ intersection r1 (complement r2)
                                 , intersection (complement r1) r2]

-------------------------------------------------------------------------------

-- | A system of linear regex equations.
type System x = Map x (RHS x)

-- | The right-hand side of an equation Xᵢ = c₀ + c₁⋅X₁ + c₂⋅X₂ + … + cₙ⋅Xₙ,
-- with c₀ being a known constant term. Each unknown term c⋅X, consisting of a
-- coefficient c and a variable X, is represented as a mapping from X to c.
type RHS x = (Regex, Map x Regex)

-- | Combine two right-hand sides. For example,
--
--     combine (a + bX) (c + dX + eY)  =  (a+c) + (b+d)X + eY.
--
combine :: Ord x => RHS x -> RHS x -> RHS x
combine (c01,xs1) (c02,xs2) = 
  (Plus [c01,c02], Map.unionWith (\a b -> Plus [a,b]) xs1 xs2)

-- | Multiply each RHS term by a constant, i.e., concatenating the constant
-- regex in front of each term. For example,
-- 
--    scale c (a + bX)  =  ca + cbX.
--
scale :: Regex -> RHS x -> RHS x
scale r (c0,xs) = (r <> c0, Map.map (r <>) xs)

-- | Try to eliminate a variable using Arden's lemma (1961), which states that
--
--     X = A⋅X + B
--       = A*⋅B
-- 
-- as long as A is not nullable. For example,
--
--     elim X (a + bX + cY)  =  (b*a + b*cY).
--
elim :: Ord x => x -> RHS x -> RHS x
elim x (c0,xs) = case Map.lookup x xs of
  Nothing -> (c0,xs)  
  Just cx -> assert (not $ nullable cx)
             scale (Star cx) (c0, Map.delete x xs)

-- | @solve f X₁@ constructs and solves a system of linear regex equations,
-- given an initial unknown variable @X₁@ and a generating function @f@ that
-- computes the right-hand side of any unknown variable @Xᵢ@.
--
-- This implementation largely follows Acay (unpublished manuscript, 2018).
solve :: forall x. Ord x => (x -> RHS x) -> x -> Regex
solve f x0 = evalState (go x0) mempty
 where
  go :: x -> State (System x) Regex
  go x = do
    rhs <- gets $ Map.lookup x
    case rhs of
      Just (c0,xs) ->
        assert (null xs)
        return c0

      Nothing -> do
        -- generate the RHS for x and resolve all known variables
        rhsX <- resolve (f x)
        
        -- eliminate X using Arden's lemma and add the solution to the system
        let (c0,ys) = elim x rhsX
        modify' $ Map.insert x (c0,ys)

        -- recursively solve each remaining variable in the RHS
        cs <- mapM (\(y,c) -> (c <>) <$> go y) (Map.toList ys)
        
        -- add the final closed solution for X to the system and return it
        let c0' = Plus (c0:cs)
        modify' $ Map.insert x (c0', mempty)
        return c0'

  resolve :: RHS x -> State (System x) (RHS x)
  resolve (c0,xs) = do
    rs <- mapM resolveTerm (Map.toList xs)
    return $ foldr combine (c0, mempty) rs

  resolveTerm :: (x, Regex) -> State (System x) (RHS x)
  resolveTerm (x,c) = do
    rhs <- gets $ Map.lookup x
    case rhs of
      Just (c0,xs) -> scale c <$> resolve (c0,xs)
      Nothing      -> return (Zero, Map.singleton x c)

-------------------------------------------------------------------------------

-- | The  /next literals/ of a regex are a set {A₁,A₂,...,Aₙ} of mutually
-- disjoint character sets Aᵢ such that all symbols in each character set yield
-- the same derivative, allowing us to avoid enumerating the entire alphabet
-- during 'intersection' (Keil and Thiemann 2014, section 5.2).
next :: Regex -> Set CharSet
next = \case
  One            -> Set.singleton CS.empty
  Lit a          -> Set.singleton a
  Plus (r:rs)    -> next r ⋈ next (Plus rs)
  Times (r:rs)
    | nullable r -> next r ⋈ next (Times rs)
    | otherwise  -> next r
  Star r         -> next r
  Opt r          -> next One ⋈ next r

  -- impossible cases; to avoid warnings
  Plus  [] -> Set.singleton CS.empty
  Times [] -> Set.singleton CS.empty

-- | Given two sets of mutually disjoint literals, ⨝ (join) builds a new set of
-- mutually disjoint literals that covers the union of the two sets (Keil and
-- Thiemann 2014, Definition 7).
(⋈) :: Set CharSet -> Set CharSet -> Set CharSet
l1 ⋈ l2 = Set.fromList $ concat $
  [ [ CS.intersection a1 a2
    , CS.intersection a1 (CS.complement $ CS.unions l2)
    , CS.intersection a2 (CS.complement $ CS.unions l1)
    ]
  | a1 <- Set.toList l1, a2 <- Set.toList l2
  ]
