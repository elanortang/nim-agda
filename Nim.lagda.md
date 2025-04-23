# Nim

```agda
module Nim where

-- ⊤ and _×_
open import Data.Unit
open import Data.Product hiding (map)

-- ⊥ and _⊎_
open import Data.Empty
-- open import Data.Sum hiding (map)

-- Bool and ℕ
open import Data.Bool
open import Data.Nat as ℕ
open import Data.Nat.Properties

-- List
open import Data.List as List using (List; []; _∷_; _++_; drop; length; head)
-- import Data.List.Properties as List
open import Data.Maybe.Base as Maybe

-- Vec
open import Data.Vec.Functional as Vec using (Vector; []; _∷_; foldr; updateAt; length)
open import Data.Fin.Base hiding (_+_)

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

-- Positive numbers
-- Used https://stackoverflow.com/questions/40098289/how-do-i-implement-positive-numbers-in-agda
isPos : ℕ -> Set
isPos zero = ⊥
isPos _    = ⊤

data Pos : Set where
  one : Pos
  succ : Pos → Pos

toPos : ∀ n {_ : isPos n} → Pos
toPos  0 {()}
toPos  1            = one
toPos (suc (suc n)) = succ (toPos (suc n))

toNat : Pos → ℕ 
toNat one = suc zero
toNat (succ n) = suc (toNat n)

---------------------------------------------------------------------------------------------------
-- Game Structures

-- Our two players are A and B
data Player : Set where
  A B : Player

-- Use R to distinguish the Bool outcome of the game from the Bool outcome of a predicate
R : Set
R = Bool

-- Number of piles, currently set to 3
NumPiles : ℕ
NumPiles = 3

-- The first element is an index into which pile (hence it must be < the number of piles)
-- The second element is the number of items to remove. This should be > 0.
Move : Set
Move = Fin NumPiles × Pos

-- The number of cells corresponds to the number of piles
-- The number in each cell represents the number of remaining items
Board : Set
Board = Vector ℕ NumPiles

---------------------------------------------------------------------------------------------------
-- Gameplay Mechanics

-- Check if all entries are 0
isEmpty : Board → Bool
isEmpty board = foldr (λ n b → b ∧ (n ≡ᵇ 0)) true board

-- Remove n > 0 items from the ith pile
play : Move → Board → Board
play (i , n) board = updateAt board i (λ m → m ∸ (toNat n))

-- If Player A wins, the value of the game is true; if Player B wins, the value is false
value : Player → R
value A = true
value B = false

-- Helper function for making the players alternate turns
flip : Player → Player
flip A = B 
flip B = A

-- Given the current player, the list of moves remaining, and current state of the board, outputs the winner of the game.
-- If it is one player's turn and the board is empty, then the other player must have won on the previous turn.
-- Else, play continues and the turn passes to the other player, with an updated board and sequence of remaining moves.
outcome : Player → List Move → Board → Player
outcome player [] board with isEmpty board 
... | true = flip player 
... | false = player    -- ERROR CASE: Should not run out of moves to play when the board is non-empty
outcome player (m ∷ ms) board with isEmpty board 
... | true = flip player
... | false = outcome (flip player) ms (play m board)

-- Predicate defining the game, given a list of moves. Player A goes first.
gameplay : Board → List Move -> R 
gameplay setup ms = value (outcome A ms setup)

---------------------------------------------------------------------------------------------------
-- Defining Selection Functions

-- The sum of the setup numbers gives the maximum moves needed to finish the game
sum : Board → ℕ 
sum = foldr (λ n acc → n + acc) zero

-- Give the new state of the board, given the moves which already happened and the current board state
updateBoard : List Move -> Board -> Board
updateBoard List.[] board = board
updateBoard (m List.∷ ms) board = updateBoard ms (play m board)

-- Enumerate all possible moves for removing from pile i
pileMoves : Fin NumPiles → ℕ → List Move
pileMoves i zero = List.[]
pileMoves i (suc n) = (i , toPos (suc n)) List.∷ (pileMoves i n)

-- Enumerates all possible moves for removing from the first i piles, provided that i ≤ NumPiles
movesHelper : Board → (i : ℕ) → i ℕ.≤ NumPiles → List Move
movesHelper board zero _ = List.[]
movesHelper board (suc i) p = (pileMoves (fromℕ< p) (board (fromℕ< p))) ++ (movesHelper board i (<⇒≤ p))

-- Enumerate all possible moves, given the current state of the board
moves : Board → List Move 
moves board = movesHelper board (Vec.length board) (≤-reflexive Eq.refl)
  
-- Chooses a move that maximizes the value
argsup : List Move → (Move → R) → Move
-- ERROR: Should never reach an empty list, since we have a base case when there is one remaining element
argsup List.[] p = zero , one  
argsup (x List.∷ ms) p with p x 
... | true = x
argsup (x List.∷ List.[]) p | false = x
argsup (x List.∷ x₁ List.∷ ms) p | false = argsup (x₁ List.∷ ms) p

-- Chooses a move that minimizes the value
arginf : List Move → (Move → R) → Move
-- Alternate implementation: arginf ms p = argsup ms (λ m → not (p m))
-- ERROR: Should never reach an empty list, since we have a base case when there is one remaining element
arginf List.[] p = zero , one  
arginf (x List.∷ ms) p with p x 
... | false = x
arginf (x List.∷ List.[]) p | true = x
arginf (x List.∷ x₁ List.∷ ms) p | true = arginf (x₁ List.∷ ms) p

-- Optimal move for player A
epsilonA : Board → List Move → (Move → R) → Move
epsilonA setup h = argsup (moves (updateBoard h setup))

-- Optimal move for player B
epsilonB : Board → List Move → (Move → R) → Move
epsilonB setup h = arginf (moves (updateBoard h setup))

-- Selection functions for each point in the game
epsilons : Board → List (List Move → (Move → R) → Move)
epsilons setup = epsHelper (sum setup)
  where 
    epsHelper : ℕ -> List (List Move → (Move → R) → Move)
    -- Game should be done
    epsHelper zero = List.[]  
    -- Since we advance by 2 turns each time, and A goes first, 
    -- if there are an odd number of moves the last one should be A's move
    epsHelper (suc zero) = (epsilonA setup) List.∷ List.[]   
    -- In the general case, we let A go then let B go, and repeat
    epsHelper (suc (suc n)) = (epsilonA setup) List.∷ (epsilonB setup) List.∷ (epsHelper n)

---------------------------------------------------------------------------------------------------
-- Gameplay Optimization
-- Converted from sections 4.2 and 4.3 in the paper

-- Transforms a selection function into a quantifier
overline : {X : Set} → ((X → R) → X) → (X → R) → R 
overline e p = p (e p)

-- Composes selection function with a selection function over lists
otimes : ((Move → R) → Move) → (Move → (List Move → R) → List Move) → (List Move → R) → List Move
otimes e0 e1 p = a0 List.∷ a1
  where 
    a0 : Move
    a0 = e0 (λ x0 → overline (e1 x0) (λ x1 → p (x0 List.∷ x1)))

    a1 : List Move
    a1 = e1 a0 (λ x1 → p (a0 List.∷ x1))

{-# TERMINATING #-}
-- Terminates because the size of the input list always decreases, even if it is not a subexpression
-- Iterates composition of a list of selection functions into a selection function over lists
bigotimes : List (List Move → (Move → R) → Move) → (List Move → R) → List Move
bigotimes List.[] = λ p → List.[]
bigotimes (e List.∷ es) = otimes (e List.[]) (λ x → bigotimes (construct es x))
  where 
    construct : List (List Move → (Move → R) → Move) → Move → List (List Move → (Move → R) → Move)
    construct List.[] x = List.[]
    construct (d List.∷ es) x = (λ xs → d (x List.∷ xs)) List.∷ (construct es x)

-- Update selection functions to take past moves into account
newEpsilons : List (List Move → (Move → R) → Move) → List Move → List (List Move → (Move → R) → Move)
newEpsilons List.[] _ = List.[]
newEpsilons (e List.∷ es) h = (λ xs → e (h ++ xs)) List.∷ (newEpsilons es h) 

-- List of how the game could go when both players play optimally, given the setup
optimalPlay : Board → List Move 
optimalPlay setup = bigotimes (epsilons setup) (gameplay setup)

-- Outcome when both players play optimally, given the setup
optimalOutcome : Board → R
optimalOutcome setup = (gameplay setup) (optimalPlay setup)

-- Optimal next move, given the setup and the moves so far
optimalStrategy : Board → List Move → Maybe Move
optimalStrategy setup h = head (bigotimes epsilons' p')
  where 
    epsilons' : List (List Move → (Move → R) → Move)
    epsilons' = newEpsilons (drop (List.length h) (epsilons setup)) h

    p' : List Move → R
    p' xs = gameplay setup (h ++ xs)

---------------------------------------------------------------------------------------------------
-- Testing

-- Test [0, 0, 1]. We expect A to win and the result to be true. 
test001 : (optimalOutcome (0 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test001 = Eq.refl

-- Test [1, 0, 1]. We expect B to win and the result to be false. 
test101 : (optimalOutcome (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[])) ≡ false
test101 = Eq.refl

-- Test [0, 0, 2]. We expect A to win and the result to be true. 
test002 : (optimalOutcome (0 Vec.∷ 0 Vec.∷ 2 Vec.∷ Vec.[])) ≡ true
test002 = Eq.refl

-- Test [1, 1, 1]. We expect A to win and the result to be true. 
test111 : (optimalOutcome (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test111 = Eq.refl

-- Test [0, 2, 1]. We expect A to win and the result to be true. 
test021 : (optimalOutcome (0 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test021 = Eq.refl

-- Test [0, 2, 2]. We expect B to win and the result to be false. 
test022 : (optimalOutcome (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[])) ≡ false
test022 = Eq.refl

-- Test [0, 1, 3]. We expect A to win and the result to be true. 
test013 : (optimalOutcome (0 Vec.∷ 1 Vec.∷ 3 Vec.∷ Vec.[])) ≡ true
test013 = Eq.refl

-- Test [1, 2, 1]. We expect A to win and the result to be true. 
test121 : (optimalOutcome (1 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test121 = Eq.refl

-- -- Test [1, 2, 2]. We expect A to win and the result to be true. 
-- test122 : (optimalOutcome (1 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[])) ≡ true
-- test122 = Eq.refl

-- -- Test [0, 3, 2]. We expect A to win and the result to be true. 
-- test032 : (optimalOutcome (0 Vec.∷ 3 Vec.∷ 2 Vec.∷ Vec.[])) ≡ true
-- test032 = Eq.refl

-- -- Test [1, 2, 3]. We expect B to win and the result to be false. 
-- test123 : (optimalOutcome (1 Vec.∷ 2 Vec.∷ 3 Vec.∷ Vec.[])) ≡ false
-- test123 = Eq.refl

-- Test [3, 3, 0]. We expect B to win and the result to be false. 
-- test330 : (optimalOutcome (3 Vec.∷ 3 Vec.∷ 0 Vec.∷ Vec.[])) ≡ false
-- test330 = Eq.refl

-- -- Test [2, 2, 2]. We expect A to win and the result to be true. 
-- test222 : (optimalOutcome (2 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[])) ≡ true
-- test222 = Eq.refl

test101Play : List Move
test101Play = {! optimalPlay (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[]) !}

test022Play : List Move
test022Play = {! optimalPlay (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) !}

test013Play : List Move
test013Play = {! optimalPlay (0 Vec.∷ 1 Vec.∷ 3 Vec.∷ Vec.[]) !}

test121Play : List Move
test121Play = {! optimalPlay (1 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[]) !}

-- A has no optimal move here
test101Strategy_Move0 : Maybe Move
test101Strategy_Move0 = {! optimalStrategy (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[]) List.[] !}

-- B has exactly one optimal move here
test101Strategy_Move1_Option1 : optimalStrategy (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[]) ((zero ,  one) List.∷ List.[]) ≡ just (suc (suc zero) , one)
test101Strategy_Move1_Option1 = Eq.refl

-- B has exactly one optimal move here
test101Strategy_Move1_Option2 : optimalStrategy (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[]) ((suc (suc zero) , one) List.∷ List.[]) ≡ just (zero , one)
test101Strategy_Move1_Option2 = Eq.refl

-- A has no optimal move here
test022Strategy : Maybe Move
test022Strategy = {! optimalStrategy (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) List.[] !}

-- B has exactly one optimal move here
test022Strategy_Move1_Option1 : optimalStrategy (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) ((suc zero ,  one) List.∷ List.[]) ≡ just (suc (suc zero) , one)
test022Strategy_Move1_Option1 = Eq.refl

-- B has exactly one optimal move here
test022Strategy_Move1_Option2 : optimalStrategy (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) ((suc (suc zero) , succ one) List.∷ List.[]) ≡ just (suc zero , succ one)
test022Strategy_Move1_Option2 = Eq.refl

-- A has exactly one optimal move
test013Strategy : optimalStrategy (0 Vec.∷ 1 Vec.∷ 3 Vec.∷ Vec.[]) List.[] ≡ just (suc (suc zero), succ one)
test013Strategy = Eq.refl

-- A has exactly one optimal move
test121Strategy : optimalStrategy (1 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[]) List.[] ≡ just (suc zero , succ one)
test121Strategy = Eq.refl

---------------------------------------------------------------------------------------------------
-- Variant where players win if they do not take the last item

-- Given the current player, the list of moves remaining, and current state of the board, output the winner of the game.
-- If the board is empty, the other player just took the last item, so the player whose move it is has won
outcome' : Player → List Move → Board → Player
outcome' player [] board with isEmpty board 
... | true = player 
... | false = flip player    -- ERROR CASE: Should not run out of moves to play when the board is non-empty
outcome' player (m ∷ ms) board with isEmpty board 
... | true = player
... | false = outcome' (flip player) ms (play m board)

-- Predicate defining the variant of the game, given a list of moves. Player A goes first.
gameplay' : Board → List Move -> R 
gameplay' setup ms = value (outcome' A ms setup)

-- List of how the game could go when both players play optimally, given the setup
optimalPlay' : Board → List Move 
optimalPlay' setup = bigotimes (epsilons setup) (gameplay' setup)

-- Outcome when both players play optimally, given the setup
optimalOutcome' : Board → R
optimalOutcome' setup = (gameplay' setup) (optimalPlay' setup)

-- Optimal next move, given the setup and the moves so far
optimalStrategy' : Board → List Move → Maybe Move
optimalStrategy' setup h = head (bigotimes epsilons' p')
  where 
    epsilons' : List (List Move → (Move → R) → Move)
    epsilons' = newEpsilons (drop (List.length h) (epsilons setup)) h

    p' : List Move → R
    p' xs = gameplay' setup (h ++ xs)

-- Test [0, 0, 1]. We expect B to win and the result to be false. 
test001' : (optimalOutcome' (0 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[])) ≡ false
test001' = Eq.refl

-- Test [1, 0, 1]. We expect A to win and the result to be true. 
test101' : (optimalOutcome' (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test101' = Eq.refl

-- Test [0, 0, 2]. We expect A to win and the result to be true. 
test002' : (optimalOutcome' (0 Vec.∷ 0 Vec.∷ 2 Vec.∷ Vec.[])) ≡ true
test002' = Eq.refl

-- Test [1, 1, 1]. We expect B to win and the result to be false. 
test111' : (optimalOutcome' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[])) ≡ false
test111' = Eq.refl

-- Test [0, 2, 1]. We expect A to win and the result to be true. 
test021' : (optimalOutcome' (0 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test021' = Eq.refl

-- Test [0, 2, 2]. We expect B to win and the result to be false. 
test022' : (optimalOutcome' (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[])) ≡ false
test022' = Eq.refl

-- Test [0, 1, 3]. We expect A to win and the result to be true. 
test013' : (optimalOutcome' (0 Vec.∷ 1 Vec.∷ 3 Vec.∷ Vec.[])) ≡ true
test013' = Eq.refl

-- Test [1, 2, 1]. We expect A to win and the result to be true. 
test121' : (optimalOutcome' (1 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
test121' = Eq.refl

test111Play' : List Move
test111Play' = {! optimalPlay' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[]) !}

test022Play' : List Move
test022Play' = {! optimalPlay' (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) !}

test013Play' : List Move
test013Play' = {! optimalPlay' (0 Vec.∷ 1 Vec.∷ 3 Vec.∷ Vec.[]) !}

test121Play' : List Move
test121Play' = {! optimalPlay' (1 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[]) !}

-- B has exactly one move here
test101_Move1 : optimalStrategy' (1 Vec.∷ 0 Vec.∷ 1 Vec.∷ Vec.[]) ((suc (suc zero) , one) List.∷ List.[]) ≡ just (zero ,  one)
test101_Move1 = Eq.refl

-- A has no optimal move here
test111Strategy_Move0' : Maybe Move
test111Strategy_Move0' = {! optimalStrategy' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[]) List.[] !}

-- B has two potential optimal moves here
test111Strategy_Move1_Option1' : Maybe Move
test111Strategy_Move1_Option1' = {! optimalStrategy' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[]) ((zero ,  one) List.∷ List.[]) !}

-- B has two potential optimal moves here
test111Strategy_Move1_Option2' : Maybe Move
test111Strategy_Move1_Option2' = {! optimalStrategy' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[]) ((suc zero , one) List.∷ List.[]) !}

-- B has two potential optimal moves here
test111Strategy_Move1_Option3' : Maybe Move
test111Strategy_Move1_Option3' = {! optimalStrategy' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[]) ((suc (suc zero) ,  one) List.∷ List.[]) !}

-- A has no optimal move here
test022Strategy_Move0' : Maybe Move
test022Strategy_Move0' = {! optimalStrategy' (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) List.[] !}

-- B has exactly one optimal move here
test022Strategy_Move1_Option1' : optimalStrategy' (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) ((suc zero ,  one) List.∷ List.[]) ≡ just (suc (suc zero) , succ one)
test022Strategy_Move1_Option1' = Eq.refl

-- B has exactly one optimal move here
test022Strategy_Move1_Option2' : optimalStrategy' (0 Vec.∷ 2 Vec.∷ 2 Vec.∷ Vec.[]) ((suc (suc zero) , succ one) List.∷ List.[]) ≡ just (suc zero , one)
test022Strategy_Move1_Option2' = Eq.refl

-- A has exactly one optimal move
test013Strategy' : optimalStrategy' (0 Vec.∷ 1 Vec.∷ 3 Vec.∷ Vec.[]) List.[] ≡ just (suc (suc zero) , succ (succ one))
test013Strategy' = Eq.refl

-- A has exactly one optimal move
test121Strategy' : optimalStrategy' (1 Vec.∷ 2 Vec.∷ 1 Vec.∷ Vec.[]) List.[] ≡ just (suc zero , one)
test121Strategy' = Eq.refl

---------------------------------------------------------------------------------------------------
-- Testing four piles
-- To reproduce, change NumPiles to 4. Need to comment out all other tests. 

-- Unfortunately this is the only test which has a nonzero amount in each pile and does not time out

-- -- Test [1, 1, 1, 1]. We expect B to win and the result to be false. 
-- test1111 : (optimalOutcome (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[])) ≡ false
-- test1111 = Eq.refl

-- -- Test [1, 1, 1, 1]. We expect A to win and the result to be true. 
-- test1111' : (optimalOutcome' (1 Vec.∷ 1 Vec.∷ 1 Vec.∷ 1 Vec.∷ Vec.[])) ≡ true
-- test1111' = Eq.refl

-- TODO: How is this related to the course

```     