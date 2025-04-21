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
open import Data.List as List using (List; []; _∷_; _++_; [_]; foldr; _∷ʳ_)
-- import Data.List.Properties as List

-- Vec
open import Data.Vec.Functional as Vec
open import Data.Fin.Base

-- _≡_
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; module ≡-Reasoning)

-- Positive numbers
-- Used https://stackoverflow.com/questions/40098289/how-do-i-implement-positive-numbers-in-agda
isPos : ℕ -> Set
isPos zero = ⊥
isPos _    = ⊤

data Pos : Set where
  pos_one : Pos
  pos_suc : Pos → Pos

toPos : ∀ n {_ : isPos n} → Pos
toPos  0 {()}
toPos  1            = pos_one
toPos (suc (suc n)) = pos_suc (toPos (suc n))

toNat : Pos → ℕ 
toNat pos_one = suc zero
toNat (pos_suc n) = suc (toNat n)

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

-- The first is an index into which pile (hence it must be < the number of piles)
-- The second is the number of items to remove. This should be > 0.
Move : Set
Move = Fin NumPiles × Pos

-- The number of cells corresponds to the number of piles
-- The number in each cell represents the number of remaining items
Board : Set
Board = Vector ℕ NumPiles

-- Initial setup of game, currently set to [1, 2, 3]
setup : Board
setup = 1 Vec.∷ 2 Vec.∷ 3 Vec.∷ Vec.[]

---------------------------------------------------------------------------------------------------
-- Gameplay Mechanics

-- Check if all entries are 0
is_empty : Board → Bool
is_empty board = Vec.foldr (λ n b → b ∧ (n ≡ᵇ 0)) true board

-- Remove n items from the ith pile
-- Note: n must be > 0
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
outcome player [] board with is_empty board 
... | true = flip player 
... | false = player    -- ERROR CASE: Should not run out of moves to play when the board is non-empty
outcome player (m ∷ ms) board with is_empty board 
... | true = flip player
... | false = outcome (flip player) ms (play m board)

-- Predicate defining the game, given a list of moves. Player A goes first.
p : List Move -> R 
p ms = value (outcome A ms setup)

---------------------------------------------------------------------------------------------------
-- Defining Selection Functions

-- The sum of the setup numbers gives the maximum moves needed to finish the game
sum : Board → ℕ 
sum = Vec.foldr (λ n acc → n ℕ.+ acc) zero

-- Give the new state of the board, given the moves which already happened and the current board state
update_board : List Move -> Board -> Board
update_board List.[] board = board
update_board (m List.∷ ms) board = update_board ms (play m board)

-- Enumerate all possible moves for removing from pile i
pile_moves : Fin NumPiles → ℕ → List Move
pile_moves i zero = List.[]
pile_moves i (suc n) = (i , toPos (suc n)) List.∷ (pile_moves i n)

-- Enumerates all possible moves for removing from the first i piles, provided that i ≤ NumPiles
moves_helper : Board → (i : ℕ) → i ℕ.≤ NumPiles → List Move
moves_helper board zero _ = List.[]
moves_helper board (suc i) p = (pile_moves (fromℕ< p) (board (fromℕ< p))) List.++ (moves_helper board i (<⇒≤ p))

-- Enumerate all possible moves, given the current state of the board
moves : Board → List Move 
moves board = moves_helper board (length board) (≤-reflexive Eq.refl)
  
-- Chooses a move that maximizes the value
argsup : List Move → (Move → R) → Move
-- ERROR: Should never reach an empty list, since we have a base case when there is one remaining element
argsup List.[] p = zero , pos_one  
argsup (x List.∷ ms) p with p x 
... | true = x
argsup (x List.∷ List.[]) p | false = x
argsup (x List.∷ x₁ List.∷ ms) p | false = argsup (x₁ List.∷ ms) p

-- Chooses a move that minimizes the value
arginf : List Move → (Move → R) → Move
-- ERROR: Should never reach an empty list, since we have a base case when there is one remaining element
arginf List.[] p = zero , pos_one  
arginf (x List.∷ ms) p with p x 
... | false = x
arginf (x List.∷ List.[]) p | true = x
arginf (x List.∷ x₁ List.∷ ms) p | true = argsup (x₁ List.∷ ms) p

-- Optimal move for player A
epsilonA : List Move → (Move → R) → Move
epsilonA h = argsup (moves (update_board h setup))

-- Optimal move for player B
epsilonB : List Move → (Move → R) → Move
epsilonB h = arginf (moves (update_board h setup))

-- Selection functions for each point in the game
epsilons : List (List Move → (Move → R) → Move)
epsilons = eps_helper (sum setup)
  where 
    eps_helper : ℕ -> List (List Move → (Move → R) → Move)
    -- Game should be done
    eps zero helper = List.[]  
    -- Since we advance by 2 turns each time, and A goes first, 
    -- if there are an odd number of moves the last one should be A's move
    eps suc zero helper = epsilonA List.∷ List.[]   
    -- In the general case, we let A go then let B go, and repeat
    eps suc (suc n) helper = epsilonA List.∷ epsilonB List.∷ (eps_helper n)

---------------------------------------------------------------------------------------------------
-- Gameplay Optimization
-- The following are pulled directly from section 4.3 in the paper. 
-- The implementation should be the same as for tic-tac-toe.

optimalPlay : List Move 
optimalPlay = {! bigotimes (epsilons p) !}
-- See the end of 4.2 for how bigotimes will be implemented

optimalOutcome : R
optimalOutcome = p optimalPlay

optimalStrategy : List Move → Move
optimalStrategy ms = {!  !}
-- See 4.3 for how it will be implemented
```  