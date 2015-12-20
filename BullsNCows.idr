module Main

import Effects
import Effect.System
import Effect.StdIO
import Effect.Random
import Data.So
import Data.Fin
import Data.Vect

-----------------------------------------------------------------------
-- GAME STATE
-----------------------------------------------------------------------

{- First, the game state, GState, where the type specifies how many guesses
are left and how many missing letters there are still to get. -}

data GState = Running Nat Nat | NotRunning

data BullsNCows : GState -> Type where
     Init     : BullsNCows NotRunning -- initialising, but not ready
     GameWon  : String -> BullsNCows NotRunning
     GameLost : String -> BullsNCows NotRunning
     MkH      : (word : String) ->
                (guesses : Nat) ->
                (got : List Char) ->
                (missing : Vect m Char) ->
                BullsNCows (Running guesses m)

instance Default (BullsNCows NotRunning) where
    default = Init

instance Show (BullsNCows s) where
    show Init = "Not ready yet"
    show (GameWon w) = "You won! Successfully guessed " ++ w
    show (GameLost w) = "You lost! The word was " ++ w
    show (MkH w guesses got missing)
         = let w' = pack (map showGot (unpack w)) in
               w' ++ "\n\n" ++ show guesses ++ " guesses left"
      where showGot : Char -> Char
            showGot ' ' = '/'
            showGot c = if ((not (isAlpha c)) || (c `elem` got)) then c else '-'

{- Initialise the state with the missing letters in a word -}

total
letters : String -> List Char
letters x with (strM x)
  letters "" | StrNil = []
  letters (strCons y xs) | (StrCons y xs) 
          = let xs' = assert_total (letters xs) in
                if ((not (isAlpha y)) || (y `elem` xs')) then xs' else y :: xs'

initState : (x : String) -> BullsNCows (Running 6 (length (letters x)))
initState w = let xs = letters w in
                  MkH w _ [] (fromList (letters w))

-----------------------------------------------------------------------
-- RULES
-----------------------------------------------------------------------

{- Now, the rules of the game, written as an Effect. 
We can think of the rules as giving a protocol that the game player and
the machine must follow for an implementation of the game to make sense.
-}

data BullsNCowsRules : Effect where

-- Rule:
-- Precondition: we can make a guess if we have one or more guess available 
-- (S g) and one or more letters are still missing (S w)

-- Postcondition: return whether the character was in the word. If so, reduce
-- the number of missing letters, if not, reduce the number of guesses left

     Guess : (x : Char) ->
             sig BullsNCowsRules Bool
                 (BullsNCows (Running (S g) (S w)))
                 (\inword =>
                        BullsNCows (case inword of
                             True => (Running (S g) w)
                             False => (Running g (S w))))

-- The 'Won' operation requires that there are no missing letters

     Won  : sig BullsNCowsRules ()
                (BullsNCows (Running g 0))
                (BullsNCows NotRunning)

-- The 'Lost' operation requires that there are no guesses left

     Lost : sig BullsNCowsRules ()
                (BullsNCows (Running 0 g))
                (BullsNCows NotRunning)

-- Set up a new game, initialised with 6 guesses and the missing letters in
-- the given word. Note that if there are no letters in the word, we won't
-- be able to run 'Guess'!

     NewWord : (w : String) -> 
               sig BullsNCowsRules () h (BullsNCows (Running 6 (length (letters w))))

-- Finally, allow us to get the current game state
     
     Get  : sig BullsNCowsRules h h

BULLSNCOWS : GState -> EFFECT
BULLSNCOWS h = MkEff (BullsNCows h) BullsNCowsRules

-- Promote explicit effects to Eff programs

guess : Char -> Eff Bool
                [BULLSNCOWS (Running (S g) (S w))]
                (\inword => [BULLSNCOWS (case inword of
                                        True => Running (S g) w
                                        False => Running g (S w))])
guess c = call (Main.Guess c)

won :  Eff () [BULLSNCOWS (Running g 0)] [BULLSNCOWS NotRunning]
won = call Won

lost : Eff () [BULLSNCOWS (Running 0 g)] [BULLSNCOWS NotRunning]
lost = call Lost

new_word : (w : String) -> Eff () [BULLSNCOWS h] 
                                  [BULLSNCOWS (Running 6 (length (letters w)))]
new_word w = call (NewWord w)

get : Eff (BullsNCows h) [BULLSNCOWS h]
get = call Get

-----------------------------------------------------------------------
-- SHRINK
-----------------------------------------------------------------------

instance Uninhabited (Elem x []) where
    uninhabited Here impossible

shrink : (xs : Vect (S n) a) -> Elem x xs -> Vect n a
shrink (x :: ys) Here = ys
shrink (y :: []) (There p) = absurd p
shrink (y :: (x :: xs)) (There p) = y :: shrink (x :: xs) p

-----------------------------------------------------------------------
-- IMPLEMENTATION OF THE RULES
-----------------------------------------------------------------------

{- This effect handler simply updates the game state as necessary for
each operation. 'Guess' is slightly tricky, in that it needs to check
whether the letter is in the word, and branch accordingly (and if it
is in the word, update the vector of missing letters to be the right
length). -}

instance Handler BullsNCowsRules m where
    handle (MkH w g got []) Won k = k () (GameWon w)
    handle (MkH w Z got m) Lost k = k () (GameLost w)

    handle st Get k = k st st
    handle st (NewWord w) k = k () (initState w)

    handle (MkH w (S g) got m) (Guess x) k =
      case isElem x m of
           No _ => k False (MkH w _ got m)
           Yes p => k True (MkH w _ (x :: got) (shrink m p))

-----------------------------------------------------------------------
-- USER INTERFACE 
-----------------------------------------------------------------------

{- Finally, an implementation of the game which reads user input and calls
the operations we defined above when appropriate. 
The type indicates that the game must start in a running state, with some
guesses available, and get to a not running state (i.e. won or lost). 
Since we picked a word at random, we can't actually make the assumption there
were valid letters in it!
-}

soRefl : So x -> (x = True)
soRefl Oh = Refl 

game : Eff () [BULLSNCOWS (Running (S g) w), STDIO]
              [BULLSNCOWS NotRunning, STDIO]
game {w=Z} = won 
game {w=S _}
     = do putStrLn (show !get)
          putStr "Enter guess: "
          let guess = trim !getStr
          case choose (not (guess == "")) of
               (Left p) => processGuess (strHead' guess (soRefl p))
               (Right p) => do putStrLn "Invalid input!"
                               game
  where 
    processGuess : Char -> Eff () [BULLSNCOWS (Running (S g) (S w)), STDIO] 
                                  [BULLSNCOWS NotRunning, STDIO] 
    processGuess {g} c {w}
      = case !(guess c) of
             True => do putStrLn "Good guess!"
                        case w of
                             Z => won
                             (S k) => game
             False => do putStrLn "No, sorry"
                         case g of
                              Z => lost
                              (S k) => game

{- Some candidate words. We'll use programming languages. We don't want to
write the length explicitly, so infer it with a proof search. -}

words : ?wlen 
words = with Vect ["idris","agda","haskell","miranda",
         "java","javascript","fortran","basic","racket",
         "coffeescript","rust","purescript","clean","links",
         "koka","cobol"]

wlen = proof search

{- It typechecks! Ship it! -}

runGame : Eff () [BULLSNCOWS NotRunning, RND, SYSTEM, STDIO]
runGame = do srand !time
             let w = index !(rndFin _) words
             new_word w
             game
             putStrLn (show !get)

{- I made a couple of mistakes while writing this. For example, the following 
were caught by the type checker:
* Forgetting to check the 'Won' state before continuing with 'game'
* Accidentally checking the number of missing letters rather than the number
  of guesses when checking if 'Lost' was callable
-}

main : IO ()
main = run runGame

-- Local Variables:
-- idris-load-packages: ("effects")
-- End:

