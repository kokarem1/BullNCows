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

data GState = Running Nat Nat | NotRunning

data BullsNCows : GState -> Type where
     Init     : BullsNCows NotRunning -- initialising, but not ready
     GameWon  : String -> BullsNCows NotRunning
     GameLost : String -> BullsNCows NotRunning
     MkG      : (word : String) ->
                (guesses : Nat) ->
                (bulls: Nat) ->
                (cows: Nat) ->
                BullsNCows (Running guesses bulls)

instance Default (BullsNCows NotRunning) where
    default = Init

instance Show (BullsNCows s) where
    show Init = "Not ready yet"
    show (GameWon w) = "You won! Successfully guessed " ++ w
    show (GameLost w) = "You lost! The number was " ++ w
    show (MkG w guesses bulls cows)
         = let w' = show bulls ++ " bulls, " ++ show cows ++ " cows" in
               w' ++ "\n\n" ++ show guesses ++ " guesses left"

total
letters : String -> List Char
letters x with (strM x)
  letters "" | StrNil = []
  letters (strCons y xs) | (StrCons y xs) 
          = let xs' = assert_total (letters xs) in
                if ((y `elem` xs')) then xs' else y :: xs'

initState : (x : String) -> BullsNCows (Running 6 (length (letters x)))
initState w = let xs = letters w in
                  MkG w _ (length (letters w)) 0

-----------------------------------------------------------------------
-- RULES
-----------------------------------------------------------------------

data BullsNCowsRules : Effect where

     Guess : (x : String) ->
             sig BullsNCowsRules ()
                 (BullsNCows (Running (S g) (S w)))
                 (BullsNCows (Running g (S w))) -- (minus (S w) inword)

     Won  : sig BullsNCowsRules ()
                (BullsNCows (Running g 0))
                (BullsNCows NotRunning)

     Lost : sig BullsNCowsRules ()
                (BullsNCows (Running 0 g))
                (BullsNCows NotRunning)

     NewWord : (w : String) -> 
               sig BullsNCowsRules () h (BullsNCows (Running 6 (length (letters w))))

     Get  : sig BullsNCowsRules h h

BULLSNCOWS : GState -> EFFECT
BULLSNCOWS h = MkEff (BullsNCows h) BullsNCowsRules

guess : String -> Eff ()
                [BULLSNCOWS (Running (S g) (S w))]
                [BULLSNCOWS (Running g (S w))]
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
-- BULLSCOUNT COWSCOUNT
-----------------------------------------------------------------------

bullsCount : String -> String -> Nat
bullsCount "" _ = 0
bullsCount _ "" = 0
bullsCount s1 s2 = let c1 = strHead s1 in let c2 = strHead s2 in
                   (if (c1 == c2)
                       then 1
                       else 0)
                   +
                   bullsCount (strTail s1) (strTail s2)

cowsCount : String -> String -> Nat
cowsCount g w = (cowsCount' g w) - (bullsCount g w)
    where
        cowsCount' : String -> String -> Nat
        cowsCount' "" _ = 0
        cowsCount' _ "" = 0
        cowsCount' g w = let c = strHead g in
                        (if (inString c w)
                            then 1
                            else 0)
                        +
                        cowsCount' (strTail g) w
                        where
                            inString : Char -> String -> Bool
                            inString c s = elem c (unpack s)

-----------------------------------------------------------------------
-- IMPLEMENTATION OF THE RULES
-----------------------------------------------------------------------

instance Handler BullsNCowsRules m where
    handle (MkG w g Z Z) Won k = k () (GameWon w)
    handle (MkG w Z b c) Lost k = k () (GameLost w)

    handle st Get k = k st st
    handle st (NewWord w) k = k () (initState w)

    handle (MkG w (S g) (S b) c) (Guess x) k =
      let bC = bullsCount x w in
      k () (MkG w _ bC (cowsCount x w))

-----------------------------------------------------------------------
-- USER INTERFACE 
-----------------------------------------------------------------------
{-
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

words : ?wlen 
words = with Vect ["idris","agda","haskell","miranda",
         "java","javascript","fortran","basic","racket",
         "coffeescript","rust","purescript","clean","links",
         "koka","cobol"]

wlen = proof search

runGame : Eff () [BULLSNCOWS NotRunning, RND, SYSTEM, STDIO]
runGame = do srand !time
             let w = index !(rndFin _) words
             new_word w
             game
             putStrLn (show !get)

main : IO ()
main = run runGame
-}
