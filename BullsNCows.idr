module Main

import Effects
import Effect.System
import Effect.StdIO
import Effect.Random
import Effect.Exception
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
                (got : List Char) ->
                (missing : Vect m Char) ->
                BullsNCows (Running guesses m)

instance Default (BullsNCows NotRunning) where
    default = Init

instance Show (BullsNCows s) where
    show Init = "Not ready yet"
    show (GameWon w) = "You won! Successfully guessed " ++ w
    show (GameLost w) = "You lost! The word was " ++ w
    show (MkG w guesses got missing)
         = let w' = pack (map showGot (unpack w)) in
               w' ++ "\n\n" ++ show guesses ++ " guesses left"
      where showGot : Char -> Char
            showGot ' ' = '/'
            showGot c = if ((not (isAlpha c)) || (c `elem` got)) then c else '-'

total
letters : String -> List Char
letters x with (strM x)
  letters "" | StrNil = []
  letters (strCons y xs) | (StrCons y xs) 
          = let xs' = assert_total (letters xs) in
                if ((not (isAlpha y)) || (y `elem` xs')) then xs' else y :: xs'

initState : (x : String) -> BullsNCows (Running 6 (length (letters x)))
initState w = let xs = letters w in
                  MkG w _ [] (fromList (letters w))

-----------------------------------------------------------------------
-- RULES
-----------------------------------------------------------------------

data BullsNCowsRules : Effect where

     Guess : (x : Char) ->
             sig BullsNCowsRules Bool
                 (BullsNCows (Running (S g) (S w)))
                 (\inword =>
                        BullsNCows (case inword of
                             True => (Running (S g) w)
                             False => (Running g (S w))))

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

instance Handler BullsNCowsRules m where
    handle (MkG w g got []) Won k = k () (GameWon w)
    handle (MkG w Z got m) Lost k = k () (GameLost w)

    handle st Get k = k st st
    handle st (NewWord w) k = k () (initState w)

    handle (MkG w (S g) got m) (Guess x) k =
      case isElem x m of
           No _ => k False (MkG w _ got m)
           Yes p => k True (MkG w _ (x :: got) (shrink m p))

-----------------------------------------------------------------------
-- USER INTERFACE 
-----------------------------------------------------------------------

soRefl : So x -> (x = True)
soRefl Oh = Refl 

game : String -> Eff () [BULLSNCOWS (Running (S g) w), STDIO]
              [BULLSNCOWS NotRunning, STDIO]
game str {w=Z} = won 
game str {w=S _}
     = do putStrLn (show !get)
          putStr "Enter guess: "
          let guess = trim str
          case choose (not (guess == "")) of
               (Left p) => processGuess (strHead' guess (soRefl p))
               (Right p) => do putStrLn "Invalid input!"
                               game str
  where 
    processGuess : Char -> Eff () [BULLSNCOWS (Running (S g) (S w)), STDIO] 
                                  [BULLSNCOWS NotRunning, STDIO] 
    processGuess {g} c {w}
      = case !(guess c) of
             True => do putStrLn "Good guess!"
                        case w of
                             Z => won
                             (S k) => game (strTail str)
             False => do putStrLn "No, sorry"
                         case g of
                              Z => lost
                              (S k) => game (strTail str)

words : ?wlen 
words = with Vect ["idris","agda","haskell","miranda",
         "java","javascript","fortran","basic","racket",
         "coffeescript","rust","purescript","clean","links",
         "koka","cobol"]

wlen = proof search
               
runGame : String -> String -> Eff () [BULLSNCOWS NotRunning, RND, SYSTEM, STDIO]
                    runGame w tr = do srand !time
                                      new_word w
                                      game tr
                                      putStrLn (show !get)

-----------------------------------------------------------------------
-- SUBCODE
-----------------------------------------------------------------------

maybeIntToMaybeNat : Maybe Integer -> Maybe Nat
maybeIntToMaybeNat Nothing = Nothing
maybeIntToMaybeNat (Just x) = if (x >= 0)
                                  then Just (cast {to=Nat} x)
                                  else Nothing

getMaybeInt : String -> Maybe Integer
getMaybeInt str = if ( not (all isDigit (unpack str) ) )
                      then Nothing
                      else Just (cast str)

getNatFirstArg : List String -> Maybe Nat
getNatFirstArg xs = maybeIntToMaybeNat ( getMaybeInt ( fromMaybe "" (index' 1 xs) ) )

getRndExcept : List Integer -> Eff Integer [RND]
getRndExcept [] = rndInt 0 9
getRndExcept xs = do
    num <- rndInt 0 9
    if (elem num xs)
        then getRndExcept xs
        else pure num

getRndNumber : Eff (Integer, Integer, Integer, Integer) [RND]
getRndNumber = do
    n1 <- rndInt 1 9
    n2 <- getRndExcept [n1]
    n3 <- getRndExcept [n1, n2]
    n4 <- getRndExcept [n1, n2, n3]
    pure (n1, n2, n3, n4)

numToString : (Integer, Integer, Integer, Integer) -> String
numToString (d1, d2, d3, d4) = intToStr d1 ++ intToStr d2 ++
                               intToStr d3 ++ intToStr d4
    where
        intToStr : Integer -> String
        intToStr i = cast {to=String} i

printArgs : Eff () [BULLSNCOWS NotRunning, RND, SYSTEM, STDIO, EXCEPTION String]
printArgs = do  args <- getArgs
                if (length args /= 2)
                    then raise "Wrong number of arguments"
                    else do
                        let m_tries = getNatFirstArg args
                        printLn m_tries
                        if (m_tries == Nothing)
                            then raise "Provided argument is not a natural number"
                            else do
                                let tries = fromMaybe 0 m_tries
                                t <- time
                                srand t
                                (d1, d2, d3, d4) <- getRndNumber
                                let word = numToString (d1, d2, d3, d4)
                                try_word <- getStr
                                printLn try_word
                                printLn word
                                printLn args
                                printLn tries
                                runGame word try_word

main : IO ()
main = run printArgs
