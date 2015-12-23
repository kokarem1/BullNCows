module Main

import Effects
import Effect.Exception
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
     GameWon  : (String, String) -> BullsNCows NotRunning
     GameLost : (String, String) -> BullsNCows NotRunning
     MkG      : (word : String) ->
                (gue: List Char) ->
                (gueS: String) ->
                (guesses : Nat) ->
                (got : List Char) ->
                (missing : Vect m Char) ->
                BullsNCows (Running guesses m)

instance Default (BullsNCows NotRunning) where
    default = Init

getStrings : (BullsNCows s) -> (String, String)
getStrings (GameWon (w,g)) = (w,g)
getStrings (GameLost (w,g)) = (w,g)
getStrings _ = ("","")

isWon : (BullsNCows s) -> Bool
isWon (GameWon _) = True
isWon _ = False

instance Show (BullsNCows s) where
    show Init = "Not ready yet"
    show (GameWon (w,g) ) = "You won! Successfully guessed " ++ w
    show (GameLost (w,g) ) = "You lost! The word was " ++ w
    show (MkG w gue gueS guesses got missing)
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
                if ({-(not (isAlpha y)) || -}(y `elem` xs')) then xs' else y :: xs'

initState : (x : String) -> (g : List Char) -> BullsNCows (Running 4 (length (letters x)))
initState w g = let xs = letters w in
                    MkG w g (pack g) _ [] (fromList (letters w))

-----------------------------------------------------------------------
-- RULES
-----------------------------------------------------------------------

data BullsNCowsRules : Effect where

     Guess : sig BullsNCowsRules Bool
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
               (g: List Char) ->
               sig BullsNCowsRules () h (BullsNCows (Running 4 (length (letters w))))

     Get  : sig BullsNCowsRules h h

BULLSNCOWS : GState -> EFFECT
BULLSNCOWS h = MkEff (BullsNCows h) BullsNCowsRules

guess : Eff Bool
        [BULLSNCOWS (Running (S g) (S w))]
        (\inword => [BULLSNCOWS (case inword of
                                True => Running (S g) w
                                False => Running g (S w))])
guess = call (Main.Guess)

won :  Eff () [BULLSNCOWS (Running g 0)] [BULLSNCOWS NotRunning]
won = call Won

lost : Eff () [BULLSNCOWS (Running 0 g)] [BULLSNCOWS NotRunning]
lost = call Lost

new_word : (w : String) -> (g : List Char) -> Eff () [BULLSNCOWS h] 
                                           [BULLSNCOWS (Running 4 (length (letters w)))]
new_word w g = call (NewWord w g)

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
    handle (MkG w gue gueS g got []) Won k = k () (GameWon (w,gueS))
    handle (MkG w gue gueS Z got m) Lost k = k () (GameLost (w,gueS))

    handle st Get k = k st st
    handle st (NewWord w g) k = k () (initState w g)

    handle (MkG w gue gueS (S g) got m) (Guess) k =
      case nonEmpty gue of
           Yes _ => let x = head gue in
                        case isElem x m of
                             No _ => k False (MkG w (tail gue) gueS _ got m)
                             Yes p => k True (MkG w (tail gue) gueS _ (x :: got) (shrink m p))
           No _ => k False (MkG w gue gueS _ got m)

-----------------------------------------------------------------------
-- USER INTERFACE 
-----------------------------------------------------------------------

soRefl : So x -> (x = True)
soRefl Oh = Refl 

game : Eff () [BULLSNCOWS (Running (S g) w), STDIO]
              [BULLSNCOWS NotRunning, STDIO]
game {w=Z} = won 
game {w=S _}
     = do 
          processGuess
  where 
    processGuess : Eff () [BULLSNCOWS (Running (S g) (S w)), STDIO] 
                          [BULLSNCOWS NotRunning, STDIO] 
    processGuess {g} {w}
      = case !(guess) of
             True => do 
                        case w of
                             Z => won
                             (S k) => game
             False => do 
                         case g of
                              Z => lost
                              (S k) => game

words : ?wlen 
words = with Vect ["idris","agda","haskell","miranda",
         "java","javascript","fortran","basic","racket",
         "coffeescript","rust","purescript","clean","links",
         "koka","cobol"]

wlen = proof search

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

runStep : String -> Nat -> Nat -> Eff () [BULLSNCOWS NotRunning, RND, SYSTEM, STDIO, EXCEPTION String]
runStep word
        tries
        counter
        = do
            if (counter >= tries)
                then putStrLn $ "You louse. The word was " ++ word ++ "\n"
                else do
                    putStrLn $ "Tries left: " ++ (show $ tries - counter) ++ "\n"
                    let try_word = unpack (substr 0 4 !getStr)
                    if (head' try_word == Just 'q')
                        then putStrLn $ "The word was " ++ word ++ ". Bye bye" ++ "\n"
                        else do
                               new_word word try_word
                               game
                               if (isWon !get)
                                   then putStrLn $ "Yes, that is it! You win!" ++ "\n"
                                   else do
                                          let (post_word, post_try) = getStrings !get
                                          let bCount = bullsCount post_word post_try
                                          let cCount = cowsCount post_word post_try
                                          putStrLn $ "Bulls: " ++ (show bCount) ++ "\n" ++ "Cows: " ++ (show cCount) ++ "\n"
                                          runStep word tries (S counter)

runGame : Eff () [BULLSNCOWS NotRunning, RND, SYSTEM, STDIO, EXCEPTION String]
runGame = do
            args <- getArgs
            if (length args /= 2)
                then raise "Wrong number of arguments"
                else do
                    let m_tries = getNatFirstArg args
                    if (m_tries == Nothing)
                        then raise "Provided argument is not a natural number"
                        else do
                            let tries = fromMaybe 0 m_tries
                            t <- time
                            srand t
                            (d1, d2, d3, d4) <- getRndNumber
                            let word = numToString (d1, d2, d3, d4)
                            runStep word tries Z

main : IO ()
main = run runGame

