
import NDProver.Datatypes (Formula, Sequent(..), readSequent)
import NDProver.Combine

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO


data Flag = Help
    deriving (Eq, Show)

help :: String
help = unlines
  [ "Usage: ndprover [-h]"
  , ""
  , "Takes a propositional logic sequent from input and tries to prove it"
  , "and find a contradiction simultaneously."
  , ""
  , "Sequents have the following form: P, ..., P |- C"
  , "Where P are premises and C are conclusions, both propositions."
  , ""
  , "Supported propositions are:"
  , "  P & Q    Conjuction of P and Q."
  , "  P | Q    Disjuction of P and Q."
  , "  P -> Q   P implies Q."
  , "  ~P       Negation of P"
  , "  _        Absurdity."
  , "  x        Propositon variable. Can be any combination"
  , "           of symbols a-z, A-Z, 0-9."
  ]

flags :: [OptDescr Flag]
flags =
      [ Option ['h'] ["help"] (NoArg Help) "Print help page and exit."
      ]

parse :: [String] -> IO ([Flag], [String])
parse argv = case getOpt Permute flags argv of
    (args, fs, []) -> do
        if Help `elem` args
            then do hPutStrLn stderr (usageInfo help flags)
                    exitWith ExitSuccess
            else return (args, fs)
    (_, _, errs) -> do
        hPutStrLn stderr (concat errs ++ usageInfo help flags)
        exitWith (ExitFailure 1)

maybeCrash :: String -> Maybe a -> IO a
maybeCrash msg (Just a) = return a
maybeCrash msg Nothing  =
  do putStrLn msg
     exitWith (ExitFailure 1)

main :: IO ()
main = do
    getArgs >>= parse
    line <- getLine
    sequent <- maybeCrash "Error: Cannot parse sequent." (readSequent line)
    let Sequent ps c = sequent
    r <- proveFormal ps c
    putStrLn r
