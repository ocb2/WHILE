import WHILE

import System.Environment
import System.Exit
import System.IO

main :: IO ()
main = do
    args <- getArgs

    if (length args /= 2 || ((args !! 0) /= "interpret" &&
                             (args !! 0) /= "compile"))
        then do
            hPutStrLn stderr usage
            exitWith (ExitFailure 1)
        else return ()

    p <- readFile (args !! 1)

    case runParseTerms p of
        Nothing -> do
            hPutStrLn stderr "Syntax error"
            exitWith (ExitFailure 2)
        Just p' -> case (args !! 0) of
            "interpret" -> mapM_ (putStrLn . show) (snd (interpret p'))
            "compile" -> (putStrLn . show) (compile p')

    exitWith ExitSuccess

usage = "usage: ./WHILE interpret <path>\n       ./WHILE compile   <path>"