module Main where

seek :: String -> String
seek ('{':'-':'<':'!':'-':'}':s) = "     " ++ hide True s
seek ('{':'-':'<':'-':'}':s) = hide False s
seek (c : s) = c : seek s
seek [] = []

hide :: Bool -> String -> String
hide True ('{':'-':'>':'-':'}':s) = "     " ++ seek s
hide False ('{':'-':'>':'-':'}':s) = seek s
hide True (c : s) = ' ' : hide True s
hide False (c : s) = hide False s
hide _ [] = []

main :: IO ()
main = interact seek
