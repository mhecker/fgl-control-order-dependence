{-# LANGUAGE TemplateHaskell #-}
module Program.Properties.NameOfFunction where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

pr :: Name -> ExpQ
pr n = [| putStrLn ( $(lift (nameBase n ++ " = ")) ++ show $(varE n) ) |]
