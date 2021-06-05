{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances #-}
import Prelude hiding(EQ)
import System.Environment
import System.Exit
import Debug.Trace
import Data.List
import AST
import Data.Either
import Control.Monad(foldM)

-- 8. Dependently yped lang + MiniTT (sum types, recursive.
-- Fuck this, I'm going to copy the miniTT implementation from
-- cubicaltt!
