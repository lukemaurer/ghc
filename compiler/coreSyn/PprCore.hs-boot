{-# OPTIONS_GHC -fno-warn-orphans #-}

module PprCore () where

import Outputable
import Var

instance OutputableBndr Var