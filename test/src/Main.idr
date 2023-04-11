module Main

import GroupSolver
import Prim.Bits8
import Prim.Bits16
import Prim.Bits32
import Prim.Bits64
import Prim.Char
import Prim.Int8
import Prim.Int16
import Prim.Int32
import Prim.Int64
import Prim.Integer
import Prim.String
import Hedgehog

%default total

main : IO ()
main = test
  [ Bits8.props
  , Bits16.props
  , Bits32.props
  , Bits64.props
  , Char.props
  , Int8.props
  , Int16.props
  , Int32.props
  , Int64.props
  , Integer.props
  , String.props
  ]
