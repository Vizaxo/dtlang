module ASM where

import qualified Data.Text as T
import Data.Text (Text)
import Data.List

import Term
import Types

data RegSize = R8 | R16 | R32 | R64
  deriving Show

data M (a :: RegSize) where
  RegAddr :: (R a) -> M size
deriving instance Show (M size)

data R (a :: RegSize) where
  EAX :: R R32
  EBX :: R R32
  ECX :: R R32
  EDX :: R R32
  ESI :: R R32
  EDI :: R R32
  ESP :: R R32
  EBP :: R R32
  AX :: R R16
  BX :: R R16
  CX :: R R16
  DX :: R R16
  AH :: R R8
  BH :: R R8
  CH :: R R8
  DH :: R R8
  AL :: R R8
  BL :: R R8
  CL :: R R8
  DL :: R R8
deriving instance Show (R size)

data RM size = RMReg (R size) | RMMem (M size)
  deriving Show

data Inst
  = ADD32 (R R32) (RM R32)
  deriving Show

data Instructions = Instructions [Inst]

testInst :: Instructions
testInst = Instructions [ADD32 EAX (RMReg EAX), ADD32 EBX (RMMem (RegAddr ECX))]

class ASM a where
  toAsm :: a -> Text

instance ASM (R size) where
  toAsm = T.toLower . T.pack . show

instance ASM (M size) where
  toAsm (RegAddr reg) = "[" <> toAsm reg <> "]"

instance ASM (RM size) where
  toAsm (RMReg reg) = toAsm reg
  toAsm (RMMem mem) = toAsm mem

instance ASM Inst where
  toAsm (ADD32 r32 rm32) = "add " <> toAsm r32 <> " " <> toAsm rm32

instance ASM Instructions where
  toAsm (Instructions is) = T.concat $ intersperse "\n" $ (map toAsm is)
