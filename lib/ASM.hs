{-# LANGUAGE UndecidableInstances #-}
-- | This module aims to provide a type-safe Haskell representation of
-- x86 assembly instructions. The goal is that any assembly file
-- representable by these types will assemble without error.
module ASM where

import Control.Monad
import Control.Monad.Trans
import Data.Kind
import Data.List
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word
import GHC.TypeLits
import System.Exit
import System.Process
import Data.HList hiding (Label)

import Term

-- | Available register sizes
data RegSize = R8 | R16 | R32 | R64
  deriving Show

-- | Available sizes for displacement vaules in memory addressing
data Displacement = D0 | D8 | D16 | D32

-- | Available scale factors for memory addressing
data Scale = S1 | S2 | S4 | S8
  deriving Show

data Label = L Text
  deriving Show

-- | Memory addresses, indexed by target size.
data M (a :: RegSize) where
  -- TODO: ESP not allowed as index register
  -- TODO: how do sizes of targets affect sizes of base/index registers?
  Addr :: forall (d :: Displacement) size a. Show (DispWord d)
    => (R size) -> Maybe (R size, Scale) -> DispWord d -> M size

  Label :: Label -> M size
deriving instance Show (M size)

data Addr (a :: RegSize) where
  AbsGP :: R a -> Addr a
  AbsPtr :: Label -> Addr R32
  Rel :: forall (d :: Displacement) (a :: RegSize). Show (DispWord d) => DispWord d -> Addr a
deriving instance Show (RegWord a) => Show (Addr a)

-- | Registers, indexed by size.
data R (a :: RegSize) where
  -- General-purpose
  RAX, RBX, RCX, RDX :: R R64
  EAX, EBX, ECX, EDX :: R R32
  AX,  BX,  CX,  DX  :: R R16
  AH,  BH,  CH,  DH  :: R R8
  AL,  BL,  CL,  DL  :: R R8

  -- Special-purpose
  RSI, RDI, RSP, RBP :: R R64
  ESI, EDI, ESP, EBP :: R R32
deriving instance Show (R size)

-- | Immediate values, indexed by size.
data I (a :: RegSize) where
  I :: forall (size :: RegSize). RegWord size -> I size
deriving instance Show (RegWord size) => Show (I size)

-- | Convert a register size into a Haskell type of the given size.
type family RegWord (r :: RegSize) = res where
  RegWord R8 = Word8
  RegWord R16 = Word16
  RegWord R32 = Word32
  RegWord R64 = Word64

-- NOTE: type family dependency used for inference of size from () argument to Addr.
-- | Convert a displacement size into a Haskell type of the given size.
type family DispWord (r :: Displacement) = (res :: Type) | res -> r where
  DispWord D0 = ()
  DispWord D8 = Word8
  DispWord D16 = Word16
  DispWord D32 = Word32

-- | @RMI@ is either a register, a memory location, or an immediate
-- value.  It can only be a memeory value if @mem@ is @0@. This allows
-- instructions to limiit the number of memory-accessing arguments.
-- It can only be an immediate value if @imm@ is @True@.
data RMI (mem :: Nat) (imm :: Bool) (size :: RegSize) :: Type where
  Reg :: R size -> RMI n b size
  Mem :: M size -> RMI 0 b size
  Imm :: I size -> RMI n 'True size
deriving instance Show (RegWord size) => Show (RMI n b size)

data JumpCond = ECXZ | E | Z
  deriving Show

--  NOTE: info from Intel Architectures Software Developer's Manual
-- | Assembly instructions.
data Inst where
  -- ADD dest src will store the result of src+dest into dest.
  -- Max 1 argument can be a memory location.
  -- The src can be an immediate value.
  ADD :: forall mem size. Show (RegWord size)
    => (RMI mem 'False size) -> (RMI (mem-1) 'True size) -> Inst

  -- MOV dest src will move src into dest.
  -- The src can be an immediate value.
  MOV :: Show (RegWord size) => (RMI 0 'False size) -> (RMI 0 'True size) -> Inst

  J :: Show (RegWord a) => JumpCond -> Addr a -> Inst

  LAB :: Label -> Inst -> Inst

  NOP :: Inst
deriving instance Show Inst

-- | Multiple assembly instructions.
data Instructions where
  Instructions :: forall (ctx :: [Maybe Label]). HList (Map Inst LabelCtx) -> Instructions
deriving instance Show Instructions

type family Map (f :: a -> b) (x :: [a]) :: [b]  where
  Map f (LabelCtx '[]) = '[]

{-
type family Insts (ctx :: LabelCtx) where
  Insts '[] = HNil
  Insts ('Nothing ': ctx) = (Inst Nothing
-}

data LabelCtx = LabelCtx [Maybe Label]
  deriving Show

-- | The @ASM@ class is for types which can be printed to form valid
-- assembly code.
class ASM a where
  toAsm :: a -> Text

instance ASM (R size) where
  toAsm = T.toLower . T.pack . show

instance ASM (M size) where
  --TODO: asm scale and displacement
  toAsm (Addr reg _ _) = "[" <> toAsm reg <> "]"

instance Show (RegWord size) => ASM (RMI n b size) where
  toAsm (Reg reg) = toAsm reg
  toAsm (Mem mem) = toAsm mem
  toAsm (Imm imm) = toAsm imm

instance Show (RegWord size) => ASM (I size) where
  toAsm (I word) = T.pack $ show word

instance ASM Label where
  toAsm (L t) = t

instance ASM JumpCond where
  toAsm = T.toLower . T.pack . show

instance ASM (Addr size) where
  toAsm (AbsGP r) = toAsm r
  toAsm (AbsPtr l) = toAsm l
  --toAsm (Rel disp) = toAsm disp

-- TODO: write generics for this?
instance ASM Inst where
  toAsm (ADD dest src) = "\tadd " <> toAsm dest <> ", " <> toAsm src
  toAsm (MOV dest src) = "\tmov " <> toAsm dest <> ", " <> toAsm src
  toAsm NOP = "\tnop"
  toAsm (LAB l i) = toAsm l <> ":" <> toAsm i
  toAsm (J c l) = "\tj" <> toAsm c <> " " <> toAsm l

instance ASM Instructions where
  toAsm (Instructions is) = T.concat $ (<> ["\n"]) $ intersperse "\n" $ (map toAsm is)


testInst :: Instructions
testInst = Instructions
  [ MOV (Reg EAX) (Imm (I 12))
  , LAB (L "fooo") $ ADD (Reg EAX) (Reg EAX)
  , MOV (Reg EBX) (Reg EAX)
  , NOP
  , ADD (Reg EBX) (Mem (Addr ECX Nothing ())) -- No address offset
  , ADD (Reg EDX) (Mem (Addr ECX (Just (EDX, S4)) (6 :: Word8))) -- 8-bit address offset of 6
  , J Z (AbsPtr (L "fooo"))
  ]

-- | Assemble instructions using nasm.
assemble :: (MonadPlus m, MonadIO m) => Instructions -> m ()
assemble is = do
  liftIO $ writeFile "tmp.asm" (T.unpack $ toAsm is)
  liftIO (system "nasm tmp.asm -o tmp.out") >>= \case
    ExitSuccess -> return ()
    ExitFailure _ -> mzero

{-
TODO:
- Rename RMI to operand
- Generics for ASM instances (instructions of any number and type of operands)
- More instructions
- Labels (maybe with a context) and addresses
- Non-instruction features (such as reserved memory, globals, etc.)
- Calling functions
-}
