(* A context-sensitive operand-stack checker for final EVM bytecode.
   Known words survive PUSH, DUP and SWAP; all other results are unknown.
   Exhausted fuel rejects. CALL/CREATE successors include their eventual result. *)
Theory stackBoundDefs
Ancestors
  arithmetic list rich_list option pair finite_map words
  vfmTypes vfmOperation vfmContext
Libs
  wordsLib

Type abstract_stack = ``:num option list``;
Type stack_state = ``:num # abstract_stack``;

(* Stack effects of decoded EVM operations. DUP/SWAP are handled separately. *)
Definition bytecode_stack_io_def:
    bytecode_stack_io Stop = (0, 0)
  /\ bytecode_stack_io Add = (2, 1)
  /\ bytecode_stack_io Mul = (2, 1)
  /\ bytecode_stack_io Sub = (2, 1)
  /\ bytecode_stack_io Div = (2, 1)
  /\ bytecode_stack_io SDiv = (2, 1)
  /\ bytecode_stack_io Mod = (2, 1)
  /\ bytecode_stack_io SMod = (2, 1)
  /\ bytecode_stack_io AddMod = (3, 1)
  /\ bytecode_stack_io MulMod = (3, 1)
  /\ bytecode_stack_io Exp = (2, 1)
  /\ bytecode_stack_io SignExtend = (2, 1)
  /\ bytecode_stack_io LT = (2, 1)
  /\ bytecode_stack_io GT = (2, 1)
  /\ bytecode_stack_io SLT = (2, 1)
  /\ bytecode_stack_io SGT = (2, 1)
  /\ bytecode_stack_io Eq = (2, 1)
  /\ bytecode_stack_io IsZero = (1, 1)
  /\ bytecode_stack_io And = (2, 1)
  /\ bytecode_stack_io Or = (2, 1)
  /\ bytecode_stack_io XOr = (2, 1)
  /\ bytecode_stack_io Not = (1, 1)
  /\ bytecode_stack_io Byte = (2, 1)
  /\ bytecode_stack_io ShL = (2, 1)
  /\ bytecode_stack_io ShR = (2, 1)
  /\ bytecode_stack_io SAR = (2, 1)
  /\ bytecode_stack_io CLZ = (1, 1)
  /\ bytecode_stack_io Keccak256 = (2, 1)
  /\ bytecode_stack_io Address = (0, 1)
  /\ bytecode_stack_io Balance = (1, 1)
  /\ bytecode_stack_io Origin = (0, 1)
  /\ bytecode_stack_io Caller = (0, 1)
  /\ bytecode_stack_io CallValue = (0, 1)
  /\ bytecode_stack_io CallDataLoad = (1, 1)
  /\ bytecode_stack_io CallDataSize = (0, 1)
  /\ bytecode_stack_io CallDataCopy = (3, 0)
  /\ bytecode_stack_io CodeSize = (0, 1)
  /\ bytecode_stack_io CodeCopy = (3, 0)
  /\ bytecode_stack_io GasPrice = (0, 1)
  /\ bytecode_stack_io ExtCodeSize = (1, 1)
  /\ bytecode_stack_io ExtCodeCopy = (4, 0)
  /\ bytecode_stack_io ReturnDataSize = (0, 1)
  /\ bytecode_stack_io ReturnDataCopy = (3, 0)
  /\ bytecode_stack_io ExtCodeHash = (1, 1)
  /\ bytecode_stack_io BlockHash = (1, 1)
  /\ bytecode_stack_io CoinBase = (0, 1)
  /\ bytecode_stack_io TimeStamp = (0, 1)
  /\ bytecode_stack_io Number = (0, 1)
  /\ bytecode_stack_io PrevRandao = (0, 1)
  /\ bytecode_stack_io GasLimit = (0, 1)
  /\ bytecode_stack_io ChainId = (0, 1)
  /\ bytecode_stack_io SelfBalance = (0, 1)
  /\ bytecode_stack_io BaseFee = (0, 1)
  /\ bytecode_stack_io BlobHash = (1, 1)
  /\ bytecode_stack_io BlobBaseFee = (0, 1)
  /\ bytecode_stack_io Pop = (1, 0)
  /\ bytecode_stack_io MLoad = (1, 1)
  /\ bytecode_stack_io MStore = (2, 0)
  /\ bytecode_stack_io MStore8 = (2, 0)
  /\ bytecode_stack_io SLoad = (1, 1)
  /\ bytecode_stack_io SStore = (2, 0)
  /\ bytecode_stack_io Jump = (1, 0)
  /\ bytecode_stack_io JumpI = (2, 0)
  /\ bytecode_stack_io PC = (0, 1)
  /\ bytecode_stack_io MSize = (0, 1)
  /\ bytecode_stack_io Gas = (0, 1)
  /\ bytecode_stack_io JumpDest = (0, 0)
  /\ bytecode_stack_io TLoad = (1, 1)
  /\ bytecode_stack_io TStore = (2, 0)
  /\ bytecode_stack_io MCopy = (3, 0)
  /\ bytecode_stack_io (Push n ws) = (0, 1)
  /\ bytecode_stack_io (Dup n) = (n + 1, n + 2)
  /\ bytecode_stack_io (Swap n) = (n + 2, n + 2)
  /\ bytecode_stack_io (Log n) = (n + 2, 0)
  /\ bytecode_stack_io Create = (3, 1)
  /\ bytecode_stack_io Call = (7, 1)
  /\ bytecode_stack_io CallCode = (7, 1)
  /\ bytecode_stack_io Return = (2, 0)
  /\ bytecode_stack_io DelegateCall = (6, 1)
  /\ bytecode_stack_io Create2 = (4, 1)
  /\ bytecode_stack_io StaticCall = (6, 1)
  /\ bytecode_stack_io Revert = (2, 0)
  /\ bytecode_stack_io Invalid = (0, 0)
  /\ bytecode_stack_io SelfDestruct = (1, 0)
End

(* Known destinations are validated; an unknown destination fans out. *)
Definition bytecode_jump_targets_def:
  bytecode_jump_targets (parsed:num |-> opname) dests target =
    case target of
      NONE => dests
    | SOME pc => if FLOOKUP parsed pc = SOME JumpDest then [pc] else []
End

(* No successors means the instruction terminates or fails before pushing. *)
Definition bytecode_stack_successors_def:
  bytecode_stack_successors parsed dests (pc, stk:abstract_stack) =
    case FLOOKUP parsed pc of
      NONE => []
    | SOME op =>
      let next = pc + LENGTH (opcode op) in
      case op of
        Stop => []
      | Return => []
      | Revert => []
      | Invalid => []
      | SelfDestruct => []
      | Push n ws =>
          [(next, SOME (w2n (word_of_bytes_le (REVERSE ws):bytes32)) :: stk)]
      | Dup n => if n < LENGTH stk then [(next, EL n stk :: stk)] else []
      | Swap n =>
          if SUC n < LENGTH stk then
            [(next, [EL (SUC n) stk] ++ TAKE n (TL stk) ++
                    [HD stk] ++ DROP (n + 2) stk)]
          else []
      | Jump =>
          if NULL stk then [] else
            MAP (\dst. (dst, TL stk))
              (bytecode_jump_targets parsed dests (HD stk))
      | JumpI =>
          if LENGTH stk < 2 then [] else
            (next, DROP 2 stk) ::
            MAP (\dst. (dst, DROP 2 stk))
              (bytecode_jump_targets parsed dests (HD stk))
      | _ =>
          let (pops, pushes) = bytecode_stack_io op in
          if pops <= LENGTH stk then
            [(next, REPLICATE pushes NONE ++ DROP pops stk)]
          else []
End

(* The finite map indexes visited stacks by pc, avoiding comparisons at
   unrelated instructions. Fuel counts worklist removals, including repeats. *)
Definition bytecode_stack_closure_def:
  bytecode_stack_closure fuel limit parsed dests todo seen =
    case todo of
      [] => T
    | (pc, stk)::pending =>
      case fuel of
        0 => F
      | SUC remaining =>
        let old = case FLOOKUP seen pc of NONE => [] | SOME stacks => stacks in
        if MEM stk old then
          bytecode_stack_closure remaining limit parsed dests pending seen
        else LENGTH stk <= limit /\
          bytecode_stack_closure remaining limit parsed dests
            (bytecode_stack_successors parsed dests (pc, stk) ++ pending)
            (seen |+ (pc, stk :: old))
End

(* Checks a frame entering runtime bytecode at pc 0 with an empty stack. *)
Definition bytecode_stack_check_def:
  bytecode_stack_check fuel limit code =
    let parsed = parse_code 0 FEMPTY code in
    let dests = FILTER (\pc. FLOOKUP parsed pc = SOME JumpDest)
                       (GENLIST I (LENGTH code)) in
    bytecode_stack_closure fuel limit parsed dests [(0, [])] FEMPTY
End

(* A known abstract word describes exactly one concrete EVM word. *)
Definition bytecode_stack_describes_def:
  bytecode_stack_describes (abstract:abstract_stack) (concrete:bytes32 list) <=>
    LIST_REL (\a w. case a of NONE => T | SOME n => n = w2n w)
      abstract concrete
End
