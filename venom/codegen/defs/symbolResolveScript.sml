(*
 * Symbol Resolution and Bytecode Encoding
 *
 * Assembly → Bytecode (Stage 2).
 * Resolves labels to PC offsets, encodes assembly to EVM bytecode.
 *
 * Python uses fixed SYMBOL_SIZE = 2 for ALL label references.
 * No variable-width encoding, no fixpoint iteration needed.
 *
 * TOP-LEVEL:
 *   assemble — asm_inst list → byte list
 *   evm_opcode_byte — string → byte option
 *)

Theory symbolResolve
Ancestors
  planExec

(* =========================================================================
   EVM Opcode Encoding (as lookup table)
   ========================================================================= *)

Definition evm_opcode_table_def:
  evm_opcode_table : (string # byte) list = [
    ("STOP", 0x00w); ("ADD", 0x01w); ("MUL", 0x02w); ("SUB", 0x03w);
    ("DIV", 0x04w); ("SDIV", 0x05w); ("MOD", 0x06w); ("SMOD", 0x07w);
    ("ADDMOD", 0x08w); ("MULMOD", 0x09w); ("EXP", 0x0Aw);
    ("SIGNEXTEND", 0x0Bw);
    ("LT", 0x10w); ("GT", 0x11w); ("SLT", 0x12w); ("SGT", 0x13w);
    ("EQ", 0x14w); ("ISZERO", 0x15w);
    ("AND", 0x16w); ("OR", 0x17w); ("XOR", 0x18w); ("NOT", 0x19w);
    ("BYTE", 0x1Aw); ("SHL", 0x1Bw); ("SHR", 0x1Cw); ("SAR", 0x1Dw);
    ("SHA3", 0x20w);
    ("ADDRESS", 0x30w); ("BALANCE", 0x31w); ("ORIGIN", 0x32w);
    ("CALLER", 0x33w); ("CALLVALUE", 0x34w);
    ("CALLDATALOAD", 0x35w); ("CALLDATASIZE", 0x36w);
    ("CALLDATACOPY", 0x37w);
    ("CODESIZE", 0x38w); ("CODECOPY", 0x39w); ("GASPRICE", 0x3Aw);
    ("EXTCODESIZE", 0x3Bw); ("EXTCODECOPY", 0x3Cw);
    ("RETURNDATASIZE", 0x3Dw); ("RETURNDATACOPY", 0x3Ew);
    ("EXTCODEHASH", 0x3Fw);
    ("BLOCKHASH", 0x40w); ("COINBASE", 0x41w); ("TIMESTAMP", 0x42w);
    ("NUMBER", 0x43w); ("PREVRANDAO", 0x44w); ("GASLIMIT", 0x45w);
    ("CHAINID", 0x46w); ("SELFBALANCE", 0x47w); ("BASEFEE", 0x48w);
    ("BLOBHASH", 0x49w); ("BLOBBASEFEE", 0x4Aw);
    ("POP", 0x50w); ("MLOAD", 0x51w); ("MSTORE", 0x52w);
    ("MSTORE8", 0x53w);
    ("SLOAD", 0x54w); ("SSTORE", 0x55w);
    ("JUMP", 0x56w); ("JUMPI", 0x57w);
    ("MSIZE", 0x59w); ("GAS", 0x5Aw); ("JUMPDEST", 0x5Bw);
    ("TLOAD", 0x5Cw); ("TSTORE", 0x5Dw); ("MCOPY", 0x5Ew);
    ("PUSH0", 0x5Fw);
    (* DUP1..DUP16 *)
    ("DUP1", 0x80w); ("DUP2", 0x81w); ("DUP3", 0x82w); ("DUP4", 0x83w);
    ("DUP5", 0x84w); ("DUP6", 0x85w); ("DUP7", 0x86w); ("DUP8", 0x87w);
    ("DUP9", 0x88w); ("DUP10", 0x89w); ("DUP11", 0x8Aw);
    ("DUP12", 0x8Bw); ("DUP13", 0x8Cw); ("DUP14", 0x8Dw);
    ("DUP15", 0x8Ew); ("DUP16", 0x8Fw);
    (* SWAP1..SWAP16 *)
    ("SWAP1", 0x90w); ("SWAP2", 0x91w); ("SWAP3", 0x92w);
    ("SWAP4", 0x93w); ("SWAP5", 0x94w); ("SWAP6", 0x95w);
    ("SWAP7", 0x96w); ("SWAP8", 0x97w); ("SWAP9", 0x98w);
    ("SWAP10", 0x99w); ("SWAP11", 0x9Aw); ("SWAP12", 0x9Bw);
    ("SWAP13", 0x9Cw); ("SWAP14", 0x9Dw); ("SWAP15", 0x9Ew);
    ("SWAP16", 0x9Fw);
    (* LOG *)
    ("LOG0", 0xA0w); ("LOG1", 0xA1w); ("LOG2", 0xA2w);
    ("LOG3", 0xA3w); ("LOG4", 0xA4w);
    (* System *)
    ("CREATE", 0xF0w); ("CALL", 0xF1w); ("RETURN", 0xF3w);
    ("DELEGATECALL", 0xF4w); ("CREATE2", 0xF5w);
    ("STATICCALL", 0xFAw); ("REVERT", 0xFDw);
    ("INVALID", 0xFEw); ("SELFDESTRUCT", 0xFFw)
  ]
End

Definition evm_opcode_byte_def:
  evm_opcode_byte name = ALOOKUP evm_opcode_table name
End

(* =========================================================================
   Fixed Symbol Size
   Python: SYMBOL_SIZE = 2. All label references use exactly 2 bytes.
   PUSHLABEL → PUSH2 (3 bytes: 0x61 hi lo)
   DataLabel → 2 bytes (big-endian offset)
   ========================================================================= *)

Definition symbol_size_def:
  symbol_size = 2 : num
End

(* Pad a byte list to exactly n bytes (left-pad with zeros) *)
Definition pad_bytes_def:
  pad_bytes n (bytes : byte list) =
    if LENGTH bytes ≥ n then bytes
    else REPLICATE (n - LENGTH bytes) (0w : byte) ++ bytes
End

(* =========================================================================
   Instruction Size Computation (fixed widths)
   ========================================================================= *)

Definition asm_inst_size_def:
  asm_inst_size (AsmOp _) = 1 ∧
  asm_inst_size (AsmPush bytes) =
    (if bytes = [] then 1 else 1 + LENGTH bytes) ∧
  asm_inst_size (AsmPushLabel _) = 1 + symbol_size ∧
  asm_inst_size (AsmPushOfst _ _) = 1 + symbol_size ∧
  asm_inst_size (AsmLabel _) = 1 ∧
  asm_inst_size (AsmDataHeader _) = 0 ∧
  asm_inst_size (AsmDataItem bytes) = LENGTH bytes ∧
  asm_inst_size (AsmDataLabel _) = symbol_size
End

(* =========================================================================
   Label Offset Computation (single pass, fixed sizes)
   ========================================================================= *)

Definition compute_label_offsets_def:
  compute_label_offsets asm =
    FOLDL (λ(pc : num, labels : (string, num) fmap) inst.
      let labels' =
        case inst of
          AsmLabel lbl => labels |+ (lbl, pc)
        | AsmDataHeader lbl => labels |+ (lbl, pc)
        | _ => labels in
      (pc + asm_inst_size inst, labels'))
    (0, FEMPTY) asm
End

(* =========================================================================
   Bytecode Encoding
   ========================================================================= *)

Definition encode_inst_def:
  encode_inst offsets (AsmOp name) =
    (case evm_opcode_byte name of
      SOME b => [b]
    | NONE => [] : byte list) ∧
  encode_inst offsets (AsmPush []) = [0x5Fw] ∧
  encode_inst offsets (AsmPush bytes) =
    (n2w (0x5F + LENGTH bytes) : byte) :: bytes ∧
  encode_inst offsets (AsmPushLabel lbl) =
    (case FLOOKUP offsets lbl of
      SOME off =>
        let bytes = pad_bytes symbol_size (encode_num_bytes off) in
        (0x61w : byte) :: bytes   (* PUSH2 = 0x5F + 2 = 0x61 *)
    | NONE => (0x61w : byte) :: REPLICATE symbol_size (0w : byte)) ∧
  encode_inst offsets (AsmPushOfst lbl delta) =
    (case FLOOKUP offsets lbl of
      SOME off =>
        let bytes = pad_bytes symbol_size (encode_num_bytes (off + delta)) in
        (0x61w : byte) :: bytes
    | NONE => (0x61w : byte) :: REPLICATE symbol_size (0w : byte)) ∧
  encode_inst offsets (AsmLabel _) = [0x5Bw] ∧
  encode_inst offsets (AsmDataHeader _) = [] ∧
  encode_inst offsets (AsmDataItem bytes) = bytes ∧
  encode_inst offsets (AsmDataLabel lbl) =
    (case FLOOKUP offsets lbl of
      SOME off => pad_bytes symbol_size (encode_num_bytes off)
    | NONE => REPLICATE symbol_size (0w : byte))
End

(* =========================================================================
   Byte Offset → Instruction Index (inverse of layout)
   ========================================================================= *)

(* Maps byte offsets to instruction indices. Companion to
   compute_label_offsets; both use asm_inst_size. *)
Definition build_offset_to_pc_def:
  build_offset_to_pc prog =
    FST (FOLDL (λ(m, off) (i, inst).
      (m |+ (off, i), off + asm_inst_size inst))
    (FEMPTY : (num, num) fmap, 0n)
    (MAPi (λi inst. (i, inst)) prog))
End

(* =========================================================================
   Top-Level Assembly
   ========================================================================= *)

Definition assemble_def:
  assemble asm =
    let (_, offsets) = compute_label_offsets asm in
    FLAT (MAP (encode_inst offsets) asm) : byte list
End
