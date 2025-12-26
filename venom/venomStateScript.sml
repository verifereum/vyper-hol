(*
 * Venom State Definition
 *
 * This theory defines the state model for Venom IR execution.
 * Venom is a register-based SSA IR targeting the EVM.
 * Uses types from verifereum.
 *)

Theory venomState
Ancestors
  vfmTypes vfmState

(* --------------------------------------------------------------------------
   Venom uses the same basic types as EVM (from verifereum):
   - bytes32 for 256-bit words
   - address for 160-bit addresses
   - byte for 8-bit values
   - storage for key-value storage
   -------------------------------------------------------------------------- *)

(* Variable environment maps variable names to 256-bit values *)
Type var_env = ``:string |-> bytes32``

(* --------------------------------------------------------------------------
   Execution Context (from EVM environment)

   This provides the environmental information needed for opcodes like
   CALLER, CALLVALUE, ADDRESS, etc.
   -------------------------------------------------------------------------- *)

Datatype:
  call_context = <|
    cc_caller : address;           (* Caller address (CALLER) *)
    cc_address : address;          (* Current contract address (ADDRESS) *)
    cc_callvalue : bytes32;        (* Value sent with call (CALLVALUE) *)
    cc_calldata : byte list;       (* Call data (CALLDATALOAD, etc.) *)
    cc_gas : num                   (* Remaining gas (GAS) *)
  |>
End

Datatype:
  tx_context = <|
    tc_origin : address;           (* Transaction origin (ORIGIN) *)
    tc_gasprice : bytes32;         (* Gas price (GASPRICE) *)
    tc_chainid : bytes32           (* Chain ID (CHAINID) *)
  |>
End

Datatype:
  block_context = <|
    bc_coinbase : address;         (* Block coinbase (COINBASE) *)
    bc_timestamp : bytes32;        (* Block timestamp (TIMESTAMP) *)
    bc_number : bytes32;           (* Block number (NUMBER) *)
    bc_prevrandao : bytes32;       (* Previous randao (PREVRANDAO) *)
    bc_gaslimit : bytes32;         (* Block gas limit (GASLIMIT) *)
    bc_basefee : bytes32;          (* Base fee (BASEFEE) *)
    bc_blobbasefee : bytes32;      (* Blob base fee (BLOBBASEFEE) *)
    bc_blockhash : num -> bytes32  (* Block hash lookup (BLOCKHASH) *)
  |>
End

(* --------------------------------------------------------------------------
   Operands - values that can be used as instruction arguments
   -------------------------------------------------------------------------- *)

Datatype:
  operand =
    Lit bytes32        (* Literal 256-bit value *)
  | Var string         (* Variable reference (SSA) *)
  | Label string       (* Basic block label reference *)
End

(* --------------------------------------------------------------------------
   Venom Execution State

   Venom operates at a higher level than raw EVM:
   - Register-based (SSA variables) instead of stack-based
   - Explicit control flow via basic blocks
   - Memory/storage semantics match EVM
   -------------------------------------------------------------------------- *)

Datatype:
  venom_state = <|
    vs_memory : byte list;           (* Memory as byte list (like verifereum) *)
    vs_storage : storage;            (* Contract storage *)
    vs_transient : storage;          (* Transient storage (EIP-1153) *)
    vs_vars : var_env;               (* SSA variable bindings *)
    vs_prev_bb : string option;      (* Previous basic block (for PHI resolution) *)
    vs_current_bb : string;          (* Current basic block label *)
    vs_inst_idx : num;               (* Instruction index within block *)
    vs_returndata : byte list;       (* Return data buffer *)
    vs_halted : bool;                (* Execution halted? *)
    vs_reverted : bool;              (* Execution reverted? *)
    vs_accounts : evm_accounts;      (* Account states for BALANCE, etc. *)
    vs_call_ctx : call_context;      (* Call context *)
    vs_tx_ctx : tx_context;          (* Transaction context *)
    vs_block_ctx : block_context     (* Block context *)
  |>
End

(* Default context values *)
Definition empty_call_context_def:
  empty_call_context = <|
    cc_caller := 0w;
    cc_address := 0w;
    cc_callvalue := 0w;
    cc_calldata := [];
    cc_gas := 0
  |>
End

Definition empty_tx_context_def:
  empty_tx_context = <|
    tc_origin := 0w;
    tc_gasprice := 0w;
    tc_chainid := 0w
  |>
End

Definition empty_block_context_def:
  empty_block_context = <|
    bc_coinbase := 0w;
    bc_timestamp := 0w;
    bc_number := 0w;
    bc_prevrandao := 0w;
    bc_gaslimit := 0w;
    bc_basefee := 0w;
    bc_blobbasefee := 0w;
    bc_blockhash := K 0w
  |>
End

(* Initial state for a function *)
Definition init_venom_state_def:
  init_venom_state entry_label = <|
    vs_memory := [];
    vs_storage := empty_storage;
    vs_transient := empty_storage;
    vs_vars := FEMPTY;
    vs_prev_bb := NONE;
    vs_current_bb := entry_label;
    vs_inst_idx := 0;
    vs_returndata := [];
    vs_halted := F;
    vs_reverted := F;
    vs_accounts := empty_accounts;
    vs_call_ctx := empty_call_context;
    vs_tx_ctx := empty_tx_context;
    vs_block_ctx := empty_block_context
  |>
End

(* --------------------------------------------------------------------------
   State Accessors and Updaters
   -------------------------------------------------------------------------- *)

(* Variable operations *)
Definition update_var_def:
  update_var x v s = s with vs_vars := s.vs_vars |+ (x, v)
End

Definition lookup_var_def:
  lookup_var x s = FLOOKUP s.vs_vars x
End

(* Memory operations - using verifereum-style byte list memory *)
Definition read_memory_def:
  read_memory offset size s =
    TAKE size (DROP offset s.vs_memory)
End

Definition write_memory_def:
  write_memory offset bytes s =
    let mem = s.vs_memory in
    let newmem = TAKE offset mem ++ bytes ++ DROP (offset + LENGTH bytes) mem in
    s with vs_memory := newmem
End

Definition expand_memory_def:
  expand_memory n s =
    s with vs_memory := s.vs_memory ++ REPLICATE n 0w
End

(* Expand memory if needed, then write bytes at offset *)
Definition write_memory_with_expansion_def:
  write_memory_with_expansion offset bytes s =
    let mem = s.vs_memory in
    let size = LENGTH bytes in
    let needed = (offset + size) - LENGTH mem in
    let expanded = if needed > 0 then mem ++ REPLICATE needed 0w else mem in
    let newmem = TAKE offset expanded ++ bytes ++ DROP (offset + size) expanded in
    s with vs_memory := newmem
End

(* Load a 32-byte word from memory (big-endian) *)
Definition mload_def:
  mload offset s =
    let bytes = TAKE 32 (DROP offset s.vs_memory ++ REPLICATE 32 0w) in
    word_of_bytes T (0w:bytes32) bytes
End

(* Store a 32-byte word to memory (big-endian) *)
Definition mstore_def:
  mstore offset (value:bytes32) s =
    let bytes = word_to_bytes value T in
    let mem = s.vs_memory in
    let needed = (offset + 32) - LENGTH mem in
    let expanded = if needed > 0 then mem ++ REPLICATE needed 0w else mem in
    s with vs_memory := TAKE offset expanded ++ bytes ++ DROP (offset + 32) expanded
End

(* Storage operations - using verifereum storage type *)
Definition sload_def:
  sload key s = lookup_storage key s.vs_storage
End

Definition sstore_def:
  sstore key value s =
    s with vs_storage := update_storage key value s.vs_storage
End

(* Transient storage operations *)
Definition tload_def:
  tload key s = lookup_storage key s.vs_transient
End

Definition tstore_def:
  tstore key value s =
    s with vs_transient := update_storage key value s.vs_transient
End

(* Control flow *)
Definition jump_to_def:
  jump_to lbl s = s with <|
    vs_prev_bb := SOME s.vs_current_bb;
    vs_current_bb := lbl;
    vs_inst_idx := 0
  |>
End

Definition next_inst_def:
  next_inst s = s with vs_inst_idx := s.vs_inst_idx + 1
End

(* Termination *)
Definition halt_state_def:
  halt_state s = s with vs_halted := T
End

Definition revert_state_def:
  revert_state s = s with <| vs_halted := T; vs_reverted := T |>
End

Definition set_returndata_def:
  set_returndata rd s = s with vs_returndata := rd
End

(* --------------------------------------------------------------------------
   Operand Evaluation
   -------------------------------------------------------------------------- *)

(* Evaluate an operand to a value (NONE if variable not defined) *)
Definition eval_operand_def:
  eval_operand (Lit v) s = SOME v /\
  eval_operand (Var x) s = lookup_var x s /\
  eval_operand (Label _) s = NONE
End

(* Get label from operand *)
Definition get_label_def:
  get_label (Label l) = SOME l /\
  get_label _ = NONE
End

(* Evaluate a list of operands *)
Definition eval_operands_def:
  eval_operands [] s = SOME [] /\
  eval_operands (op::ops) s =
    case eval_operand op s of
      NONE => NONE
    | SOME v =>
        case eval_operands ops s of
          NONE => NONE
        | SOME vs => SOME (v::vs)
End

