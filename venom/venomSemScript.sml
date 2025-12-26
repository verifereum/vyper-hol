(*
 * Venom Semantics
 *
 * This theory defines the operational semantics for Venom IR execution.
 * It includes the effects system and instruction stepping.
 *)

Theory venomSem
Ancestors
  venomState venomInst keccak

(* --------------------------------------------------------------------------
   Effects System

   Effects track what state an instruction reads or writes.
   This is crucial for optimization passes (CSE, DCE, reordering).
   -------------------------------------------------------------------------- *)

Datatype:
  effect =
    | Eff_STORAGE
    | Eff_TRANSIENT
    | Eff_MEMORY
    | Eff_MSIZE
    | Eff_IMMUTABLES
    | Eff_RETURNDATA
    | Eff_LOG
    | Eff_BALANCE
    | Eff_EXTCODE
End

(* Effects as a set *)
Type effects = ``:effect set``

Definition empty_effects_def:
  empty_effects : effects = {}
End

Definition all_effects_def:
  all_effects : effects =
    {Eff_STORAGE; Eff_TRANSIENT; Eff_MEMORY; Eff_MSIZE;
     Eff_IMMUTABLES; Eff_RETURNDATA; Eff_LOG; Eff_BALANCE; Eff_EXTCODE}
End

(* Read effects for each opcode *)
Definition read_effects_def:
  read_effects SLOAD = {Eff_STORAGE} /\
  read_effects TLOAD = {Eff_TRANSIENT} /\
  read_effects ILOAD = {Eff_IMMUTABLES} /\
  read_effects MLOAD = {Eff_MEMORY} /\
  read_effects MCOPY = {Eff_MEMORY} /\
  read_effects CALL = all_effects /\
  read_effects DELEGATECALL = all_effects /\
  read_effects STATICCALL = all_effects /\
  read_effects CREATE = all_effects /\
  read_effects CREATE2 = all_effects /\
  read_effects INVOKE = all_effects /\
  read_effects RETURNDATASIZE = {Eff_RETURNDATA} /\
  read_effects RETURNDATACOPY = {Eff_RETURNDATA} /\
  read_effects BALANCE = {Eff_BALANCE} /\
  read_effects SELFBALANCE = {Eff_BALANCE} /\
  read_effects EXTCODECOPY = {Eff_EXTCODE} /\
  read_effects EXTCODESIZE = {Eff_EXTCODE} /\
  read_effects EXTCODEHASH = {Eff_EXTCODE} /\
  read_effects SELFDESTRUCT = {Eff_BALANCE} /\
  read_effects LOG = {Eff_MEMORY} /\
  read_effects REVERT = {Eff_MEMORY} /\
  read_effects SHA3 = {Eff_MEMORY} /\
  read_effects SHA3_64 = {Eff_MEMORY} /\
  read_effects MSIZE = {Eff_MSIZE} /\
  read_effects RETURN = {Eff_MEMORY} /\
  read_effects _ = empty_effects
End

(* Write effects for each opcode *)
Definition write_effects_def:
  write_effects SSTORE = {Eff_STORAGE} /\
  write_effects TSTORE = {Eff_TRANSIENT} /\
  write_effects MSTORE = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects ISTORE = {Eff_IMMUTABLES; Eff_MSIZE} /\
  write_effects CALL = all_effects DIFF {Eff_IMMUTABLES} /\
  write_effects DELEGATECALL = all_effects DIFF {Eff_IMMUTABLES} /\
  write_effects STATICCALL = {Eff_MEMORY; Eff_RETURNDATA; Eff_MSIZE} /\
  write_effects CREATE = all_effects DIFF {Eff_MEMORY; Eff_IMMUTABLES} /\
  write_effects CREATE2 = all_effects DIFF {Eff_MEMORY; Eff_IMMUTABLES} /\
  write_effects INVOKE = all_effects /\
  write_effects LOG = {Eff_LOG} /\
  write_effects DLOADBYTES = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects DLOAD = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects RETURNDATACOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects CALLDATACOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects CODECOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects EXTCODECOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects MCOPY = {Eff_MEMORY; Eff_MSIZE} /\
  write_effects _ = empty_effects
End

(* Check if two instructions can be reordered *)
Definition effects_independent_def:
  effects_independent op1 op2 <=>
    DISJOINT (write_effects op1) (read_effects op2 UNION write_effects op2) /\
    DISJOINT (write_effects op2) (read_effects op1 UNION write_effects op1)
End

(* --------------------------------------------------------------------------
   Arithmetic/Logic Operations (using bytes32 = 256 word)
   -------------------------------------------------------------------------- *)

(* Division with zero check *)
Definition safe_div_def:
  safe_div (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else x // y
End

Definition safe_mod_def:
  safe_mod (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else word_mod x y
End

(* Signed division *)
Definition safe_sdiv_def:
  safe_sdiv (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else x / y
End

Definition safe_smod_def:
  safe_smod (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else word_rem x y
End

(* Modular arithmetic *)
Definition addmod_def:
  addmod (a:bytes32) (b:bytes32) (n:bytes32) : bytes32 =
    if n = 0w then 0w else n2w ((w2n a + w2n b) MOD w2n n)
End

Definition mulmod_def:
  mulmod (a:bytes32) (b:bytes32) (n:bytes32) : bytes32 =
    if n = 0w then 0w else n2w ((w2n a * w2n b) MOD w2n n)
End

(* Boolean to word *)
Definition bool_to_word_def:
  bool_to_word T = (1w:bytes32) /\
  bool_to_word F = (0w:bytes32)
End

(* --------------------------------------------------------------------------
   Execution Result Type
   -------------------------------------------------------------------------- *)

Datatype:
  exec_result =
    | OK venom_state              (* Normal continuation *)
    | Halt venom_state            (* Normal termination *)
    | Revert venom_state          (* Revert termination *)
    | Error string                (* Execution error *)
End

(* --------------------------------------------------------------------------
   PHI Node Resolution

   PHI nodes select a value based on which predecessor block we came from.
   Format: %out = phi @pred1, %val1, @pred2, %val2, ...
   -------------------------------------------------------------------------- *)

(* Find the value for a PHI based on predecessor block *)
Definition resolve_phi_def:
  resolve_phi prev_bb [] = NONE /\
  resolve_phi prev_bb [_] = NONE /\
  resolve_phi prev_bb (Label lbl :: val_op :: rest) =
    (if lbl = prev_bb then SOME val_op else resolve_phi prev_bb rest) /\
  resolve_phi prev_bb (_ :: _ :: rest) = resolve_phi prev_bb rest
End

(* --------------------------------------------------------------------------
   Instruction Semantics
   -------------------------------------------------------------------------- *)

(* Execute a binary arithmetic operation *)
Definition exec_binop_def:
  exec_binop f inst s =
    case inst.inst_operands of
      [op1; op2] =>
        (case (eval_operand op1 s, eval_operand op2 s) of
          (SOME v1, SOME v2) =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v1 v2) s)
            | _ => Error "binop requires single output")
        | _ => Error "undefined operand")
    | _ => Error "binop requires 2 operands"
End

(* Execute a unary operation *)
Definition exec_unop_def:
  exec_unop f inst s =
    case inst.inst_operands of
      [op1] =>
        (case eval_operand op1 s of
          SOME v =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v) s)
            | _ => Error "unop requires single output")
        | NONE => Error "undefined operand")
    | _ => Error "unop requires 1 operand"
End

(* Execute a ternary modular operation *)
Definition exec_modop_def:
  exec_modop f inst s =
    case inst.inst_operands of
      [op1; op2; op3] =>
        (case (eval_operand op1 s, eval_operand op2 s, eval_operand op3 s) of
          (SOME v1, SOME v2, SOME v3) =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v1 v2 v3) s)
            | _ => Error "modop requires single output")
        | _ => Error "undefined operand")
    | _ => Error "modop requires 3 operands"
End

(* Step a single instruction *)
Definition step_inst_def:
  step_inst inst s =
    case inst.inst_opcode of
    (* Arithmetic *)
    | ADD => exec_binop word_add inst s
    | SUB => exec_binop word_sub inst s
    | MUL => exec_binop word_mul inst s
    | Div => exec_binop safe_div inst s
    | Mod => exec_binop safe_mod inst s
    | SDIV => exec_binop safe_sdiv inst s
    | SMOD => exec_binop safe_smod inst s
    | ADDMOD => exec_modop addmod inst s
    | MULMOD => exec_modop mulmod inst s

    (* Comparison *)
    | EQ => exec_binop (\x y. bool_to_word (x = y)) inst s
    | LT => exec_binop (\x y. bool_to_word (w2n x < w2n y)) inst s
    | GT => exec_binop (\x y. bool_to_word (w2n x > w2n y)) inst s
    | SLT => exec_binop (\x y. bool_to_word (word_lt x y)) inst s
    | SGT => exec_binop (\x y. bool_to_word (word_gt x y)) inst s
    | ISZERO => exec_unop (\x. bool_to_word (x = 0w)) inst s

    (* Bitwise *)
    | AND => exec_binop word_and inst s
    | OR => exec_binop word_or inst s
    | XOR => exec_binop word_xor inst s
    | NOT => exec_unop word_1comp inst s
    | SHL => exec_binop (\n w. word_lsl w (w2n n)) inst s
    | SHR => exec_binop (\n w. word_lsr w (w2n n)) inst s
    | SAR => exec_binop (\n w. word_asr w (w2n n)) inst s

    (* Memory *)
    | MLOAD =>
        (case inst.inst_operands of
          [op1] =>
            (case eval_operand op1 s of
              SOME addr =>
                (case inst.inst_outputs of
                  [out] => OK (update_var out (mload (w2n addr) s) s)
                | _ => Error "mload requires single output")
            | NONE => Error "undefined operand")
        | _ => Error "mload requires 1 operand")

    | MSTORE =>
        (case inst.inst_operands of
          [op_val; op_addr] =>
            (case (eval_operand op_val s, eval_operand op_addr s) of
              (SOME value, SOME addr) => OK (mstore (w2n addr) value s)
            | _ => Error "undefined operand")
        | _ => Error "mstore requires 2 operands")

    (* Storage *)
    | SLOAD =>
        (case inst.inst_operands of
          [op1] =>
            (case eval_operand op1 s of
              SOME key =>
                (case inst.inst_outputs of
                  [out] => OK (update_var out (sload key s) s)
                | _ => Error "sload requires single output")
            | NONE => Error "undefined operand")
        | _ => Error "sload requires 1 operand")

    | SSTORE =>
        (case inst.inst_operands of
          [op_val; op_key] =>
            (case (eval_operand op_val s, eval_operand op_key s) of
              (SOME value, SOME key) => OK (sstore key value s)
            | _ => Error "undefined operand")
        | _ => Error "sstore requires 2 operands")

    (* Transient storage *)
    | TLOAD =>
        (case inst.inst_operands of
          [op1] =>
            (case eval_operand op1 s of
              SOME key =>
                (case inst.inst_outputs of
                  [out] => OK (update_var out (tload key s) s)
                | _ => Error "tload requires single output")
            | NONE => Error "undefined operand")
        | _ => Error "tload requires 1 operand")

    | TSTORE =>
        (case inst.inst_operands of
          [op_val; op_key] =>
            (case (eval_operand op_val s, eval_operand op_key s) of
              (SOME value, SOME key) => OK (tstore key value s)
            | _ => Error "undefined operand")
        | _ => Error "tstore requires 2 operands")

    (* Control flow - JMP *)
    | JMP =>
        (case inst.inst_operands of
          [Label lbl] => OK (jump_to lbl s)
        | _ => Error "jmp requires label operand")

    (* Control flow - JNZ (conditional) *)
    | JNZ =>
        (case inst.inst_operands of
          [cond_op; Label if_nonzero; Label if_zero] =>
            (case eval_operand cond_op s of
              SOME cond =>
                if cond <> 0w then OK (jump_to if_nonzero s)
                else OK (jump_to if_zero s)
            | NONE => Error "undefined condition")
        | _ => Error "jnz requires cond and 2 labels")

    (* Termination *)
    | STOP => Halt (halt_state s)
    | RETURN => Halt (halt_state s)
    | REVERT => Revert (revert_state s)
    | SINK => Halt (halt_state s)

    (* Assertions *)
    | ASSERT =>
        (case inst.inst_operands of
          [cond_op] =>
            (case eval_operand cond_op s of
              SOME cond =>
                if cond = 0w then Revert (revert_state s)
                else OK s
            | NONE => Error "undefined operand")
        | _ => Error "assert requires 1 operand")

    | ASSERT_UNREACHABLE =>
        (case inst.inst_operands of
          [cond_op] =>
            (case eval_operand cond_op s of
              SOME cond =>
                if cond <> 0w then Halt (halt_state s)
                else OK s
            | NONE => Error "undefined operand")
        | _ => Error "assert_unreachable requires 1 operand")

    (* SSA - PHI node *)
    | PHI =>
        (case inst.inst_outputs of
          [out] =>
            (case s.vs_prev_bb of
              NONE => Error "phi at entry block"
            | SOME prev =>
                (case resolve_phi prev inst.inst_operands of
                  NONE => Error "phi: no matching predecessor"
                | SOME val_op =>
                    (case eval_operand val_op s of
                      SOME v => OK (update_var out v s)
                    | NONE => Error "phi: undefined operand")))
        | _ => Error "phi requires single output")

    (* SSA - ASSIGN *)
    | ASSIGN =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([op1], [out]) =>
            (case eval_operand op1 s of
              SOME v => OK (update_var out v s)
            | NONE => Error "undefined operand")
        | _ => Error "assign requires 1 operand and single output")

    (* NOP *)
    | NOP => OK s

    (* Environment - Call context *)
    | CALLER =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (w2w s.vs_call_ctx.cc_caller) s)
        | _ => Error "caller requires single output")

    | ADDRESS =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (w2w s.vs_call_ctx.cc_address) s)
        | _ => Error "address requires single output")

    | CALLVALUE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_call_ctx.cc_callvalue s)
        | _ => Error "callvalue requires single output")

    | GAS =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (n2w s.vs_call_ctx.cc_gas) s)
        | _ => Error "gas requires single output")

    (* Environment - Transaction context *)
    | ORIGIN =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (w2w s.vs_tx_ctx.tc_origin) s)
        | _ => Error "origin requires single output")

    | GASPRICE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_tx_ctx.tc_gasprice s)
        | _ => Error "gasprice requires single output")

    | CHAINID =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_tx_ctx.tc_chainid s)
        | _ => Error "chainid requires single output")

    (* Environment - Block context *)
    | COINBASE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (w2w s.vs_block_ctx.bc_coinbase) s)
        | _ => Error "coinbase requires single output")

    | TIMESTAMP =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_block_ctx.bc_timestamp s)
        | _ => Error "timestamp requires single output")

    | NUMBER =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_block_ctx.bc_number s)
        | _ => Error "number requires single output")

    | PREVRANDAO =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_block_ctx.bc_prevrandao s)
        | _ => Error "prevrandao requires single output")

    | GASLIMIT =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_block_ctx.bc_gaslimit s)
        | _ => Error "gaslimit requires single output")

    | BASEFEE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_block_ctx.bc_basefee s)
        | _ => Error "basefee requires single output")

    | BLOBBASEFEE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out s.vs_block_ctx.bc_blobbasefee s)
        | _ => Error "blobbasefee requires single output")

    | BLOCKHASH =>
        (case inst.inst_operands of
          [op1] =>
            (case eval_operand op1 s of
              SOME blocknum =>
                (case inst.inst_outputs of
                  [out] => OK (update_var out (s.vs_block_ctx.bc_blockhash (w2n blocknum)) s)
                | _ => Error "blockhash requires single output")
            | NONE => Error "undefined operand")
        | _ => Error "blockhash requires 1 operand")

    (* Environment - Balance *)
    | BALANCE =>
        (case inst.inst_operands of
          [op1] =>
            (case eval_operand op1 s of
              SOME addr =>
                (case inst.inst_outputs of
                  [out] =>
                    let acct = lookup_account (w2w addr) s.vs_accounts in
                    OK (update_var out (n2w acct.balance) s)
                | _ => Error "balance requires single output")
            | NONE => Error "undefined operand")
        | _ => Error "balance requires 1 operand")

    | SELFBALANCE =>
        (case inst.inst_outputs of
          [out] =>
            let acct = lookup_account s.vs_call_ctx.cc_address s.vs_accounts in
            OK (update_var out (n2w acct.balance) s)
        | _ => Error "selfbalance requires single output")

    (* Calldata *)
    | CALLDATASIZE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (n2w (LENGTH s.vs_call_ctx.cc_calldata)) s)
        | _ => Error "calldatasize requires single output")

    | CALLDATALOAD =>
        (case inst.inst_operands of
          [op1] =>
            (case eval_operand op1 s of
              SOME offset =>
                (case inst.inst_outputs of
                  [out] =>
                    let data = s.vs_call_ctx.cc_calldata in
                    let bytes = TAKE 32 (DROP (w2n offset) data ++ REPLICATE 32 0w) in
                    OK (update_var out (word_of_bytes T (0w:bytes32) bytes) s)
                | _ => Error "calldataload requires single output")
            | NONE => Error "undefined operand")
        | _ => Error "calldataload requires 1 operand")

    | CALLDATACOPY =>
        (case inst.inst_operands of
          [op_size; op_offset; op_destOffset] =>
            (case (eval_operand op_size s, eval_operand op_offset s, eval_operand op_destOffset s) of
              (SOME size_val, SOME offset, SOME destOffset) =>
                let data = s.vs_call_ctx.cc_calldata in
                let size = w2n size_val in
                let src_offset = w2n offset in
                let bytes = TAKE size (DROP src_offset data ++ REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n destOffset) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "calldatacopy requires 3 operands")

    (* Return data *)
    | RETURNDATASIZE =>
        (case inst.inst_outputs of
          [out] => OK (update_var out (n2w (LENGTH s.vs_returndata)) s)
        | _ => Error "returndatasize requires single output")

    | RETURNDATACOPY =>
        (case inst.inst_operands of
          [op_size; op_offset; op_destOffset] =>
            (case (eval_operand op_size s, eval_operand op_offset s, eval_operand op_destOffset s) of
              (SOME size_val, SOME offset, SOME destOffset) =>
                let size = w2n size_val in
                let src_offset = w2n offset in
                (* Check for out-of-bounds access *)
                if src_offset + size > LENGTH s.vs_returndata then
                  Revert (revert_state s)
                else
                  let bytes = TAKE size (DROP src_offset s.vs_returndata) in
                  OK (write_memory_with_expansion (w2n destOffset) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "returndatacopy requires 3 operands")

    (* Memory size *)
    | MSIZE =>
        (case inst.inst_outputs of
          [out] =>
            (* MSIZE returns memory size rounded up to 32-byte words *)
            let size = LENGTH s.vs_memory in
            let words = (size + 31) DIV 32 in
            OK (update_var out (n2w (words * 32)) s)
        | _ => Error "msize requires single output")

    (* Hashing - using Keccak256 like EVM *)
    | SHA3 =>
        (case inst.inst_operands of
          [op_size; op_offset] =>
            (case (eval_operand op_size s, eval_operand op_offset s) of
              (SOME size_val, SOME offset) =>
                (case inst.inst_outputs of
                  [out] =>
                    let size = w2n size_val in
                    let off = w2n offset in
                    let data = TAKE size (DROP off s.vs_memory ++ REPLICATE size 0w) in
                    let hash = word_of_bytes T (0w:bytes32) (Keccak_256_w64 data) in
                    OK (update_var out hash s)
                | _ => Error "sha3 requires single output")
            | _ => Error "undefined operand")
        | _ => Error "sha3 requires 2 operands")

    | SHA3_64 =>
        (* SHA3_64 is a Vyper optimization: hash exactly 64 bytes (two words) *)
        (case inst.inst_operands of
          [op2; op1] =>
            (case (eval_operand op1 s, eval_operand op2 s) of
              (SOME v1, SOME v2) =>
                (case inst.inst_outputs of
                  [out] =>
                    let data = word_to_bytes v1 T ++ word_to_bytes v2 T in
                    let hash = word_of_bytes T (0w:bytes32) (Keccak_256_w64 data) in
                    OK (update_var out hash s)
                | _ => Error "sha3_64 requires single output")
            | _ => Error "undefined operand")
        | _ => Error "sha3_64 requires 2 operands")

    (* Default - unimplemented *)
    | _ => Error "unimplemented opcode"
End

(* --------------------------------------------------------------------------
   Block and Function Execution
   -------------------------------------------------------------------------- *)

(* Non-terminator instructions preserve inst_idx *)
Theorem step_inst_preserves_inst_idx:
  !inst s s'.
    step_inst inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  rw[step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_binop_def, exec_unop_def, exec_modop_def] >>
  gvs[AllCaseEqs()] >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def]
QED

(* Step within a basic block - returns (result, is_terminator) *)
Definition step_in_block_def:
  step_in_block fn bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => (Error "block not terminated", T)
    | SOME inst =>
        case step_inst inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then (OK s', T)
            else (OK (next_inst s'), F)
        | Halt s' => (Halt s', T)
        | Revert s' => (Revert s', T)
        | Error e => (Error e, T)
End

(* Run a basic block until we hit a terminator *)
Definition run_block_def:
  run_block fn bb s =
    case step_in_block fn bb s of
      (OK s', is_term) =>
        if s'.vs_halted then Halt s'
        else if is_term then OK s'
        else run_block fn bb s'
    | (Halt s', _) => Halt s'
    | (Revert s', _) => Revert s'
    | (Error e, _) => Error e
Termination
  (* Termination measure: remaining instructions in block.
     Each non-terminator step increments inst_idx via next_inst, so measure decreases.
     Terminators exit the loop immediately (is_term = T). *)
  WF_REL_TAC `measure (\(fn, bb, s). LENGTH bb.bb_instructions - s.vs_inst_idx)` >>
  rw[step_in_block_def] >>
  gvs[AllCaseEqs()] >>
  (* Now we have:
     - get_instruction bb s.vs_inst_idx = SOME inst
     - step_inst inst s = OK s''
     - ~is_terminator inst.inst_opcode (since is_term = F)
     - s' = next_inst s'' *)
  imp_res_tac step_inst_preserves_inst_idx >>
  fs[next_inst_def, get_instruction_def]
End

(* Run a function from current state - uses fuel for termination *)
Definition run_function_def:
  run_function fuel fn s =
    case fuel of
      0 => Error "out of fuel"
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => Error "block not found"
        | SOME bb =>
            case run_block fn bb s of
              OK s' =>
                if s'.vs_halted then Halt s'
                else run_function fuel' fn s'
            | other => other
End

