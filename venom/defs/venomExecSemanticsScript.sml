(*
 * Venom Semantics
 *
 * This theory defines the operational semantics for Venom IR execution.
 * It includes the effects system and instruction stepping.
 *)

Theory venomExecSemantics
Ancestors
  venomState venomInst keccak

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
    | IntRet (bytes32 list) venom_state  (* Internal function return *)
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

(* --------------------------------------------------------------------------
   Instruction Execution Helpers

   Categorized by operand count and state dependency:
     exec_pure{1,2,3} : pure computation (f doesn't depend on state)
     exec_read{0,1}   : state-reading (f depends on state)
     exec_write2      : state-mutating (2 operands, no output)
   -------------------------------------------------------------------------- *)

(* Pure 1-operand: eval operand, apply pure f, update output *)
Definition exec_pure1_def:
  exec_pure1 f inst s =
    case inst.inst_operands of
      [op1] =>
        (case eval_operand op1 s of
          SOME v =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v) s)
            | _ => Error "pure1 requires single output")
        | NONE => Error "undefined operand")
    | _ => Error "pure1 requires 1 operand"
End

(* Pure 2-operand: eval both operands, apply pure f, update output *)
Definition exec_pure2_def:
  exec_pure2 f inst s =
    case inst.inst_operands of
      [op1; op2] =>
        (case (eval_operand op1 s, eval_operand op2 s) of
          (SOME v1, SOME v2) =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v1 v2) s)
            | _ => Error "pure2 requires single output")
        | _ => Error "undefined operand")
    | _ => Error "pure2 requires 2 operands"
End

(* Pure 3-operand: eval all operands, apply pure f, update output *)
Definition exec_pure3_def:
  exec_pure3 f inst s =
    case inst.inst_operands of
      [op1; op2; op3] =>
        (case (eval_operand op1 s, eval_operand op2 s, eval_operand op3 s) of
          (SOME v1, SOME v2, SOME v3) =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v1 v2 v3) s)
            | _ => Error "pure3 requires single output")
        | _ => Error "undefined operand")
    | _ => Error "pure3 requires 3 operands"
End

(* State-read 0-operand: read value from state, update output *)
Definition exec_read0_def:
  exec_read0 f inst s =
    case inst.inst_outputs of
      [out] => OK (update_var out (f s) s)
    | _ => Error "read0 requires single output"
End

(* State-read 1-operand: eval operand, read from state, update output *)
Definition exec_read1_def:
  exec_read1 f inst s =
    case inst.inst_operands of
      [op1] =>
        (case eval_operand op1 s of
          SOME v =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v s) s)
            | _ => Error "read1 requires single output")
        | NONE => Error "undefined operand")
    | _ => Error "read1 requires 1 operand"
End

(* State-write 2-operand: eval both operands, mutate state, no output *)
Definition exec_write2_def:
  exec_write2 f inst s =
    case inst.inst_operands of
      [op1; op2] =>
        (case (eval_operand op1 s, eval_operand op2 s) of
          (SOME v1, SOME v2) => OK (f v1 v2 s)
        | _ => Error "undefined operand")
    | _ => Error "write2 requires 2 operands"
End

(* Step a single instruction *)
Definition step_inst_def:
  step_inst inst s =
    case inst.inst_opcode of
    (* Arithmetic *)
    | ADD => exec_pure2 word_add inst s
    | SUB => exec_pure2 word_sub inst s
    | MUL => exec_pure2 word_mul inst s
    | Div => exec_pure2 safe_div inst s
    | Mod => exec_pure2 safe_mod inst s
    | SDIV => exec_pure2 safe_sdiv inst s
    | SMOD => exec_pure2 safe_smod inst s
    | ADDMOD => exec_pure3 addmod inst s
    | MULMOD => exec_pure3 mulmod inst s

    (* Comparison *)
    | EQ => exec_pure2 (\x y. bool_to_word (x = y)) inst s
    | LT => exec_pure2 (\x y. bool_to_word (w2n x < w2n y)) inst s
    | GT => exec_pure2 (\x y. bool_to_word (w2n x > w2n y)) inst s
    | SLT => exec_pure2 (\x y. bool_to_word (word_lt x y)) inst s
    | SGT => exec_pure2 (\x y. bool_to_word (word_gt x y)) inst s
    | ISZERO => exec_pure1 (\x. bool_to_word (x = 0w)) inst s

    (* Bitwise *)
    | AND => exec_pure2 word_and inst s
    | OR => exec_pure2 word_or inst s
    | XOR => exec_pure2 word_xor inst s
    | NOT => exec_pure1 word_1comp inst s
    | SHL => exec_pure2 (\n w. word_lsl w (w2n n)) inst s
    | SHR => exec_pure2 (\n w. word_lsr w (w2n n)) inst s
    | SAR => exec_pure2 (\n w. word_asr w (w2n n)) inst s

    (* Memory *)
    | MLOAD => exec_read1 (\addr s. mload (w2n addr) s) inst s
    | MSTORE => exec_write2 (\val addr s. mstore (w2n addr) val s) inst s

    (* Storage *)
    | SLOAD => exec_read1 (\key s. sload key s) inst s
    | SSTORE => exec_write2 (\val key s. sstore key val s) inst s

    (* Transient storage *)
    | TLOAD => exec_read1 (\key s. tload key s) inst s
    | TSTORE => exec_write2 (\val key s. tstore key val s) inst s

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

    (* Internal function call - PARAM reads from vs_params by index *)
    | PARAM =>
        (case inst.inst_operands of
          [Lit idx] =>
            let i = w2n idx in
            (case inst.inst_outputs of
              [out] =>
                if i < LENGTH s.vs_params then
                  OK (update_var out (EL i s.vs_params) s)
                else Error "param index out of bounds"
            | _ => Error "param requires single output")
        | _ => Error "param requires literal index operand")

    (* Internal function return - RET evaluates operands and returns IntRet *)
    | RET =>
        (case eval_operands inst.inst_operands s of
          SOME vals => IntRet vals s
        | NONE => Error "ret: undefined operand")

    (* Environment - Call context *)
    | CALLER => exec_read0 (\s. w2w s.vs_call_ctx.cc_caller) inst s
    | ADDRESS => exec_read0 (\s. w2w s.vs_call_ctx.cc_address) inst s
    | CALLVALUE => exec_read0 (\s. s.vs_call_ctx.cc_callvalue) inst s
    | GAS => exec_read0 (\s. n2w s.vs_call_ctx.cc_gas) inst s

    (* Environment - Transaction context *)
    | ORIGIN => exec_read0 (\s. w2w s.vs_tx_ctx.tc_origin) inst s
    | GASPRICE => exec_read0 (\s. s.vs_tx_ctx.tc_gasprice) inst s
    | CHAINID => exec_read0 (\s. s.vs_tx_ctx.tc_chainid) inst s

    (* Environment - Block context *)
    | COINBASE => exec_read0 (\s. w2w s.vs_block_ctx.bc_coinbase) inst s
    | TIMESTAMP => exec_read0 (\s. s.vs_block_ctx.bc_timestamp) inst s
    | NUMBER => exec_read0 (\s. s.vs_block_ctx.bc_number) inst s
    | PREVRANDAO => exec_read0 (\s. s.vs_block_ctx.bc_prevrandao) inst s
    | GASLIMIT => exec_read0 (\s. s.vs_block_ctx.bc_gaslimit) inst s
    | BASEFEE => exec_read0 (\s. s.vs_block_ctx.bc_basefee) inst s
    | BLOBBASEFEE => exec_read0 (\s. s.vs_block_ctx.bc_blobbasefee) inst s
    | BLOCKHASH => exec_read1 (\v s. s.vs_block_ctx.bc_blockhash (w2n v)) inst s

    (* Environment - Balance *)
    | BALANCE => exec_read1
        (\addr s. n2w (lookup_account (w2w addr) s.vs_accounts).balance) inst s
    | SELFBALANCE => exec_read0
        (\s. n2w (lookup_account s.vs_call_ctx.cc_address s.vs_accounts).balance) inst s

    (* Calldata *)
    | CALLDATASIZE => exec_read0 (\s. n2w (LENGTH s.vs_call_ctx.cc_calldata)) inst s
    | CALLDATALOAD => exec_read1
        (\offset s. let data = s.vs_call_ctx.cc_calldata in
                    let bytes = TAKE 32 (DROP (w2n offset) data ++ REPLICATE 32 0w) in
                    word_of_bytes T (0w:bytes32) bytes) inst s

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
    | RETURNDATASIZE => exec_read0 (\s. n2w (LENGTH s.vs_returndata)) inst s

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
    | MSIZE => exec_read0
        (\s. let size = LENGTH s.vs_memory in
             let words = (size + 31) DIV 32 in
             n2w (words * 32)) inst s

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

    (* Default - unimplemented *)
    | _ => Error "unimplemented opcode"
End

(* --------------------------------------------------------------------------
   Block and Function Execution
   -------------------------------------------------------------------------- *)

(* Non-terminator instructions preserve inst_idx.
   Co-located with run_block definition because run_block's
   termination proof depends on this theorem. *)
Theorem step_inst_preserves_inst_idx:
  !inst s s'.
    step_inst inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  rw[step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def] >>
  gvs[AllCaseEqs()] >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, eval_operands_def]
QED

(* --------------------------------------------------------------------------
   Block Step (single instruction within a block)

   Does NOT handle INVOKE — use run_block for cross-function execution.
   Useful as a single-step abstraction for pass correctness proofs.
   -------------------------------------------------------------------------- *)

Definition block_step_def:
  block_step bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => (Error "block not terminated", T)
    | SOME inst =>
        case step_inst inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then (OK s', T)
            else (OK (next_inst s'), F)
        | Halt s' => (Halt s', T)
        | Revert s' => (Revert s', T)
        | IntRet vals s' => (IntRet vals s', T)
        | Error e => (Error e, T)
End

(* --------------------------------------------------------------------------
   INVOKE Helpers
   -------------------------------------------------------------------------- *)

(* Side-effect merge: keep callee's shared mutable state, caller's locals *)
Definition merge_callee_state_def:
  merge_callee_state caller callee =
    caller with <|
      vs_memory     := callee.vs_memory;
      vs_storage    := callee.vs_storage;
      vs_transient  := callee.vs_transient;
      vs_accounts   := callee.vs_accounts;
      vs_returndata := callee.vs_returndata
    |>
End

(* Prepare callee state: fresh vars, params, entry block *)
Definition setup_callee_def:
  setup_callee fn args s =
    if NULL fn.fn_blocks then NONE
    else SOME (s with <|
      vs_vars       := FEMPTY;
      vs_params     := args;
      vs_current_bb := (HD fn.fn_blocks).bb_label;
      vs_inst_idx   := 0;
      vs_prev_bb    := NONE;
      vs_halted     := F;
      vs_reverted   := F
    |>)
End

(* Decode INVOKE operands: first is Label (callee name), rest are args *)
Definition decode_invoke_def:
  decode_invoke inst =
    case inst.inst_operands of
      (Label callee_name :: arg_ops) => SOME (callee_name, arg_ops)
    | _ => NONE
End

(* Bind return values to output variables *)
Definition bind_outputs_def:
  bind_outputs outs vals s =
    if LENGTH outs = LENGTH vals then
      SOME (FOLDL (\s' (out, val). update_var out val s') s (ZIP (outs, vals)))
    else NONE
End

(* --------------------------------------------------------------------------
   Preservation lemmas (needed by run_block/run_function termination proof)
   -------------------------------------------------------------------------- *)

Theorem merge_callee_state_inst_idx:
  (merge_callee_state c e).vs_inst_idx = c.vs_inst_idx
Proof
  simp[merge_callee_state_def]
QED

Theorem update_var_inst_idx:
  (update_var x v s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[update_var_def]
QED

Theorem foldl_update_var_inst_idx:
  !kvs s. (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_inst_idx =
          s.vs_inst_idx
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rw[Once update_var_def] >> simp[update_var_inst_idx]
QED

Theorem bind_outputs_inst_idx:
  bind_outputs outs vals s = SOME s' ==> s'.vs_inst_idx = s.vs_inst_idx
Proof
  rw[bind_outputs_def] >> gvs[foldl_update_var_inst_idx]
QED

(* --------------------------------------------------------------------------
   Block and Function Execution (mutually recursive)

   run_block intercepts INVOKE for cross-function calls; delegates all
   other opcodes to step_inst.  run_function dispatches blocks using fuel.

   Fuel bounds function-call depth (not instruction count).  Within a
   block, termination is structural (inst_idx increases toward block end).
   -------------------------------------------------------------------------- *)

Definition run_block_def:
  (run_block fuel ctx bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => Error "block not terminated"
    | SOME inst =>
        if inst.inst_opcode = INVOKE then
          case decode_invoke inst of
            NONE => Error "invoke: bad operand format"
          | SOME (callee_name, arg_ops) =>
              case lookup_function callee_name ctx.ctx_functions of
                NONE => Error "invoke: function not found"
              | SOME callee_fn =>
                  case eval_operands arg_ops s of
                    NONE => Error "invoke: undefined argument"
                  | SOME args =>
                      case setup_callee callee_fn args s of
                        NONE => Error "invoke: empty function"
                      | SOME callee_s =>
                          case run_function fuel ctx callee_fn callee_s of
                            IntRet vals callee_s' =>
                              (case bind_outputs inst.inst_outputs vals
                                      (merge_callee_state s callee_s') of
                                SOME s' =>
                                  run_block fuel ctx bb (next_inst s')
                              | NONE =>
                                  Error "invoke: return arity mismatch")
                          | Halt s' => Halt s'
                          | Revert s' => Revert s'
                          | Error e => Error e
                          | OK _ => Error "invoke: callee did not return"
        else
          case step_inst inst s of
            OK s' =>
              if is_terminator inst.inst_opcode then
                if s'.vs_halted then Halt s' else OK s'
              else run_block fuel ctx bb (next_inst s')
          | IntRet vals s' => IntRet vals s'
          | Halt s' => Halt s'
          | Revert s' => Revert s'
          | Error e => Error e)
/\
  (run_function fuel ctx fn s =
    case fuel of
      0 => Error "out of fuel"
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => Error "block not found"
        | SOME bb =>
            case run_block fuel' ctx bb s of
              OK s' =>
                if s'.vs_halted then Halt s'
                else run_function fuel' ctx fn s'
            | IntRet vals s' => IntRet vals s'
            | other => other)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
      | INL (fuel, ctx, bb, s) =>
          (fuel, LENGTH bb.bb_instructions - s.vs_inst_idx)
      | INR (fuel, ctx, fn, s) => (fuel, 0))` >>
  rpt strip_tac >>
  imp_res_tac step_inst_preserves_inst_idx >>
  imp_res_tac bind_outputs_inst_idx >>
  gvs[next_inst_def, merge_callee_state_inst_idx, get_instruction_def]
End

(* --------------------------------------------------------------------------
   Context Entry Point
   -------------------------------------------------------------------------- *)

Definition run_context_def:
  run_context fuel ctx s =
    case ctx.ctx_entry of
      NONE => Error "no entry function"
    | SOME entry_name =>
        case lookup_function entry_name ctx.ctx_functions of
          NONE => Error "entry function not found"
        | SOME entry_fn =>
            case entry_block entry_fn of
              NONE => Error "empty entry function"
            | SOME entry_bb =>
                run_function fuel ctx entry_fn
                  (s with <|
                    vs_current_bb := entry_bb.bb_label;
                    vs_inst_idx   := 0;
                    vs_prev_bb    := NONE
                  |>)
End
