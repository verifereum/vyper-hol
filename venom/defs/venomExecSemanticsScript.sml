(*
 * Venom Semantics
 *
 * This theory defines the operational semantics for Venom IR execution.
 * It includes the effects system and instruction stepping.
 *)

Theory venomExecSemantics
Ancestors
  venomState venomInst keccak vfmExecution

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

(* Sign extension: extend byte n of w to 256 bits.
   If n >= 31, w is already fully represented.
   Otherwise, extend sign bit of byte n across higher bytes.
   Matches EVM SIGNEXTEND semantics. *)
Definition sign_extend_def:
  sign_extend (n:bytes32) (w:bytes32) : bytes32 =
    if w2n n > 30 then w
    else
      let byte_pos = w2n n in
      let bit_pos = byte_pos * 8 + 7 in
      let mask = (1w:bytes32) << (bit_pos + 1) - 1w in
      let sign_bit = (w >>> bit_pos) && 1w in
      if sign_bit = 1w then w || ¬mask
      else w && mask
End

(* Memory copy: copy sz bytes from src to dst in memory *)
Definition mcopy_def:
  mcopy (dst:num) (src:num) (sz:num) (s:venom_state) =
    let data = TAKE sz (DROP src s.vs_memory ++ REPLICATE sz 0w) in
    write_memory_with_expansion dst data s
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
    | Halt venom_state            (* Normal termination (STOP/RETURN) *)
    | Revert venom_state          (* Revert termination *)
    | IntRet (bytes32 list) venom_state  (* Internal function return (RET) *)
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

(* Extract label names from operand list (for DJMP target list) *)
Definition extract_labels_def:
  extract_labels [] = SOME [] /\
  extract_labels (Label lbl :: rest) =
    (case extract_labels rest of
       SOME lbls => SOME (lbl :: lbls)
     | NONE => NONE) /\
  extract_labels _ = NONE
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

(* --------------------------------------------------------------------------
   External Call Helpers (using verifereum EVM semantics)

   External calls build an EVM execution_state, run the callee's bytecode
   via vfmExecution$run, and extract the result. This matches the approach
   used in the Vyper source-level semantics (run_ext_call).

   CALL/STATICCALL/DELEGATECALL: make_venom_call_state + extract_venom_call_result
   CREATE/CREATE2: make_venom_create_state + extract_venom_create_result
   -------------------------------------------------------------------------- *)

(* Build transaction_parameters from venom state for EVM sub-execution.
   Mirrors vyper_to_tx_params in vyperInterpreterScript.sml.
   prevHashes comes from vs_prev_hashes; authRefund defaults to 0. *)
Definition venom_to_tx_params_def:
  venom_to_tx_params s : transaction_parameters =
    <| origin := s.vs_tx_ctx.tc_origin;
       gasPrice := w2n s.vs_tx_ctx.tc_gasprice;
       baseFeePerGas := w2n s.vs_block_ctx.bc_basefee;
       baseFeePerBlobGas := w2n s.vs_block_ctx.bc_blobbasefee;
       blockNumber := w2n s.vs_block_ctx.bc_number;
       blockTimeStamp := w2n s.vs_block_ctx.bc_timestamp;
       blockCoinBase := s.vs_block_ctx.bc_coinbase;
       blockGasLimit := w2n s.vs_block_ctx.bc_gaslimit;
       prevRandao := s.vs_block_ctx.bc_prevrandao;
       prevHashes := s.vs_prev_hashes;
       blobHashes := s.vs_tx_ctx.tc_blobhashes;
       chainId := w2n s.vs_tx_ctx.tc_chainid;
       authRefund := 0 |>
End

(* Shared: build a sub-context transaction record *)
Definition make_sub_tx_def:
  make_sub_tx (caller:address) (target:address) value gas calldata =
    <| from := caller; to := SOME target;
       data := calldata; nonce := 0; value := value;
       gasLimit := gas; gasPrice := 0;
       accessList := [];
       blobVersionedHashes := [];
       maxFeePerBlobGas := NONE;
       maxFeePerGas := NONE;
       authorizationList := [] |>
End

(* Shared: build initial rollback and accesses *)
Definition make_rollback_def:
  make_rollback accounts (caller:address) (target:address) =
    let accesses = <| addresses := fINSERT caller (fINSERT target fEMPTY);
                      storageKeys := fEMPTY |> in
    <| accounts := accounts;
       tStorage := empty_transient_storage;
       accesses := accesses;
       toDelete := [] |>
End

(* Build an EVM execution_state for CALL/STATICCALL/DELEGATECALL *)
Definition make_venom_call_state_def:
  make_venom_call_state s (target:address) gas value calldata code is_static =
    let caller = s.vs_call_ctx.cc_address in
    let tx = make_sub_tx caller target value gas calldata in
    let ctxt = initial_context target code is_static
                 empty_return_destination tx in
    let accounts = transfer_value caller target value s.vs_accounts in
    let rb = make_rollback accounts caller target in
    <| contexts := [(ctxt, rb)];
       txParams := venom_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Build an EVM execution_state for CREATE/CREATE2.
   Mirrors verifereum's proceed_create: transfers value, uses Code address
   as return destination so handle_create deploys the init code's output. *)
Definition make_venom_create_state_def:
  make_venom_create_state s (new_address:address) gas value init_code =
    let caller = s.vs_call_ctx.cc_address in
    let tx = make_sub_tx caller new_address value gas [] in
    let ctxt = initial_context new_address init_code F
                 (Code new_address) tx in
    let accounts = transfer_value caller new_address value s.vs_accounts in
    let rb = make_rollback accounts caller new_address in
    <| contexts := [(ctxt, rb)];
       txParams := venom_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Extract result from verifereum execution into Venom state update.
   output_val: function mapping success to output word
     (CALL: \_ => 1w, CREATE: \addr => w2w addr)
   update_mem: whether to copy returndata into memory *)
Definition extract_venom_result_def:
  extract_venom_result s output_val retOff retSize run_result =
    case run_result of
    | NONE => NONE
    | SOME (result, final_state) =>
      (case final_state.contexts of
       | [(ctxt, _)] =>
           let returndata = ctxt.returnData in
           let (success, accounts) =
             (case result of
              | INR NONE => (T, final_state.rollback.accounts)
              | INR (SOME Reverted) => (F, s.vs_accounts)
              | _ => (F, s.vs_accounts)) in
           let new_logs =
             (case result of
              | INR NONE => ctxt.logs
              | _ => []) in
           let output : bytes32 =
             if success then output_val else 0w in
           let s' = s with <|
             vs_returndata := returndata;
             vs_accounts := accounts;
             vs_logs := s.vs_logs ++ new_logs;
             vs_memory := (write_memory_with_expansion retOff
                             (TAKE retSize returndata) s).vs_memory
           |> in
           SOME (output, s')
       | _ => NONE)
End

(* Execute an external call via verifereum EVM semantics.
   CALL: operands = [gas; addr; value; argsOff; argsSize; retOff; retSize]
   STATICCALL/DELEGATECALL: operands = [gas; addr; argsOff; argsSize; retOff; retSize]
*)
Definition exec_ext_call_def:
  exec_ext_call inst s gas addr_w value argsOff argsSize retOff retSize is_static =
    let calldata = read_memory (w2n argsOff) (w2n argsSize) s in
    let target : address = w2w addr_w in
    let code = (lookup_account target s.vs_accounts).code in
    let evm_s = make_venom_call_state s target (w2n gas) (w2n value)
                  calldata code is_static in
    case extract_venom_result s 1w (w2n retOff) (w2n retSize) (run evm_s) of
    | SOME (output, s') =>
        (case inst.inst_outputs of
           [out] => OK (update_var out output s')
         | _ => Error "ext_call requires single output")
    | NONE => Error "ext_call: non-terminating or invalid state"
End

(* Execute CREATE/CREATE2 via verifereum EVM semantics.
   CREATE: salt_opt = NONE, address from sender + nonce
   CREATE2: salt_opt = SOME salt, address from sender + salt + code hash
*)
Definition exec_create_def:
  exec_create inst s value offset sz salt_opt =
    let init_code = read_memory (w2n offset) (w2n sz) s in
    let sender = s.vs_call_ctx.cc_address in
    let sender_acct = lookup_account sender s.vs_accounts in
    let new_address =
      (case salt_opt of
         NONE => address_for_create sender sender_acct.nonce
       | SOME salt => address_for_create2 sender salt init_code) in
    let evm_s = make_venom_create_state s new_address 0 (w2n value)
                  init_code in
    case extract_venom_result s (w2w new_address) 0 0 (run evm_s) of
    | SOME (output, s') =>
        (case inst.inst_outputs of
           [out] => OK (update_var out output s')
         | _ => Error "create requires single output")
    | NONE => Error "create: non-terminating or invalid state"
End

(* Bump-allocate memory and record in vs_allocas *)
Definition exec_alloca_def:
  exec_alloca inst s alloc_size alloc_id =
    case inst.inst_outputs of
      [out] =>
        let offset = LENGTH s.vs_memory in
        let sz = w2n alloc_size in
        let s' = s with <|
          vs_memory := s.vs_memory ++ REPLICATE sz 0w;
          vs_allocas := s.vs_allocas |+ (w2n alloc_id, (offset, sz))
        |> in
        OK (update_var out (n2w offset) s')
    | _ => Error "alloca requires single output"
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
    | Exp => exec_pure2 word_exp inst s
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
    | SIGNEXTEND => exec_pure2 sign_extend inst s

    (* Memory *)
    | MLOAD => exec_read1 (\addr s. mload (w2n addr) s) inst s
    | MSTORE => exec_write2 (\val addr s. mstore (w2n addr) val s) inst s
    | MCOPY =>
        (case inst.inst_operands of
          [op_size; op_src; op_dst] =>
            (case (eval_operand op_size s, eval_operand op_src s,
                   eval_operand op_dst s) of
              (SOME sz, SOME src, SOME dst) =>
                OK (mcopy (w2n dst) (w2n src) (w2n sz) s)
            | _ => Error "undefined operand")
        | _ => Error "mcopy requires 3 operands")

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

    (* Control flow - DJMP (dynamic jump / jump table) *)
    | DJMP =>
        (case inst.inst_operands of
          selector_op :: label_ops =>
            (case (eval_operand selector_op s, extract_labels label_ops) of
              (SOME idx, SOME labels) =>
                let i = w2n idx in
                if i < LENGTH labels then
                  OK (jump_to (EL i labels) s)
                else Error "djmp: index out of range"
            | _ => Error "djmp: undefined operand or invalid labels")
        | _ => Error "djmp requires selector and labels")

    (* Function parameter access *)
    | PARAM =>
        (case inst.inst_operands of
          [Lit idx] =>
            let i = w2n idx in
            if i < LENGTH s.vs_params then
              (case inst.inst_outputs of
                [out] => OK (update_var out (EL i s.vs_params) s)
              | _ => Error "param requires single output")
            else Error "param: index out of range"
        | _ => Error "param requires literal index")

    (* Return from internal function *)
    | RET =>
        (case eval_operands inst.inst_operands s of
          SOME ret_vals => IntRet ret_vals s
        | NONE => Error "ret: undefined return value")

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
                if cond = 0w then Revert (revert_state s)
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
    | BLOBHASH => exec_read1
        (\v s. let idx = w2n v in
               let hashes = s.vs_tx_ctx.tc_blobhashes in
               if idx < LENGTH hashes then EL idx hashes else 0w) inst s

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

    (* Code introspection *)
    | CODESIZE => exec_read0 (\s. n2w (LENGTH s.vs_code)) inst s
    | EXTCODESIZE => exec_read1
        (\addr s. n2w (LENGTH (lookup_account (w2w addr)
                                              s.vs_accounts).code)) inst s
    | EXTCODEHASH =>
        exec_read1
          (\addr s.
            let code = (lookup_account (w2w addr) s.vs_accounts).code in
            if NULL code then 0w
            else word_of_bytes T (0w:bytes32)
                   (Keccak_256_w64 code)) inst s

    (* Allocation pointer arithmetic - GEP is base + offset, pure *)
    | GEP => exec_pure2 word_add inst s

    (* Immutables - separate from memory, used during constructor *)
    | ILOAD => exec_read1
        (\off s.
          case FLOOKUP s.vs_immutables (w2n off) of
            SOME v => v
          | NONE => 0w) inst s
    | ISTORE =>
        (case inst.inst_operands of
          [offset_op; val_op] =>
            (case (eval_operand offset_op s, eval_operand val_op s) of
              (SOME off, SOME v) =>
                OK (s with vs_immutables := s.vs_immutables |+ (w2n off, v))
            | _ => Error "undefined operand")
        | _ => Error "istore requires 2 operands")

    (* Data section reads *)
    | DLOAD => exec_read1
        (\off s.
          let bytes = TAKE 32 (DROP (w2n off) s.vs_data_section ++
                               REPLICATE 32 0w) in
          word_of_bytes T (0w:bytes32) bytes) inst s

    | DLOADBYTES =>
        (case inst.inst_operands of
          [op_size; op_src; op_dst] =>
            (case (eval_operand op_size s, eval_operand op_src s,
                   eval_operand op_dst s) of
              (SOME size_val, SOME src, SOME dst) =>
                let size = w2n size_val in
                let bytes = TAKE size (DROP (w2n src) s.vs_data_section ++
                                      REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n dst) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "dloadbytes requires 3 operands")

    (* Code access *)
    | CODECOPY =>
        (case inst.inst_operands of
          [op_size; op_src; op_dst] =>
            (case (eval_operand op_size s, eval_operand op_src s,
                   eval_operand op_dst s) of
              (SOME size_val, SOME src, SOME dst) =>
                let size = w2n size_val in
                let bytes = TAKE size (DROP (w2n src) s.vs_code ++
                                      REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n dst) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "codecopy requires 3 operands")

    | EXTCODECOPY =>
        (case inst.inst_operands of
          [op_addr; op_dst; op_src; op_size] =>
            (case (eval_operand op_addr s, eval_operand op_dst s,
                   eval_operand op_src s, eval_operand op_size s) of
              (SOME addr, SOME dst, SOME src, SOME size_val) =>
                let code = (lookup_account (w2w addr) s.vs_accounts).code in
                let size = w2n size_val in
                let bytes = TAKE size (DROP (w2n src) code ++
                                      REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n dst) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "extcodecopy requires 4 operands")

    (* Label offset computation - resolves label address + operand offset *)
    | OFFSET =>
        (case inst.inst_operands of
          [Label lbl; offset_op] =>
            (case eval_operand offset_op s of
              SOME off =>
                (case inst.inst_outputs of
                  [out] =>
                    (case FLOOKUP s.vs_label_offsets lbl of
                      SOME lbl_addr => OK (update_var out (lbl_addr + off) s)
                    | NONE => Error "offset: unknown label")
                | _ => Error "offset requires single output")
            | NONE => Error "offset: undefined operand")
        | _ => Error "offset requires label and operand")

    (* Logging - variable operand count.
       Venom IR format: log topic_count, topic_{n-1}, ..., topic_0, size, offset
       First operand is Lit topic_count (metadata), rest are evaluated. *)
    | LOG =>
        (case inst.inst_operands of
          Lit tc :: rest =>
            let n = w2n tc in
            (* rest should be: n topics (reversed) ++ [size; offset] *)
            if LENGTH rest <> n + 2 then Error "log: wrong operand count"
            else
              let topic_ops = TAKE n rest in
              let size_op = EL n rest in
              let offset_op = EL (n + 1) rest in
              (case (eval_operands topic_ops s,
                     eval_operand size_op s,
                     eval_operand offset_op s) of
                (SOME topics, SOME sz, SOME off) =>
                  let data = TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++
                                            REPLICATE (w2n sz) 0w) in
                  let ev = <| logger := w2w s.vs_call_ctx.cc_address;
                              topics := REVERSE topics;
                              data := data |> in
                  OK (s with vs_logs := s.vs_logs ++ [ev])
              | _ => Error "log: undefined operand")
        | _ => Error "log requires Lit topic_count as first operand")

    (* Selfdestruct: transfer balance to beneficiary, then halt.
       Deprecated post-Cancun but still defined in Venom IR. *)
    | SELFDESTRUCT =>
        (case inst.inst_operands of
          [addr_op] =>
            (case eval_operand addr_op s of
              SOME addr =>
                let self = s.vs_call_ctx.cc_address in
                let bal = (lookup_account self s.vs_accounts).balance in
                let beneficiary = w2w addr in
                let accts = s.vs_accounts in
                let self_acct = lookup_account self accts in
                let ben_acct = lookup_account beneficiary accts in
                let accts' = (\a. if a = self then
                                    self_acct with balance := 0
                                  else if a = beneficiary then
                                    ben_acct with balance := ben_acct.balance + bal
                                  else accts a) in
                Halt (halt_state (s with vs_accounts := accts'))
            | NONE => Error "selfdestruct: undefined operand")
        | _ => Error "selfdestruct requires 1 operand")

    (* Invalid opcode — always reverts (EVM: consumes all gas + reverts) *)
    | INVALID => Revert (revert_state s)

    (* ----------------------------------------------------------------
       External calls
       ---------------------------------------------------------------- *)
    | CALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; val_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand val_op s, eval_operand ao_op s,
                   eval_operand as_op s, eval_operand ro_op s,
                   eval_operand rs_op s) of
              (SOME gas, SOME addr, SOME value, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s gas addr value ao as_ ro rs
                  s.vs_call_ctx.cc_static
            | _ => Error "undefined operand")
        | _ => Error "call requires 7 operands")

    | STATICCALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand ao_op s, eval_operand as_op s,
                   eval_operand ro_op s, eval_operand rs_op s) of
              (SOME gas, SOME addr, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s gas addr (0w:bytes32) ao as_ ro rs T
            | _ => Error "undefined operand")
        | _ => Error "staticcall requires 6 operands")

    | DELEGATECALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand ao_op s, eval_operand as_op s,
                   eval_operand ro_op s, eval_operand rs_op s) of
              (SOME gas, SOME addr, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s gas addr s.vs_call_ctx.cc_callvalue ao as_ ro rs
                  s.vs_call_ctx.cc_static
            | _ => Error "undefined operand")
        | _ => Error "delegatecall requires 6 operands")

    | CREATE =>
        (case inst.inst_operands of
          [val_op; off_op; sz_op] =>
            (case (eval_operand val_op s, eval_operand off_op s,
                   eval_operand sz_op s) of
              (SOME value, SOME offset, SOME sz) =>
                exec_create inst s value offset sz NONE
            | _ => Error "undefined operand")
        | _ => Error "create requires 3 operands")

    | CREATE2 =>
        (case inst.inst_operands of
          [val_op; off_op; sz_op; salt_op] =>
            (case (eval_operand val_op s, eval_operand off_op s,
                   eval_operand sz_op s, eval_operand salt_op s) of
              (SOME value, SOME offset, SOME sz, SOME salt) =>
                exec_create inst s value offset sz (SOME salt)
            | _ => Error "undefined operand")
        | _ => Error "create2 requires 4 operands")

    (* ----------------------------------------------------------------
       Memory Allocation

       All three variants are identical at runtime: bump-allocate in
       vs_memory and record in vs_allocas. The distinction is metadata
       for the compiler (PALLOCA=param, CALLOCA=caller-side staging).

       Operands: [Lit size, Lit alloca_id] (CALLOCA has Label callee too)
       Output: [out] = base address (word256) of allocated region
       ---------------------------------------------------------------- *)
    | ALLOCA =>
        (case inst.inst_operands of
          [Lit alloc_size; Lit alloc_id] =>
            exec_alloca inst s alloc_size alloc_id
        | _ => Error "alloca requires 2 literal operands")

    | PALLOCA =>
        (case inst.inst_operands of
          [Lit alloc_size; Lit alloc_id] =>
            exec_alloca inst s alloc_size alloc_id
        | _ => Error "palloca requires 2 literal operands")

    | CALLOCA =>
        (case inst.inst_operands of
          Lit alloc_size :: Lit alloc_id :: _ =>  (* Label callee ignored at runtime *)
            exec_alloca inst s alloc_size alloc_id
        | _ => Error "calloca requires literal size and id")

    (* Default - truly unknown opcode *)
    | _ => Error "unknown opcode"
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
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
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
