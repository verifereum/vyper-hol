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
   External Call Helpers
   -------------------------------------------------------------------------- *)

(* Execute an external call via the oracle and apply results to state.
   call_type: CALL | STATICCALL | DELEGATECALL
   CALL: operands = [gas; addr; value; argsOff; argsSize; retOff; retSize]
   STATICCALL/DELEGATECALL: operands = [gas; addr; argsOff; argsSize; retOff; retSize]
*)
Definition exec_ext_call_def:
  exec_ext_call inst s addr_w value argsOff argsSize retOff retSize is_static =
    let calldata = read_memory (w2n argsOff) (w2n argsSize) s in
    let target : address = w2w addr_w in
    let result = s.vs_ext_call_oracle s.vs_accounts target (w2n value) calldata is_static NONE in
    let s' = s with <|
      vs_returndata := result.ecr_returndata;
      vs_accounts := result.ecr_accounts;
      vs_logs := s.vs_logs ++ result.ecr_new_logs;
      vs_memory := (write_memory_with_expansion (w2n retOff)
                      (TAKE (w2n retSize) result.ecr_returndata) s).vs_memory
    |> in
    case inst.inst_outputs of
      [out] => OK (update_var out result.ecr_output s')
    | _ => Error "ext_call requires single output"
End

(* Execute CREATE/CREATE2 via the oracle.
   CREATE: operands = [value; offset; size], salt = NONE
   CREATE2: operands = [value; offset; size; salt], salt = SOME salt_val
*)
Definition exec_create_def:
  exec_create inst s value offset sz salt_opt =
    let init_code = read_memory (w2n offset) (w2n sz) s in
    let result = s.vs_ext_call_oracle s.vs_accounts (0w:address) (w2n value) init_code F salt_opt in
    let s' = s with <|
      vs_returndata := result.ecr_returndata;
      vs_accounts := result.ecr_accounts;
      vs_logs := s.vs_logs ++ result.ecr_new_logs
    |> in
    case inst.inst_outputs of
      [out] => OK (update_var out result.ecr_output s')
    | _ => Error "create requires single output"
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
                      SOME base => OK (update_var out (base + off) s)
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
              (SOME _, SOME addr, SOME value, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s addr value ao as_ ro rs F
            | _ => Error "undefined operand")
        | _ => Error "call requires 7 operands")

    | STATICCALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand ao_op s, eval_operand as_op s,
                   eval_operand ro_op s, eval_operand rs_op s) of
              (SOME _, SOME addr, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s addr (0w:bytes32) ao as_ ro rs T
            | _ => Error "undefined operand")
        | _ => Error "staticcall requires 6 operands")

    | DELEGATECALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand ao_op s, eval_operand as_op s,
                   eval_operand ro_op s, eval_operand rs_op s) of
              (SOME _, SOME addr, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s addr s.vs_call_ctx.cc_callvalue ao as_ ro rs F
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
     exec_ext_call_def, exec_create_def, exec_alloca_def] >>
  gvs[AllCaseEqs()] >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     revert_state_def]
QED

(* Step within a basic block - returns (result, is_terminator) *)
Definition step_in_block_def:
  step_in_block bb s =
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

(* Run a basic block until we hit a terminator *)
Definition run_block_def:
  run_block bb s =
    case step_in_block bb s of
      (OK s', is_term) =>
        if s'.vs_halted then Halt s'
        else if is_term then OK s'
        else run_block bb s'
    | (Halt s', _) => Halt s'
    | (Revert s', _) => Revert s'
    | (IntRet vals s', _) => IntRet vals s'
    | (Error e, _) => Error e
Termination
  (* Termination measure: remaining instructions in block.
     Each non-terminator step increments inst_idx via next_inst, so measure decreases.
     Terminators exit the loop immediately (is_term = T). *)
  WF_REL_TAC `measure (\(bb, s). LENGTH bb.bb_instructions - s.vs_inst_idx)` >>
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
            case run_block bb s of
              OK s' =>
                if s'.vs_halted then Halt s'
                else run_function fuel' fn s'
            | other => other
End
