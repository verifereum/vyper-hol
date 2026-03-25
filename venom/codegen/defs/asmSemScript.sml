(*
 * Assembly Interpreter
 *
 * Executes asm_inst programs directly, using pre-computed label offsets.
 * Bridges between Venom IR codegen and EVM bytecode execution.
 *
 * Key difference from EVM: PC indexes asm_inst list (not byte offset).
 * Label offsets are pre-computed (same as assemble) and used for:
 *   - AsmPushLabel: push resolved byte offset onto stack
 *   - JUMP/JUMPI: pop byte offset, map back to asm index via offset_to_pc
 *
 * External calls build execution_state directly from asm_state fields
 * and delegate to verifereum's run.
 *
 * TOP-LEVEL:
 *   asm_state, asm_result    — execution state and result types
 *   asm_step                 — single instruction step
 *   run_asm                  — fuel-based execution
 *   build_offset_to_pc       — byte_offset → asm_index map
 *)

Theory asmSem
Ancestors
  symbolResolve venomExecSemantics

(* ===== Types ===== *)

Datatype:
  asm_state = <|
    as_stack : bytes32 list;
    as_memory : byte list;
    as_accounts : evm_accounts;
    as_transient : transient_storage;
    as_returndata : byte list;
    as_logs : event list;
    as_pc : num;
    as_call_ctx : call_context;
    as_tx_ctx : tx_context;
    as_block_ctx : block_context;
    as_code : byte list;
    as_prev_hashes : bytes32 list
  |>
End

Datatype:
  asm_result =
    | AsmOK asm_state
    | AsmHalt asm_state
    | AsmRevert asm_state
    | AsmFault asm_state
    | AsmError string
End

(* ===== Pre-computation ===== *)

(* Byte offset → asm instruction index (inverse of instruction layout) *)
Definition build_offset_to_pc_def:
  build_offset_to_pc prog =
    FST (FOLDL (λ(m, off) (i, inst).
      (m |+ (off, i), off + asm_inst_size inst))
    (FEMPTY : (num, num) fmap, 0n)
    (MAPi (λi inst. (i, inst)) prog))
End

(* ===== Memory Helpers (pure, on byte lists) ===== *)

Definition read_bytes_def:
  read_bytes offset sz (mem : byte list) =
    TAKE sz (DROP offset mem ++ REPLICATE sz 0w)
End

Definition write_bytes_def:
  write_bytes offset (data : byte list) mem =
    let needed = offset + LENGTH data in
    let expanded = if needed > LENGTH mem
                   then mem ++ REPLICATE (needed - LENGTH mem) 0w
                   else mem in
    TAKE offset expanded ++ data ++ DROP (offset + LENGTH data) expanded
End

Definition w256_to_bytes_def:
  w256_to_bytes (w : bytes32) : byte list =
    MAP (λi. (w2w (w >>> (i * 8))) : byte) (REVERSE (GENLIST I 32))
End

(* ===== Stack Operation Helpers ===== *)

Definition asm_next_def:
  asm_next s = s with as_pc := s.as_pc + 1
End

Definition asm_binop_def:
  asm_binop f s =
    case s.as_stack of
      a :: b :: stk =>
        AsmOK (asm_next (s with as_stack := f a b :: stk))
    | _ => AsmError "stack underflow"
End

Definition asm_unop_def:
  asm_unop f s =
    case s.as_stack of
      a :: stk =>
        AsmOK (asm_next (s with as_stack := f a :: stk))
    | _ => AsmError "stack underflow"
End

Definition asm_ternop_def:
  asm_ternop f s =
    case s.as_stack of
      a :: b :: c :: stk =>
        AsmOK (asm_next (s with as_stack := f a b c :: stk))
    | _ => AsmError "stack underflow"
End

Definition asm_push_val_def:
  asm_push_val v s =
    AsmOK (asm_next (s with as_stack := v :: s.as_stack))
End

Definition asm_pop_def:
  asm_pop s =
    case s.as_stack of
      _ :: stk => AsmOK (asm_next (s with as_stack := stk))
    | _ => AsmError "stack underflow"
End

Definition asm_dup_def:
  asm_dup n s =
    if n < LENGTH s.as_stack then
      AsmOK (asm_next (s with as_stack :=
        EL n s.as_stack :: s.as_stack))
    else AsmError "dup: stack underflow"
End

Definition asm_swap_def:
  asm_swap n s =
    if n < LENGTH s.as_stack ∧ 0 < n then
      let stk = s.as_stack in
      AsmOK (asm_next (s with as_stack :=
        LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk)))
    else AsmError "swap: invalid"
End

(* f takes popped value AND full state (for context reads) *)
Definition asm_state_unop_def:
  asm_state_unop f s =
    case s.as_stack of
      a :: stk =>
        AsmOK (asm_next (s with as_stack := f a s :: stk))
    | _ => AsmError "stack underflow"
End

(* ===== Lookup Tables (DUP/SWAP/LOG families) ===== *)

Definition dup_table_def:
  dup_table : (string # num) list =
    [("DUP1",0n);("DUP2",1);("DUP3",2);("DUP4",3);
     ("DUP5",4);("DUP6",5);("DUP7",6);("DUP8",7);
     ("DUP9",8);("DUP10",9);("DUP11",10);("DUP12",11);
     ("DUP13",12);("DUP14",13);("DUP15",14);("DUP16",15)]
End

Definition swap_table_def:
  swap_table : (string # num) list =
    [("SWAP1",1n);("SWAP2",2);("SWAP3",3);("SWAP4",4);
     ("SWAP5",5);("SWAP6",6);("SWAP7",7);("SWAP8",8);
     ("SWAP9",9);("SWAP10",10);("SWAP11",11);("SWAP12",12);
     ("SWAP13",13);("SWAP14",14);("SWAP15",15);("SWAP16",16)]
End

Definition log_table_def:
  log_table : (string # num) list =
    [("LOG0",0n);("LOG1",1);("LOG2",2);("LOG3",3);("LOG4",4)]
End

(* ===== Memory/Storage Operations ===== *)

Definition asm_mload_def:
  asm_mload s =
    case s.as_stack of
      offset :: stk =>
        let v = word_of_bytes T (0w:bytes32)
                  (read_bytes (w2n offset) 32 s.as_memory) in
        AsmOK (asm_next (s with as_stack := v :: stk))
    | _ => AsmError "mload: stack underflow"
End

Definition asm_mstore_def:
  asm_mstore s =
    case s.as_stack of
      offset :: value :: stk =>
        AsmOK (asm_next (s with <|
          as_stack := stk;
          as_memory := write_bytes (w2n offset)
                         (w256_to_bytes value) s.as_memory |>))
    | _ => AsmError "mstore: stack underflow"
End

Definition asm_sload_def:
  asm_sload s =
    case s.as_stack of
      key :: stk =>
        let addr = s.as_call_ctx.cc_address in
        let v = lookup_storage key
                  (lookup_account addr s.as_accounts).storage in
        AsmOK (asm_next (s with as_stack := v :: stk))
    | _ => AsmError "sload: stack underflow"
End

Definition asm_sstore_def:
  asm_sstore s =
    case s.as_stack of
      key :: value :: stk =>
        let addr = s.as_call_ctx.cc_address in
        let acct = lookup_account addr s.as_accounts in
        let acct' = acct with storage :=
          update_storage key value acct.storage in
        AsmOK (asm_next (s with <|
          as_stack := stk;
          as_accounts := update_account addr acct' s.as_accounts |>))
    | _ => AsmError "sstore: stack underflow"
End

Definition asm_tload_def:
  asm_tload s =
    case s.as_stack of
      key :: stk =>
        let addr = s.as_call_ctx.cc_address in
        let v = lookup_transient_storage addr s.as_transient key in
        AsmOK (asm_next (s with as_stack := v :: stk))
    | _ => AsmError "tload: stack underflow"
End

Definition asm_tstore_def:
  asm_tstore s =
    case s.as_stack of
      key :: value :: stk =>
        let addr = s.as_call_ctx.cc_address in
        let cur = lookup_transient_storage addr s.as_transient in
        let new_stor = update_storage key value cur in
        AsmOK (asm_next (s with <|
          as_stack := stk;
          as_transient := update_transient_storage
            addr new_stor s.as_transient |>))
    | _ => AsmError "tstore: stack underflow"
End

(* ===== Control Flow ===== *)

Definition asm_jump_def:
  asm_jump offset_to_pc s =
    case s.as_stack of
      dest :: stk =>
        (case FLOOKUP offset_to_pc (w2n dest) of
           SOME pc => AsmOK (s with <| as_stack := stk; as_pc := pc |>)
         | NONE => AsmError "jump: invalid destination")
    | _ => AsmError "jump: stack underflow"
End

Definition asm_jumpi_def:
  asm_jumpi offset_to_pc s =
    case s.as_stack of
      dest :: cond :: stk =>
        if cond = 0w then
          AsmOK (asm_next (s with as_stack := stk))
        else
          (case FLOOKUP offset_to_pc (w2n dest) of
             SOME pc =>
               AsmOK (s with <| as_stack := stk; as_pc := pc |>)
           | NONE => AsmError "jumpi: invalid destination")
    | _ => AsmError "jumpi: stack underflow"
End

Definition asm_return_op_def:
  asm_return_op s =
    case s.as_stack of
      off_w :: sz_w :: stk =>
        let rd = read_bytes (w2n off_w) (w2n sz_w) s.as_memory in
        AsmHalt (s with <| as_stack := stk; as_returndata := rd |>)
    | _ => AsmError "return: stack underflow"
End

Definition asm_revert_op_def:
  asm_revert_op s =
    case s.as_stack of
      off_w :: sz_w :: stk =>
        let rd = read_bytes (w2n off_w) (w2n sz_w) s.as_memory in
        AsmRevert (s with <| as_stack := stk; as_returndata := rd |>)
    | _ => AsmError "revert: stack underflow"
End

(* ===== Logging ===== *)

Definition asm_log_def:
  asm_log n s =
    if LENGTH s.as_stack < n + 2 then AsmError "log: stack underflow"
    else
      let offset = HD s.as_stack in
      let sz = EL 1 s.as_stack in
      let topics = TAKE n (DROP 2 s.as_stack) in
      let stk = DROP (n + 2) s.as_stack in
      let data = read_bytes (w2n offset) (w2n sz) s.as_memory in
      let ev = <| logger := w2w s.as_call_ctx.cc_address;
                  topics := topics;
                  data := data |> in
      AsmOK (asm_next (s with <|
        as_stack := stk;
        as_logs := s.as_logs ++ [ev] |>))
End

(* ===== SHA3 ===== *)

Definition asm_sha3_def:
  asm_sha3 s =
    case s.as_stack of
      off_w :: sz_w :: stk =>
        let bs = read_bytes (w2n off_w) (w2n sz_w) s.as_memory in
        let h = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs) in
        AsmOK (asm_next (s with as_stack := h :: stk))
    | _ => AsmError "sha3: stack underflow"
End

(* ===== Copy Operations ===== *)

Definition asm_copy_to_mem_def:
  asm_copy_to_mem (src : byte list) s =
    case s.as_stack of
      destOff :: srcOff :: sz :: stk =>
        let bytes = read_bytes (w2n srcOff) (w2n sz) src in
        AsmOK (asm_next (s with <|
          as_stack := stk;
          as_memory := write_bytes (w2n destOff) bytes s.as_memory |>))
    | _ => AsmError "copy: stack underflow"
End

(* RETURNDATACOPY: OOB is exceptional halt per EIP-211 *)
Definition asm_returndatacopy_def:
  asm_returndatacopy s =
    case s.as_stack of
      destOff :: srcOff :: sz :: stk =>
        if w2n srcOff + w2n sz > LENGTH s.as_returndata then
          AsmFault s
        else
          let bytes = TAKE (w2n sz)
                        (DROP (w2n srcOff) s.as_returndata) in
          AsmOK (asm_next (s with <|
            as_stack := stk;
            as_memory := write_bytes (w2n destOff) bytes s.as_memory |>))
    | _ => AsmError "returndatacopy: stack underflow"
End

(* EXTCODECOPY: 4 args (addr, destOff, srcOff, sz) *)
Definition asm_extcodecopy_def:
  asm_extcodecopy s =
    case s.as_stack of
      addr :: destOff :: srcOff :: sz :: stk =>
        let code = (lookup_account (w2w addr) s.as_accounts).code in
        let bytes = read_bytes (w2n srcOff) (w2n sz) code in
        AsmOK (asm_next (s with <|
          as_stack := stk;
          as_memory := write_bytes (w2n destOff) bytes s.as_memory |>))
    | _ => AsmError "extcodecopy: stack underflow"
End

Definition asm_selfdestruct_def:
  asm_selfdestruct s =
    case s.as_stack of
      addr :: stk =>
        let self = s.as_call_ctx.cc_address in
        let bal = (lookup_account self s.as_accounts).balance in
        let beneficiary : address = w2w addr in
        let self_acct = lookup_account self s.as_accounts in
        let ben_acct = lookup_account beneficiary s.as_accounts in
        let accts' = (λa. if a = self then
                            self_acct with balance := 0
                          else if a = beneficiary then
                            ben_acct with balance :=
                              ben_acct.balance + bal
                          else s.as_accounts a) in
        AsmHalt (s with <|
          as_stack := stk; as_accounts := accts' |>)
    | _ => AsmError "selfdestruct: stack underflow"
End

(* ===== External Call Bridge ===== *)

(* Build transaction_parameters from asm_state *)
Definition asm_to_tx_params_def:
  asm_to_tx_params (s : asm_state) : transaction_parameters =
    <| origin := s.as_tx_ctx.tc_origin;
       gasPrice := w2n s.as_tx_ctx.tc_gasprice;
       baseFeePerGas := w2n s.as_block_ctx.bc_basefee;
       baseFeePerBlobGas := w2n s.as_block_ctx.bc_blobbasefee;
       blockNumber := w2n s.as_block_ctx.bc_number;
       blockTimeStamp := w2n s.as_block_ctx.bc_timestamp;
       blockCoinBase := s.as_block_ctx.bc_coinbase;
       blockGasLimit := w2n s.as_block_ctx.bc_gaslimit;
       prevRandao := s.as_block_ctx.bc_prevrandao;
       prevHashes := s.as_prev_hashes;
       blobHashes := s.as_tx_ctx.tc_blobhashes;
       chainId := w2n s.as_tx_ctx.tc_chainid;
       authRefund := 0 |>
End

(* Build execution_state for CALL/STATICCALL directly from asm_state *)
Definition make_asm_call_state_def:
  make_asm_call_state s (target:address) gas value calldata code is_static =
    let caller = s.as_call_ctx.cc_address in
    let tx = make_sub_tx caller target value gas calldata in
    let ctxt = initial_context target code is_static
                 empty_return_destination tx in
    let accounts = transfer_value caller target value s.as_accounts in
    let rb = make_rollback accounts s.as_transient caller target in
    <| contexts := [(ctxt, rb)];
       txParams := asm_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Build execution_state for DELEGATECALL *)
Definition make_asm_delegatecall_state_def:
  make_asm_delegatecall_state s (target:address) gas calldata code is_static =
    let caller = s.as_call_ctx.cc_address in
    let original_caller = s.as_call_ctx.cc_caller in
    let call_value = w2n s.as_call_ctx.cc_callvalue in
    let tx = make_sub_tx original_caller caller call_value gas calldata in
    let ctxt = initial_context caller code is_static
                 empty_return_destination tx in
    let rb = make_rollback s.as_accounts s.as_transient caller target in
    <| contexts := [(ctxt, rb)];
       txParams := asm_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Build execution_state for CREATE/CREATE2 *)
Definition make_asm_create_state_def:
  make_asm_create_state s (new_address:address) gas value init_code =
    let caller = s.as_call_ctx.cc_address in
    let tx = make_sub_tx caller new_address value gas [] in
    let ctxt = initial_context new_address init_code F
                 (Code new_address) tx in
    let accounts = transfer_value caller new_address value s.as_accounts in
    let rb = make_rollback accounts s.as_transient caller new_address in
    <| contexts := [(ctxt, rb)];
       txParams := asm_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Extract result from verifereum run back into asm_state.
   Mirrors extract_venom_result but operates on asm_state directly.
   output_val: success → value pushed onto stack (1w for CALL, addr for CREATE) *)
Definition extract_asm_result_def:
  extract_asm_result s output_val retOff retSize run_result =
    case run_result of
    | NONE => NONE
    | SOME (result, final_state) =>
      (case final_state.contexts of
       | [(ctxt, _)] =>
           let returndata = ctxt.returnData in
           let (success, accounts) =
             (case result of
              | INR NONE => (T, final_state.rollback.accounts)
              | INR (SOME Reverted) => (F, s.as_accounts)
              | _ => (F, s.as_accounts)) in
           let new_logs =
             (case result of
              | INR NONE => ctxt.logs
              | _ => []) in
           let output : bytes32 =
             if success then output_val else 0w in
           let new_transient =
             if success then final_state.rollback.tStorage
             else s.as_transient in
           let ret_bytes = TAKE retSize returndata in
           let new_memory = write_bytes retOff ret_bytes s.as_memory in
           let s' = s with <|
             as_returndata := returndata;
             as_accounts := accounts;
             as_logs := s.as_logs ++ new_logs;
             as_memory := new_memory;
             as_transient := new_transient
           |> in
           SOME (output, s')
       | _ => NONE)
End

(* CALL: pop [gas, addr, value, argsOff, argsSize, retOff, retSize] *)
Definition asm_exec_call_def:
  asm_exec_call is_static s =
    case s.as_stack of
      gas :: addr_w :: value :: ao :: as_ :: ro :: rs :: stk =>
        let calldata = read_bytes (w2n ao) (w2n as_) s.as_memory in
        let target : address = w2w addr_w in
        let code = (lookup_account target s.as_accounts).code in
        let evm_s = make_asm_call_state s target (w2n gas)
                      (w2n value) calldata code is_static in
        (case extract_asm_result s 1w (w2n ro) (w2n rs)
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "call: non-terminating")
    | _ => AsmError "call: stack underflow"
End

(* STATICCALL: pop [gas, addr, argsOff, argsSize, retOff, retSize] *)
Definition asm_exec_staticcall_def:
  asm_exec_staticcall s =
    case s.as_stack of
      gas :: addr_w :: ao :: as_ :: ro :: rs :: stk =>
        let calldata = read_bytes (w2n ao) (w2n as_) s.as_memory in
        let target : address = w2w addr_w in
        let code = (lookup_account target s.as_accounts).code in
        let evm_s = make_asm_call_state s target (w2n gas)
                      0 calldata code T in
        (case extract_asm_result s 1w (w2n ro) (w2n rs)
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "staticcall: non-terminating")
    | _ => AsmError "staticcall: stack underflow"
End

(* DELEGATECALL: pop [gas, addr, argsOff, argsSize, retOff, retSize] *)
Definition asm_exec_delegatecall_def:
  asm_exec_delegatecall s =
    case s.as_stack of
      gas :: addr_w :: ao :: as_ :: ro :: rs :: stk =>
        let calldata = read_bytes (w2n ao) (w2n as_) s.as_memory in
        let target : address = w2w addr_w in
        let code = (lookup_account target s.as_accounts).code in
        let evm_s = make_asm_delegatecall_state s target
                      (w2n gas) calldata code
                      s.as_call_ctx.cc_static in
        (case extract_asm_result s 1w (w2n ro) (w2n rs)
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "delegatecall: non-terminating")
    | _ => AsmError "delegatecall: stack underflow"
End

(* CREATE: pop [value, offset, sz] *)
Definition asm_exec_create_def:
  asm_exec_create s =
    case s.as_stack of
      value :: offset :: sz :: stk =>
        let init_code = read_bytes (w2n offset) (w2n sz) s.as_memory in
        let sender = s.as_call_ctx.cc_address in
        let nonce = (lookup_account sender s.as_accounts).nonce in
        let new_addr = address_for_create sender nonce in
        let gas = s.as_call_ctx.cc_gas -
                  s.as_call_ctx.cc_gas DIV 64 in
        let evm_s = make_asm_create_state s new_addr gas
                      (w2n value) init_code in
        (case extract_asm_result s (w2w new_addr) 0 0
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "create: non-terminating")
    | _ => AsmError "create: stack underflow"
End

(* CREATE2: pop [value, offset, sz, salt] *)
Definition asm_exec_create2_def:
  asm_exec_create2 s =
    case s.as_stack of
      value :: offset :: sz :: salt :: stk =>
        let init_code = read_bytes (w2n offset) (w2n sz) s.as_memory in
        let sender = s.as_call_ctx.cc_address in
        let new_addr = address_for_create2 sender salt init_code in
        let gas = s.as_call_ctx.cc_gas -
                  s.as_call_ctx.cc_gas DIV 64 in
        let evm_s = make_asm_create_state s new_addr gas
                      (w2n value) init_code in
        (case extract_asm_result s (w2w new_addr) 0 0
                (run evm_s) of
           SOME (output, s') =>
             AsmOK (asm_next (s' with as_stack := output :: stk))
         | NONE => AsmError "create2: non-terminating")
    | _ => AsmError "create2: stack underflow"
End

(* ===== Opcode Dispatch (grouped) ===== *)

Definition asm_step_arith_def:
  asm_step_arith name s =
    if name = "ADD" then SOME (asm_binop word_add s) else
    if name = "MUL" then SOME (asm_binop word_mul s) else
    if name = "SUB" then SOME (asm_binop word_sub s) else
    if name = "DIV" then
      SOME (asm_binop (λx y. if y = 0w then 0w else x // y) s) else
    if name = "SDIV" then
      SOME (asm_binop (λx y. if y = 0w then 0w else x / y) s) else
    if name = "MOD" then
      SOME (asm_binop (λx y. if y = 0w then 0w else word_mod x y) s) else
    if name = "SMOD" then
      SOME (asm_binop (λx y. if y = 0w then 0w else word_rem x y) s) else
    if name = "EXP" then SOME (asm_binop word_exp s) else
    if name = "ADDMOD" then SOME (asm_ternop (λa b n.
      if n = 0w then 0w else n2w ((w2n a + w2n b) MOD w2n n)) s) else
    if name = "MULMOD" then SOME (asm_ternop (λa b n.
      if n = 0w then 0w else n2w ((w2n a * w2n b) MOD w2n n)) s) else
    NONE
End

Definition asm_step_compare_def:
  asm_step_compare name s =
    if name = "LT" then
      SOME (asm_binop (λx y. b2w (w2n x < w2n y)) s) else
    if name = "GT" then
      SOME (asm_binop (λx y. b2w (w2n x > w2n y)) s) else
    if name = "SLT" then
      SOME (asm_binop (λx y. b2w (word_lt x y)) s) else
    if name = "SGT" then
      SOME (asm_binop (λx y. b2w (word_gt x y)) s) else
    if name = "EQ" then
      SOME (asm_binop (λx y. b2w (x = y)) s) else
    if name = "ISZERO" then
      SOME (asm_unop (λx. b2w (x = 0w)) s) else
    NONE
End

Definition asm_step_bitwise_def:
  asm_step_bitwise name s =
    if name = "AND" then SOME (asm_binop word_and s) else
    if name = "OR" then SOME (asm_binop word_or s) else
    if name = "XOR" then SOME (asm_binop word_xor s) else
    if name = "NOT" then SOME (asm_unop word_1comp s) else
    if name = "SHL" then
      SOME (asm_binop (λn w. word_lsl w (w2n n)) s) else
    if name = "SHR" then
      SOME (asm_binop (λn w. word_lsr w (w2n n)) s) else
    if name = "SAR" then
      SOME (asm_binop (λn w. word_asr w (w2n n)) s) else
    if name = "SIGNEXTEND" then SOME (asm_binop sign_extend s) else
    if name = "BYTE" then SOME (asm_binop evm_byte s) else
    NONE
End

Definition asm_step_memory_def:
  asm_step_memory name s =
    if name = "POP" then SOME (asm_pop s) else
    if name = "MLOAD" then SOME (asm_mload s) else
    if name = "MSTORE" then SOME (asm_mstore s) else
    if name = "MCOPY" then SOME (asm_copy_to_mem s.as_memory s) else
    if name = "MSIZE" then
      SOME (asm_push_val (n2w (LENGTH s.as_memory)) s) else
    if name = "SLOAD" then SOME (asm_sload s) else
    if name = "SSTORE" then SOME (asm_sstore s) else
    if name = "TLOAD" then SOME (asm_tload s) else
    if name = "TSTORE" then SOME (asm_tstore s) else
    if name = "SHA3" then SOME (asm_sha3 s) else
    NONE
End

Definition asm_step_control_def:
  asm_step_control offset_to_pc name s =
    if name = "JUMP" then SOME (asm_jump offset_to_pc s) else
    if name = "JUMPI" then SOME (asm_jumpi offset_to_pc s) else
    if name = "JUMPDEST" then SOME (AsmOK (asm_next s)) else
    if name = "STOP" then SOME (AsmHalt s) else
    if name = "RETURN" then SOME (asm_return_op s) else
    if name = "REVERT" then SOME (asm_revert_op s) else
    if name = "INVALID" then SOME (AsmFault s) else
    NONE
End

Definition asm_step_extcall_def:
  asm_step_extcall name s =
    if name = "CALL" then
      SOME (asm_exec_call s.as_call_ctx.cc_static s) else
    if name = "STATICCALL" then SOME (asm_exec_staticcall s) else
    if name = "DELEGATECALL" then SOME (asm_exec_delegatecall s) else
    if name = "CREATE" then SOME (asm_exec_create s) else
    if name = "CREATE2" then SOME (asm_exec_create2 s) else
    if name = "SELFDESTRUCT" then SOME (asm_selfdestruct s) else
    NONE
End

Definition asm_step_copy_def:
  asm_step_copy name s =
    if name = "CALLDATACOPY" then
      SOME (asm_copy_to_mem s.as_call_ctx.cc_calldata s) else
    if name = "RETURNDATACOPY" then SOME (asm_returndatacopy s) else
    if name = "CODECOPY" then SOME (asm_copy_to_mem s.as_code s) else
    if name = "EXTCODECOPY" then SOME (asm_extcodecopy s) else
    NONE
End

Definition asm_step_context_def:
  asm_step_context name s =
    if name = "CALLER" then
      SOME (asm_push_val (w2w s.as_call_ctx.cc_caller) s) else
    if name = "ADDRESS" then
      SOME (asm_push_val (w2w s.as_call_ctx.cc_address) s) else
    if name = "CALLVALUE" then
      SOME (asm_push_val s.as_call_ctx.cc_callvalue s) else
    if name = "GAS" then
      SOME (asm_push_val (n2w s.as_call_ctx.cc_gas) s) else
    if name = "CALLDATASIZE" then
      SOME (asm_push_val (n2w (LENGTH s.as_call_ctx.cc_calldata)) s) else
    if name = "CALLDATALOAD" then SOME (asm_state_unop (λoff s.
      word_of_bytes T (0w:bytes32)
        (read_bytes (w2n off) 32 s.as_call_ctx.cc_calldata)) s) else
    if name = "ORIGIN" then
      SOME (asm_push_val (w2w s.as_tx_ctx.tc_origin) s) else
    if name = "GASPRICE" then
      SOME (asm_push_val s.as_tx_ctx.tc_gasprice s) else
    if name = "CHAINID" then
      SOME (asm_push_val s.as_tx_ctx.tc_chainid s) else
    if name = "COINBASE" then
      SOME (asm_push_val (w2w s.as_block_ctx.bc_coinbase) s) else
    if name = "TIMESTAMP" then
      SOME (asm_push_val s.as_block_ctx.bc_timestamp s) else
    if name = "NUMBER" then
      SOME (asm_push_val s.as_block_ctx.bc_number s) else
    if name = "PREVRANDAO" then
      SOME (asm_push_val s.as_block_ctx.bc_prevrandao s) else
    if name = "GASLIMIT" then
      SOME (asm_push_val s.as_block_ctx.bc_gaslimit s) else
    if name = "BASEFEE" then
      SOME (asm_push_val s.as_block_ctx.bc_basefee s) else
    if name = "BLOBBASEFEE" then
      SOME (asm_push_val s.as_block_ctx.bc_blobbasefee s) else
    if name = "BLOCKHASH" then SOME (asm_state_unop (λv s.
      s.as_block_ctx.bc_blockhash (w2n v)) s) else
    if name = "BLOBHASH" then SOME (asm_state_unop (λv s.
      let idx = w2n v in
      let hashes = s.as_tx_ctx.tc_blobhashes in
      if idx < LENGTH hashes then EL idx hashes else 0w) s) else
    if name = "BALANCE" then SOME (asm_state_unop (λaddr s.
      n2w (lookup_account (w2w addr) s.as_accounts).balance) s) else
    if name = "SELFBALANCE" then SOME (asm_push_val
      (n2w (lookup_account s.as_call_ctx.cc_address
              s.as_accounts).balance) s) else
    if name = "CODESIZE" then
      SOME (asm_push_val (n2w (LENGTH s.as_code)) s) else
    if name = "EXTCODESIZE" then SOME (asm_state_unop (λaddr s.
      n2w (LENGTH (lookup_account (w2w addr)
                     s.as_accounts).code)) s) else
    if name = "EXTCODEHASH" then SOME (asm_state_unop (λaddr s.
      let acct = lookup_account (w2w addr) s.as_accounts in
      if account_empty acct then 0w
      else word_of_bytes T (0w:bytes32)
             (Keccak_256_w64 acct.code)) s) else
    if name = "RETURNDATASIZE" then
      SOME (asm_push_val (n2w (LENGTH s.as_returndata)) s) else
    NONE
End

(* Top-level dispatch: try each group, fall back to DUP/SWAP/LOG tables *)
Definition asm_step_op_def:
  asm_step_op offset_to_pc name s =
    case asm_step_arith name s of SOME r => r | NONE =>
    case asm_step_compare name s of SOME r => r | NONE =>
    case asm_step_bitwise name s of SOME r => r | NONE =>
    case asm_step_memory name s of SOME r => r | NONE =>
    case asm_step_control offset_to_pc name s of SOME r => r | NONE =>
    case asm_step_extcall name s of SOME r => r | NONE =>
    case asm_step_copy name s of SOME r => r | NONE =>
    case asm_step_context name s of SOME r => r | NONE =>
    case (ALOOKUP dup_table name,
          ALOOKUP swap_table name,
          ALOOKUP log_table name) of
      (SOME n, _, _) => asm_dup n s
    | (_, SOME n, _) => asm_swap n s
    | (_, _, SOME n) => asm_log n s
    | _ => AsmError ("unknown opcode: " ++ name)
End

(* ===== Single Instruction Step ===== *)

Definition asm_step_def:
  asm_step label_offsets offset_to_pc inst s =
    case inst of
      AsmOp name => asm_step_op offset_to_pc name s
    | AsmPush bytes =>
        AsmOK (asm_next (s with as_stack :=
          word_of_bytes T (0w:bytes32) bytes :: s.as_stack))
    | AsmPushLabel lbl =>
        (case FLOOKUP label_offsets lbl of
           SOME off =>
             AsmOK (asm_next (s with as_stack :=
               n2w off :: s.as_stack))
         | NONE => AsmError ("unknown label: " ++ lbl))
    | AsmPushOfst lbl delta =>
        (case FLOOKUP label_offsets lbl of
           SOME off =>
             AsmOK (asm_next (s with as_stack :=
               n2w (off + delta) :: s.as_stack))
         | NONE => AsmError ("unknown label: " ++ lbl))
    | AsmLabel _ => AsmOK (asm_next s)
    | AsmDataHeader _ => AsmError "executed data header"
    | AsmDataItem _ => AsmError "executed data item"
    | AsmDataLabel _ => AsmError "executed data label"
End

(* ===== Step-Counted Execution (for simulation lemmas) ===== *)

(* Execute exactly n steps from current PC in the program.
   Unlike run_asm_aux, 0 steps = success (not out-of-fuel error).
   PC is always meaningful — fetched from prog via as_pc. *)
Definition asm_steps_def:
  asm_steps label_offsets offset_to_pc prog 0 s = AsmOK s ∧
  asm_steps label_offsets offset_to_pc prog (SUC n) s =
    if s.as_pc ≥ LENGTH prog then AsmError "pc out of bounds"
    else
      case asm_step label_offsets offset_to_pc
             (EL s.as_pc prog) s of
        AsmOK s' => asm_steps label_offsets offset_to_pc prog n s'
      | other => other
End

(* Predicate: asm instructions from codegen are placed at prog[pc..pc+len) *)
Definition asm_block_at_def:
  asm_block_at prog pc asm_insts ⇔
    pc + LENGTH asm_insts ≤ LENGTH prog ∧
    ∀j. j < LENGTH asm_insts ⇒ EL (pc + j) prog = EL j asm_insts
End

(* ===== Fuel-Based Execution ===== *)

Definition run_asm_aux_def:
  run_asm_aux label_offsets offset_to_pc prog (fuel:num) s =
    if fuel = 0 then AsmError "out of fuel"
    else if s.as_pc ≥ LENGTH prog then AsmHalt s
    else
      case asm_step label_offsets offset_to_pc
             (EL s.as_pc prog) s of
        AsmOK s' =>
          run_asm_aux label_offsets offset_to_pc prog (fuel - 1) s'
      | other => other
Termination
  WF_REL_TAC `measure (λ(_, _, _, fuel, _). fuel)`
End

Definition run_asm_def:
  run_asm fuel prog s =
    let (_, label_offsets) = compute_label_offsets prog in
    let offset_to_pc = build_offset_to_pc prog in
    run_asm_aux label_offsets offset_to_pc prog fuel s
End
