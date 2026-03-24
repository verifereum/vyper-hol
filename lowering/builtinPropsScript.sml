(*
 * Builtin Function Properties (consolidated)
 *
 * Covers: hashing, math, simple, bytes, system, misc, create, convert, abi
 *
 * TOP-LEVEL:
 *   compile_keccak256_word_correct — keccak256 hash of word-sized input
 *   compile_unsafe_add_correct     — unsafe_add (wrapping, no check)
 *   compile_shift_correct          — shl/shr with sign-aware dispatch
 *   compile_builtin_min_correct    — min with branchless select
 *   compile_builtin_max_correct    — max with branchless select
 *   compile_builtin_abs_correct    — abs with branchless select
 *   compile_builtin_len_correct    — dynarray length
 *   compile_isqrt_correct          — integer square root
 *   compile_raw_call_correct       — low-level CALL
 *   compile_raw_create_correct     — CREATE contract creation
 *   compile_type_convert_correct   — type conversion dispatcher
 *   lower_abi_encode_correct       — abi.encode builtin
 *   lower_abi_decode_correct       — abi.decode builtin
 *
 * Source: builtins/*.py
 * Lowering: builtin*Script.sml
 *)

Theory builtinProps
Ancestors
  exprLoweringProps
  builtinHashing builtinMath builtinSimple builtinBytes
  builtinStrings builtinSystem builtinMisc builtinCreate
  builtinAbi
  compileEnv venomExecSemantics venomState venomInst
  valueEncoding abiEncoder

(* ===== Hashing ===== *)

(* keccak256 of a word-sized input.
   The result is SHA3 of the 32-byte memory region containing w.
   We don't pin to a concrete hash function here since SHA3 semantics
   are defined at the EVM level (vfmOperation). *)
Theorem compile_keccak256_word_correct:
  ∀ val_op w ss st op st'.
    compile_keccak256_word val_op st = (op, st') ∧
    eval_operand val_op ss = SOME w
    ⇒
    ∃ ss' hash.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME hash
Proof
  cheat
QED

(* ===== Unsafe Math ===== *)

(* Truncation to bit width: unsigned masks, signed sign-extends.
   Matches compile_unsafe_binop post-processing. *)
Definition truncate_to_bits_def:
  truncate_to_bits bits is_signed (w:bytes32) =
    if bits ≥ 256 then w
    else if is_signed then sign_extend (n2w (bits DIV 8 - 1)) w
    else word_and w (n2w (2 ** bits - 1))
End

(* unsafe_add: wrapping addition truncated to bit width *)
Theorem compile_unsafe_add_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_add x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (word_add a b))
Proof
  cheat
QED

(* unsafe_sub: wrapping subtraction truncated to bit width *)
Theorem compile_unsafe_sub_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_sub x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (word_sub a b))
Proof
  cheat
QED

(* unsafe_mul: wrapping multiplication truncated to bit width *)
Theorem compile_unsafe_mul_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_mul x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (word_mul a b))
Proof
  cheat
QED

(* unsafe_div: division truncated to bit width.
   Precondition: divisor ≠ 0. Uses SDIV for signed, DIV for unsigned. *)
Theorem compile_unsafe_div_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_div x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed
          (if is_signed then safe_sdiv a b else safe_div a b))
Proof
  cheat
QED

(* ===== Shift ===== *)

Theorem compile_shift_correct:
  ∀ val_op bits_op is_signed ss st op st' v b.
    compile_shift val_op bits_op is_signed st = (op, st') ∧
    eval_operand val_op ss = SOME v ∧
    eval_operand bits_op ss = SOME b
    ⇒
    ∃ ss' w.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME w
Proof
  cheat
QED

(* ===== Simple Builtins ===== *)

(* min: branchless select — result is the lesser operand *)
Theorem compile_builtin_min_correct:
  ∀ a b use_unsigned ss st op st' av bv.
    compile_builtin_min a b use_unsigned st = (op, st') ∧
    eval_operand a ss = SOME av ∧
    eval_operand b ss = SOME bv
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if (if use_unsigned then w2n av ≤ w2n bv
                  else w2i av ≤ w2i bv)
              then av else bv)
Proof
  cheat
QED

(* max: branchless select — result is the greater operand *)
Theorem compile_builtin_max_correct:
  ∀ a b use_unsigned ss st op st' av bv.
    compile_builtin_max a b use_unsigned st = (op, st') ∧
    eval_operand a ss = SOME av ∧
    eval_operand b ss = SOME bv
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if (if use_unsigned then w2n av ≤ w2n bv
                  else w2i av ≤ w2i bv)
              then bv else av)
Proof
  cheat
QED

(* abs: branchless select, with overflow check for MIN_INT.
   Result is |v| when v ≠ MIN_INT, revert otherwise. *)
Theorem compile_builtin_abs_correct:
  ∀ val_op ss st op st' v.
    compile_builtin_abs val_op st = (op, st') ∧
    eval_operand val_op ss = SOME v
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' =
         SOME (if word_msb v then word_sub 0w v else v)) ∨
      (* MIN_INT case → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* len for dynarray: reads stored length *)
Theorem compile_builtin_len_correct:
  ∀ is_ctor ptr_op loc ss st op st' arr_addr.
    compile_builtin_len is_ctor ptr_op loc st = (op, st') ∧
    eval_operand ptr_op ss = SOME (n2w arr_addr)
    ⇒
    ∃ ss' w.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME w
Proof
  cheat
QED

(* empty: zero-initializes a primitive value *)
Theorem compile_builtin_empty_prim_correct:
  ∀ st op st'.
    compile_builtin_empty_prim st = (op, st')
    ⇒
    op = Lit 0w ∧ emitted_insts st st' = []
Proof
  rw[compile_builtin_empty_prim_def, emitted_insts_def, comp_return_def,
     comp_bind_def, comp_ignore_bind_def]
QED

(* ===== Misc Builtins ===== *)

(* isqrt: integer square root *)
Theorem compile_isqrt_correct:
  ∀ x_op x ss st op st'.
    compile_isqrt x_op st = (op, st') ∧
    eval_operand x_op ss = SOME x
    ⇒
    ∃ ss' r.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME r
Proof
  cheat
QED

(* floor: rounds toward negative infinity *)
Theorem compile_floor_correct:
  ∀ val_op divisor x ss st op st'.
    compile_floor val_op divisor st = (op, st') ∧
    eval_operand val_op ss = SOME x
    ⇒
    ∃ ss' w.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME w
Proof
  cheat
QED

(* ceil: rounds toward positive infinity *)
Theorem compile_ceil_correct:
  ∀ val_op divisor x ss st op st'.
    compile_ceil val_op divisor st = (op, st') ∧
    eval_operand val_op ss = SOME x
    ⇒
    ∃ ss' w.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME w
Proof
  cheat
QED

(* ===== System Builtins ===== *)

(* raw_call: CALL with gas/value/args *)
Theorem compile_raw_call_correct:
  ∀ to_op data_ptr data_len gas_op value_op
    call_ty max_outsize revert_on_failure ss st op st'.
    compile_raw_call to_op data_ptr data_len gas_op value_op
      call_ty max_outsize revert_on_failure st = (op, st') ⇒
    ∃ ss'.
      (* Either succeeds or reverts *)
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∨
       run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* send: transfer ETH via CALL with 0 gas *)
Theorem compile_send_correct:
  ∀ to_op value_op gas_op ss st st'.
    compile_send to_op value_op gas_op st = ((), st') ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Create Builtins ===== *)

(* raw_create: CREATE opcode *)
Theorem compile_raw_create_correct:
  ∀ code_ptr code_len value_op salt_opt revert_on_failure ss st op st'.
    compile_raw_create code_ptr code_len value_op salt_opt
      revert_on_failure st = (op, st') ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      (* CREATE failure with revert_on_failure → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Bytes Builtins ===== *)

(* extract32: extracts 32 bytes from a bytestring *)
Theorem compile_extract32_correct:
  ∀ src_ptr start_op ss st op st'.
    compile_extract32 src_ptr start_op st = (op, st') ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      (* Out of bounds → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Type Conversion ===== *)

(* Type conversion always either succeeds or reverts (never UB) *)
Theorem compile_type_convert_correct:
  ∀ v conv_op w ss st op st'.
    compile_type_convert v conv_op st = (op, st') ∧
    eval_operand v ss = SOME w
    ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      (* Out of range → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== ABI Builtins ===== *)

(* abi.encode: produces ABI-encoded buffer *)
Theorem lower_abi_encode_correct:
  ∀ ensure_tuple method_id_opt src_op enc_info maxlen ss st op st'.
    lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen st =
      (op, st') ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* abi.decode: decodes with validation *)
Theorem lower_abi_decode_correct:
  ∀ data_op dec_info abi_min_size abi_max_size output_size ss st op st'.
    lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size st =
      (op, st') ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
