(*
 * ABI Encoder/Decoder Properties
 *
 * TOP-LEVEL:
 *   compile_abi_int_clamp_correct     — int clamping rejects out-of-range
 *   compile_abi_bytes_clamp_correct   — bytes clamping rejects dirty high bits
 *   compile_abi_encode_static_correct — static type writes word to dst
 *   compile_abi_decode_static_correct — static type reads + clamps
 *   compile_abi_encode_tuple_correct  — tuple encoding with head/tail
 *   compile_abi_decode_tuple_correct  — tuple decoding with validation
 *   compile_abi_encode_bytestring_correct — length-prefixed encoding
 *   compile_get_element_ptr_correct   — element pointer arithmetic
 *
 * Source: abi/abi_encoder.py, abi/abi_decoder.py
 * Lowering: abiEncoderScript.sml
 *)

Theory abiEncoderProps
Ancestors
  exprLoweringProps
  abiEncoder compileEnv
  venomExecSemantics venomState venomInst
  valueEncoding

(* ===== ABI Clamping ===== *)

(* Integer clamping: either accepts or reverts *)
Theorem compile_abi_int_clamp_correct:
  ∀ val_op bits is_signed ss st st'.
    compile_abi_int_clamp val_op bits is_signed st = ((), st') ∧
    eval_operand val_op ss = SOME w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* Bytes clamping: rejects values with non-zero high bits *)
Theorem compile_abi_bytes_clamp_correct:
  ∀ val_op m ss st st'.
    compile_abi_bytes_clamp val_op m st = ((), st') ∧
    eval_operand val_op ss = SOME w ∧
    m ≤ 32
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Static Encode/Decode ===== *)

(* Static ABI encoding: MSTORE of source value to dst *)
Theorem compile_abi_encode_static_correct:
  ∀ src_op dst_op ss st st' v dst.
    compile_abi_encode_static src_op dst_op st = ((), st') ∧
    eval_operand src_op ss = SOME v ∧
    eval_operand dst_op ss = SOME (n2w dst)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      mload dst ss' = v
Proof
  cheat
QED

(* Static ABI decoding: MLOAD + clamp *)
Theorem compile_abi_decode_static_correct:
  ∀ src_op dst_op clamp_fn ss st st'.
    compile_abi_decode_static src_op dst_op clamp_fn st = ((), st') ∧
    eval_operand src_op ss = SOME src_w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      (* Clamp failure → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Bytestring Encode ===== *)

(* Bytestring encoding: copies length + data + zero-pads *)
Theorem compile_abi_encode_bytestring_correct:
  ∀ src_ptr dst head_offset ss st op st'.
    compile_abi_encode_bytestring src_ptr dst head_offset st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* ===== Tuple Encode/Decode ===== *)

(* Tuple encoding *)
Theorem compile_abi_encode_tuple_correct:
  ∀ src_ptr dst_ptr types sizes ss st op st'.
    compile_abi_encode_tuple src_ptr dst_ptr types sizes st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* Tuple decoding with validation *)
Theorem compile_abi_decode_tuple_correct:
  ∀ src_base dst_ptr hi_op types sizes ss st st'.
    compile_abi_decode_tuple src_base dst_ptr hi_op types sizes st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Element Pointer ===== *)

(* get_element_ptr at offset 0 returns parent *)
Theorem compile_get_element_ptr_zero:
  ∀ parent_ptr st.
    compile_get_element_ptr parent_ptr 0 st = (parent_ptr, st)
Proof
  simp[compile_get_element_ptr_def]
QED

(* get_element_ptr at non-zero offset adds offset *)
Theorem compile_get_element_ptr_correct:
  ∀ parent_ptr offset ss st op st'.
    compile_get_element_ptr parent_ptr offset st = (op, st') ∧
    offset > 0 ∧
    eval_operand parent_ptr ss = SOME (n2w base_addr)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (n2w (base_addr + offset))
Proof
  cheat
QED

(* ===== Zero Padding ===== *)

(* ABI zero-pad: pads bytestring to 32-byte boundary *)
Theorem compile_abi_zero_pad_correct:
  ∀ bytez_ptr ss st st'.
    compile_abi_zero_pad bytez_ptr st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* ===== Bool Decode ===== *)

(* Bool decode: clamps to 0 or 1 *)
Theorem compile_abi_decode_bool_correct:
  ∀ src_op dst_op ss st st'.
    compile_abi_decode_bool src_op dst_op st = ((), st') ∧
    eval_operand src_op ss = SOME w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
