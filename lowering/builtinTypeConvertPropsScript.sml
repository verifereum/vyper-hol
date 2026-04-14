Theory builtinTypeConvertProps
Ancestors
  builtinTypeConvert1 builtinTypeConvert2

(* ===== Semantic specification of type conversion results ===== *)

(* Helper: load a bytestring's data word from memory.
   Bytestrings are stored as [length:32][data:32] at pointer w.
   load_bytestring_val reads data, right-shifts by (32-length)*8 bits.
   shift_fn selects word_asr (signed) or word_lsr (unsigned). *)
Definition load_bytestring_val_def:
  load_bytestring_val shift_fn (w:bytes32) (ss:venom_state) =
    let length = mload (w2n w) ss in
    let data = mload (w2n w + 32) ss in
    let num_zero_bits = (32w - length) * 8w in
    shift_fn data (w2n num_zero_bits)
End

(* The value computed by compile_type_convert on the OK path.
   For cases that can revert, this is the value when they don't. *)
Definition type_convert_val_def:
  (* Bool: iszero(iszero(x)) = bool_to_word (x ≠ 0w) *)
  type_convert_val ConvToBool w ss =
    bool_to_word (w ≠ 0w) ∧
  (* Int→Int: identity (bounds check only) *)
  type_convert_val (ConvIntToInt _ _ _ _) w ss = w ∧
  (* BytesM→Int: right-shift (signed or unsigned) *)
  type_convert_val (ConvBytesToInt m is_signed _) w ss =
    (let shift = (32 - m) * 8 in
     if is_signed then word_asr w shift
     else word_lsr w shift) ∧
  (* Int→BytesM: left-shift *)
  type_convert_val (ConvIntToBytesM _ _ m) w ss =
    word_lsl w ((32 - m) * 8) ∧
  (* Int→Decimal: multiply by divisor *)
  type_convert_val (ConvIntToDecimal _ _ divisor _ _) w ss =
    w * n2w divisor ∧
  (* Decimal→Int: signed divide by divisor *)
  type_convert_val (ConvDecimalToInt divisor _ _ _ _ _) w ss =
    safe_sdiv w (n2w divisor) ∧
  (* Bool→Decimal: multiply by divisor *)
  type_convert_val (ConvBoolToDecimal divisor) w ss =
    w * n2w divisor ∧
  (* Int→Address: identity (bounds check only) *)
  type_convert_val ConvToAddress w ss = w ∧
  (* BytesM→Address: right-shift (unsigned) *)
  type_convert_val (ConvBytesToAddress m) w ss =
    word_lsr w ((32 - m) * 8) ∧
  (* Int→Flag: identity (mask check only) *)
  type_convert_val (ConvToFlag _) w ss = w ∧
  (* BytesM→Decimal: signed right-shift *)
  type_convert_val (ConvBytesMToDecimal m _ _ _) w ss =
    word_asr w ((32 - m) * 8) ∧
  (* BytesM→BytesM: identity (downcast check only) *)
  type_convert_val (ConvBytesMToBytesM _ _) w ss = w ∧
  (* Bytestring→Bool: load + shift + bool *)
  type_convert_val ConvBytestringToBool w ss =
    bool_to_word (load_bytestring_val word_lsr w ss ≠ 0w) ∧
  (* Bytestring→Int: load + shift *)
  type_convert_val (ConvBytestringToInt is_signed _) w ss =
    load_bytestring_val (if is_signed then word_asr else word_lsr) w ss ∧
  (* Bytestring→Address: load + unsigned shift *)
  type_convert_val ConvBytestringToAddress w ss =
    load_bytestring_val word_lsr w ss ∧
  (* Bytestring→Decimal: load + signed shift *)
  type_convert_val (ConvBytestringToDecimal _ _ _) w ss =
    load_bytestring_val word_asr w ss ∧
  (* Bytestring→BytesM: load + re-shift to left-align *)
  type_convert_val (ConvBytestringToBytesM _) w ss =
    (let shifted_r = load_bytestring_val word_lsr w ss in
     let length = mload (w2n w) ss in
     let num_zero_bits = (32w - length) * 8w in
     word_lsl shifted_r (w2n num_zero_bits)) ∧
  (* Bytestring downcast: identity (length check only) *)
  type_convert_val (ConvBytestringCast _) w ss = w ∧
  (* Fixed→Bytestring: returns new buffer pointer (depends on alloca state) *)
  type_convert_val (ConvFixedToBytestring _) w ss =
    n2w ss.vs_alloca_next ∧
  (* Identity: no-op *)
  type_convert_val ConvIdentity w ss = w
End

(* Combine the per-arm theorems from split files *)

Theorem compile_type_convert_correct:
  ∀ v conv_op w ss st op st'.
    compile_type_convert v conv_op st = (op, st') ∧
    eval_operand v ss = SOME w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (type_convert_val conv_op w ss)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
