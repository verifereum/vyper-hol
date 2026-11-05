(* Dynamic-source conversion simulation before the exact source-exemption lift. *)
Theory exprSimConvertFromBytes
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimConvert exprSimHyps  exprLowering compileEnv
  exprSimBuffer valueEncoding valueEncodingProofs
  vyperTypeSystem vyperValueOperation vyperValue vyperInterpreter
  fragExec freshWrites loweringSlice venomExecSemantics venomState
  words list integer_word emitHelperProps builtinConvertPrefix exprLoweringProps
  venomMemDefs vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  builtinIntClamp varsExt exprOperandVar vyperState

val () = augment_srw_ss [rewrites
  [fcpLib.INDEX_CONV ``dimindex(:8)``,
   fcpLib.INDEX_CONV ``dimindex(:160)``,
   fcpLib.INDEX_CONV ``dimindex(:256)``]];

Theorem dynamic_emit_update_exact[local]:
  emit_op opc ops st = (v,st') /\ fresh_vars_wrt st ss /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) ss =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) z ss) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME z /\ fresh_vars_wrt st' ss' /\
    ss'.vs_memory = ss.vs_memory /\ ss'.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p ss' = SOME w)
Proof
  cheat
QED

Theorem dynamic_emit_load_exact[local]:
  emit_op MLOAD [a] st = (v,st') /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME (mload (w2n x) ss) /\
    fresh_vars_wrt st' ss' /\ ss'.vs_memory = ss.vs_memory /\
    ss'.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p ss' = SOME w)
Proof
  cheat
QED

Theorem dynamic_emit_binary_exact[local]:
  emit_op opc [a;b] st = (v,st') /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt st ss /\
  ((opc = ADD /\ z = x + y) \/ (opc = SUB /\ z = x - y) \/
   (opc = MUL /\ z = x * y) \/
   (opc = SHR /\ z = word_lsr y (w2n x)) \/
   (opc = SAR /\ z = word_asr y (w2n x))) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    eval_operand v ss' = SOME z /\ fresh_vars_wrt st' ss' /\
    ss'.vs_memory = ss.vs_memory /\ ss'.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p ss' = SOME w)
Proof
  cheat
QED

Theorem dynamic_emit_iszero_exact[local]:
  emit_op ISZERO [a] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (if x = 0w then 1w else 0w) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_mask_payload_exact[local]:
  emit_op ISZERO [len] sa = (empty,s1) /\
  emit_op ISZERO [empty] s1 = (nonempty,s2) /\
  emit_op MUL [data;nonempty] s2 = (masked,sb) /\
  eval_operand len ss = SOME n /\ eval_operand data ss = SOME d /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand masked sf = SOME (if n = 0w then 0w else d) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_load_payload_exact[local]:
  emit_op MLOAD [v] sa = (len,s1) /\
  emit_op ADD [v; Lit 32w] s1 = (dp,s2) /\
  emit_op MLOAD [dp] s2 = (data,sb) /\
  eval_operand v ss = SOME addrword /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand len sf = SOME (mload (w2n addrword) ss) /\
    eval_operand data sf = SOME (mload (w2n (addrword + 32w)) ss) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_shift_payload_exact[local]:
  emit_op SUB [Lit 32w; len] sa = (sub,s1) /\
  emit_op MUL [sub; Lit 8w] s1 = (k,s2) /\
  emit_op opc [k; data] s2 = (r,sb) /\ (opc = SHR \/ opc = SAR) /\
  eval_operand len ss = SOME n /\ eval_operand data ss = SOME d /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand k sf = SOME ((32w - n) * 8w) /\
    eval_operand r sf = SOME
      (if opc = SHR then word_lsr d (w2n ((32w - n) * 8w))
       else word_asr d (w2n ((32w - n) * 8w))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_load_word_raw_exact[local]:
  load_bytestring_as_word v opc sa = ((r,k),sb) /\
  (opc = SHR \/ opc = SAR) /\ eval_operand v ss = SOME a /\
  mload (w2n a) ss = n /\ mload (w2n (a + 32w)) ss = d /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand k sf = SOME ((32w - n) * 8w) /\
    eval_operand r sf = SOME
      (if opc = SHR then word_lsr d (w2n ((32w - n) * 8w))
       else word_asr (if n = 0w then 0w else d)
              (w2n ((32w - n) * 8w))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED




Theorem dynamic_convert_typing_boundary[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es ==>
  valid_conversion (expr_type e) dst /\ ann = dst /\
  well_formed_type env.type_defs dst
Proof
  cheat
QED

Theorem dynamic_decimal_convert_op[local]:
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) =
    ConvBytestringToDecimal 10000000000
      (w2i (FST (type_bounds (BaseT DecimalT))))
      (w2i (SND (type_bounds (BaseT DecimalT)))) n
Proof
  cheat
QED

Theorem dynamic_bytes_scalar_partition[local]:
  valid_conversion (BaseT (BytesT (Dynamic n))) dst /\
  ~is_bytestring_type dst ==>
  (dst = BaseT BoolT /\ n <= 32) \/
  (?b. dst = BaseT (UintT b) /\ n <= 32) \/
  (?b. dst = BaseT (IntT b) /\ n <= 32) \/
  (dst = BaseT AddressT /\ n <= 32) \/
  (dst = BaseT DecimalT /\ n <= 32) \/
  (?m. dst = BaseT (BytesT (Fixed m)) /\ n <= m)
Proof
  cheat
QED

Theorem dynamic_string_scalar_partition[local]:
  valid_conversion (BaseT (StringT n)) dst /\
  ~is_bytestring_type dst ==>
  ?m. dst = BaseT (BytesT (Fixed m)) /\ n <= m
Proof
  cheat
QED

Theorem dynamic_scalar_convert_ops[local]:
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT BoolT) =
    ConvBytestringToBool /\
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT AddressT) =
    ConvBytestringToInt F 160 n /\
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT (IntT b)) =
    ConvBytestringToInt T b n /\
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) =
    ConvBytestringToInt F b n /\
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Fixed m))) =
    ConvBytestringToBytesM m /\
  mk_convert_op (BaseT (StringT n)) (BaseT (BytesT (Fixed m))) =
    ConvBytestringToBytesM m
Proof
  cheat
QED

(* The dynamic representation constrains exactly the payload bytes, not a
   capacity-sized or word-rounded suffix. *)
Theorem dynamic_bytes_memory_boundary[local]:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) off mem <=>
  mem_word_at off mem = n2w (LENGTH bs) /\
  mem_bytes_at (off + 32) (LENGTH bs) mem = bs
Proof
  cheat
QED

Theorem dynamic_empty_memory_boundary[local]:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV []) off mem <=>
  mem_word_at off mem = 0w
Proof
  cheat
QED

Theorem dynamic_string_memory_boundary[local]:
  val_in_memory (BaseTV (StringT n)) (StringV str) off mem <=>
  mem_word_at off mem = n2w (LENGTH str) /\
  mem_bytes_at (off + 32) (LENGTH str) mem = MAP (n2w o ORD) str
Proof
  cheat
QED

Theorem dynamic_bytes_operand_memory[local]:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op s ==>
  ?w. eval_operand op s = SOME w /\
      mem_word_at (w2n w) s.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs
Proof
  cheat
QED

Theorem dynamic_get_byte_encoding[local]:
  j < 32 ==>
  byte$get_byte (n2w j:bytes32) (word_of_bytes_be bs:bytes32) T =
    if j < LENGTH bs then EL j bs else 0w
Proof
  cheat
QED

Theorem dynamic_get_byte_bit[local]:
  j < 32 /\ r < 8 ==>
  ((byte$get_byte (n2w j:bytes32) (w:bytes32) T : byte) ' r =
   w ' (8 * (31 - j) + r))
Proof
  cheat
QED

Theorem dynamic_word_bit_byte[local]:
  i < 256 ==>
  ((w:bytes32) ' i =
   (byte$get_byte (n2w (31 - i DIV 8):bytes32) w T : byte) ' (i MOD 8))
Proof
  cheat
QED

Theorem dynamic_payload_prefix_bits[local]:
  n <= 32 /\ LENGTH xs = 32 /\ LENGTH bs = n /\ TAKE n xs = bs ==>
  !i. 8 * (32 - n) <= i /\ i < 256 ==>
    ((word_of_bytes_be xs:bytes32) ' i =
     (word_of_bytes_be bs:bytes32) ' i)
Proof
  cheat
QED

Theorem dynamic_payload_low_bits[local]:
  LENGTH bs <= 32 ==>
  !i. i < 8 * (32 - LENGTH bs) ==>
    ~((word_of_bytes_be bs:bytes32) ' i)
Proof
  cheat
QED

Theorem dynamic_lsr_high_cong[local]:
  (!i. k <= i /\ i < 256 ==> (u:bytes32) ' i = (v:bytes32) ' i) ==>
  word_lsr u k = word_lsr v k
Proof
  cheat
QED

Theorem dynamic_asr_high_cong[local]:
  k < 256 /\
  (!i. k <= i /\ i < 256 ==> (u:bytes32) ' i = (v:bytes32) ' i) ==>
  word_asr u k = word_asr v k
Proof
  cheat
QED

Theorem dynamic_lsr_lsl_mask[local]:
  (!i. i < k /\ i < 256 ==> ~((w:bytes32) ' i)) ==>
  word_lsl (word_lsr w k) k = w
Proof
  cheat
QED

Theorem dynamic_payload_lsr[local]:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs ==>
  word_lsr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)) =
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  cheat
QED

Theorem dynamic_payload_asr[local]:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs /\ bs <> [] ==>
  word_asr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)) =
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  cheat
QED

Theorem dynamic_payload_mask[local]:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs ==>
  word_lsl
    (word_lsr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)))
    (8 * (32 - LENGTH bs)) = word_of_bytes_be bs
Proof
  cheat
QED

Theorem dynamic_memory_payload_prefix[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  LENGTH (TAKE 32 (DROP off mem ++ REPLICATE 32 0w)) = 32 /\
  TAKE (LENGTH bs) (TAKE 32 (DROP off mem ++ REPLICATE 32 0w)) = bs
Proof
  cheat
QED

Theorem dynamic_memory_payload_lsr[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  word_lsr (mem_word_at off mem) (8 * (32 - LENGTH bs)) =
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  cheat
QED

Theorem dynamic_memory_payload_asr[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs /\ bs <> [] ==>
  word_asr (mem_word_at off mem) (8 * (32 - LENGTH bs)) =
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  cheat
QED

Theorem dynamic_memory_payload_mask[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  word_lsl
    (word_lsr (mem_word_at off mem) (8 * (32 - LENGTH bs)))
    (8 * (32 - LENGTH bs)) = (word_of_bytes_be bs:bytes32)
Proof
  cheat
QED

Theorem dynamic_string_operand_memory[local]:
  evaluate_type (get_tenv cx) (BaseT (StringT n)) = SOME (BaseTV (StringT n)) /\
  expr_val_rel cx (BaseT (StringT n)) (StringV str) op s ==>
  ?w. eval_operand op s = SOME w /\
      mem_word_at (w2n w) s.vs_memory = n2w (LENGTH str) /\
      mem_bytes_at (w2n w + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str
Proof
  cheat
QED

Theorem dynamic_load_word_decoded_exact[local]:
  load_bytestring_as_word v opc sa = ((r,k),sb) /\
  (opc = SHR \/ opc = SAR) /\ (opc = SAR ==> bs <> []) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= 32 /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand k sf = SOME (n2w (8 * (32 - LENGTH bs))) /\
    eval_operand r sf = SOME
      (if opc = SHR then word_lsr (word_of_bytes_be bs) (8 * (32 - LENGTH bs))
       else word_asr (word_of_bytes_be bs) (8 * (32 - LENGTH bs))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_local_region_bound[local]:
  local_ptrs_rel func cenv scopes s /\ local_region cenv scopes s name b sz ==>
  b + sz <= s.vs_alloca_next
Proof
  cheat
QED

Theorem dynamic_operand_header_bound[local]:
  stmt_state_rel ctx func cenv cx es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  expr_val_at cenv cx t sarg sa es v op s /\
  32 <= val_footprint tv v /\ eval_operand op s = SOME a ==>
  w2n a + 32 < dimword (:256)
Proof
  cheat
QED

Theorem dynamic_convert_operand_typed[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
  (do r <- eval_expr cx e1; read_result cx r od) es = (INL v, es1) ==>
  ?stv. evaluate_type (get_tenv cx) (expr_type e1) = SOME stv /\
        value_has_type stv v
Proof
  cheat
QED

Theorem dynamic_bytes_value_typed[local]:
  value_has_type (BaseTV (BytesT (Dynamic n))) v ==>
  ?bs. v = BytesV bs /\ LENGTH bs <= n
Proof
  cheat
QED

Theorem dynamic_string_value_typed[local]:
  value_has_type (BaseTV (StringT n)) v ==>
  ?str. v = StringV str /\ LENGTH str <= n
Proof
  cheat
QED

Theorem dynamic_bytes_operand_view[local]:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME stv /\
  value_has_type stv v /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_rel cx (BaseT (BytesT (Dynamic n))) v op s /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sarg sa es v op s ==>
  ?bs a. v = BytesV bs /\ LENGTH bs <= n /\
    eval_operand op s = SOME a /\
    w2n a + 32 < dimword (:256) /\
    mem_word_at (w2n a) s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (w2n a + 32) (LENGTH bs) s.vs_memory = bs
Proof
  cheat
QED

Theorem dynamic_string_operand_view[local]:
  evaluate_type (get_tenv cx) (BaseT (StringT n)) = SOME stv /\
  value_has_type stv v /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_rel cx (BaseT (StringT n)) v op s /\
  expr_val_at cenv cx (BaseT (StringT n)) sarg sa es v op s ==>
  ?str a. v = StringV str /\ LENGTH str <= n /\
    eval_operand op s = SOME a /\
    w2n a + 32 < dimword (:256) /\
    mem_word_at (w2n a) s.vs_memory = n2w (LENGTH str) /\
    mem_bytes_at (w2n a + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str
Proof
  cheat
QED

Theorem dynamic_unsigned_padding[local]:
  LENGTH bs <= 32 ==>
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) =
    word_of_bytes_be (PAD_LEFT 0w 32 bs)
Proof
  cheat
QED

Theorem dynamic_payload_zero[local]:
  LENGTH bs <= 32 ==>
  (((word_of_bytes_be bs:bytes32) = 0w) <=> EVERY (\b. b = 0w) bs)
Proof
  cheat
QED

Theorem dynamic_unsigned_zero[local]:
  LENGTH bs <= 32 ==>
  ((word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) = 0w) <=>
    EVERY (\b. b = 0w) bs)
Proof
  cheat
QED

Theorem dynamic_unsigned_bound[local]:
  LENGTH bs <= 32 ==>
  w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) <
    2 ** (8 * LENGTH bs)
Proof
  cheat
QED

Theorem dynamic_fixed_bytes_encoding[local]:
  LENGTH bs <= m /\ m <= 32 ==>
  typed_val_to_w256 (BaseTV (BytesT (Fixed m)))
    (BytesV (PAD_RIGHT 0w m bs)) = (word_of_bytes_be bs:bytes32)
Proof
  cheat
QED

Theorem dynamic_signed_padding[local]:
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) =
  word_asr (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32)
    (8 * (32 - LENGTH bs))
Proof
  cheat
QED

Theorem dynamic_signed_roundtrip[local]:
  i2w (w2i (word_asr (word_of_bytes_be bs:bytes32)
    (8 * (32 - LENGTH bs)))) =
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  cheat
QED

Theorem dynamic_asr_sign[local]:
  word_msb (word_asr (w:bytes32) k) = word_msb w
Proof
  cheat
QED

Theorem dynamic_asr_complement[local]:
  word_1comp (word_asr (w:bytes32) k) = word_asr (word_1comp w) k
Proof
  cheat
QED

Theorem dynamic_asr_clear_sign[local]:
  ~word_msb (w:bytes32) ==> word_asr w k = word_lsr w k
Proof
  cheat
QED

Theorem dynamic_complement_sign[local]:
  word_msb (word_1comp (w:bytes32)) = ~word_msb w
Proof
  cheat
QED

Theorem dynamic_clear_sign_bound[local]:
  ~word_msb (w:bytes32) ==> w2n w < 2 ** 255
Proof
  cheat
QED

Theorem dynamic_clear_sign_value[local]:
  ~word_msb (w:bytes32) ==> w2i w = &(w2n w)
Proof
  cheat
QED

Theorem dynamic_clear_sign_lsr_bound[local]:
  ~word_msb (w:bytes32) /\ k < 256 ==>
  w2n (word_lsr w k) < 2 ** (255 - k)
Proof
  cheat
QED

Theorem dynamic_negative_complement_value[local]:
  word_msb (w:bytes32) ==> w2i w = -(&(w2n (word_1comp w))) - 1
Proof
  cheat
QED

Theorem dynamic_asr_signed_range[local]:
  !(w:bytes32) k. k < 256 ==>
  -(&(2 ** (255-k))) <= w2i (word_asr w k) /\
  w2i (word_asr w k) < &(2 ** (255-k))
Proof
  cheat
QED

Theorem dynamic_payload_signed_range[local]:
  0 < LENGTH bs /\ LENGTH bs <= 32 ==>
  -(&(2 ** (8 * LENGTH bs - 1))) <=
    w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) /\
  w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) <
    &(2 ** (8 * LENGTH bs - 1))
Proof
  cheat
QED

Theorem dynamic_signed_range_widen[local]:
  0 < a /\ a <= b /\ -(&(2 ** (a-1))) <= i /\ i < &(2 ** (a-1)) ==>
  within_int_bound (Signed b) i
Proof
  cheat
QED

Theorem dynamic_payload_signed_bound[local]:
  0 < LENGTH bs /\ LENGTH bs <= 32 /\ 8 * LENGTH bs <= b ==>
  within_int_bound (Signed b)
    (w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))))
Proof
  cheat
QED

Theorem dynamic_payload_decimal_bound[local]:
  0 < LENGTH bs /\ LENGTH bs <= 32 /\ 8 * LENGTH bs <= 168 ==>
  within_int_bound decimal_bound
    (w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))))
Proof
  cheat
QED

Theorem dynamic_emit_shl_exact[local]:
  emit_op SHL [a;b] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (word_lsl y (w2n x)) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_convert_bool_raw_exact[local]:
  compile_type_convert v ConvBytestringToBool sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= 32 /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME
      (if word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) = 0w
       then 0w else 1w) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_convert_fixed_raw_exact[local]:
  compile_type_convert v (ConvBytestringToBytesM m) sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= 32 /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (word_of_bytes_be bs) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_bool_encoding[local]:
  LENGTH bs <= 32 ==>
  typed_val_to_w256 (BaseTV BoolT) (BoolV (EXISTS (\b. b <> 0w) bs)) =
    (if word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) = 0w
     then 0w else 1w)
Proof
  cheat
QED

Theorem dynamic_convert_bool_exact[local]:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT BoolT)) sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= 32 /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  ?vout sf. convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT BoolT)
      (BytesV bs) = INL vout /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 (BaseTV BoolT) vout) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_fixed_conversion_result[local]:
  ((src = BaseT (BytesT (Dynamic n)) /\ vin = BytesV bs) \/
   (?s. src = BaseT (StringT n) /\ vin = StringV s /\
        bs = MAP (n2w o ORD) s)) /\ LENGTH bs <= m ==>
  convert_result cx src (BaseT (BytesT (Fixed m))) vin =
    INL (BytesV (PAD_RIGHT 0w m bs))
Proof
  cheat
QED

Theorem dynamic_convert_fixed_exact[local]:
  ((src = BaseT (BytesT (Dynamic n)) /\ vin = BytesV bs) \/
   (?s. src = BaseT (StringT n) /\ vin = StringV s /\
        bs = MAP (n2w o ORD) s)) /\
  compile_type_convert v (mk_convert_op src (BaseT (BytesT (Fixed m))))
    sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= m /\ m <= 32 /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  ?vout sf. convert_result cx src (BaseT (BytesT (Fixed m))) vin = INL vout /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) vout) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_emit_gt_exact[local]:
  emit_op GT [a;b] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (bool_to_word (w2n x > w2n y)) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_emit_assert_exact[local]:
  emit_void ASSERT [a] sa = (u,sb) /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt sa ss ==>
  run_inst_seq (emitted_insts sa sb) ss =
    (if x = 0w then Abort Revert_abort (revert_state (set_returndata [] ss))
     else OK ss) /\ fresh_vars_wrt sb ss
Proof
  cheat
QED

Theorem dynamic_uint_clamp_raw_exact[local]:
  compile_int_clamp F b v sa = (r,sb) /\
  eval_operand v ss = SOME x /\ fresh_vars_wrt sa ss ==>
  if w2n x <= w2n (n2w (2 ** b - 1):bytes32) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_emit_signed_cmp_exact[local]:
  (opc = SLT \/ opc = SGT) /\
  emit_op opc [a;b] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (bool_to_word (if opc = SLT then x < y else x > y)) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_emit_and_exact[local]:
  emit_op AND [a;b] sa = (v,sb) /\
  eval_operand a ss = SOME x /\ eval_operand b ss = SOME y /\
  fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand v sf = SOME (x && y) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_sint_clamp_raw_exact[local]:
  compile_int_clamp T b v sa = (r,sb) /\
  eval_operand v ss = SOME x /\ fresh_vars_wrt sa ss ==>
  if ~(x < (i2w (- &(2 ** (b-1))):bytes32)) /\
     ~(x > (i2w (&(2 ** (b-1) - 1)):bytes32)) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_uint_clamp_test[local]:
  b <= 256 ==>
  (w2n (x:bytes32) <= w2n (n2w (2 ** b - 1):bytes32) <=>
   within_int_bound (Unsigned b) (&(w2n x)))
Proof
  cheat
QED

Theorem dynamic_sint_clamp_test[local]:
  0 < b /\ b <= 256 ==>
  (~((x:bytes32) < (i2w (- &(2 ** (b-1))):bytes32)) /\
   ~(x > (i2w (&(2 ** (b-1) - 1)):bytes32)) <=>
   within_int_bound (Signed b) (w2i x))
Proof
  cheat
QED

Theorem dynamic_int_clamp_exact[local]:
  compile_int_clamp sg b v sa = (r,sb) /\
  eval_operand v ss = SOME x /\ fresh_vars_wrt sa ss /\
  0 < b /\ b <= 256 ==>
  if within_int_bound (if sg then Signed b else Unsigned b)
       (if sg then w2i x else &(w2n x)) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_convert_empty_signed_exact[local]:
  compile_type_convert v (ConvBytestringToInt T b n) sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  n <= 32 /\ 0 < b /\ b <= 256 /\
  mem_word_at (w2n a) ss.vs_memory = 0w ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME 0w /\ fresh_vars_wrt sb sf /\
    sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
Proof
  cheat
QED

Theorem dynamic_empty_signed_result[local]:
  0 < b ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (IntT b)) (BytesV []) =
    INL (IntV 0)
Proof
  cheat
QED

Theorem dynamic_empty_decimal_result[local]:
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) (BytesV []) =
    INL (DecimalV 0)
Proof
  cheat
QED

Theorem dynamic_payload_int_bound[local]:
  LENGTH bs <= 32 /\ 8 * LENGTH bs <= b /\ (sg ==> 0 < LENGTH bs) ==>
  within_int_bound (if sg then Signed b else Unsigned b)
    (if sg then w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))
     else &(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))))
Proof
  cheat
QED

Theorem dynamic_convert_int_raw_exact[local]:
  compile_type_convert v (ConvBytestringToInt sg b n) sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ 0 < b /\ b <= 256 /\ (sg ==> bs <> []) /\
  w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  let x = if sg then word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
          else word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) in
  if within_int_bound (if sg then Signed b else Unsigned b)
       (if sg then w2i x else &(w2n x)) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_address_encoding[local]:
  w2n (x:bytes32) < 2 ** 160 ==>
  typed_val_to_w256 (BaseTV AddressT) (AddressV (n2w (w2n x))) = x
Proof
  cheat
QED

Theorem dynamic_integer_conversion_result[local]:
  LENGTH bs <= 32 /\ (sg ==> bs <> []) ==>
  convert_result cx (BaseT (BytesT (Dynamic n)))
    (BaseT (if sg then IntT b else UintT b)) (BytesV bs) =
  let i = if sg then
      w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))
    else &(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))) in
  if within_int_bound (if sg then Signed b else Unsigned b) i
  then INL (IntV i)
  else INR (Error (RuntimeError
    (if sg then "convert BytesV int bound" else "convert BytesV uint bound")))
Proof
  cheat
QED

Theorem dynamic_convert_integer_exact[local]:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (if sg then IntT b else UintT b))) sa = (r,sb) /\
  convert_result cx (BaseT (BytesT (Dynamic n)))
    (BaseT (if sg then IntT b else UintT b)) (BytesV bs) = res /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ 0 < b /\ b <= 256 /\ (sg ==> bs <> []) /\
  w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  case res of
  | INL vout => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME
        (typed_val_to_w256 (BaseTV (if sg then IntT b else UintT b)) vout) /\
      fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
      sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  | INR ex => ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_address_conversion_result[local]:
  LENGTH bs <= 32 ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs) =
  let x = word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) in
  if within_int_bound (Unsigned 160) (&(w2n x))
  then INL (AddressV (n2w (w2n x)))
  else INR (Error (RuntimeError "convert bytes address"))
Proof
  cheat
QED

Theorem dynamic_convert_address_exact[local]:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT AddressT)) sa = (r,sb) /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs) = res /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  case res of
  | INL vout => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV AddressT) vout) /\
      fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
      sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  | INR ex => ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_decimal_integer_compile[local]:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT DecimalT)) =
  compile_type_convert v (ConvBytestringToInt T 168 n)
Proof
  cheat
QED

Theorem dynamic_decimal_conversion_result[local]:
  bs <> [] ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) (BytesV bs) =
  let i = w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) in
  if within_int_bound (Signed 168) i then INL (DecimalV i)
  else INR (Error (RuntimeError "bounded_decimal_op"))
Proof
  cheat
QED

Theorem dynamic_convert_decimal_exact[local]:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT DecimalT)) sa = (r,sb) /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) (BytesV bs) = res /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ bs <> [] /\ w2n (a + 32w) = w2n a + 32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a + 32) (LENGTH bs) ss.vs_memory = bs ==>
  case res of
  | INL vout => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV DecimalT) vout) /\
      fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
      sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  | INR ex => ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED

Theorem dynamic_scalar_run_exact:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  fresh_vars_wrt sa ss /\ eval_operand op ss = SOME a /\
  w2n a + 32 < dimword (:256) /\
  val_in_memory stv v (w2n a) ss.vs_memory ==>
  case res of
  | INL vout => ?dtv sf. evaluate_type (get_tenv cx) dst = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 dtv vout) /\
      fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
      sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  cheat
QED









Theorem dynamic_operand_packet[local]:
  is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  stmt_state_rel ctx func cenv cx es s /\ expr_val_rel cx src v op s /\
  expr_val_at cenv cx src sarg sa es v op s ==>
  ?a. eval_operand op s = SOME a /\ w2n a + 32 < dimword (:256) /\
      val_in_memory stv v (w2n a) s.vs_memory
Proof
  cheat
QED

Theorem dynamic_frag_writes_fresh_exact:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  writes_fresh sa (emitted_insts sa sb) /\ local_ptrs_reserved cenv sa /\
  (!ss. P ss ==> P (drop_fresh sa ss)) /\
  (!ss. fresh_vars_wrt sa ss /\ P ss ==>
     (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME w) \/
     (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
  (!a ss. A a ==> R (Abort a ss)) ==>
  frag_exec ctx sa sb
    (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
    (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
      (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
               lookup_var x ss = SOME w') /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP ss.vs_allocas aid = SOME b) /\
      ss.vs_memory = s0.vs_memory /\ ss.vs_allocas = s0.vs_allocas) R
Proof
  cheat
QED




Theorem dynamic_frag_straight_fresh_exact[local]:
  straight_fresh m /\ m sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
  (!ss. P ss ==> P (drop_fresh sa ss)) /\
  (!ss. fresh_vars_wrt sa ss /\ P ss ==>
    (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME w) \/
    (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
  (!a ss. A a ==> R (Abort a ss)) ==>
  frag_exec ctx sa sb
    (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
    (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
      (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
               lookup_var x ss = SOME w') /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP ss.vs_allocas aid = SOME b) /\
      ss.vs_memory = s0.vs_memory /\ ss.vs_allocas = s0.vs_allocas) R
Proof
  cheat
QED

Definition dynamic_writes_fresh_def:
  dynamic_writes_fresh st is <=>
    EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
               EVERY (\x. ~not_fresh_at st x) i.inst_outputs) is
End

Definition dynamic_straight_fresh_def:
  dynamic_straight_fresh (m : 'a compiler) <=>
    !st x st'. m st = (x, st') ==>
      st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
      st.cs_next_var <= st'.cs_next_var /\
      dynamic_writes_fresh st (emitted_insts st st')
End

Theorem dynamic_step_read_fresh[local]:
  (fresh_write_op inst.inst_opcode \/ inst.inst_opcode = MLOAD) /\
  step_inst_base inst ss = OK tt ==>
  tt = ss with vs_vars := tt.vs_vars /\
  (!x. ~MEM x inst.inst_outputs ==>
       FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x)
Proof
  cheat
QED

Theorem dynamic_run_read_fresh[local]:
  !is st ss tt.
    dynamic_writes_fresh st is /\ run_inst_seq is ss = OK tt ==>
    tt = ss with vs_vars := tt.vs_vars /\
    !x. not_fresh_at st x ==> FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x
Proof
  cheat
QED

Theorem dynamic_read_fresh_safe[local]:
  fresh_write_op opc \/ opc = MLOAD ==>
  opc <> INVOKE /\ ~is_terminator opc /\ ~is_ext_call_op opc
Proof
  cheat
QED

Theorem dynamic_writes_fresh_mono[local]:
  dynamic_writes_fresh st' is /\ st.cs_next_var <= st'.cs_next_var ==>
  dynamic_writes_fresh st is
Proof
  cheat
QED

Theorem dynamic_straight_fresh_return[local]:
  dynamic_straight_fresh (comp_return x)
Proof
  cheat
QED

Theorem dynamic_straight_fresh_emit_op[local]:
  fresh_write_op opc \/ opc = MLOAD ==>
  dynamic_straight_fresh (emit_op opc ops)
Proof
  cheat
QED

Theorem dynamic_straight_fresh_emit_void[local]:
  fresh_write_op opc \/ opc = MLOAD ==>
  dynamic_straight_fresh (emit_void opc ops)
Proof
  cheat
QED

Theorem dynamic_straight_fresh_bind[local]:
  !mm ff. dynamic_straight_fresh mm /\ (!a. dynamic_straight_fresh (ff a)) ==>
          dynamic_straight_fresh (comp_bind mm ff)
Proof
  cheat
QED

Theorem dynamic_straight_fresh_ignore_bind[local]:
  dynamic_straight_fresh mm /\ dynamic_straight_fresh ff ==>
  dynamic_straight_fresh (comp_ignore_bind mm ff)
Proof
  cheat
QED

val dynamic_sf_step = FIRST [
  irule dynamic_straight_fresh_bind >> conj_tac,
  irule dynamic_straight_fresh_ignore_bind >> conj_tac,
  simp[pairTheory.FORALL_PROD] >> gen_tac >> BETA_TAC,
  irule dynamic_straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
  irule dynamic_straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
  MATCH_ACCEPT_TAC dynamic_straight_fresh_return,
  IF_CASES_TAC];

Theorem dynamic_straight_fresh_convert[local]:
  dynamic_straight_fresh (compile_type_convert op ConvBytestringToBool) /\
  dynamic_straight_fresh (compile_type_convert op (ConvBytestringToInt sg b n)) /\
  dynamic_straight_fresh (compile_type_convert op (ConvBytestringToDecimal d lo hi n)) /\
  dynamic_straight_fresh (compile_type_convert op (ConvBytestringToBytesM m))
Proof
  cheat
QED

Theorem dynamic_frag_read_fresh_exact:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  dynamic_writes_fresh sa (emitted_insts sa sb) /\ local_ptrs_reserved cenv sa /\
  (!ss. P ss ==> P (drop_fresh sa ss)) /\
  (!ss. fresh_vars_wrt sa ss /\ P ss ==>
     (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME w) \/
     (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
  (!a ss. A a ==> R (Abort a ss)) ==>
  frag_exec ctx sa sb
    (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
    (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
      (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
               lookup_var x ss = SOME w') /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP ss.vs_allocas aid = SOME b) /\
      ss.vs_memory = s0.vs_memory /\ ss.vs_allocas = s0.vs_allocas) R
Proof
  cheat
QED




Theorem dynamic_frag_straight_read_fresh_exact[local]:
  dynamic_straight_fresh m /\ m sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
  (!ss. P ss ==> P (drop_fresh sa ss)) /\
  (!ss. fresh_vars_wrt sa ss /\ P ss ==>
    (?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME w) \/
    (?a ss'. run_inst_seq (emitted_insts sa sb) ss = Abort a ss' /\ A a)) /\
  (!a ss. A a ==> R (Abort a ss)) ==>
  frag_exec ctx sa sb
    (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
    (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
      (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
               lookup_var x ss = SOME w') /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP ss.vs_allocas aid = SOME b) /\
      ss.vs_memory = s0.vs_memory /\ ss.vs_allocas = s0.vs_allocas) R
Proof
  cheat
QED

Theorem dynamic_scalar_straight_read_fresh[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst ==>
  dynamic_straight_fresh (compile_type_convert op (mk_convert_op src dst))
Proof
  cheat
QED

Theorem dynamic_scalar_frag_success[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = INL vout /\
  evaluate_type (get_tenv cx) dst = SOME dtv /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  local_ptrs_reserved cenv sa /\
  (!z. op = Var z ==> not_fresh_at sa z) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
      (?a. eval_operand op s = SOME a /\ w2n a + 32 < dimword (:256) /\
           val_in_memory stv v (w2n a) s.vs_memory))
    (\s. stmt_state_rel ctx func cenv cx es s /\
      eval_operand r s = SOME (typed_val_to_w256 dtv vout) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x s = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b) /\
      s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas)
    (expr_exit (INL vout))
Proof
  cheat
QED

Theorem dynamic_scalar_frag_abort[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = INR ex /\
  INR ex <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
      (?a. eval_operand op s = SOME a /\ w2n a + 32 < dimword (:256) /\
           val_in_memory stv v (w2n a) s.vs_memory)) Q (expr_exit (INR ex))
Proof
  cheat
QED

Theorem dynamic_scalar_fragment:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  local_ptrs_reserved cenv sa /\
  (!z. op = Var z ==> not_fresh_at sa z) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         expr_val_rel cx src v op s /\ expr_val_at cenv cx src sarg sa0 es v op s)
    (\s. ?vout dtv. res = INL vout /\
         evaluate_type (get_tenv cx) dst = SOME dtv /\
         stmt_state_rel ctx func cenv cx es s /\
         eval_operand r s = SOME (typed_val_to_w256 dtv vout) /\
         s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w))
    (expr_exit res)
Proof
  cheat
QED




Theorem dynamic_expr_post_convert[local]:
  expr_post ctx func cenv cx e1 es sa s1 s0 es' v1 x t0 /\
  stmt_state_rel ctx func cenv cx es' ss /\
  evaluate_type (get_tenv cx) ann = SOME dtv /\
  eval_operand op ss = SOME (typed_val_to_w256 dtv v) /\
  (!z w. not_fresh_at s1 z /\ lookup_var z t0 = SOME w ==>
         lookup_var z ss = SOME w) /\
  ss.vs_allocas = t0.vs_allocas /\ ss.vs_memory = t0.vs_memory /\
  is_word_type ann /\ sa.cs_next_var <= s1.cs_next_var ==>
  expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0 es'
    v op ss
Proof
  cheat
QED

Theorem dynamic_scalar_type[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  well_formed_type tenv dst ==>
  is_word_type dst /\ (!n. dst <> FlagT n)
Proof
  cheat
QED

(* New public semantic boundary; no memory payload is needed for empty input. *)
Theorem dynamic_empty_scalar_convert:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  (v = BytesV [] \/ v = StringV "") /\
  convert_result cx src dst v = res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) ==>
  ?vout dtv. res = INL vout /\
    evaluate_type (get_tenv cx) dst = SOME dtv /\
    typed_val_to_w256 dtv vout = 0w
Proof
  cheat
QED

(* New public proof-only boundary for the capacity-zero producer branch. *)
Theorem lower_value_dynamic_convert:
  !cenv ty ann t e1 sa op sb.
    lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa =
      (op,sb) /\ is_bytestring_type (expr_type e1) /\ is_word_type t /\
    (!n. t <> FlagT n) ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
      (if lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
          lowered_value_type cenv e1 = BaseT (StringT 0)
       then op = Lit 0w /\ sb = s1
       else compile_type_convert x (mk_convert_op (expr_type e1) t) s1 = (op,sb))
Proof
  cheat
QED

Theorem dynamic_convert_lower_case:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
  is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
  (!a f args d. e1 = Call a (IntCall f) args d ==>
     lowered_value_type cenv e1 = expr_type e1) /\
  expr_sim ctx func cenv cx (expr_type e1) e1 es /\
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa = (op,sb) /\
  (do raw <- eval_expr cx (TypeBuiltin ann Convert t [e1]);
      read_result cx raw od) es = (res,es') /\ expr_res_ok res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0 es' v op s)
    (expr_exit res)
Proof
  cheat
QED


Theorem compile_convert_from_bytestring_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    (!a f args d. e1 = Call a (IntCall f) args d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    !env ty es sa sb vv res es' s0.
      expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
      (nocalls ==> int_calls_expr (TypeBuiltin ann Convert t [e1]) = []) /\
      compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa = (vv, sb) /\
      eval_expr cx (TypeBuiltin ann Convert t [e1]) es = (res, es') /\
      expr_vv_res_ok res /\
      res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post ctx func cenv cx (TypeBuiltin ann Convert t [e1])
                    es sa sb s0 es' tv vv s)
        (expr_exit res)
Proof
  cheat
QED

