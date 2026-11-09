(* Dynamic-source conversion simulation. *)
Theory exprSimConvertFromBytes
Ancestors
  exprSimHypsDefs exprSimSource
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimConvert exprSimHyps  exprLowering compileEnv
  exprSimBuffer valueEncoding valueEncodingProofs
  vyperTypeSystem vyperValueOperation vyperValue vyperInterpreter
  fragExec freshWrites loweringSlice venomExecSemantics venomState
  words list integer_word emitHelperProps builtinConvertPrefix exprLoweringProps
  venomMemDefs vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  builtinIntClamp varsExt exprOperandVar vyperState
  fragGasSeq fragGasSeqAbort fragGasMode fragGasPath gasSummary

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
  rpt strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, eval_operand_update_var] >>
  drule emit_op_extends >> strip_tac >>
  conj_tac
  >- (irule fresh_vars_wrt_advance >> simp[] >>
      goal_assum $ drule_at Any >> gvs[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[update_var_def] >> rpt strip_tac >>
  irule eval_operand_update_fresh >> simp[] >>
  goal_assum $ drule_at Any >> gvs[]
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
  rpt strip_tac >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  irule step_MLOAD >> simp[]
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
  rpt strip_tac >> gvs[] >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  FIRST [irule step_ADD, irule (SRULE [] step_SUB), irule step_MUL,
         irule step_SHR, irule step_SAR] >> simp[]
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
  rpt strip_tac >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  drule step_ISZERO >> Cases_on `x = 0w` >> simp[bool_to_word_def]
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
  rpt strip_tac >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `eval_operand data t2 = SOME d` by metis_tac[] >>
  `?t3. run_inst_seq (emitted_insts s2 sb) t2 = OK t3 /\
    eval_operand masked t3 = SOME (if n = 0w then 0w else d) /\
    fresh_vars_wrt sb t3 /\ t3.vs_memory = t2.vs_memory /\
    t3.vs_allocas = t2.vs_allocas /\
    (!p w. eval_operand p t2 = SOME w ==> eval_operand p t3 = SOME w)` by
    (irule dynamic_emit_binary_exact >> simp[] >>
     goal_assum $ drule_at (Pat `emit_op`) >>
     Cases_on `n = 0w` >> gvs[] >> metis_tac[]) >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s2`] >> simp[]) >>
  qexists_tac `t3` >> simp[] >> metis_tac[]
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
  rpt strip_tac >>
  drule_all dynamic_emit_load_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  `eval_operand v t1 = SOME addrword` by metis_tac[] >>
  `?t2. run_inst_seq (emitted_insts s1 s2) t1 = OK t2 /\
    eval_operand dp t2 = SOME (addrword + 32w) /\ fresh_vars_wrt s2 t2 /\
    t2.vs_memory = t1.vs_memory /\ t2.vs_allocas = t1.vs_allocas /\
    (!p w. eval_operand p t1 = SOME w ==> eval_operand p t2 = SOME w)` by
    (irule dynamic_emit_binary_exact >> simp[eval_operand_lit] >>
     goal_assum $ drule_at (Pat `emit_op`) >> simp[eval_operand_lit]) >>
  `eval_operand dp t2 = SOME (addrword + 32w)` by simp[] >>
  qpat_assum `emit_op MLOAD [dp] _ = _`
    (mp_then Any mp_tac dynamic_emit_load_exact) >>
  disch_then (qspecl_then [`addrword + 32w`,`t2`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t3` strip_assume_tac) >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s2`] >> simp[]) >>
  qexists_tac `t3` >> simp[mload_def] >>
  metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  `?t1. run_inst_seq (emitted_insts sa s1) ss = OK t1 /\
    eval_operand sub t1 = SOME (32w - n) /\ fresh_vars_wrt s1 t1 /\
    t1.vs_memory = ss.vs_memory /\ t1.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p t1 = SOME w)` by
    (irule dynamic_emit_binary_exact >> simp[] >>
     goal_assum $ drule_at (Pat `emit_op`) >> simp[eval_operand_lit]) >>
  `?t2. run_inst_seq (emitted_insts s1 s2) t1 = OK t2 /\
    eval_operand k t2 = SOME ((32w - n) * 8w) /\ fresh_vars_wrt s2 t2 /\
    t2.vs_memory = t1.vs_memory /\ t2.vs_allocas = t1.vs_allocas /\
    (!p w. eval_operand p t1 = SOME w ==> eval_operand p t2 = SOME w)` by
    (irule dynamic_emit_binary_exact >> simp[] >>
     goal_assum $ drule_at (Pat `emit_op`) >> simp[eval_operand_lit]) >>
  `eval_operand data t2 = SOME d` by metis_tac[] >>
  qpat_assum `emit_op opc _ _ = _`
    (mp_then Any mp_tac dynamic_emit_binary_exact) >>
  disch_then (qspecl_then [
    `if opc = SHR then word_lsr d (w2n ((32w - n) * 8w))
     else word_asr d (w2n ((32w - n) * 8w))`,
    `d`,`(32w - n) * 8w`,`t2`] mp_tac) >>
  (impl_tac >- (Cases_on `opc = SHR` >> gvs[])) >>
  disch_then (qx_choose_then `t3` strip_assume_tac) >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s2`] >> simp[]) >>
  qexists_tac `t3` >> simp[] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  Cases_on `opc = SHR` >> gvs[] >>
  qpat_x_assum `load_bytestring_as_word _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [load_bytestring_as_word_def, comp_bind_def,
                      comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[comp_return_def]) >> strip_tac >> gvs[]
  >- suspend "unsigned"
  >> suspend "signed"
QED

Resume dynamic_load_word_raw_exact[unsigned]:

  rename1 `emit_op MLOAD [v] sa = (len,s1)` >>
  rename1 `emit_op ADD [v; Lit 32w] s1 = (dp,s2)` >>
  rename1 `emit_op MLOAD [dp] s2 = (data,s3)` >>
  rename1 `emit_op SUB [Lit 32w; len] s3 = (sub,s4)` >>
  rename1 `emit_op MUL [sub; Lit 8w] s4 = (k,s5)` >>
  rename1 `emit_op _ [k; data] s5 = (r,sb)` >>
  drule_all dynamic_load_payload_exact >>
  disch_then (qx_choose_then `sm` strip_assume_tac) >>
  FIRST [drule_all (SRULE [] (Q.INST [`opc` |-> `SHR`] dynamic_shift_payload_exact)),
         drule_all (SRULE [] (Q.INST [`opc` |-> `SAR`] dynamic_shift_payload_exact))] >>
  disch_then (qx_choose_then `sf` strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `inst_extends sa s3` by metis_tac[inst_extends_trans] >>
  `inst_extends s3 s5` by metis_tac[inst_extends_trans] >>
  `inst_extends s3 sb` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK sf` by
    (irule run_inst_seq_compose_ok >> qexistsl [`sm`,`s3`] >> simp[]) >>
  qexists_tac `sf` >> simp[] >> metis_tac[]
QED

Resume dynamic_load_word_raw_exact[signed]:
  rename1 `emit_op MLOAD [v] sa = (len,s1)` >>
  rename1 `emit_op ADD [v; Lit 32w] s1 = (dp,s2)` >>
  rename1 `emit_op MLOAD [dp] s2 = (data,s3)` >>
  rename1 `emit_op ISZERO [len] s3 = (empty,s4)` >>
  rename1 `emit_op ISZERO [empty] s4 = (nonempty,s5)` >>
  rename1 `emit_op MUL [data;nonempty] s5 = (masked,s6)` >>
  rename1 `emit_op SUB [Lit 32w;len] s6 = (sub,s7)` >>
  rename1 `emit_op MUL [sub;Lit 8w] s7 = (k,s8)` >>
  rename1 `emit_op SAR [k;masked] s8 = (r,sb)` >>
  drule_all dynamic_load_payload_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all dynamic_mask_payload_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `eval_operand len t2 = SOME (mload (w2n a) ss)` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `SAR`] dynamic_shift_payload_exact)) >>
  disch_then (qx_choose_then `sf` strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends sa s3` by metis_tac[inst_extends_trans] >>
  `inst_extends s3 s6` by metis_tac[inst_extends_trans] >>
  `inst_extends s6 sb` by metis_tac[inst_extends_trans] >>
  `inst_extends sa s6` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa s6) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s3`] >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) ss = OK sf` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s6`] >> simp[]) >>
  qexists_tac `sf` >> simp[] >> metis_tac[]
QED

Finalise dynamic_load_word_raw_exact

Theorem dynamic_convert_typing_boundary[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es ==>
  valid_conversion (expr_type e) dst /\ ann = dst /\
  well_formed_type env.type_defs dst
Proof
  simp[expr_body_pre_def, well_typed_expr_def,
       well_typed_type_builtin_args_def, type_builtin_result_ok_def] >>
  metis_tac[]
QED

Theorem dynamic_decimal_convert_op[local]:
  mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) =
    ConvBytestringToDecimal 10000000000
      (w2i (FST (type_bounds (BaseT DecimalT))))
      (w2i (SND (type_bounds (BaseT DecimalT)))) n
Proof
  simp[mk_convert_op_def, is_bytestring_type_def] >> pairarg_tac >> simp[]
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
  Cases_on `dst` >> simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT (BytesT bd))` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def]
QED

Theorem dynamic_string_scalar_partition[local]:
  valid_conversion (BaseT (StringT n)) dst /\
  ~is_bytestring_type dst ==>
  ?m. dst = BaseT (BytesT (Fixed m)) /\ n <= m
Proof
  Cases_on `dst` >> simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT (BytesT bd))` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def]
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
  simp[mk_convert_op_def, is_bytestring_type_def]
QED

(* The dynamic representation constrains exactly the payload bytes, not a
   capacity-sized or word-rounded suffix. *)
Theorem dynamic_bytes_memory_boundary[local]:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) off mem <=>
  mem_word_at off mem = n2w (LENGTH bs) /\
  mem_bytes_at (off + 32) (LENGTH bs) mem = bs
Proof
  simp[val_in_memory_def]
QED

Theorem dynamic_empty_memory_boundary[local]:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV []) off mem <=>
  mem_word_at off mem = 0w
Proof
  simp[dynamic_bytes_memory_boundary, mem_bytes_at_def]
QED

Theorem dynamic_string_memory_boundary[local]:
  val_in_memory (BaseTV (StringT n)) (StringV str) off mem <=>
  mem_word_at off mem = n2w (LENGTH str) /\
  mem_bytes_at (off + 32) (LENGTH str) mem = MAP (n2w o ORD) str
Proof
  simp[val_in_memory_def]
QED

Theorem dynamic_bytes_operand_memory[local]:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic n))) (BytesV bs) op s ==>
  ?w. eval_operand op s = SOME w /\
      mem_word_at (w2n w) s.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs
Proof
  strip_tac >> gvs[expr_val_rel_def, is_word_type_def, val_in_memory_def]
QED

Theorem dynamic_get_byte_encoding[local]:
  j < 32 ==>
  byte$get_byte (n2w j:bytes32) (word_of_bytes_be bs:bytes32) T =
    if j < LENGTH bs then EL j bs else 0w
Proof
  strip_tac >>
  simp[byteTheory.word_of_bytes_be_def,
       byteTheory.get_byte_word_of_bytes_be, byteTheory.first_byte_at_0w,
       wordsTheory.dimword_def]
QED

Theorem dynamic_get_byte_bit[local]:
  j < 32 /\ r < 8 ==>
  ((byte$get_byte (n2w j:bytes32) (w:bytes32) T : byte) ' r =
   w ' (8 * (31 - j) + r))
Proof
  strip_tac >>
  simp[byteTheory.get_byte_def, byteTheory.byte_index_def,
       wordsTheory.dimword_def,
       wordsTheory.w2w, wordsTheory.word_lsr_def, fcpTheory.FCP_BETA] >>
  AP_TERM_TAC >> decide_tac
QED

Theorem dynamic_word_bit_byte[local]:
  i < 256 ==>
  ((w:bytes32) ' i =
   (byte$get_byte (n2w (31 - i DIV 8):bytes32) w T : byte) ' (i MOD 8))
Proof
  strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  `31 - i DIV 8 < 32 /\ i MOD 8 < 8` by simp[] >>
  drule_all dynamic_get_byte_bit >>
  disch_then (qspec_then `w` mp_tac) >>
  `8 * (31 - (31 - i DIV 8)) + i MOD 8 = i` by intLib.ARITH_TAC >>
  simp[]
QED

Theorem dynamic_payload_prefix_bits[local]:
  n <= 32 /\ LENGTH xs = 32 /\ LENGTH bs = n /\ TAKE n xs = bs ==>
  !i. 8 * (32 - n) <= i /\ i < 256 ==>
    ((word_of_bytes_be xs:bytes32) ' i =
     (word_of_bytes_be bs:bytes32) ' i)
Proof
  rpt strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  `31 - i DIV 8 < n /\ 31 - i DIV 8 < 32` by intLib.ARITH_TAC >>
  simp[dynamic_word_bit_byte, dynamic_get_byte_encoding] >>
  `EL (31 - i DIV 8) bs = EL (31 - i DIV 8) xs` by
    metis_tac[EL_TAKE] >> simp[]
QED

Theorem dynamic_payload_low_bits[local]:
  LENGTH bs <= 32 ==>
  !i. i < 8 * (32 - LENGTH bs) ==>
    ~((word_of_bytes_be bs:bytes32) ' i)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  `i < 256 /\ 31 - i DIV 8 < 32 /\ LENGTH bs <= 31 - i DIV 8` by intLib.ARITH_TAC >>
  simp[dynamic_word_bit_byte, dynamic_get_byte_encoding,
       wordsTheory.word_0, fcpTheory.FCP_BETA]
QED

Theorem dynamic_lsr_high_cong[local]:
  (!i. k <= i /\ i < 256 ==> (u:bytes32) ' i = (v:bytes32) ' i) ==>
  word_lsr u k = word_lsr v k
Proof
  strip_tac >>
  simp[wordsTheory.word_lsr_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i + k < 256` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem dynamic_asr_high_cong[local]:
  k < 256 /\
  (!i. k <= i /\ i < 256 ==> (u:bytes32) ' i = (v:bytes32) ' i) ==>
  word_asr u k = word_asr v k
Proof
  strip_tac >>
  `u ' 255 = v ' 255` by (first_x_assum irule >> decide_tac) >>
  simp[wordsTheory.word_asr_def, wordsTheory.word_msb_def,
       fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `256 <= i + k` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem dynamic_lsr_lsl_mask[local]:
  (!i. i < k /\ i < 256 ==> ~((w:bytes32) ' i)) ==>
  word_lsl (word_lsr w k) k = w
Proof
  strip_tac >>
  simp[wordsTheory.word_lsl_def, wordsTheory.word_lsr_def,
       fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i < k` >> simp[] >>
  metis_tac[]
QED

Theorem dynamic_payload_lsr[local]:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs ==>
  word_lsr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)) =
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  strip_tac >> irule dynamic_lsr_high_cong >>
  metis_tac[dynamic_payload_prefix_bits]
QED

Theorem dynamic_payload_asr[local]:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs /\ bs <> [] ==>
  word_asr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)) =
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  strip_tac >> irule dynamic_asr_high_cong >>
  conj_tac >- metis_tac[dynamic_payload_prefix_bits] >>
  `LENGTH bs <> 0` by simp[] >> decide_tac
QED

Theorem dynamic_payload_mask[local]:
  LENGTH xs = 32 /\ LENGTH bs <= 32 /\ TAKE (LENGTH bs) xs = bs ==>
  word_lsl
    (word_lsr (word_of_bytes_be xs:bytes32) (8 * (32 - LENGTH bs)))
    (8 * (32 - LENGTH bs)) = word_of_bytes_be bs
Proof
  strip_tac >> drule_all dynamic_payload_lsr >> disch_then SUBST1_TAC >>
  irule dynamic_lsr_lsl_mask >>
  metis_tac[dynamic_payload_low_bits]
QED

Theorem dynamic_memory_payload_prefix[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  LENGTH (TAKE 32 (DROP off mem ++ REPLICATE 32 0w)) = 32 /\
  TAKE (LENGTH bs) (TAKE 32 (DROP off mem ++ REPLICATE 32 0w)) = bs
Proof
  strip_tac >> conj_tac >- simp[LENGTH_TAKE_EQ] >>
  simp[TAKE_TAKE_MIN, arithmeticTheory.MIN_DEF] >>
  `TAKE (LENGTH bs) (DROP off mem ++ REPLICATE 32 0w) =
   TAKE (LENGTH bs) (DROP off mem ++ REPLICATE (LENGTH bs) 0w)` by
    (irule TAKE_append_REPLICATE >> simp[]) >>
  Cases_on `LENGTH bs < 32` >- gvs[mem_bytes_at_def] >>
  `LENGTH bs = 32` by decide_tac >> gvs[mem_bytes_at_def]
QED

Theorem dynamic_memory_payload_lsr[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  word_lsr (mem_word_at off mem) (8 * (32 - LENGTH bs)) =
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  strip_tac >> drule_all dynamic_memory_payload_prefix >> strip_tac >>
  simp[mem_word_at_def, GSYM byteTheory.word_of_bytes_be_def] >>
  irule dynamic_payload_lsr >> simp[]
QED

Theorem dynamic_memory_payload_asr[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs /\ bs <> [] ==>
  word_asr (mem_word_at off mem) (8 * (32 - LENGTH bs)) =
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  strip_tac >> drule_all dynamic_memory_payload_prefix >> strip_tac >>
  simp[mem_word_at_def, GSYM byteTheory.word_of_bytes_be_def] >>
  irule dynamic_payload_asr >> simp[]
QED

Theorem dynamic_memory_payload_mask[local]:
  LENGTH bs <= 32 /\ mem_bytes_at off (LENGTH bs) mem = bs ==>
  word_lsl
    (word_lsr (mem_word_at off mem) (8 * (32 - LENGTH bs)))
    (8 * (32 - LENGTH bs)) = (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >> drule_all dynamic_memory_payload_prefix >> strip_tac >>
  simp[mem_word_at_def, GSYM byteTheory.word_of_bytes_be_def] >>
  irule dynamic_payload_mask >> simp[]
QED

Theorem dynamic_string_operand_memory[local]:
  evaluate_type (get_tenv cx) (BaseT (StringT n)) = SOME (BaseTV (StringT n)) /\
  expr_val_rel cx (BaseT (StringT n)) (StringV str) op s ==>
  ?w. eval_operand op s = SOME w /\
      mem_word_at (w2n w) s.vs_memory = n2w (LENGTH str) /\
      mem_bytes_at (w2n w + 32) (LENGTH str) s.vs_memory = MAP (n2w o ORD) str
Proof
  strip_tac >> gvs[expr_val_rel_def, is_word_type_def, val_in_memory_def]
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
  rpt gen_tac >> strip_tac >>
  `((32w - n2w (LENGTH bs)) * 8w : bytes32) =
    n2w (8 * (32 - LENGTH bs))` by
    (simp[GSYM wordsTheory.n2w_sub, wordsTheory.word_mul_n2w,
          arithmeticTheory.MULT_COMM]) >>
  `w2n (n2w (8 * (32 - LENGTH bs)) : bytes32) = 8 * (32 - LENGTH bs)` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `mload (w2n a) ss = n2w (LENGTH bs)` by
    gvs[mload_def, mem_word_at_def] >>
  drule dynamic_load_word_raw_exact >>
  disch_then (qspecl_then [`ss`,`n2w (LENGTH bs)`,
    `mload (w2n (a + 32w)) ss`,`a`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sf` strip_assume_tac) >>
  qexists_tac `sf` >> simp[] >>
  gvs[mload_def, GSYM mem_word_at_def] >>
  FIRST [irule dynamic_memory_payload_lsr,
         irule dynamic_memory_payload_asr] >> simp[]
QED

Theorem dynamic_local_region_bound[local]:
  local_ptrs_rel func cenv scopes s /\ local_region cenv scopes s name b sz ==>
  b + sz <= s.vs_alloca_next
Proof
  rw[local_ptrs_rel_def, local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem dynamic_operand_header_bound[local]:
  stmt_state_rel ctx func cenv cx es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
  expr_val_at cenv cx t sarg sa es v op s /\
  32 <= val_footprint tv v /\ eval_operand op s = SOME a ==>
  w2n a + 32 < dimword (:256)
Proof
  rpt strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `local_ptrs_rel func cenv es.scopes s` by
    metis_tac[stmt_state_rel_def, state_rel_def] >>
  `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    b + sz <= s.vs_alloca_next` by
    gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (first_x_assum drule >> decide_tac) >>
  drule_all dynamic_local_region_bound >> decide_tac
QED

Theorem dynamic_convert_operand_typed[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
  (do r <- eval_expr cx e1; read_result cx r od) es = (INL v, es1) ==>
  ?stv. evaluate_type (get_tenv cx) (expr_type e1) = SOME stv /\
        value_has_type stv v
Proof
  rpt strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
QED

Theorem dynamic_bytes_value_typed[local]:
  value_has_type (BaseTV (BytesT (Dynamic n))) v ==>
  ?bs. v = BytesV bs /\ LENGTH bs <= n
Proof
  Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]
QED

Theorem dynamic_string_value_typed[local]:
  value_has_type (BaseTV (StringT n)) v ==>
  ?str. v = StringV str /\ LENGTH str <= n
Proof
  Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]
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
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  drule_at (Pat `expr_val_rel _ _ _ _ _`) dynamic_bytes_operand_memory >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  `w2n w + 32 < dimword (:256)` by
    (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
       dynamic_operand_header_bound >>
     simp[vyperValueTheory.evaluate_type_def, val_footprint_def, is_word_type_def] >>
     disch_then drule >> simp[]) >>
  qexists_tac `w` >> gvs[wordsTheory.dimword_def]
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
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_string_value_typed >> strip_tac >> gvs[] >>
  drule_at (Pat `expr_val_rel _ _ _ _ _`) dynamic_string_operand_memory >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  `w2n w + 32 < dimword (:256)` by
    (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
       dynamic_operand_header_bound >>
     simp[vyperValueTheory.evaluate_type_def, val_footprint_def, is_word_type_def] >>
     disch_then drule >> simp[]) >>
  qexists_tac `w` >> gvs[wordsTheory.dimword_def]
QED

Theorem dynamic_unsigned_padding[local]:
  LENGTH bs <= 32 ==>
  word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) =
    word_of_bytes_be (PAD_LEFT 0w 32 bs)
Proof
  strip_tac >>
  simp[wordsTheory.word_lsr_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  Cases_on `i + 8 * (32 - LENGTH bs) < 256`
  >- (simp[dynamic_word_bit_byte, dynamic_get_byte_encoding,
           PAD_LEFT, rich_listTheory.EL_APPEND, EL_GENLIST] >>
      intLib.ARITH_TAC) >>
  simp[dynamic_word_bit_byte, dynamic_get_byte_encoding,
       PAD_LEFT, rich_listTheory.EL_APPEND, EL_GENLIST] >>
  `31 < i DIV 8 + 32 - LENGTH bs` by intLib.ARITH_TAC >>
  simp[wordsTheory.word_0, fcpTheory.FCP_BETA]
QED

Theorem dynamic_payload_zero[local]:
  LENGTH bs <= 32 ==>
  (((word_of_bytes_be bs:bytes32) = 0w) <=> EVERY (\b. b = 0w) bs)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> simp[EVERY_EL] >> rpt strip_tac >> rename1 `j < LENGTH bs` >>
      `j < 32` by decide_tac >>
      drule dynamic_get_byte_encoding >>
      disch_then (qspec_then `bs` mp_tac) >>
      simp[byteTheory.get_byte_def, wordsTheory.ZERO_SHIFT,
           wordsTheory.w2w_0]) >>
  simp[EVERY_EL] >> strip_tac >>
  simp[fcpTheory.CART_EQ, wordsTheory.word_0, fcpTheory.FCP_BETA] >>
  rpt strip_tac >>
  gvs[dynamic_word_bit_byte, dynamic_get_byte_encoding] >>
  Cases_on `31 - i DIV 8 < LENGTH bs` >>
  gvs[wordsTheory.word_0, fcpTheory.FCP_BETA]
QED

Theorem dynamic_unsigned_zero[local]:
  LENGTH bs <= 32 ==>
  ((word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) = 0w) <=>
    EVERY (\b. b = 0w) bs)
Proof
  strip_tac >>
  `word_lsl
     (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))
     (8 * (32 - LENGTH bs)) = word_of_bytes_be bs` by
    (irule dynamic_lsr_lsl_mask >> simp[dynamic_payload_low_bits]) >>
  drule dynamic_payload_zero >> strip_tac >> eq_tac
  >- (strip_tac >> gvs[wordsTheory.ZERO_SHIFT]) >>
  strip_tac >> gvs[wordsTheory.ZERO_SHIFT]
QED

Theorem dynamic_unsigned_bound[local]:
  LENGTH bs <= 32 ==>
  w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) <
    2 ** (8 * LENGTH bs)
Proof
  strip_tac >> simp[wordsTheory.w2n_lsr] >>
  `256 = 8 * LENGTH bs + 8 * (32 - LENGTH bs)` by decide_tac >>
  mp_tac (wordsTheory.w2n_lt |> Q.ISPEC `(word_of_bytes_be bs:bytes32)`) >>
  simp[wordsTheory.dimword_def, arithmeticTheory.EXP_ADD,
       arithmeticTheory.DIV_LT_X]
QED

Theorem dynamic_fixed_bytes_encoding[local]:
  LENGTH bs <= m /\ m <= 32 ==>
  typed_val_to_w256 (BaseTV (BytesT (Fixed m)))
    (BytesV (PAD_RIGHT 0w m bs)) = (word_of_bytes_be bs:bytes32)
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right,
       PAD_RIGHT, GSYM rich_listTheory.REPLICATE_GENLIST,
       byteTheory.word_of_bytes_be_def, word_of_bytes_append_zero]
QED

Theorem dynamic_signed_padding[local]:
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) =
  word_asr (word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32)
    (8 * (32 - LENGTH bs))
Proof
  simp[word_of_bytes_be_pad_right]
QED

Theorem dynamic_signed_roundtrip[local]:
  i2w (w2i (word_asr (word_of_bytes_be bs:bytes32)
    (8 * (32 - LENGTH bs)))) =
  word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))
Proof
  simp[integer_wordTheory.i2w_w2i]
QED

Theorem dynamic_asr_sign[local]:
  word_msb (word_asr (w:bytes32) k) = word_msb w
Proof
  simp[wordsTheory.word_msb_def, wordsTheory.word_asr_def,
       fcpTheory.FCP_BETA] >>
  Cases_on `k = 0` >> simp[]
QED

Theorem dynamic_asr_complement[local]:
  word_1comp (word_asr (w:bytes32) k) = word_asr (word_1comp w) k
Proof
  simp[wordsTheory.word_1comp_def, wordsTheory.word_asr_def,
       wordsTheory.word_msb_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i + k < 256` >> simp[]
QED

Theorem dynamic_asr_clear_sign[local]:
  ~word_msb (w:bytes32) ==> word_asr w k = word_lsr w k
Proof
  simp[wordsTheory.word_asr_def, wordsTheory.word_lsr_def,
       fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  rpt strip_tac >> Cases_on `i + k < 256` >> simp[]
QED

Theorem dynamic_complement_sign[local]:
  word_msb (word_1comp (w:bytes32)) = ~word_msb w
Proof
  simp[wordsTheory.word_msb_def, wordsTheory.word_1comp_def,
       fcpTheory.FCP_BETA]
QED

Theorem dynamic_clear_sign_bound[local]:
  ~word_msb (w:bytes32) ==> w2n w < 2 ** 255
Proof
  Cases_on `w` >>
  simp[wordsTheory.word_msb_n2w_numeric, wordsTheory.INT_MIN_def,
       wordsTheory.dimword_def]
QED

Theorem dynamic_clear_sign_value[local]:
  ~word_msb (w:bytes32) ==> w2i w = &(w2n w)
Proof
  strip_tac >> drule dynamic_clear_sign_bound >>
  simp[integer_wordTheory.w2i_eq_w2n, wordsTheory.INT_MIN_def]
QED

Theorem dynamic_clear_sign_lsr_bound[local]:
  ~word_msb (w:bytes32) /\ k < 256 ==>
  w2n (word_lsr w k) < 2 ** (255 - k)
Proof
  strip_tac >> drule dynamic_clear_sign_bound >>
  `255 = 255 - k + k` by decide_tac >>
  simp[wordsTheory.w2n_lsr, arithmeticTheory.DIV_LT_X,
       GSYM arithmeticTheory.EXP_ADD] >>
  metis_tac[]
QED

Theorem dynamic_negative_complement_value[local]:
  word_msb (w:bytes32) ==> w2i w = -(&(w2n (word_1comp w))) - 1
Proof
  Cases_on `w` >>
  simp[wordsTheory.word_msb_n2w_numeric, wordsTheory.INT_MIN_def,
       wordsTheory.dimword_def, integer_wordTheory.w2i_eq_w2n,
       wordsTheory.word_1comp_n2w] >>
  rpt strip_tac >>
  gvs[wordsTheory.dimword_def] >> intLib.ARITH_TAC
QED

Theorem dynamic_asr_signed_range[local]:
  !(w:bytes32) k. k < 256 ==>
  -(&(2 ** (255-k))) <= w2i (word_asr w k) /\
  w2i (word_asr w k) < &(2 ** (255-k))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `word_msb w`
  >- ( `word_msb (word_asr w k)` by simp[dynamic_asr_sign] >>
       `~word_msb (word_1comp w)` by simp[dynamic_complement_sign] >>
       drule_all dynamic_clear_sign_lsr_bound >> strip_tac >>
       drule dynamic_negative_complement_value >>
       simp[dynamic_asr_complement, dynamic_asr_clear_sign] >>
       intLib.ARITH_TAC) >>
  drule_all dynamic_clear_sign_lsr_bound >> strip_tac >>
  `~word_msb (word_asr w k)` by simp[dynamic_asr_sign] >>
  drule dynamic_clear_sign_value >>
  simp[dynamic_asr_clear_sign] >> intLib.ARITH_TAC
QED

Theorem dynamic_payload_signed_range[local]:
  0 < LENGTH bs /\ LENGTH bs <= 32 ==>
  -(&(2 ** (8 * LENGTH bs - 1))) <=
    w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) /\
  w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) <
    &(2 ** (8 * LENGTH bs - 1))
Proof
  strip_tac >>
  `8 * (32 - LENGTH bs) < 256 /\
   255 - 8 * (32 - LENGTH bs) = 8 * LENGTH bs - 1` by decide_tac >>
  drule dynamic_asr_signed_range >> simp[]
QED

Theorem dynamic_signed_range_widen[local]:
  0 < a /\ a <= b /\ -(&(2 ** (a-1))) <= i /\ i < &(2 ** (a-1)) ==>
  within_int_bound (Signed b) i
Proof
  strip_tac >>
  `0 < b /\ a - 1 <= b - 1` by decide_tac >>
  `2 ** (a-1) <= 2 ** (b-1)` by simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  simp[within_int_bound_def] >>
  Cases_on `i < 0` >> simp[] >> intLib.ARITH_TAC
QED

Theorem dynamic_payload_signed_bound[local]:
  0 < LENGTH bs /\ LENGTH bs <= 32 /\ 8 * LENGTH bs <= b ==>
  within_int_bound (Signed b)
    (w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))))
Proof
  strip_tac >> drule_all dynamic_payload_signed_range >> strip_tac >>
  irule dynamic_signed_range_widen >> qexists_tac `8 * LENGTH bs` >> simp[]
QED

Theorem dynamic_payload_decimal_bound[local]:
  0 < LENGTH bs /\ LENGTH bs <= 32 /\ 8 * LENGTH bs <= 168 ==>
  within_int_bound decimal_bound
    (w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))))
Proof
  simp[decimal_bound_def, decimal_bits_def, dynamic_payload_signed_bound]
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
  rpt strip_tac >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  irule step_SHL >> simp[]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def,
                   comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `load_bytestring_as_word v SHR sa = ((shifted,k),s1)` >>
  qpat_x_assum `_ s1 = (r,sb)` mp_tac >>
  simp_tac pure_ss [comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ISZERO [shifted] s1 = (z,s2)` >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `SHR`] dynamic_load_word_decoded_exact)) >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t3` strip_assume_tac) >>
  `inst_extends sa s1` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s2`] >> simp[]) >>
  qexists_tac `t3` >>
  Cases_on `word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) = 0w` >>
  gvs[] >> metis_tac[]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def,
                   comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `load_bytestring_as_word v SHR sa = ((shifted,k),s1)` >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `SHR`] dynamic_load_word_decoded_exact)) >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all dynamic_emit_shl_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `inst_extends sa s1` by metis_tac[inst_extends_load_bytestring_as_word] >>
  `inst_extends s1 sb` by metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa sb) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  `8 * (32 - LENGTH bs) < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  qexists_tac `t2` >> simp[] >>
  irule dynamic_lsr_lsl_mask >>
  metis_tac[dynamic_payload_low_bits]
QED

Theorem dynamic_bool_encoding[local]:
  LENGTH bs <= 32 ==>
  typed_val_to_w256 (BaseTV BoolT) (BoolV (EXISTS (\b. b <> 0w) bs)) =
    (if word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) = 0w
     then 0w else 1w)
Proof
  strip_tac >>
  `EXISTS (\b. b <> 0w) bs = ~EVERY (\b. b = 0w) bs` by
    (Induct_on `bs` >> simp[]) >>
  drule dynamic_unsigned_zero >> strip_tac >>
  Cases_on `EVERY (\b. b = 0w) bs` >>
  asm_rewrite_tac[typed_val_to_w256_def, val_to_w256_def, bool_to_word_def]
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
  simp[dynamic_scalar_convert_ops] >> rpt strip_tac >>
  drule_all dynamic_convert_bool_raw_exact >>
  disch_then (qx_choose_then `sf` strip_assume_tac) >>
  qexistsl [`BoolV (EXISTS (\b. b <> 0w) bs)`,`sf`] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       dynamic_bool_encoding]
QED

Theorem dynamic_fixed_conversion_result[local]:
  ((src = BaseT (BytesT (Dynamic n)) /\ vin = BytesV bs) \/
   (?s. src = BaseT (StringT n) /\ vin = StringV s /\
        bs = MAP (n2w o ORD) s)) /\ LENGTH bs <= m ==>
  convert_result cx src (BaseT (BytesT (Fixed m))) vin =
    INL (BytesV (PAD_RIGHT 0w m bs))
Proof
  strip_tac >> gvs[convert_result_def, evaluate_convert_from_def,
                   evaluate_convert_def]
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
  rpt gen_tac >> disch_tac >>
  `convert_result cx src (BaseT (BytesT (Fixed m))) vin =
     INL (BytesV (PAD_RIGHT 0w m bs))` by
    (irule dynamic_fixed_conversion_result >> metis_tac[]) >>
  `mk_convert_op src (BaseT (BytesT (Fixed m))) = ConvBytestringToBytesM m` by
    (gvs[dynamic_scalar_convert_ops]) >>
  gvs[] >> simp[dynamic_fixed_bytes_encoding] >>
  irule dynamic_convert_fixed_raw_exact >> simp[] >>
  goal_assum $ drule_at (Pat `compile_type_convert`) >> simp[] >>
  goal_assum $ drule_at (Pat `eval_operand`) >> simp[]
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
  rpt strip_tac >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  simp[clamp_step_equations, exec_pure2_def, venomInstTheory.mk_inst_def]
QED

Theorem dynamic_emit_assert_exact[local]:
  emit_void ASSERT [a] sa = (u,sb) /\
  eval_operand a ss = SOME x /\ fresh_vars_wrt sa ss ==>
  run_inst_seq (emitted_insts sa sb) ss =
    (if x = 0w then Abort Revert_abort (revert_state (set_returndata [] ss))
     else OK ss) /\ fresh_vars_wrt sb ss
Proof
  rpt gen_tac >> strip_tac >> Cases_on `u` >> conj_tac
  >- (drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
      Cases_on `x = 0w` >> simp[run_inst_seq_def, clamp_assert_step]) >>
  metis_tac[fresh_vars_wrt_emit_void]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_int_clamp _ _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_int_clamp_def, COND_CLAUSES, comp_bind_def,
                   comp_ignore_bind_def, comp_return_def, LET_THM] >>
  qabbrev_tac `hi:bytes32 = n2w (2 ** b - 1)` >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op GT [v; _] sa = (gt,s1)` >>
  rename1 `emit_op ISZERO [gt] s1 = (ok,s2)` >>
  rename1 `emit_void ASSERT [ok] s2 = ((),sb)` >>
  `eval_operand (Lit hi) ss = SOME hi` by simp[eval_operand_def] >>
  drule_all dynamic_emit_gt_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  drule_all dynamic_emit_assert_exact >> strip_tac >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `inst_extends sa s2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  Cases_on `w2n x <= w2n hi` >> gvs[bool_to_word_def]
  >- (qexists_tac `t2` >> simp[] >>
      irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s2`] >> simp[]) >>
  drule_all run_inst_seq_emit_extend >> simp[]
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
  rpt strip_tac >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  simp[clamp_step_equations, exec_pure2_def, venomInstTheory.mk_inst_def]
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
  rpt strip_tac >> irule dynamic_emit_update_exact >> simp[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> simp[] >>
  simp[clamp_step_equations, exec_pure2_def, venomInstTheory.mk_inst_def]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_int_clamp _ _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_int_clamp_def, COND_CLAUSES, comp_bind_def,
                   comp_ignore_bind_def, comp_return_def, LET_THM] >>
  qabbrev_tac `lo:bytes32 = i2w (- &(2 ** (b-1)))` >>
  qabbrev_tac `hi:bytes32 = i2w (&(2 ** (b-1) - 1))` >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op SLT [v; Lit lo] sa = (lt,s1)` >>
  rename1 `emit_op ISZERO [lt] s1 = (ok1,s2)` >>
  rename1 `emit_op SGT [v; Lit hi] s2 = (gt,s3)` >>
  rename1 `emit_op ISZERO [gt] s3 = (ok2,s4)` >>
  rename1 `emit_op AND [ok1;ok2] s4 = (ok,s5)` >>
  rename1 `emit_void ASSERT [ok] s5 = ((),sb)` >>
  `eval_operand (Lit lo) ss = SOME lo` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `SLT`] dynamic_emit_signed_cmp_exact)) >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `eval_operand v t2 = SOME x /\ eval_operand (Lit hi) t2 = SOME hi` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `SGT`] dynamic_emit_signed_cmp_exact)) >>
  disch_then (qx_choose_then `t3` strip_assume_tac) >>
  drule_all dynamic_emit_iszero_exact >>
  disch_then (qx_choose_then `t4` strip_assume_tac) >>
  `eval_operand ok1 t4 = SOME (if bool_to_word (x < lo) = 0w then 1w else 0w)` by
    (qpat_x_assum `!p w. eval_operand p t3 = _ ==> _` irule >>
     qpat_x_assum `!p w. eval_operand p t2 = _ ==> _` irule >> simp[]) >>
  drule_all dynamic_emit_and_exact >>
  disch_then (qx_choose_then `t5` strip_assume_tac) >>
  drule_all dynamic_emit_assert_exact >> strip_tac >>
  `inst_extends sa s1 /\ inst_extends s1 s2 /\ inst_extends s2 s3 /\
   inst_extends s3 s4 /\ inst_extends s4 s5 /\ inst_extends s5 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `inst_extends sa s2 /\ inst_extends sa s3 /\ inst_extends sa s4 /\
   inst_extends sa s5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa s2) ss = OK t2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >> simp[]) >>
  `run_inst_seq (emitted_insts sa s3) ss = OK t3` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t2`,`s2`] >> simp[]) >>
  `run_inst_seq (emitted_insts sa s4) ss = OK t4` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t3`,`s3`] >> simp[]) >>
  `run_inst_seq (emitted_insts sa s5) ss = OK t5` by
    (irule run_inst_seq_compose_ok >> qexistsl [`t4`,`s4`] >> simp[]) >>
  Cases_on `x < lo` >> Cases_on `x > hi` >>
  gvs[bool_to_word_def, wordsTheory.WORD_AND_CLAUSES] >>
  drule_all run_inst_seq_emit_extend >>
  simp[wordsTheory.WORD_AND_CLAUSES] >> metis_tac[]
QED

Theorem dynamic_uint_clamp_test[local]:
  b <= 256 ==>
  (w2n (x:bytes32) <= w2n (n2w (2 ** b - 1):bytes32) <=>
   within_int_bound (Unsigned b) (&(w2n x)))
Proof
  strip_tac >>
  `2 ** b <= 2 ** 256` by simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `0 < 2 ** b` by simp[] >>
  `2 ** b - 1 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, within_int_bound_def] >>
  decide_tac
QED

Theorem dynamic_sint_clamp_test[local]:
  0 < b /\ b <= 256 ==>
  (~((x:bytes32) < (i2w (- &(2 ** (b-1))):bytes32)) /\
   ~(x > (i2w (&(2 ** (b-1) - 1)):bytes32)) <=>
   within_int_bound (Signed b) (w2i x))
Proof
  strip_tac >> `b - 1 <= 255` by decide_tac >>
  drule arithmeticPropsTheory.w2i_i2w_neg_pow2 >> strip_tac >>
  drule arithmeticPropsTheory.w2i_i2w_pow2_sub1 >> strip_tac >>
  `0 < 2 ** (b-1)` by simp[] >>
  `&(2 ** (b-1) - 1):int = &(2 ** (b-1)) - 1` by
    (simp[integerTheory.INT_SUB]) >>
  simp[integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi,
       within_int_bound_def] >>
  Cases_on `w2i x < 0` >> simp[] >> intLib.ARITH_TAC
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
  rpt gen_tac >> strip_tac >> Cases_on `sg` >> simp[]
  >- (drule_all dynamic_sint_clamp_raw_exact >>
      simp[dynamic_sint_clamp_test]) >>
  drule_all dynamic_uint_clamp_raw_exact >> simp[dynamic_uint_clamp_test]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def,
                   comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `load_bytestring_as_word v SAR sa = ((shifted,k),s1)` >>
  drule dynamic_load_word_raw_exact >>
  disch_then (qspecl_then [`ss`,`0w`,`mload (w2n (a + 32w)) ss`,`a`] mp_tac) >>
  simp[mload_def, GSYM mem_word_at_def] >> strip_tac >>
  `within_int_bound (Signed b) 0` by simp[within_int_bound_def] >>
  `inst_extends sa s1` by metis_tac[inst_extends_load_bytestring_as_word] >>
  Cases_on `8 * n > b` >> gvs[]
  >- (`b <= 256` by decide_tac >>
      drule_all dynamic_int_clamp_exact >> simp[integer_wordTheory.w2i_def] >> strip_tac >>
      qexists_tac `sf'` >> simp[] >>
      irule run_inst_seq_compose_ok >> qexistsl [`sf`,`s1`] >>
      metis_tac[inst_extends_compile_int_clamp]) >>
  gvs[comp_return_def] >> metis_tac[]
QED

Theorem dynamic_empty_signed_result[local]:
  0 < b ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (IntT b)) (BytesV []) =
    INL (IntV 0)
Proof
  strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       PAD_RIGHT, byteTheory.word_of_bytes_be_def,
       integer_wordTheory.w2i_def, within_int_bound_def] >> EVAL_TAC >>
  simp[arithmeticTheory.EXP_POS]
QED

Theorem dynamic_empty_decimal_result[local]:
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) (BytesV []) =
    INL (DecimalV 0)
Proof
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       bounded_decimal_op_def, decimal_bound_def, decimal_bits_def,
       PAD_RIGHT, byteTheory.word_of_bytes_be_def,
       integer_wordTheory.w2i_def, within_int_bound_def] >> EVAL_TAC >>
  simp[arithmeticTheory.EXP_POS]
QED

Theorem dynamic_payload_int_bound[local]:
  LENGTH bs <= 32 /\ 8 * LENGTH bs <= b /\ (sg ==> 0 < LENGTH bs) ==>
  within_int_bound (if sg then Signed b else Unsigned b)
    (if sg then w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))
     else &(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))))
Proof
  strip_tac >> Cases_on `sg` >> gvs[]
  >- simp[dynamic_payload_signed_bound] >>
  drule dynamic_unsigned_bound >>
  `2 ** (8 * LENGTH bs) <= 2 ** b` by simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  simp[within_int_bound_def]
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
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def,
                   comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `load_bytestring_as_word v (if sg then SAR else SHR) sa = ((shifted,k),s1)` >>
  `?t1. run_inst_seq (emitted_insts sa s1) ss = OK t1 /\
    eval_operand shifted t1 = SOME
      (if sg then word_asr (word_of_bytes_be bs) (8 * (32 - LENGTH bs))
       else word_lsr (word_of_bytes_be bs) (8 * (32 - LENGTH bs))) /\
    fresh_vars_wrt s1 t1 /\ t1.vs_memory = ss.vs_memory /\
    t1.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p t1 = SOME w)` by
    (drule dynamic_load_word_decoded_exact >>
     disch_then (qspecl_then [`ss`,`bs`,`a`] mp_tac) >>
     Cases_on `sg` >> simp[] >> metis_tac[]) >>
  `inst_extends sa s1` by metis_tac[inst_extends_load_bytestring_as_word] >>
  Cases_on `8 * n > b` >> gvs[]
  >- (`b <= 256` by decide_tac >>
      drule_all dynamic_int_clamp_exact >> simp[] >>
      qmatch_goalsub_abbrev_tac `if bounded then _ else _` >>
      Cases_on `bounded` >> simp[] >> strip_tac
      >- (qexists_tac `sf` >> simp[] >>
          irule run_inst_seq_compose_ok >> qexistsl [`t1`,`s1`] >>
          metis_tac[inst_extends_compile_int_clamp]) >>
      `inst_extends s1 sb` by metis_tac[inst_extends_compile_int_clamp] >>
      drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]) >>
  `within_int_bound (if sg then Signed b else Unsigned b)
     (if sg then w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))
      else &(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)))))` by
    (irule dynamic_payload_int_bound >> simp[] >>
     Cases_on `bs` >> gvs[] >> decide_tac) >>
  gvs[comp_return_def] >> qexists_tac `t1` >> simp[]
QED

Theorem dynamic_address_encoding[local]:
  w2n (x:bytes32) < 2 ** 160 ==>
  typed_val_to_w256 (BaseTV AddressT) (AddressV (n2w (w2n x))) = x
Proof
  strip_tac >>
  gvs[typed_val_to_w256_def, GSYM word_to_bytes_w2w_address,
       byteTheory.word_of_bytes_be_def,
       vfmTypesTheory.word_to_bytes_word_of_bytes_256,
       wordsTheory.w2w_n2w, wordsTheory.w2n_n2w,
       wordsTheory.dimword_def, arithmeticTheory.LESS_MOD,
       bitTheory.BITS_ZERO3]
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
  strip_tac >> Cases_on `sg` >>
  gvs[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
      dynamic_unsigned_padding, dynamic_signed_padding] >>
  IF_CASES_TAC >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (if sg then IntT b else UintT b)) = ConvBytestringToInt sg b n` by
    (Cases_on `sg` >> simp[dynamic_scalar_convert_ops]) >>
  `LENGTH bs <= 32` by decide_tac >>
  qpat_x_assum `mk_convert_op _ _ = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  drule_all dynamic_convert_int_raw_exact >> simp[] >>
  qpat_x_assum `convert_result _ _ _ _ = _` mp_tac >>
  simp[dynamic_integer_conversion_result] >>
  qmatch_goalsub_abbrev_tac `within_int_bound bound i` >>
  Cases_on `within_int_bound bound i` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `sg` >> simp[typed_val_to_w256_def, val_to_w256_def, Abbr `i`,
    integer_wordTheory.i2w_w2i]
QED

Theorem dynamic_address_conversion_result[local]:
  LENGTH bs <= 32 ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs) =
  let x = word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs)) in
  if within_int_bound (Unsigned 160) (&(w2n x))
  then INL (AddressV (n2w (w2n x)))
  else INR (Error (RuntimeError "convert bytes address"))
Proof
  strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       dynamic_unsigned_padding, within_int_bound_def] >>
  IF_CASES_TAC >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `compile_type_convert v (ConvBytestringToInt F 160 n) sa = (r,sb)` by
    gvs[dynamic_scalar_convert_ops] >>
  `LENGTH bs <= 32` by decide_tac >>
  drule dynamic_convert_int_raw_exact >>
  disch_then (qspecl_then [`ss`,`bs`,`a`] mp_tac) >> simp[] >>
  qpat_x_assum `convert_result _ _ _ _ = _` mp_tac >>
  simp[dynamic_address_conversion_result] >>
  qmatch_goalsub_abbrev_tac `within_int_bound (Unsigned 160) i` >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `w2n (word_lsr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) < 2 ** 160` by
    gvs[within_int_bound_def, Abbr `i`] >>
  simp[dynamic_address_encoding]
QED

Theorem dynamic_decimal_integer_compile[local]:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n))) (BaseT DecimalT)) =
  compile_type_convert v (ConvBytestringToInt T 168 n)
Proof
  simp[dynamic_decimal_convert_op, type_bounds_def, type_bits_def,
       is_signed_type_def, compile_type_convert_def, compile_int_clamp_def,
       integer_wordTheory.i2w_w2i] >>
  Cases_on `8 * n <= 168` >> simp[]
QED

Theorem dynamic_decimal_conversion_result[local]:
  bs <> [] ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) (BytesV bs) =
  let i = w2i (word_asr (word_of_bytes_be bs:bytes32) (8 * (32 - LENGTH bs))) in
  if within_int_bound (Signed 168) i then INL (DecimalV i)
  else INR (Error (RuntimeError "bounded_decimal_op"))
Proof
  strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       dynamic_signed_padding, bounded_decimal_op_def,
       decimal_bound_def, decimal_bits_def] >>
  IF_CASES_TAC >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `compile_type_convert v (ConvBytestringToInt T 168 n) sa = (r,sb)` by
    gvs[dynamic_decimal_integer_compile] >>
  drule dynamic_convert_int_raw_exact >>
  disch_then (qspecl_then [`ss`,`bs`,`a`] mp_tac) >> simp[] >>
  qpat_x_assum `convert_result _ _ _ _ = _` mp_tac >>
  simp[dynamic_decimal_conversion_result] >>
  qmatch_goalsub_abbrev_tac `within_int_bound (Signed 168) i` >>
  Cases_on `within_int_bound (Signed 168) i` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  simp[typed_val_to_w256_def, val_to_w256_def, Abbr `i`, integer_wordTheory.i2w_w2i]
QED

Theorem dynamic_scalar_run_exact:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
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
  rpt gen_tac >> strip_tac >>
  `w2n (a + 32w) = w2n a + 32` by
    (Cases_on `a` >> gvs[wordsTheory.word_add_n2w,
       wordsTheory.dimword_def, arithmeticTheory.LESS_MOD]) >>
  qpat_x_assum `is_bytestring_type src` mp_tac >>
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_bytestring_type_def]
  >- suspend "string" >>
  rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
  simp[is_bytestring_type_def] >>
  drule_all dynamic_bytes_scalar_partition >> strip_tac >> gvs[]
  >- suspend "bool"
  >- suspend "uint"
  >- suspend "int"
  >- suspend "address"
  >- suspend "decimal"
  >> suspend "fixed"
QED

Resume dynamic_scalar_run_exact[bool]:
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_bytes_memory_boundary] >>
  drule dynamic_convert_bool_exact >>
  disch_then (qspecl_then [`ss`,`cx`,`bs`,`a`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  strip_tac >> gvs[vyperValueTheory.evaluate_type_def]
QED

Resume dynamic_scalar_run_exact[uint]:
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_bytes_memory_boundary, well_formed_type_def,
      vyperValueTheory.evaluate_type_def] >>
  drule (SRULE [] (Q.INST [`sg` |-> `F`] dynamic_convert_integer_exact)) >>
  disch_then (qspecl_then [`ss`,`convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) (BytesV bs)`,`cx`,`bs`,`a`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `LENGTH bs <= 32` by decide_tac >>
  simp[SRULE [] (Q.INST [`sg` |-> `F`] dynamic_integer_conversion_result)] >>
  IF_CASES_TAC >> simp[]
QED

Resume dynamic_scalar_run_exact[int]:
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_bytes_memory_boundary, well_formed_type_def,
      vyperValueTheory.evaluate_type_def] >>
  Cases_on `bs = []`
  >- (gvs[] >>
      `0 < b` by decide_tac >>
      gvs[dynamic_empty_signed_result, dynamic_scalar_convert_ops] >>
      `0 < b` by decide_tac >>
      drule_all dynamic_convert_empty_signed_exact >>
      simp[vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
           val_to_w256_def, integer_wordTheory.i2w_def]) >>
  drule (SRULE [] (Q.INST [`sg` |-> `T`] dynamic_convert_integer_exact)) >>
  disch_then (qspecl_then [`ss`,`convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (IntT b)) (BytesV bs)`,`cx`,`bs`,`a`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `LENGTH bs <= 32` by decide_tac >>
  simp[SRULE [] (Q.INST [`sg` |-> `T`] dynamic_integer_conversion_result)] >>
  IF_CASES_TAC >> simp[]
QED

Resume dynamic_scalar_run_exact[address]:
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_bytes_memory_boundary] >>
  drule dynamic_convert_address_exact >>
  disch_then (qspecl_then [`ss`,`convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT AddressT) (BytesV bs)`,`cx`,`bs`,`a`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `LENGTH bs <= 32` by decide_tac >>
  simp[dynamic_address_conversion_result] >> IF_CASES_TAC >> simp[]
QED

Resume dynamic_scalar_run_exact[decimal]:
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_bytes_memory_boundary] >>
  Cases_on `bs = []`
  >- (gvs[dynamic_empty_decimal_result] >>
      gvs[dynamic_decimal_integer_compile] >>
      drule dynamic_convert_empty_signed_exact >>
      disch_then (qspecl_then [`ss`,`a`] mp_tac) >>
      simp[vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
           val_to_w256_def, integer_wordTheory.i2w_def]) >>
  drule dynamic_convert_decimal_exact >>
  disch_then (qspecl_then [`ss`,`convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT DecimalT) (BytesV bs)`,`cx`,`bs`,`a`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[dynamic_decimal_conversion_result] >> IF_CASES_TAC >> simp[]
QED

Resume dynamic_scalar_run_exact[fixed]:
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_bytes_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_bytes_memory_boundary, well_formed_type_def,
      vyperValueTheory.evaluate_type_def] >>
  `LENGTH bs <= m` by decide_tac >>
  drule_all (SRULE [] (Q.INST
    [`src` |-> `BaseT (BytesT (Dynamic n))`, `vin` |-> `BytesV bs`]
    dynamic_convert_fixed_exact)) >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def]
QED

Resume dynamic_scalar_run_exact[string]:
  drule_all dynamic_string_scalar_partition >> strip_tac >> gvs[] >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  drule dynamic_string_value_typed >> strip_tac >> gvs[] >>
  gvs[dynamic_string_memory_boundary, well_formed_type_def,
      vyperValueTheory.evaluate_type_def] >>
  rename1 `LENGTH str <= n` >>
  `LENGTH str <= m` by decide_tac >>
  drule_all (SRULE [] (Q.INST
    [`src` |-> `BaseT (StringT n)`, `vin` |-> `StringV str`,
     `bs` |-> `MAP (n2w o ORD) str`] dynamic_convert_fixed_exact)) >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def]
QED

Finalise dynamic_scalar_run_exact[local]

Theorem dynamic_operand_packet[local]:
  is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  stmt_state_rel ctx func cenv cx es s /\ expr_val_rel cx src v op s /\
  expr_val_at cenv cx src sarg sa es v op s ==>
  ?a. eval_operand op s = SOME a /\ w2n a + 32 < dimword (:256) /\
      val_in_memory stv v (w2n a) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `~is_word_type src` by
    (Cases_on `src` >> gvs[is_bytestring_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `32 <= val_footprint stv v` by
    (Cases_on `src` >> gvs[is_bytestring_type_def] >>
     rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def]
     >- (drule dynamic_string_value_typed >> strip_tac >>
         gvs[val_footprint_def]) >>
     rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
     drule dynamic_bytes_value_typed >> strip_tac >> gvs[val_footprint_def]) >>
  gvs[expr_val_rel_def] >>
  drule_all dynamic_operand_header_bound >> simp[]
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
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (fs[writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
     res_tac >> imp_res_tac fresh_write_op_simple >> simp[]) >>
  irule frag_exec_run_inst_seq_drop_fresh >> simp[] >> rpt strip_tac >>
  `P (drop_fresh sa s0)` by metis_tac[] >>
  qspecl_then [`sa`,`s0`] assume_tac fresh_vars_wrt_drop_fresh >>
  qpat_x_assum `!ss. fresh_vars_wrt _ _ /\ _ ==> _`
    (qspec_then `drop_fresh sa s0` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac
  >- (disj1_tac >> qexists_tac `ss'` >> asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      drule_all run_inst_seq_writes_fresh >> strip_tac >>
      `!x v. not_fresh_at sa x /\ FLOOKUP s0.vs_vars x = SOME v ==>
        FLOOKUP t.vs_vars x = SOME v` by
        (rpt strip_tac >>
         `FLOOKUP (drop_fresh sa s0).vs_vars x = SOME v` by
           simp[drop_fresh_def, finite_mapTheory.FLOOKUP_DRESTRICT, boolTheory.IN_DEF] >>
         fs[vars_ext_def] >> metis_tac[finite_mapTheory.FLOOKUP_SUBMAP]) >>
      `t with vs_inst_idx := LENGTH sb.cs_current_insts =
        (s0 with vs_vars := t.vs_vars) with
        vs_inst_idx := LENGTH sb.cs_current_insts` by
        (fs[vars_ext_def, drop_fresh_def] >>
         qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         simp[venom_state_component_equality]) >>
      pop_assum SUBST1_TAC >> simp[stmt_state_rel_inst_idx] >>
      conj_tac >- suspend "state" >>
      conj_tac >- suspend "operand" >>
      conj_tac >- (rw[lookup_var_def] >> fs[lookup_var_def]) >>
      fs[vars_ext_def] >>
      qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      simp[drop_fresh_def]) >>
  disj2_tac >> qexistsl_tac [`a`,`ss'`] >> simp[]
QED

Resume dynamic_frag_writes_fresh_exact[state]:
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac
  >~ [`cenv.ce_imm_alloca = SOME (Var p)`]
  >- (`not_fresh_at sa p` by
        (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      `FLOOKUP s0.vs_vars p = SOME 0w` by
        fs[stmt_state_rel_def, immutable_base_zero_def,
           eval_operand_def, lookup_var_def] >>
      qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _`
        (qspecl_then [`p`, `0w`] mp_tac) >>
      fs[lookup_var_def]) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
  fs[lookup_var_def] >>
  qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _` drule >> simp[]
QED

Resume dynamic_frag_writes_fresh_exact[operand]:
  `eval_operand op t = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[eval_operand_vars_ext]) >>
  `t.vs_labels = s0.vs_labels` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[drop_fresh_def]) >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def]
QED

Finalise dynamic_frag_writes_fresh_exact[local]

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
  rpt strip_tac >> irule dynamic_frag_writes_fresh_exact >>
  qpat_x_assum `straight_fresh _` (mp_tac o REWRITE_RULE [straight_fresh_def]) >>
  disch_then drule >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `A` >> asm_rewrite_tac[]) >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
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
  strip_tac >- metis_tac[step_fresh_write_op] >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >>
  gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      venom_state_component_equality]
QED

Theorem dynamic_run_read_fresh[local]:
  !is st ss tt.
    dynamic_writes_fresh st is /\ run_inst_seq is ss = OK tt ==>
    tt = ss with vs_vars := tt.vs_vars /\
    !x. not_fresh_at st x ==> FLOOKUP tt.vs_vars x = FLOOKUP ss.vs_vars x
Proof
  Induct >- simp[run_inst_seq_def, venom_state_component_equality] >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp[dynamic_writes_fresh_def, run_inst_seq_def] >> strip_tac >>
  (Cases_on `step_inst_base inst ss` >> gvs[] >>
  rename1 `step_inst_base inst ss = OK s1` >>
  `s1 = ss with vs_vars := s1.vs_vars /\
   (!x. ~MEM x inst.inst_outputs ==>
        FLOOKUP s1.vs_vars x = FLOOKUP ss.vs_vars x)` by
    metis_tac[dynamic_step_read_fresh] >>
  first_x_assum (qspecl_then [`st`, `s1`, `tt`] mp_tac) >>
  simp[dynamic_writes_fresh_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
      fs[venom_state_component_equality]) >>
  rpt strip_tac >>
  `~MEM x inst.inst_outputs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[])
QED

Theorem dynamic_read_fresh_safe[local]:
  fresh_write_op opc \/ opc = MLOAD ==>
  opc <> INVOKE /\ ~is_terminator opc /\ ~is_ext_call_op opc
Proof
  strip_tac >- metis_tac[fresh_write_op_simple] >>
  gvs[venomInstTheory.is_terminator_def, venomInstTheory.is_ext_call_op_def]
QED

Theorem dynamic_writes_fresh_path_opcodes[local]:
  dynamic_writes_fresh sa code ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode) code
Proof
  rw[dynamic_writes_fresh_def, EVERY_MEM] >>
  first_x_assum drule >>
  simp[fresh_write_op_def] >> rpt strip_tac >>
  gvs[venomInstTheory.is_terminator_def, venomInstTheory.is_ext_call_op_def]
QED

Theorem dynamic_writes_fresh_mono[local]:
  dynamic_writes_fresh st' is /\ st.cs_next_var <= st'.cs_next_var ==>
  dynamic_writes_fresh st is
Proof
  rw[dynamic_writes_fresh_def, EVERY_MEM] >> res_tac >>
  fs[EVERY_MEM] >> metis_tac[not_fresh_at_mono]
QED

Theorem dynamic_straight_fresh_return[local]:
  dynamic_straight_fresh (comp_return x)
Proof
  rw[dynamic_straight_fresh_def, comp_return_def, emitted_insts_refl,
     dynamic_writes_fresh_def]
QED

Theorem dynamic_straight_fresh_emit_op[local]:
  fresh_write_op opc \/ opc = MLOAD ==>
  dynamic_straight_fresh (emit_op opc ops)
Proof
  rw[dynamic_straight_fresh_def] >> imp_res_tac emit_op_extends >>
  imp_res_tac emitted_insts_emit_op >>
  fs[same_blocks_def, dynamic_writes_fresh_def, venomInstTheory.mk_inst_def,
     not_fresh_at_def]
QED

Theorem dynamic_straight_fresh_emit_void[local]:
  fresh_write_op opc \/ opc = MLOAD ==>
  dynamic_straight_fresh (emit_void opc ops)
Proof
  rw[dynamic_straight_fresh_def] >> imp_res_tac emit_void_extends >>
  imp_res_tac emitted_insts_emit_void >>
  fs[same_blocks_def, dynamic_writes_fresh_def, venomInstTheory.mk_inst_def]
QED

Theorem dynamic_straight_fresh_bind[local]:
  !mm ff. dynamic_straight_fresh mm /\ (!a. dynamic_straight_fresh (ff a)) ==>
          dynamic_straight_fresh (comp_bind mm ff)
Proof
  rewrite_tac[dynamic_straight_fresh_def, comp_bind_def] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> Cases_on `mm st` >> simp[] >> strip_tac >>
  rename1 `mm st = (a, mid)` >>
  qpat_x_assum `!st x st'. mm st = _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!a st x st'. ff a st = _ ==> _` (drule_then strip_assume_tac) >>
  `emitted_insts st st' = emitted_insts st mid ++ emitted_insts mid st'` by
    (irule emitted_insts_append >> simp[]) >>
  `dynamic_writes_fresh st (emitted_insts mid st')` by
    (irule dynamic_writes_fresh_mono >> qexists_tac `mid` >> simp[]) >>
  gvs[dynamic_writes_fresh_def, EVERY_APPEND]
QED

Theorem dynamic_straight_fresh_ignore_bind[local]:
  dynamic_straight_fresh mm /\ dynamic_straight_fresh ff ==>
  dynamic_straight_fresh (comp_ignore_bind mm ff)
Proof
  rw[comp_ignore_bind_def] >> irule dynamic_straight_fresh_bind >> simp[]
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
  rw[compile_type_convert_def, load_bytestring_as_word_def,
     compile_int_clamp_def] >> rpt dynamic_sf_step
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
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (fs[dynamic_writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
     metis_tac[dynamic_read_fresh_safe]) >>
  irule frag_exec_run_inst_seq_drop_fresh >> simp[] >> rpt strip_tac >>
  `P (drop_fresh sa s0)` by metis_tac[] >>
  qspecl_then [`sa`,`s0`] assume_tac fresh_vars_wrt_drop_fresh >>
  qpat_x_assum `!ss. fresh_vars_wrt _ _ /\ _ ==> _`
    (qspec_then `drop_fresh sa s0` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac
  >- (disj1_tac >> qexists_tac `ss'` >> asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      drule_all dynamic_run_read_fresh >> strip_tac >>
      `!x v. not_fresh_at sa x /\ FLOOKUP s0.vs_vars x = SOME v ==>
        FLOOKUP t.vs_vars x = SOME v` by
        (rpt strip_tac >>
         `FLOOKUP (drop_fresh sa s0).vs_vars x = SOME v` by
           simp[drop_fresh_def, finite_mapTheory.FLOOKUP_DRESTRICT, boolTheory.IN_DEF] >>
         fs[vars_ext_def] >> metis_tac[finite_mapTheory.FLOOKUP_SUBMAP]) >>
      `t with vs_inst_idx := LENGTH sb.cs_current_insts =
        (s0 with vs_vars := t.vs_vars) with
        vs_inst_idx := LENGTH sb.cs_current_insts` by
        (fs[vars_ext_def, drop_fresh_def] >>
         qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         simp[venom_state_component_equality]) >>
      pop_assum SUBST1_TAC >> simp[stmt_state_rel_inst_idx] >>
      conj_tac >- suspend "state" >>
      conj_tac >- suspend "operand" >>
      conj_tac >- (rw[lookup_var_def] >> fs[lookup_var_def]) >>
      fs[vars_ext_def] >>
      qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      simp[drop_fresh_def]) >>
  disj2_tac >> qexistsl_tac [`a`,`ss'`] >> simp[]
QED

Resume dynamic_frag_read_fresh_exact[state]:
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac
  >~ [`cenv.ce_imm_alloca = SOME (Var p)`]
  >- (`not_fresh_at sa p` by
        (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      `FLOOKUP s0.vs_vars p = SOME 0w` by
        fs[stmt_state_rel_def, immutable_base_zero_def,
           eval_operand_def, lookup_var_def] >>
      qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _`
        (qspecl_then [`p`, `0w`] mp_tac) >>
      fs[lookup_var_def]) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
  fs[lookup_var_def] >>
  qpat_x_assum `!x v. not_fresh_at sa x /\ _ ==> _` drule >> simp[]
QED

Resume dynamic_frag_read_fresh_exact[operand]:
  `eval_operand op t = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[eval_operand_vars_ext]) >>
  `t.vs_labels = s0.vs_labels` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     qpat_x_assum `ss' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[drop_fresh_def]) >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def]
QED

Finalise dynamic_frag_read_fresh_exact[local]

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
  rpt strip_tac >> irule dynamic_frag_read_fresh_exact >>
  qpat_x_assum `dynamic_straight_fresh _`
    (mp_tac o REWRITE_RULE [dynamic_straight_fresh_def]) >>
  disch_then drule >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac >- (qexists_tac `A` >> asm_rewrite_tac[]) >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem dynamic_scalar_straight_read_fresh[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst ==>
  dynamic_straight_fresh (compile_type_convert op (mk_convert_op src dst))
Proof
  rpt strip_tac >>
  qpat_x_assum `is_bytestring_type src` mp_tac >>
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_bytestring_type_def]
  >- (drule_all dynamic_string_scalar_partition >> strip_tac >>
      gvs[dynamic_scalar_convert_ops, dynamic_straight_fresh_convert]) >>
  rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
  simp[is_bytestring_type_def] >>
  drule_all dynamic_bytes_scalar_partition >> strip_tac >>
  gvs[dynamic_scalar_convert_ops, dynamic_decimal_convert_op,
      dynamic_straight_fresh_convert]
QED

Theorem dynamic_code_prefix[local]:
  dynamic_straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  simp[dynamic_straight_fresh_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  simp[DROP_APPEND]
QED

Theorem dynamic_clean_success_path[local]:
  dynamic_straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK t0 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s0 = OK t /\ vars_ext t0 t /\
      gas_marked_path F ctx func s0 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt strip_tac >>
  `dynamic_writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[dynamic_straight_fresh_def] >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all dynamic_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  simp[] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  simp[gas_marked_path_def] >> disch_then irule >>
  conj_tac >- (fs[EVERY_MEM]) >>
  qexists_tac `bb` >> gvs[]
QED

Theorem dynamic_clean_abort_path[local]:
  dynamic_straight_fresh m /\ m sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = Abort a t0 ==>
  ?t j. gas_marked_path F ctx func s0 0 (Abort a (t with vs_inst_idx := j))
Proof
  rpt strip_tac >>
  `dynamic_writes_fresh sa (emitted_insts sa sb)` by
    metis_tac[dynamic_straight_fresh_def] >>
  drule dynamic_writes_fresh_path_opcodes >> strip_tac >>
  `vars_ext_result
     (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >>
     simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >>
  drule_all dynamic_code_prefix >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) run_inst_seq_abort_zero_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[EVERY_MEM])) >> metis_tac[]
QED

Theorem dynamic_run_post[local]:
  dynamic_straight_fresh m /\ m sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK t0 /\
  eval_operand op t0 = SOME w /\
  run_inst_seq (emitted_insts sa sb) s0 = OK t /\ vars_ext t0 t ==>
  stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w /\
  (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
    lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME v) /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_allocas = s0.vs_allocas /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_memory = s0.vs_memory /\
  ~(t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
  (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  `dynamic_writes_fresh sa (emitted_insts sa sb) /\ sb.cs_current_bb = sa.cs_current_bb` by
    metis_tac[dynamic_straight_fresh_def] >>
  drule_all dynamic_run_read_fresh >> strip_tac >>
  `eval_operand op t = SOME w` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = t0 with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  `stmt_state_rel ctx func cenv cx es (s0 with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[lookup_var_def]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
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
  rpt strip_tac >>
  ho_match_mp_tac (Q.INST
    [`A` |-> `\a. F`, `op` |-> `r`,
     `m` |-> `compile_type_convert op (mk_convert_op src dst)`]
    dynamic_frag_straight_read_fresh_exact) >>
  simp[] >> conj_tac
  >- (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> qexists_tac `a` >>
      simp[eval_operand_drop_fresh, drop_fresh_def]) >>
  rpt strip_tac >> fs[wordsTheory.dimword_def] >>
  drule_all (SRULE [wordsTheory.dimword_def]
    (Q.INST [`res` |-> `INL vout`] dynamic_scalar_run_exact)) >>
  simp[] >> metis_tac[]
QED

Theorem dynamic_scalar_frag_abort[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = INR ex /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
      (?a. eval_operand op s = SOME a /\ w2n a + 32 < dimword (:256) /\
           val_in_memory stv v (w2n a) s.vs_memory)) Q (expr_exit (INR ex))
Proof
  rpt strip_tac >>
  `dynamic_straight_fresh (compile_type_convert op (mk_convert_op src dst))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  qpat_x_assum `dynamic_straight_fresh _`
    (mp_tac o REWRITE_RULE [dynamic_straight_fresh_def]) >>
  disch_then drule >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (fs[dynamic_writes_fresh_def, EVERY_MEM] >> rpt strip_tac >>
     metis_tac[dynamic_read_fresh_safe]) >>
  irule frag_exec_run_inst_seq_drop_fresh >>
  simp[rich_listTheory.IS_PREFIX_APPEND3] >> rpt strip_tac >>
  `eval_operand op (drop_fresh sa s0) = SOME a` by
    simp[eval_operand_drop_fresh] >>
  qspecl_then [`sa`,`s0`] assume_tac fresh_vars_wrt_drop_fresh >>
  `val_in_memory stv v (w2n a) (drop_fresh sa s0).vs_memory` by
    simp[drop_fresh_def] >>
  gvs[wordsTheory.dimword_def] >>
  drule_all (SRULE [wordsTheory.dimword_def]
    (Q.INST [`res` |-> `INR ex`] dynamic_scalar_run_exact)) >>
  simp[] >> strip_tac >> disj2_tac >>
  qexistsl_tac [`Revert_abort`,`sf`] >>
  gvs[expr_exit_def]
QED

Theorem dynamic_scalar_fragment:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
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
  rpt strip_tac >> irule frag_exec_pointwise >> rpt strip_tac >> gvs[] >>
  drule_all dynamic_operand_packet >> strip_tac >>
  Cases_on `convert_result cx src dst v`
  >- suspend "success" >>
  suspend "abort"
QED

Resume dynamic_scalar_fragment[success]:
  rename1 `convert_result cx src dst v = INL vout` >>
  `eval_operand op (drop_fresh sa s0) = SOME a` by
    simp[eval_operand_drop_fresh] >>
  qspecl_then [`sa`,`s0`] assume_tac fresh_vars_wrt_drop_fresh >>
  `val_in_memory stv v (w2n a) (drop_fresh sa s0).vs_memory` by
    simp[drop_fresh_def] >>
  gvs[wordsTheory.dimword_def] >>
  drule_all (SRULE [wordsTheory.dimword_def]
    (Q.INST [`res` |-> `INL vout`] dynamic_scalar_run_exact)) >>
  strip_tac >>
  drule_all dynamic_scalar_frag_success >>
  disch_then (qspecl_then [`s0`,`func`,`es`,`ctx`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> simp[wordsTheory.dimword_def]
QED

Resume dynamic_scalar_fragment[abort]:
  drule_all dynamic_scalar_frag_abort >>
  disch_then (qspecl_then [`s0`,`func`,`es`,`ctx`] mp_tac) >>
  disch_then (qspec_then `cenv` (qspec_then `\s. F` mp_tac)) >>
  disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
  disch_then irule >> simp[wordsTheory.dimword_def] >>
  fs[wordsTheory.dimword_def] >>
  qx_gen_tac `exit` >> Cases_on `exit` >> Cases_on `y` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Finalise dynamic_scalar_fragment[local]

Theorem dynamic_scalar_counted_fragment[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  (!z. op = Var z ==> not_fresh_at sa z) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_val_rel cx src v op s0 /\ expr_val_at cenv cx src sarg sa0 es v op s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out. gas_marked_path F ctx func s0 0 out /\
    ((?s vout dtv. out = OK s /\ res = INL vout /\
       evaluate_type (get_tenv cx) dst = SOME dtv /\
       stmt_state_rel ctx func cenv cx es s /\
       eval_operand r s = SOME (typed_val_to_w256 dtv vout) /\
       s.vs_memory = s0.vs_memory /\ s.vs_allocas = s0.vs_allocas /\
       (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
              lookup_var x s = SOME w) /\
       ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result out /\ expr_exit res out))
Proof
  rpt strip_tac >>
  drule_all dynamic_operand_packet >> strip_tac >>
  `dynamic_straight_fresh (compile_type_convert op (mk_convert_op src dst))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[]) >>
  `eval_operand op (drop_fresh sa s0) = SOME a` by
    simp[eval_operand_drop_fresh] >>
  qspecl_then [`sa`,`s0`] assume_tac fresh_vars_wrt_drop_fresh >>
  `val_in_memory stv v (w2n a) (drop_fresh sa s0).vs_memory` by
    simp[drop_fresh_def] >>
  drule_all dynamic_scalar_run_exact >>
  Cases_on `res` >> simp[] >> strip_tac
  >- suspend "success" >>
  suspend "abort"
QED

Resume dynamic_scalar_counted_fragment[success]:
  drule_all dynamic_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all dynamic_run_post >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume dynamic_scalar_counted_fragment[abort]:
  drule_all dynamic_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[exit_result_def, expr_exit_def]
QED

Finalise dynamic_scalar_counted_fragment

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
  simp[expr_post_def] >> strip_tac >>
  `~expr_has_effect (TypeBuiltin ann Convert t [e1]) ==>
   pure_frame cenv func es sa s0 ss` by
    (simp[loweringPostsTheory.expr_has_effect_thm] >> strip_tac >>
     match_mp_tac exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `t0` >>
     simp[]) >>
  `locals_kept cenv es s0 ss` by
    (irule locals_kept_mem_tail >> qexists_tac `t0` >> asm_rewrite_tac[]) >>
  simp[expr_val_rel_def, expr_val_at_def, vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w` >>
      `not_fresh_at s1 z` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> asm_rewrite_tac[]) >>
      qpat_x_assum `!z w. not_fresh_at s1 z /\ lookup_var z t0 = _ ==> _`
        irule >> asm_rewrite_tac[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = _ ==> _`
        irule >> asm_rewrite_tac[]) >>
  rpt strip_tac >> fs[] >> metis_tac[]
QED

Theorem dynamic_scalar_type[local]:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  well_formed_type tenv dst ==>
  is_word_type dst /\ (!n. dst <> FlagT n)
Proof
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  Cases_on `dst` >> simp[valid_conversion_def, is_word_type_def] >>
  rename1 `BaseT dt` >> Cases_on `dt` >>
  simp[valid_conversion_def, is_word_type_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_word_type_def, is_bytestring_type_def,
       well_formed_type_def, evaluate_type_def]
QED

(* New public semantic boundary; no memory payload is needed for empty input. *)
Theorem dynamic_empty_scalar_convert:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  (v = BytesV [] \/ v = StringV "") /\
  convert_result cx src dst v = res ==>
  ?vout dtv. res = INL vout /\
    evaluate_type (get_tenv cx) dst = SOME dtv /\
    typed_val_to_w256 dtv vout = 0w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `is_bytestring_type src` mp_tac >>
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_bytestring_type_def]
  >- suspend "string" >>
  rename1 `is_bytestring_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
  simp[is_bytestring_type_def] >>
  drule_all dynamic_bytes_scalar_partition >> strip_tac >> gvs[] >>
  gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
      convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
      typed_val_to_w256_def, val_to_w256_def, bool_to_word_def,
      within_int_bound_def, word_of_bytes_be_pad_right,
      byteTheory.word_of_bytes_be_def, word_of_bytes_append_zero] >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
      listTheory.PAD_LEFT, listTheory.PAD_RIGHT,
      GSYM rich_listTheory.REPLICATE_GENLIST,
      word_of_bytes_replicate_zero, typed_val_to_w256_def, val_to_w256_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC >>
  simp[arithmeticTheory.EXP_POS, typed_val_to_w256_def, val_to_w256_def,
       integer_wordTheory.i2w_def]
QED
Resume dynamic_empty_scalar_convert[string]:
  drule_all dynamic_string_scalar_partition >> strip_tac >> gvs[] >>
  gvs[vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
      convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
      typed_val_to_w256_def, word_of_bytes_be_pad_right,
      byteTheory.word_of_bytes_be_def, word_of_bytes_append_zero] >>
  gvs[well_formed_type_def, vyperValueTheory.evaluate_type_def,
      listTheory.PAD_RIGHT, GSYM rich_listTheory.REPLICATE_GENLIST,
      word_of_bytes_replicate_zero]
QED
Finalise dynamic_empty_scalar_convert

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
  rpt strip_tac >>
  `~is_bytestring_type t` by metis_tac[is_word_type_not_bytestring] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[exprBopLoweringTheory.lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def] >>
  Cases_on `t` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[exprBopLoweringTheory.as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem dynamic_continuation_summary[local]:
  expr_post ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
  valid_conversion (expr_type e1) t /\ well_formed_type tenv t /\ ann = t /\
  is_word_type t /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME stv /\ value_has_type stv v1 /\
  ((lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
    lowered_value_type cenv e1 = BaseT (StringT 0)) ==> v1 = BytesV [] \/ v1 = StringV "") /\
  (if lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e1 = BaseT (StringT 0)
   then op = Lit 0w /\ sb = s1
   else compile_type_convert x (mk_convert_op (expr_type e1) t) s1 = (op,sb)) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at F (ctx,func) []
    (\vs. (convert_result cx (expr_type e1) t v1,vs))
    (ee with gas_obs := [],t0)
    (\res fin ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert t [e1]) es sa sb s0
        fin v op ss /\ ss.vs_current_bb = sb.cs_current_bb /\
      ss.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin out. expr_exit res out)
Proof
  strip_tac >>
  Cases_on `lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e1 = BaseT (StringT 0)`
  >- suspend "empty" >>
  gvs[] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   expr_val_rel cx (expr_type e1) v1 x t0 /\
   expr_val_at cenv cx (expr_type e1) sa s1 (ee with gas_obs := []) v1 x t0` by
    fs[expr_post_def] >>
  drule_all (Q.INST
    [`src` |-> `expr_type e1`, `dst` |-> `ann`, `v` |-> `v1`,
     `res` |-> `convert_result cx (expr_type e1) ann v1`]
    dynamic_scalar_counted_fragment |> SIMP_RULE (srw_ss()) []) >>
  strip_tac
  >- suspend "success" >>
  suspend "abort"
QED

Resume dynamic_continuation_summary[empty]:
  `?vout dtv. convert_result cx (expr_type e1) t v1 = INL vout /\
    evaluate_type (get_tenv cx) t = SOME dtv /\ typed_val_to_w256 dtv vout = 0w` by
    metis_tac[dynamic_empty_scalar_convert] >>
  gvs[] >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INL vout`,`ee`,`OK t0`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules] >>
  (irule dynamic_expr_post_convert >> simp[eval_operand_def] >>
   conj_tac >- fs[expr_post_def] >>
   qexistsl_tac [`s1`,`t0`] >> simp[] >> metis_tac[])
QED

Resume dynamic_continuation_summary[success]:
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL vout`,`ee`,`OK s`] >>
  simp[gas_marked_exec_def] >>
  conj_tac >- metis_tac[] >>
  irule dynamic_expr_post_convert >> simp[] >>
  qexistsl_tac [`s1`,`t0`] >> simp[] >> metis_tac[]
QED

Resume dynamic_continuation_summary[abort]:
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) ann v1`,`ee`,`out`] >>
  simp[gas_marked_exec_def]
QED

Finalise dynamic_continuation_summary

Theorem dynamic_convert_lower_case:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es /\
  is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
  (!a f args d. e1 = Call a (IntCall f) args d ==>
     lowered_value_type cenv e1 = expr_type e1) /\
  expr_sim ctx func cenv cx (expr_type e1) e1 es ==>
  expr_sim ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es
Proof
  strip_tac >> drule dynamic_convert_typing_boundary >> strip_tac >>
  drule_all dynamic_scalar_type >> strip_tac >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all lower_value_dynamic_convert >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `dynamic_straight_fresh (compile_type_convert x (mk_convert_op (expr_type e1) t))` by
    (irule dynamic_scalar_straight_read_fresh >> simp[] >> metis_tac[]) >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
    (Cases_on `lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
               lowered_value_type cenv e1 = BaseT (StringT 0)`
     >- gvs[cs_extends_def] >>
     fs[dynamic_straight_fresh_def, dynamic_writes_fresh_def] >>
     first_x_assum drule >> strip_tac >>
     simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND3]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "counted" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule convert_exempt_cert >> simp[]
QED

Resume dynamic_convert_lower_case[counted]:
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[eval_expr_convert_action] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac
  >- suspend "value" >>
  Cases_on `res` >- gvs[] >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INR y`,`es_end`,`r`] >>
  simp[] >> conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> simp[]) >>
  gvs[]
QED

Resume dynamic_convert_lower_case[value]:
  gvs[] >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env (TypeBuiltin ann Convert ann [e1])
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) dynamic_convert_operand_typed) >> strip_tac >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `((lowered_value_type cenv e1 = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv e1 = BaseT (StringT 0)) ==> v = BytesV [] \/ v = StringV "")` by
    (strip_tac >> drule expr_body_pre_convert >> strip_tac >>
     gvs[] >>
     metis_tac[CONV_RULE (DEPTH_CONV ETA_CONV) lowered_zero_bytestring_read_empty,
               expr_body_pre_gas_obs]) >>
  drule_all (Q.INST [`t` |-> `ann`] dynamic_continuation_summary
             |> SIMP_RULE (srw_ss()) []) >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`,`es_end'`,`r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`]
              gasSummaryComposeTheory.gas_marked_exec_bind_normal
              |> REWRITE_RULE [APPEND_NIL]) >>
       qexistsl_tac [`es_end`,`t'`,`v`] >> gvs[]) >>
   gvs[])
QED
Finalise dynamic_convert_lower_case

Theorem compile_convert_from_bytestring_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    is_bytestring_type (expr_type e1) /\ ~is_bytestring_type t /\
    (!a f args d. e1 = Call a (IntCall f) args d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])
Proof
  rw[expr_vv_case_def] >>
  drule expr_body_pre_convert >> strip_tac >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (gvs[exprs_case_def] >>
     irule expr_sim_case_apply >> conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `nocalls` >> simp[] >>
     metis_tac[int_calls_type_builtin_arg, listTheory.MEM]) >>
  `expr_sim ctx func cenv cx ty (TypeBuiltin ann Convert t [e1]) es` by
    (irule dynamic_convert_lower_case >> metis_tac[]) >>
  irule expr_vv_sim_stack >> simp[] >> conj_tac
  >- (gen_tac >> irule compile_convert_stack) >>
  metis_tac[eval_expr_type_builtin_value]
QED
