Theory abiDecodePtrBytesMember
Ancestors
  abiDecodePtrBytesTail abiDecodePtrRead abiDecodePtrPrims
  abiDecoderBytesBound abiDecoderRange abiDecoderGuard abiDecoderGuards abiDecoderContract
  emitHelperProps exprLoweringProps
  abiEncoder compileEnv emitHelper venomExecSemantics venomInst venomState
  words arithmetic arithmeticProps list rich_list pred_set
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq freshWrites
  abiDecoderBytesPhases abiDecoderBytesPrefix abiDecodePtrNormalized
  abiDecodePtrScalarAbort abiDecodePtrContinuation fragGasSeqPtr

Theorem abi_decode_range_success_bounds:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  w2n p <= w2n q /\ w2n q <= w2n h
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand e s2 = SOME q /\ eval_operand hi s2 = SOME h` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand no_wrap s4 = SOME (bool_to_word (bool_to_word (w2n q < w2n p) = 0w))` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  ntac 4 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  `run_inst_seq (emitted_insts c5 st') s5 = OK t` by
    metis_tac[run_inst_seq_emit_extend] >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
      AllCaseEqs()]
QED

(* The same checked addition occurs in both head and payload guards. *)
Theorem abi_decode_add_range_success_bounds:
  emit_op ADD [src;len] sa = (e,sb) /\
  compile_abi_decode_range_check src e hi sb = ((),sc) /\
  fresh_vars_wrt sa s /\ eval_operand src s = SOME (p:bytes32) /\
  eval_operand len s = SOME c /\ eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts sa sc) s = OK t ==>
  w2n p + w2n c <= w2n h
Proof
  strip_tac >> drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `eval_operand src u = SOME p /\ eval_operand hi u = SOME h` by metis_tac[] >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  `run_inst_seq (emitted_insts sb sc) u = OK t` by
    metis_tac[run_inst_seq_emit_extend] >>
  drule_all abi_decode_range_success_bounds >> strip_tac >>
  `w2n p + w2n c < dimword(:256)` by
    (spose_not_then assume_tac >>
     `dimword(:256) <= w2n p + w2n c` by decide_tac >>
     drule w2n_add_overflow >> decide_tac) >>
  gvs[w2n_add_2]
QED

Theorem abi_decode_bytes_head_success_bound:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s /\ eval_operand src s = SOME p /\
  eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n p + 32 <= w2n h
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_range_success_bounds >> simp[dimword_def]
QED

Theorem abi_decode_bytes_payload_success_bound:
  abi_decode_bytes_payload_guard head len hi sa = ((),sb) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s /\ eval_operand head s = SOME p /\
  eval_operand len s = SOME c /\ eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n p + w2n c <= w2n h
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_add_range_success_bounds >> simp[]
QED

Theorem abi_decode_add_range_scalar:
  emit_op ADD [src;len] sa = (e,sb) /\
  compile_abi_decode_range_check src e hi sb = ((),sc) /\
  src IN A /\ len IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sc) B /\ A SUBSET B /\ e IN B
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sa sb) (e INSERT A)` by
    (drule bop_scalar_seq_emit_op >> simp[]) >>
  `!x. x IN R ==> not_fresh_at sb x` by
    (drule emitted_insts_emit_op >> strip_tac >>
     fs[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `?B. bop_scalar_seq R (e INSERT A) (emitted_insts sb sc) B` by
    (drule abi_decode_range_scalar >>
     disch_then (qspecl_then [`R`, `e INSERT A`] mp_tac) >> simp[]) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >>
     imp_res_tac emit_op_extends >>
     imp_res_tac compile_abi_decode_range_check_shape >>
     gvs[inst_extends_def]) >>
  `e INSERT A SUBSET B` by metis_tac[bop_scalar_seq_available] >>
  qexists_tac `B` >> simp[] >>
  conj_tac >- metis_tac[bop_scalar_seq_append] >>
  fs[SUBSET_DEF]
QED

Theorem abi_decode_bytes_head_scalar:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  src IN A /\ hi IN A /\ Lit 32w IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B /\ head IN B
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all abi_decode_add_range_scalar >> simp[]
QED

Theorem abi_decode_bytes_payload_scalar:
  abi_decode_bytes_payload_guard head len hi sa = ((),sb) /\ hi <> Lit 0w /\
  head IN A /\ len IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_add_range_scalar >> metis_tac[]
QED

Theorem abi_decode_le_guard_success_bound:
  abi_decode_le_guard a b sa = ((),sb) /\
  fresh_vars_wrt sa s /\ eval_operand a s = SOME va /\
  eval_operand b s = SOME vb /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n va <= w2n vb
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [a;b] sa = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK u` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) u = OK v` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `run_inst_seq (emitted_insts c2 sb) v = OK t` by
    metis_tac[run_inst_seq_emit_extend] >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, mk_inst_def, Once step_inst_base_def, AllCaseEqs()]
QED

Theorem abi_decode_count_guard_trace:
  abi_decode_count_guard opc addr n sa = (cnt,sb) <=>
  ?sc. emit_op opc [addr] sa = (cnt,sc) /\
       abi_decode_le_guard cnt (Lit (n2w n)) sc = ((),sb)
Proof
  simp[abi_decode_count_guard_def, abi_decode_le_guard_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  metis_tac[pairTheory.PAIR, pairTheory.pair_CASES, oneTheory.one]
QED

Theorem abi_decode_le_guard_scalar:
  abi_decode_le_guard a b sa = ((),sb) /\ a IN A /\ b IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B /\ A SUBSET B
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [a;b] sa = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  `bop_scalar_seq R A (emitted_insts sa c2) (ok INSERT oob INSERT A)` by
    (qpat_assum `emit_op GT _ _ = _`
       (mp_then Any mp_tac bop_scalar_seq_emit_iszero) >>
     disch_then drule >> simp[]) >>
  `bop_scalar_seq R (ok INSERT oob INSERT A) (emitted_insts c2 sb)
     (ok INSERT oob INSERT A)` by
    (drule bop_scalar_seq_emit_assert >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa c2 ++ emitted_insts c2 sb` by
    (imp_res_tac inst_extends_emit_op >>
     imp_res_tac inst_extends_emit_void >>
     `inst_extends sa c2` by metis_tac[inst_extends_trans] >>
     irule emitted_insts_append >> gvs[inst_extends_def]) >>
  qexists_tac `ok INSERT oob INSERT A` >> simp[SUBSET_DEF] >>
  irule bop_scalar_seq_append >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_decode_count_guard_success_bound:
  abi_decode_count_guard opc addr n sa = (cnt,sb) /\
  abi_decode_source_opcode opc /\ eval_operand addr s = SOME p /\
  fresh_vars_wrt sa s /\ n < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n (abi_decode_load opc p s) <= n /\
  eval_operand cnt t = SOME (abi_decode_load opc p s)
Proof
  strip_tac >> fs[abi_decode_count_guard_trace] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK u` >>
  imp_res_tac inst_extends_emit_op >>
  drule abi_decode_le_guard_shape >> strip_tac >>
  `run_inst_seq (emitted_insts sc sb) u = OK t` by
    metis_tac[run_inst_seq_emit_extend] >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all abi_decode_le_guard_success_bound >> strip_tac >>
  `w2n (abi_decode_load opc p s) <= n` by gvs[w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  gvs[] >> metis_tac[]
QED

(* The member's memory accesses are separated from its three scalar guards. *)
Theorem abi_decode_bytes_member_phases:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w ==>
  ?head addr cnt c1 c2 c3 c4 c5.
    abi_decode_bytes_head pos hi sa = (head,c1) /\
    compile_abi_dec_addr (Var src) pos c1 = (addr,c2) /\
    emit_op MLOAD [addr] c2 = (cnt,c3) /\
    abi_decode_le_guard cnt (Lit (n2w n)) c3 = ((),c4) /\
    abi_decode_bytes_payload_guard head cnt hi c4 = ((),c5) /\
    abi_decode_bytes_runtime_tail (Var dst) addr cnt c5 = ((),sb) /\
    inst_extends sa c1 /\ inst_extends c1 c2 /\
    inst_extends c2 c3 /\ inst_extends c3 c4 /\
    inst_extends c4 c5 /\ inst_extends c5 sb /\
    same_blocks sa c1 /\ same_blocks c1 c2 /\
    same_blocks c2 c3 /\ same_blocks c3 c4 /\
    same_blocks c4 c5 /\ same_blocks c5 sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases, comp_bind_def,
    comp_ignore_bind_def, LET_THM, operand_distinct] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  fs[abi_decode_count_guard_trace] >>
  suspend "structure"
QED

Resume abi_decode_bytes_member_phases[structure]:
  imp_res_tac abi_decode_bytes_head_fragment_shape >>
  imp_res_tac abi_decode_le_guard_shape >>
  imp_res_tac abi_decode_bytes_payload_guard_fragment_shape >>
  imp_res_tac abi_decode_bytes_runtime_tail_shape >>
  fs[compile_abi_dec_addr_def] >>
  rename1 `emit_op ADD [Var src;pos] c1 = (addr,c2)` >>
  rename1 `emit_op MLOAD [addr] c2 = (cnt,c3)` >>
  rename1 `abi_decode_le_guard cnt (Lit (n2w n)) c3 = ((),c4)` >>
  rename1 `abi_decode_bytes_payload_guard head cnt hi c4 = ((),c5)` >>
  imp_res_tac emit_op_extends >>
  imp_res_tac inst_extends_emit_op >>
  `same_blocks c3 c4` by
    (qpat_x_assum `abi_decode_le_guard _ _ c3 = _` mp_tac >>
     simp[abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       comp_return_def, emit_def] >>
     strip_tac >> gvs[same_blocks_def]) >>
  fs[same_blocks_def, EVERY_CONJ]
QED

Finalise abi_decode_bytes_member_phases

(* Invert the whole member before replay: no validity premise is needed. *)
Theorem abi_decode_bytes_member_success_bounds:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w h) /\
  eval_operand (Var src) s = SOME b /\
  p < dimword(:256) /\ h < dimword(:256) /\ n < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n (mload (w2n (b+n2w p)) s) <= n /\
  p+32+w2n (mload (w2n (b+n2w p)) s) <= h
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_bytes_member_phases >> simp[] >> strip_tac >>
  `inst_extends c1 sb /\ inst_extends c2 sb /\
   inst_extends c3 sb /\ inst_extends c4 sb` by
    metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?s1. run_inst_seq (emitted_insts sa c1) s = OK s1 /\
    run_inst_seq (emitted_insts c1 sb) s1 = OK t` by
    (fs[] >> metis_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok]) >>
  `p+32 <= h` by
    (drule_all abi_decode_bytes_head_success_bound >> simp[]) >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `eval_operand head sh = SOME (n2w (p+32))` >>
  `sh = s1` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  gvs[] >>
  suspend "read"
QED

Resume abi_decode_bytes_member_success_bounds[read]:
  `emit_op ADD [Var src;pos] c1 = (addr,c2)` by fs[compile_abi_dec_addr_def] >>
  `eval_operand (Var src) s1 = SOME b /\ eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `run_inst_seq (emitted_insts c3 sb) s3 = OK t` by
    (`run_inst_seq (emitted_insts c2 sb) s2 = OK t` by
      metis_tac[run_inst_seq_emit_extend] >>
     metis_tac[run_inst_seq_emit_extend]) >>
  `emitted_insts c3 sb = emitted_insts c3 c4 ++ emitted_insts c4 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?s4. run_inst_seq (emitted_insts c3 c4) s3 = OK s4 /\
    run_inst_seq (emitted_insts c4 sb) s4 = OK t` by
    (gvs[] >> metis_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok]) >>
  suspend "count"
QED

Resume abi_decode_bytes_member_success_bounds[count]:
  `eval_operand (Lit (n2w n)) s3 = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all abi_decode_le_guard_success_bound >> strip_tac >>
  `w2n (abi_decode_load MLOAD (b+n2w p) s2) <= n` by gvs[w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  rename1 `fresh_vars_wrt c4 sl` >>
  `sl = s4` by gvs[] >>
  qpat_x_assum `sl = s4` SUBST_ALL_TAC >>
  `eval_operand head s4 = SOME (n2w (p+32)) /\
   eval_operand hi s4 = SOME (n2w h) /\
   eval_operand cnt s4 = SOME (abi_decode_load MLOAD (b+n2w p) s2)` by metis_tac[] >>
  `emitted_insts c4 sb = emitted_insts c4 c5 ++ emitted_insts c5 sb` by
    (irule emitted_insts_append >> metis_tac[inst_extends_def]) >>
  `?s5. run_inst_seq (emitted_insts c4 c5) s4 = OK s5` by
    (gvs[] >> metis_tac[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok]) >>
  drule_all abi_decode_bytes_payload_success_bound >> strip_tac >>
  `p+32 < dimword(:256)` by decide_tac >>
  gvs[w2n_n2w, abi_decode_load_def, mload_def] >> decide_tac
QED

Finalise abi_decode_bytes_member_success_bounds
