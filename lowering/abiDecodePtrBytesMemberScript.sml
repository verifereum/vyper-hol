Theory abiDecodePtrBytesMember
Ancestors
  abiDecodePtrBytesTail abiDecodePtrRead abiDecodePtrPrims abiDecodePtrScalarFrame
  abiDecodePtrBytesPrefixLive
  abiDecoderBytesBound abiDecoderRange abiDecoderGuard abiDecoderGuards abiDecoderContract
  emitHelperProps exprLoweringProps
  abiEncoder compileEnv emitHelper venomExecSemantics venomInst venomState
  words arithmetic arithmeticProps list rich_list pred_set
  bodyPtrBopScalarCompile bodyPtrBopScalarSeq freshWrites
  abiDecoderBytesPhases abiDecoderBytesPrefix abiDecodePtrNormalized
  abiDecodePtrScalarAbort abiDecodePtrContinuation fragGasSeqPtr
  abiDecodePtrMemberFrame bodyPtrDefs ptrDiscipline finite_map
  bodyPtrBopScalarOutcome bodyPtrBopHashSuffix abiDecoderBytesRuntime
  assignTuplePtrLocalBytesCopy fragExec stateFrame

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
    (qpat_assum `run_inst_seq (emitted_insts st c5) s = OK s5`
       (mp_then Any mp_tac run_inst_seq_emit_extend) >>
     disch_then (qspec_then `st'` mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `run_inst_seq (emitted_insts st st') s = OK t`
       (fn th => pure_rewrite_tac[th]) >> simp_tac (srw_ss()) []) >>
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
    (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
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
    (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
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

Theorem abi_decode_bytes_member_prefix_ptr:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ fresh_vars_wrt sa s /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s cap /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p < dimword(:256) /\ n+31 < dimword(:256) /\
  32+contractABI$ceil32 n <= cap /\ w2n d+cap < dimword(:256) /\
  w2n b+h < dimword(:256) /\
  (w2n b+h <= w2n d \/ w2n d+cap <= w2n b) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?c5 ar cnt s5 G5 tn5.
    abi_decode_bytes_runtime_tail (Var dst) (Var ar) cnt c5 = ((),sb) /\
    fn_has_code c5 sb func /\ inst_extends sa c5 /\ same_blocks sa c5 /\
    run_inst_seq (emitted_insts sa c5) s =
      OK (s5 with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa c5) s G5 tn5 /\
    ~s5.vs_halted /\ s5.vs_current_bb = c5.cs_current_bb /\
    s5.vs_inst_idx = LENGTH c5.cs_current_insts /\ fresh_vars_wrt c5 s5 /\
    abi_decode_ptr_window G5 tn5 s5 src b h /\
    abi_decode_ptr_window G5 tn5 s5 ar (b+n2w p)
      (32+w2n (mload (w2n b+p) s)) /\
    lookup_var dst s5 = SOME d /\ ptr_covers G5 tn5 dst s5 cap /\
    eval_operand cnt s5 = SOME (n2w (w2n (mload (w2n b+p) s))) /\
    op_prov G5 cnt = NONE /\ op_taint tn5 cnt = {} /\
    not_fresh_at c5 dst /\ not_fresh_at c5 ar /\
    (!x. cnt = Var x ==> not_fresh_at c5 x) /\
    w2n (mload (w2n b+p) s) <= n /\
    p+32+w2n (mload (w2n b+p) s) <= h /\
    s5.vs_memory = s.vs_memory /\ tn5.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==> lookup_var x s5 = lookup_var x s /\
      FLOOKUP G5 x = FLOOKUP G x /\ op_taint tn5 (Var x) = op_taint tn (Var x)) /\
    tn5.t_stor = tn.t_stor /\ tn5.t_trans = tn.t_trans /\ tn5.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> not_fresh_at c5 x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `h < dimword(:256) /\ n < dimword(:256)` by decide_tac >>
  `eval_operand (Var src) s = SOME b` by
    fs[abi_decode_ptr_window_def, eval_operand_def] >>
  drule_all abi_decode_bytes_member_success_bounds >> strip_tac >>
  `p+32 <= h` by decide_tac >>
  drule abi_decode_bytes_member_phases >> simp[] >> strip_tac >>
  drule_all abi_decode_bytes_prefix_protected >> strip_tac >>
  `inst_extends c1 sb /\ inst_extends c2 sb /\
   inst_extends c3 sb /\ inst_extends c4 sb` by
    metis_tac[inst_extends_trans] >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `eval_operand head sh = SOME (n2w (p+32))` >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x}
    ({pos;hi} UNION IMAGE Lit UNIV) (emitted_insts sa c1) B /\
    ({pos;hi} UNION IMAGE Lit UNIV) SUBSET B /\ head IN B` by
    (irule abi_decode_bytes_head_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {pos;hi} UNION IMAGE Lit UNIV ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[IN_UNION, IN_IMAGE] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa c1) s H tm` >>
  suspend "head_frame"
QED

Resume abi_decode_bytes_member_prefix_ptr[head_frame]:
  `op_prov H head = NONE /\ op_taint tm head = {} /\
   op_prov H hi = NONE /\ op_taint tm hi = {}` by
    (qpat_assum `!op. op IN B ==> _` mp_tac >>
     qpat_assum `{pos;hi} UNION IMAGE Lit UNIV SUBSET B` mp_tac >>
     qpat_assum `head IN B` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF, IN_UNION, IN_INSERT, NOT_IN_EMPTY] >>
     metis_tac[]) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x sh = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)` by
    (fs[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  qabbrev_tac `s1 = sh with vs_inst_idx := LENGTH c1.cs_current_insts` >>
  `abi_decode_ptr_window H tm s1 src b h` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[Abbr `s1`, lookup_var_def] >> fs[lookup_var_def]) >>
  `lookup_var dst s1 = lookup_var dst s /\
   FLOOKUP H dst = FLOOKUP G dst /\
   op_taint tm (Var dst) = op_taint tn (Var dst)` by
    (simp_tac (srw_ss()) [Abbr `s1`, lookup_var_def] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sh = _ /\ _`
       (qspec_then `dst` mp_tac) >>
     asm_simp_tac (srw_ss()) [lookup_var_def]) >>
  `lookup_var dst s1 = SOME d /\ ptr_covers H tm dst s1 cap` by
    (conj_tac >- asm_rewrite_tac[] >>
     qpat_assum `ptr_covers G tn dst s cap` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def] >>
     asm_rewrite_tac[]) >>
  `~sh.vs_halted /\ sh.vs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `sh = s with vs_vars := sh.vs_vars` (fn th =>
       once_rewrite_tac[th]) >> simp[]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = c1.cs_current_bb /\
   s1.vs_inst_idx = LENGTH c1.cs_current_insts /\
   eval_operand pos s1 = SOME (n2w p) /\ op_taint tm pos = {}` by
    (fs[same_blocks_def, Abbr `s1`, SUBSET_DEF] >>
     simp[eval_operand_def, lookup_var_def] >>
     Cases_on `pos` >> gvs[eval_operand_def, lookup_var_def]) >>
  `cs_extends sa c1 /\ cs_extends c1 sb /\
   cs_extends c1 c3 /\ cs_extends c3 sb /\
   cs_extends c1 c2 /\ cs_extends c2 c3` by
    (`inst_extends c1 c3` by
       (irule inst_extends_trans >> qexists_tac `c2` >> simp[]) >>
     fs[cs_extends_def, same_blocks_def, inst_extends_def] >>
     simp[IS_PREFIX_APPEND]) >>
  `fn_has_code c1 sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `fn_has_code c1 c3 func` by
    (drule_all fn_has_code_split >> simp[]) >>
  drule_all (abi_decode_ptr_relative_load |> Q.INST [`G` |-> `H`, `tn` |-> `tm`,
    `s` |-> `s1`, `D` |-> `D`, `PG` |-> `PG`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG H tm
    (emitted_insts c1 c3) s1 Hr tr` >>
  suspend "loaded"
QED

Resume abi_decode_bytes_member_prefix_ptr[loaded]:
  `not_fresh_at c1 src /\ not_fresh_at c1 dst` by
    (conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window Hr tr t src b h` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`H`, `s1`, `tm`] >>
     simp[] >>
     qpat_assum `!x. not_fresh_at c1 x ==> lookup_var x t = _ /\ _`
       (qspec_then `src` mp_tac) >> simp[]) >>
  `lookup_var dst t = lookup_var dst s1 /\
   FLOOKUP Hr dst = FLOOKUP H dst /\
   op_taint tr (Var dst) = op_taint tm (Var dst)` by
    (qpat_assum `!x. not_fresh_at c1 x ==> lookup_var x t = _ /\ _`
       (qspec_then `dst` mp_tac) >> simp[]) >>
  `lookup_var dst t = SOME d /\ ptr_covers Hr tr dst t cap` by
    (conj_tac >- asm_rewrite_tac[] >>
     qpat_assum `ptr_covers H tm dst s1 cap` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def] >> asm_rewrite_tac[]) >>
  `fresh_vars_wrt c1 s1` by fs[Abbr `s1`, fresh_vars_wrt_def] >>
  `fresh_vars_wrt c3 t` by metis_tac[] >>
  `!x. head = Var x ==> not_fresh_at c1 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c1.cs_next_var head` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`sh`, `n2w (p+32)`] >> asm_rewrite_tac[]) >>
     pop_assum mp_tac >>
     asm_simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!x. hi = Var x ==> not_fresh_at c1 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c1.cs_next_var hi` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`sh`, `n2w h`] >> conj_tac
        >- (qpat_assum `!op w. eval_operand op s = SOME w ==> _` irule >>
            first_assum MATCH_ACCEPT_TAC) >>
        first_assum MATCH_ACCEPT_TAC) >>
     pop_assum mp_tac >>
     asm_simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `t.vs_labels = s1.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >>
     simp_tac (srw_ss()) [state_frame_def, venom_state_component_equality]) >>
  `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==>
    eval_operand op t = eval_operand op s1 /\
    op_prov Hr op = op_prov H op /\ op_taint tr op = op_taint tm op` by
    (gen_tac >> disch_tac >> irule abi_decode_scalar_protected_operand >>
     simp[] >> qexists_tac `{x | not_fresh_at c1 x}` >> simp[]) >>
  `op_prov Hr head = NONE /\ op_taint tr head = {} /\
   op_prov Hr hi = NONE /\ op_taint tr hi = {}` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
       (qspec_then `head` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
       (qspec_then `hi` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     rpt conj_tac >> metis_tac[]) >>
  `mload (w2n b+p) s1 = mload (w2n b+p) s` by
    simp[Abbr `s1`, mload_def] >>
  `w2n (b+n2w p) = w2n b+p` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `eval_operand cnt t = SOME (mload (w2n b+p) s)` by
    fs[eval_operand_def] >>
  `eval_operand (Lit (n2w n)) t = SOME (n2w n)` by simp[eval_operand_def] >>
  `w2n (mload (w2n b+p) s) <= w2n (n2w n:bytes32)` by fs[w2n_n2w] >>
  drule_all abi_decode_le_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) t = OK sl` >>
  suspend "count_ptr"
QED

Resume abi_decode_bytes_member_prefix_ptr[count_ptr]:
  `?C. bop_scalar_seq {x | not_fresh_at c3 x}
    ({cnt} UNION IMAGE Lit UNIV) (emitted_insts c3 c4) C /\
    ({cnt} UNION IMAGE Lit UNIV) SUBSET C` by
    (irule abi_decode_le_guard_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt} UNION IMAGE Lit UNIV ==>
    op_prov Hr op = NONE /\ op_taint tr op = {}` by
    (simp_tac (srw_ss()) [IN_UNION, IN_SING, IN_IMAGE, IN_UNIV] >>
     gen_tac >> disch_then DISJ_CASES_TAC
     >- (qpat_x_assum `op = cnt` SUBST1_TAC >> asm_rewrite_tac[]) >>
     pop_assum (qx_choose_then `w` SUBST1_TAC) >>
     simp[op_prov_def, op_taint_def]) >>
  drule_all abi_decode_scalar_success_frame >>
  disch_then (qspecl_then [`LENGTH c4.cs_current_insts`, `func`, `PG`, `D`]
    strip_assume_tac) >>
  suspend "payload"
QED

Resume abi_decode_bytes_member_prefix_ptr[payload]:
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG Hr tr
    (emitted_insts c3 c4) t Hl tl` >>
  qabbrev_tac `s4 = sl with vs_inst_idx := LENGTH c4.cs_current_insts` >>
  `not_fresh_at c3 src /\ not_fresh_at c3 dst` by
    (conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window Hl tl s4 src b h` by
    (qpat_assum `!x b h. x IN {x | not_fresh_at c3 x} /\ _ ==> _` irule >>
     simp_tac (srw_ss()) [IN_GSPEC] >> conj_tac >> first_assum ACCEPT_TAC) >>
  rename1 `addr = Var ar` >>
  `abi_decode_ptr_window Hl tl s4 ar (b+n2w p) (h-p)` by
    (qpat_assum `!x b h. x IN {x | not_fresh_at c3 x} /\ _ ==> _` irule >>
     simp_tac (srw_ss()) [IN_GSPEC] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_covers Hl tl dst s4 cap` by
    (qpat_assum `!x cap. x IN {x | not_fresh_at c3 x} /\ _ ==> _` irule >>
     simp_tac (srw_ss()) [IN_GSPEC] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var dst s4 = SOME d` by
    (qpat_assum `!x. x IN {x | not_fresh_at c3 x} ==> lookup_var x _ = _ /\ _`
      (qspec_then `dst` mp_tac) >> simp[]) >>
  `eval_operand head s1 = SOME (n2w (p+32))` by
    (simp_tac (srw_ss()) [Abbr `s1`, eval_operand_def, lookup_var_def] >>
     qpat_assum `eval_operand head sh = _` mp_tac >>
     simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `eval_operand hi s1 = SOME (n2w h)` by
    (`eval_operand hi sh = SOME (n2w h)` by
       (qpat_assum `!op w. eval_operand op s = SOME w ==> _` irule >>
        first_assum MATCH_ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `s1`, eval_operand_def, lookup_var_def] >>
     pop_assum mp_tac >> simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `eval_operand head t = SOME (n2w (p+32)) /\
   eval_operand hi t = SOME (n2w h)` by
    (qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
      (qspecl_then [`head`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!op. (!x. op = Var x ==> not_fresh_at c1 x) ==> _`
      (qspecl_then [`hi`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac >> metis_tac[]) >>
  `!op w. eval_operand op t = SOME w ==> eval_operand op s4 = SOME w` by
    (rpt gen_tac >> disch_tac >>
     `eval_operand op sl = SOME w` by
       (qpat_assum `!op w. eval_operand op t = SOME w ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [Abbr `s4`, eval_operand_def, lookup_var_def] >>
     pop_assum mp_tac >> simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `fresh_vars_wrt c4 s4` by
    fs[Abbr `s4`, fresh_vars_wrt_def] >>
  `eval_operand head s4 = SOME (n2w (p+32)) /\
   eval_operand cnt s4 = SOME (n2w (w2n (mload (w2n b+p) s))) /\
   eval_operand hi s4 = SOME (n2w h)` by
    (simp[n2w_w2n] >> metis_tac[]) >>
  `hi = Lit 0w \/ ?hh. eval_operand hi s4 = SOME (n2w hh) /\
    (p+32) + w2n (mload (w2n b+p) s) <= hh /\ hh < dimword(:256)` by
    (disj2_tac >> qexists_tac `h` >> conj_tac
     >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `p+32+_ <= h` mp_tac >>
       qpat_assum `w2n (b+n2w p) = _` (fn th => rewrite_tac[th])) >>
     first_assum ACCEPT_TAC) >>
  drule abi_decode_bytes_payload_guard_sequence >>
  disch_then (qspecl_then [`s4`, `p+32`, `w2n (mload (w2n b+p) s)`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (disj2_tac >> qexists_tac `hh` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK sp` >>
  `!x. head = Var x ==> not_fresh_at c3 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c3.cs_next_var head` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`t`, `n2w (p+32)`] >> conj_tac >> first_assum ACCEPT_TAC) >>
     pop_assum mp_tac >>
     qpat_assum `head = Var x` (fn th => pure_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!x. hi = Var x ==> not_fresh_at c3 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c3.cs_next_var hi` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`t`, `n2w h`] >> conj_tac >> first_assum ACCEPT_TAC) >>
     pop_assum mp_tac >>
     qpat_assum `hi = Var x` (fn th => pure_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `!op. op IN {head;cnt;hi} ==>
    op_prov Hr op = NONE /\ op_taint tr op = {}` by
    (simp_tac (srw_ss()) [IN_INSERT, NOT_IN_EMPTY] >> metis_tac[]) >>
  `!op. op IN {head;cnt;hi} ==>
    !x. op = Var x ==> x IN {x | not_fresh_at c3 x}` by
    (gen_tac >> simp_tac (srw_ss()) [IN_INSERT, NOT_IN_EMPTY] >>
     strip_tac >> simp_tac (srw_ss()) [IN_GSPEC] >>
     pop_assum SUBST1_TAC
     >- (qpat_assum `!x. head = Var x ==> _` MATCH_ACCEPT_TAC)
     >- (qpat_assum `cnt = Var out` SUBST1_TAC >>
         simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. hi = Var x ==> _` MATCH_ACCEPT_TAC) >>
  `!op. op IN {head;cnt;hi} ==>
    op_prov Hl op = NONE /\ op_taint tl op = {}` by
    (ho_match_mp_tac (Q.INST
       [`G` |-> `Hr`, `tn` |-> `tr`, `R` |-> `{x | not_fresh_at c3 x}`]
       abi_decode_scalar_clean_set_transport) >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     gen_tac >> disch_tac >>
     qpat_assum `!op. (!x. op = Var x ==> x IN {x | not_fresh_at c3 x}) ==> _`
       (qspec_then `op` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `!op. op IN {head;cnt;hi} UNION IMAGE Lit UNIV ==>
    op_prov Hl op = NONE /\ op_taint tl op = {}` by
    (ho_match_mp_tac abi_decode_scalar_clean_set_literals >> first_assum ACCEPT_TAC) >>
  `?Bp. bop_scalar_seq {x | not_fresh_at c4 x}
    ({head;cnt;hi} UNION IMAGE Lit UNIV) (emitted_insts c4 c5) Bp /\
    ({head;cnt;hi} UNION IMAGE Lit UNIV) SUBSET Bp` by
    (irule abi_decode_bytes_payload_scalar >>
     simp_tac (srw_ss()) [IN_UNION, IN_INSERT, NOT_IN_EMPTY, IN_GSPEC] >>
     qexistsl_tac [`head`, `hi`, `cnt`] >>
     simp_tac (srw_ss()) [] >> conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (abi_decode_scalar_success_frame |> Q.INST
    [`G` |-> `Hl`, `tn` |-> `tl`, `s` |-> `s4`, `t` |-> `sp`]) >>
  disch_then (qspecl_then [`LENGTH c5.cs_current_insts`, `func`, `PG`, `D`]
    strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `inst_seq_ptr D 0 ctx func PG Hl tl
    (emitted_insts c4 c5) s4 Hp tp` >>
  qabbrev_tac `s5 = sp with vs_inst_idx := LENGTH c5.cs_current_insts` >>
  `not_fresh_at c4 src /\ not_fresh_at c4 dst /\ not_fresh_at c4 ar` by
    (rpt conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window Hp tp s5 src b h` by
    (qpat_assum `!x b h. x IN {x | not_fresh_at c4 x} /\ _ ==> _` irule >>
     simp_tac (srw_ss()) [IN_GSPEC] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window Hp tp s5 ar (b+n2w p) (h-p)` by
    (qpat_assum `!x b h. x IN {x | not_fresh_at c4 x} /\ _ ==> _` irule >>
     simp_tac (srw_ss()) [IN_GSPEC] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `ptr_covers Hp tp dst s5 cap` by
    (qpat_assum `!x cap. x IN {x | not_fresh_at c4 x} /\ _ ==> _` irule >>
     simp_tac (srw_ss()) [IN_GSPEC] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var dst s5 = SOME d` by
    (qpat_assum `!x. x IN {x | not_fresh_at c4 x} ==> lookup_var x _ = _ /\ _`
      (qspec_then `dst` mp_tac) >> simp[]) >>
  suspend "boundary"
QED

Resume abi_decode_bytes_member_prefix_ptr[boundary]:
  `fresh_vars_wrt c5 s5` by fs[Abbr `s5`, fresh_vars_wrt_def] >>
  `eval_operand cnt s5 = SOME (n2w (w2n (mload (w2n b+p) s)))` by
    (simp_tac (srw_ss()) [Abbr `s5`, eval_operand_def, lookup_var_def] >>
     qpat_assum `!op w. eval_operand op s4 = SOME w ==> _`
       (qspecl_then [`cnt`, `n2w (w2n (mload (w2n b+p) s))`] mp_tac) >>
     asm_simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  `op_prov Hp cnt = NONE /\ op_taint tp cnt = {}` by
    (qpat_assum `!op. op IN Bp ==> _` irule >>
     qpat_assum `{head;cnt;hi} UNION IMAGE Lit UNIV SUBSET Bp` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF, IN_UNION, IN_INSERT, NOT_IN_EMPTY] >>
     metis_tac[]) >>
  `not_fresh_at c5 dst /\ not_fresh_at c5 ar` by
    (conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `!x. cnt = Var x ==> not_fresh_at c5 x` by
    (gen_tac >> disch_tac >>
     `abiDecoderReentry$abi_decoder_operand_live c5.cs_next_var cnt` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_fresh >>
        qexistsl_tac [`s5`, `n2w (w2n (mload (w2n b+p) s))`] >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     pop_assum mp_tac >>
     qpat_assum `cnt = Var x` (fn th => pure_rewrite_tac[th]) >>
     simp_tac (srw_ss()) [abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `abi_decode_ptr_window Hp tp s5 ar (b+n2w p)
    (32+w2n (mload (w2n b+p) s))` by
    (`32+w2n (mload (w2n b+p) s) <= h-p` by
       (qpat_assum `p+32+_ <= h` mp_tac >>
        qpat_assum `w2n (b+n2w p) = _` (fn th => rewrite_tac[th]) >> decide_tac) >>
     pop_assum mp_tac >>
     qpat_assum `abi_decode_ptr_window Hp tp s5 ar _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [abi_decode_ptr_window_def, ptr_covers_def] >>
     rpt strip_tac >> gvs[]) >>
  suspend "compose"
QED

Resume abi_decode_bytes_member_prefix_ptr[compose]:
  `inst_extends c1 c3` by
    (irule inst_extends_trans >> qexists_tac `c2` >> asm_rewrite_tac[]) >>
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c3.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c3 /\
   c4.cs_current_insts = c3.cs_current_insts ++ emitted_insts c3 c4 /\
   c5.cs_current_insts = c4.cs_current_insts ++ emitted_insts c4 c5` by
    asm_rewrite_tac[GSYM inst_extends_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa c1) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c3) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c3 c4) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c4 c5)` by
    (`emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 sb` by
       (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
     `emitted_insts c1 sb = emitted_insts c1 c3 ++ emitted_insts c3 sb` by
       (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
     `emitted_insts c3 sb = emitted_insts c3 c4 ++ emitted_insts c4 sb` by
       (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
     `emitted_insts c4 sb = emitted_insts c4 c5 ++ emitted_insts c5 sb` by
       (irule emitted_insts_append >> asm_rewrite_tac[GSYM inst_extends_def]) >>
     qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn a =>
     qpat_assum `emitted_insts c1 sb = _` (fn b =>
     qpat_assum `emitted_insts c3 sb = _` (fn c =>
     qpat_assum `emitted_insts c4 sb = _` (fn d =>
       pure_rewrite_tac[a,b,c,d,EVERY_APPEND])))) >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sh.vs_inst_idx = s.vs_inst_idx /\ sl.vs_inst_idx = t.vs_inst_idx /\
   sp.vs_inst_idx = s4.vs_inst_idx` by
    (qpat_assum `sh = s with vs_vars := _` mp_tac >>
     qpat_assum `sl = t with vs_vars := _` mp_tac >>
     qpat_assum `sp = s4 with vs_vars := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venom_state_component_equality]) >>
  `run_inst_seq (emitted_insts sa c1) s =
      OK (s1 with vs_inst_idx := s.vs_inst_idx) /\
   run_inst_seq (emitted_insts c3 c4) t =
      OK (s4 with vs_inst_idx := t.vs_inst_idx) /\
   run_inst_seq (emitted_insts c4 c5) s4 =
      OK (s5 with vs_inst_idx := s4.vs_inst_idx)` by
    simp[Abbr `s1`, Abbr `s4`, Abbr `s5`,
      venom_state_component_equality] >>
  `s1.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa c1) /\
   t.vs_inst_idx = s1.vs_inst_idx + LENGTH (emitted_insts c1 c3) /\
   s4.vs_inst_idx = t.vs_inst_idx + LENGTH (emitted_insts c3 c4) /\
   s5.vs_inst_idx = s4.vs_inst_idx + LENGTH (emitted_insts c4 c5)` by
    simp[Abbr `s1`, Abbr `s4`, Abbr `s5`] >>
  drule_all inst_seq_ptr_append_normalized >> strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ Hr tr (emitted_insts c3 c4) _ _ _` kall_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts c3 c4 ++ emitted_insts c4 c5)` by simp[EVERY_APPEND] >>
  drule_all inst_seq_ptr_append_normalized >> strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ H tm (emitted_insts c1 c3) _ _ _` kall_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (emitted_insts c1 c3 ++ (emitted_insts c3 c4 ++ emitted_insts c4 c5))`
    by simp[EVERY_APPEND] >>
  qpat_assum `inst_seq_ptr _ _ _ _ _ G tn (emitted_insts sa c1) s H tm`
    (mp_then Any mp_tac inst_seq_ptr_append_normalized) >>
  disch_then drule_all >> strip_tac >>
  `inst_extends sa c3` by
    (irule inst_extends_trans >> qexists_tac `c1` >> asm_rewrite_tac[]) >>
  `inst_extends sa c4` by
    (irule inst_extends_trans >> qexists_tac `c3` >> asm_rewrite_tac[]) >>
  `inst_extends sa c5` by
    (irule inst_extends_trans >> qexists_tac `c4` >> asm_rewrite_tac[]) >>
  `emitted_insts sa c5 = emitted_insts sa c1 ++
      (emitted_insts c1 c3 ++ (emitted_insts c3 c4 ++ emitted_insts c4 c5))` by
    (qpat_assum `c1.cs_current_insts = _` mp_tac >>
     qpat_assum `c3.cs_current_insts = _` mp_tac >>
     qpat_assum `c4.cs_current_insts = _` mp_tac >>
     qpat_assum `c5.cs_current_insts = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  suspend "frame"
QED

Resume abi_decode_bytes_member_prefix_ptr[frame]:
  `!x. not_fresh_at sa x ==> lookup_var x s5 = lookup_var x s /\
      FLOOKUP Hp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at c1 x` by
       (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at c1 x` irule >>
        first_assum ACCEPT_TAC) >>
     `not_fresh_at c3 x` by
       (qpat_assum `!x. not_fresh_at c1 x ==> not_fresh_at c3 x` irule >>
        first_assum ACCEPT_TAC) >>
     `not_fresh_at c4 x` by
       (qpat_assum `!x. not_fresh_at c3 x ==> not_fresh_at c4 x` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sh = _ /\ _` drule >>
     qpat_assum `!x. not_fresh_at c1 x ==> lookup_var x t = _ /\ _` drule >>
     qpat_assum `!x. x IN _ ==> lookup_var x s4 = _ /\ _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. x IN _ ==> lookup_var x s5 = _ /\ _` (qspec_then `x` mp_tac) >>
     simp[Abbr `s1`, lookup_var_def] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`c5`, `ar`, `cnt`, `s5`, `Hp`, `tp`] >>
  conj_tac >- (qpat_assum `addr = Var ar` (fn th => pure_rewrite_tac[GSYM th]) >>
    first_assum ACCEPT_TAC) >>
  `same_blocks sa c5` by
    (qpat_assum `same_blocks sa c1` mp_tac >>
     qpat_assum `same_blocks c1 c2` mp_tac >>
     qpat_assum `same_blocks c2 c3` mp_tac >>
     qpat_assum `same_blocks c3 c4` mp_tac >>
     qpat_assum `same_blocks c4 c5` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[same_blocks_def]) >>
  `cs_extends sa c5 /\ cs_extends c5 sb` by
    (qpat_assum `same_blocks sa c5` mp_tac >>
     qpat_assum `same_blocks c5 sb` mp_tac >>
     qpat_assum `inst_extends sa c5` mp_tac >>
     qpat_assum `inst_extends c5 sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[inst_extends_def, same_blocks_def, cs_extends_def, IS_PREFIX_APPEND]) >>
  conj_tac >-
    (irule (cj 2 fn_has_code_split) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sa` >> conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `emitted_insts sa c5 = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `s.vs_inst_idx = LENGTH sa.cs_current_insts`
       (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `emitted_insts sa c5 = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `~s5.vs_halted /\ s5.vs_current_bb = c5.cs_current_bb /\
   s5.vs_memory = s.vs_memory` by
    (qpat_assum `sp = s4 with vs_vars := _` mp_tac >>
     qpat_assum `sl = t with vs_vars := _` mp_tac >>
     qpat_assum `t.vs_memory = _` mp_tac >>
     qpat_assum `~t.vs_halted` mp_tac >>
     qpat_assum `t.vs_current_bb = _` mp_tac >>
     qpat_assum `same_blocks c3 c4` mp_tac >>
     qpat_assum `same_blocks c4 c5` mp_tac >>
     qpat_assum `sh.vs_memory = s.vs_memory` mp_tac >>
     simp_tac (srw_ss()) [Abbr `s5`, Abbr `s4`, Abbr `s1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_x_assum `sp = _` SUBST_ALL_TAC >>
     qpat_x_assum `sl = _` SUBST_ALL_TAC >> gvs[same_blocks_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp_tac (srw_ss()) [Abbr `s5`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `abi_decode_ptr_window Hp tp s5 ar _ (32+_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `eval_operand cnt s5 = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM, n2w_w2n]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `w2n (mload _ s) <= n` mp_tac >>
     qpat_assum `w2n (b+n2w p) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  conj_tac >-
    (qpat_assum `p+32+_ <= h` mp_tac >>
     qpat_assum `w2n (b+n2w p) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM, ADD_ASSOC]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (map_every (fn q => qpat_assum q mp_tac)
       [`tp.t_mem = tl.t_mem`, `tl.t_mem = tr.t_mem`,
        `tr.t_mem = tm.t_mem`, `tm.t_mem = tn.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!x. not_fresh_at sa x ==> not_fresh_at c5 x` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!x. not_fresh_at sa x ==> not_fresh_at c1 x`,
        `!x. not_fresh_at c1 x ==> not_fresh_at c3 x`,
        `!x. not_fresh_at c3 x ==> not_fresh_at c4 x`,
        `!x. not_fresh_at c4 x ==> not_fresh_at c5 x`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  pop_assum mp_tac >>
  map_every (fn q => qpat_assum q mp_tac)
    [`tp.t_stor = tl.t_stor`, `tl.t_stor = tr.t_stor`,
     `tr.t_stor = tm.t_stor`, `tm.t_stor = tn.t_stor`,
     `tp.t_trans = tl.t_trans`, `tl.t_trans = tr.t_trans`,
     `tr.t_trans = tm.t_trans`, `tm.t_trans = tn.t_trans`,
     `tp.t_imm = tl.t_imm`, `tl.t_imm = tr.t_imm`,
     `tr.t_imm = tm.t_imm`, `tm.t_imm = tn.t_imm`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Finalise abi_decode_bytes_member_prefix_ptr
