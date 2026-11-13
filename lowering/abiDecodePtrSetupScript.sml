(* Composition boundaries for the builtin header and output allocation. *)
Theory abiDecodePtrSetup
Ancestors
  abiDecodePtrHeaderLoad abiDecodePtrLengthGuard abiDecodePtrInputWindow
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard
  abiBuiltinPrefix bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsShaAllocPath
  exprSimPtrProps appendStorageGhostPtr bodyPtrBopScalarCompile
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq exprSimAccounts instIdxIndep
  fragExec fragGasPathPtr emitHelper emitHelperProps exprLoweringProps
  compileEnv freshWrites ptrDiscipline venomState venomInst list rich_list pred_set

Theorem abi_builtin_decode_header_trace_ptr:
  abi_builtin_decode_header data mn mx sa = (inputs,sh) ==>
  ?len sm src sb.
    emit_op MLOAD [data] sa = (len,sm) /\
    emit_op ADD [data; Lit 32w] sm = (src,sb) /\
    abi_builtin_length_guard len mn mx sb = ((),sh) /\
    inputs = (len,src)
Proof
  simp[abi_builtin_decode_header_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_builtin_decode_header_success_path_ptr:
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  fn_has_code sa sh func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+n) /\
  w2n w + 32+n < dimword (:256) /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sh) s = OK t ==>
  ?G' tn' q r.
    src = Var q /\ len = Var r /\
    not_fresh_at sh q /\ not_fresh_at sh r /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sh) s G' tn' /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
    eval_operand len t = SOME (mload (w2n w) s) /\
    op_prov G' len = NONE /\ op_taint tn' len = {} /\
    lookup_var q t = SOME (w+32w) /\ ptr_covers G' tn' q t n /\
    ~t.vs_halted /\ t.vs_current_bb = sh.cs_current_bb /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\
    state_frame t = state_frame s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule abi_builtin_decode_header_trace_ptr >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  drule abi_builtin_length_guard_scalar >>
  disch_then (qspecl_then [`{x | not_fresh_at sb x}`, `{len} UNION IMAGE Lit UNIV`] mp_tac) >>
  simp[] >> strip_tac >>
  `cs_extends sb sh` by suspend "extends" >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule abi_decode_header_load_path_ptr >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`tn`, `n`, `PG`, `G`, `D`] mp_tac) >>
  (impl_tac >- simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  rename1 `src = Var q` >> rename1 `len = Var r` >>
  qmatch_asmsub_rename_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u)` >>
  `run_inst_seq (emitted_insts sb sh) u = OK (t with vs_inst_idx := u.vs_inst_idx)` by
    suspend "raw" >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sh) (DROP u.vs_inst_idx bb.bb_instructions)` by
    suspend "code" >>
  `!x. x IN {x | not_fresh_at sb x} ==> not_fresh_at sb x` by simp[] >>
  drule_all (abi_builtin_length_guard_success_path |> Q.INST [`R` |-> `{x | not_fresh_at sb x}`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "transport"
QED

Resume abi_builtin_decode_header_success_path_ptr[extends]:
  fs[same_blocks_def, cs_extends_def] >> qexists_tac `[]` >> simp[]
QED
Resume abi_builtin_decode_header_success_path_ptr[raw]:
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[arithmeticPropsTheory.extends_trans] >>
  `emitted_insts sa sh = emitted_insts sa sb ++ emitted_insts sb sh` by
    (irule emitted_insts_append >> simp[]) >>
  drule run_inst_seq_append >> disch_then (qspec_then `emitted_insts sb sh` mp_tac) >>
  simp[] >> strip_tac >>
  drule bop_scalar_seq_opcodes >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sh)` by
    gvs[EVERY_MEM] >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`u`, `s.vs_inst_idx`] mp_tac) >>
  Cases_on `run_inst_seq (emitted_insts sb sh) u` >>
  simp[exec_result_map_def] >> strip_tac >> gvs[] >>
  qpat_assum `run_inst_seq (emitted_insts sb sh) u = OK _`
    (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac bop_scalar_seq_runtime_frame) >>
  disch_then drule >> strip_tac >>
  qpat_x_assum `_ = u with vs_vars := _` mp_tac >>
  simp[venom_state_component_equality]
QED
Resume abi_builtin_decode_header_success_path_ptr[code]:
  `sh.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  qpat_x_assum `fn_has_code sb sh func` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[prefix_drop_equiv] >> strip_tac >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC
QED
Resume abi_builtin_decode_header_success_path_ptr[transport]:
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  `sh.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  `not_fresh_at sh q /\ not_fresh_at sh r` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `run_inst_seq (emitted_insts sb sh) u = OK _`
    (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac bop_scalar_seq_runtime_frame) >>
  disch_then drule >> strip_tac >>
  `!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x u` by
    (fs[lookup_var_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx func PG H tm u 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts))` by
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ H _ _ _ _ _ _` mp_tac >> simp[]) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sh.cs_current_insts))` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sh) s G' tn'` by
    suspend "sequence" >>
  qexistsl_tac [`G'`, `tn'`, `q`, `r`] >> simp[] >>
  suspend "fields"
QED
Resume abi_builtin_decode_header_success_path_ptr[fields]:
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[arithmeticPropsTheory.extends_trans] >>
  `run_inst_seq (emitted_insts sb sh) (u with vs_inst_idx := s.vs_inst_idx) = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sb) s = _`
      (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sb sh` mp_tac) >>
     `emitted_insts sa sh = emitted_insts sa sb ++ emitted_insts sb sh` by
       (irule emitted_insts_append >> simp[]) >>
     simp[] >> strip_tac >> gvs[]) >>
  qpat_assum `run_inst_seq _ (u with vs_inst_idx := s.vs_inst_idx) = OK t`
    (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac bop_scalar_seq_runtime_frame) >>
  disch_then drule >> strip_tac >>
  `!x. not_fresh_at sb x ==> op_taint tn' (Var x) = op_taint tm (Var x)` by
    (simp[op_taint_def] >> gvs[]) >>
  `op_prov G' (Var r) = NONE /\ op_taint tn' (Var r) = {}` by
    (gvs[op_prov_def] >> metis_tac[]) >>
  `ptr_covers G' tn' q t n` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  qpat_x_assum `t = u with <|vs_vars := _; vs_inst_idx := _|>` (fn th => once_rewrite_tac[th]) >> simp[]
QED
Resume abi_builtin_decode_header_success_path_ptr[sequence]:
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[arithmeticPropsTheory.extends_trans] >>
  `emitted_insts sa sh = emitted_insts sa sb ++ emitted_insts sb sh` by
    (irule emitted_insts_append >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = u.vs_inst_idx` by
    metis_tac[LENGTH_APPEND] >>
  asm_rewrite_tac[] >>
  irule bop_inst_seq_ptr_append >>
  conj_tac >-
    (qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
       (irule emitted_insts_append >> simp[]) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`H`, `u with vs_inst_idx := s.vs_inst_idx`, `tm`] >>
  gvs[]
QED
Finalise abi_builtin_decode_header_success_path_ptr

Theorem abi_builtin_decode_header_abort_path_ptr:
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  fn_has_code sa sh func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+n) /\
  w2n w + 32+n < dimword (:256) /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem) /\
  run_inst_seq (emitted_insts sa sh) s = Abort a t ==>
  ?G' tn' k j.
    gas_path_ptr D 0 ctx func PG G tn s k G' tn'
      (Abort a (t with vs_inst_idx := j)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule abi_builtin_decode_header_trace_ptr >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  drule abi_builtin_length_guard_scalar >>
  disch_then (qspecl_then [`{x | not_fresh_at sb x}`, `{len} UNION IMAGE Lit UNIV`] mp_tac) >>
  simp[] >> strip_tac >>
  `cs_extends sb sh` by
    (fs[same_blocks_def, cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule abi_decode_header_load_path_ptr >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`tn`, `n`, `PG`, `G`, `D`] mp_tac) >>
  (impl_tac >- simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  qmatch_asmsub_rename_tac `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK u)` >>
  `?v. run_inst_seq (emitted_insts sb sh) u = Abort a v /\
       !j. t with vs_inst_idx := j = v with vs_inst_idx := j` by
    suspend "raw_abort" >>
  pop_assum strip_assume_tac >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sh) (DROP u.vs_inst_idx bb.bb_instructions)` by
    suspend "code_abort" >>
  `!x. x IN {x | not_fresh_at sb x} ==> not_fresh_at sb x` by simp[] >>
  drule_all (abi_builtin_length_guard_abort_path |> Q.INST [`R` |-> `{x | not_fresh_at sb x}`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose_abort"
QED
Resume abi_builtin_decode_header_abort_path_ptr[raw_abort]:
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[arithmeticPropsTheory.extends_trans] >>
  `emitted_insts sa sh = emitted_insts sa sb ++ emitted_insts sb sh` by
    (irule emitted_insts_append >> simp[]) >>
  drule run_inst_seq_append >> disch_then (qspec_then `emitted_insts sb sh` mp_tac) >>
  simp[] >> strip_tac >>
  drule bop_scalar_seq_opcodes >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sh)` by
    gvs[EVERY_MEM] >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`u`, `s.vs_inst_idx`] mp_tac) >>
  Cases_on `run_inst_seq (emitted_insts sb sh) u` >>
  simp[exec_result_map_def] >> strip_tac >> gvs[]
QED
Resume abi_builtin_decode_header_abort_path_ptr[code_abort]:
  `sh.cs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  qpat_x_assum `fn_has_code sb sh func` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[prefix_drop_equiv] >> strip_tac >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC
QED
Resume abi_builtin_decode_header_abort_path_ptr[compose_abort]:
  `gas_path_ptr D 0 ctx func PG G tn s n' G' tn'
      (Abort a (v with vs_inst_idx := j))` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `n'`, `j`] >> simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  gvs[op_taint_def]
QED
Finalise abi_builtin_decode_header_abort_path_ptr
