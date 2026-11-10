(* Actual emitted code for the allocation-free calldata word decoder. *)
Theory calldataWordPtr
Ancestors calldataOverwritePtr calldataWordStepsPtr calldataClampPtr calldataDecodePtr abiDecoderClampedWord abiDecoderContract abiDecoderClamp
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps fragExec
  venomInst list arithmetic words bodyPtrDefs decoderGhostFramePtr
  ptrDiscipline ptrSafeRun venomState venomExecSemantics entryDispatchPtr
  fragExecPtr ghostPcTransportPtr finite_map pred_set codegenRel instIdxIndep ptrSafetyTransport

(* The calldata address step: base Lit 0w adds no instruction. *)
val calldata_pos_addr = prove(
  ``compile_abi_dec_addr (Lit 0w) pos st = (pos,st)``,
  simp[abiEncoderTheory.compile_abi_dec_addr_def, compileEnvTheory.comp_return_def]);

Theorem calldata_unclamped_word_instructions:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord NoClamp) sa = ((),sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id CALLDATALOAD [src]
       ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) MSTORE
       [Var p; Var ("%" ++ toString sa.cs_next_var)] []] /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  simp[compile_abi_decode_to_buf_def, calldata_pos_addr, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX]
QED

Theorem calldata_clamped_word_prefix_framed_uniform:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD sw s) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [compile_abi_decode_to_buf_def, calldata_pos_addr, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  `inst_extends sa c1 /\ inst_extends c2 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `same_blocks sa c1 /\ same_blocks c2 sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa c1 /\ cs_extends c2 sb` by
    (fs[inst_extends_def, same_blocks_def, cs_extends_def] >>
     conj_tac >> qexists_tac `[]` >> simp[]) >>
  `cs_extends c1 c2` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 fn /\ fn_has_code c1 sb fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code c1 c2 fn /\ fn_has_code c2 sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all calldata_load_prefix_framed_uniform >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  rename1 `fresh_vars_wrt c1 s1` >>
  `not_fresh_at sa p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `fresh_vars_wrt sa s` mp_tac >>
     simp[fresh_vars_wrt_def] >>
     qexists_tac `n` >>
     gvs[eval_operand_def, lookup_var_def, FLOOKUP_DEF]) >>
  `lookup_var p s1 = lookup_var p s` by
    metis_tac[eval_operand_def, optionTheory.SOME_11] >>
  `ptr_covers H u p s1 32` by metis_tac[ptr_covers_frame] >>
  `allocas_from lo s1` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  drule_all calldata_clamp_prefix_framed_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `fresh_vars_wrt c2 s2` >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
    (qpat_x_assum `emit_op CALLDATALOAD _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``n <= n + 1``]) >>
  `lookup_var p s2 = lookup_var p s1` by
    metis_tac[eval_operand_def, optionTheory.SOME_11] >>
  `ptr_covers G' tn' p s2 32` by metis_tac[ptr_covers_frame] >>
  `eval_operand (Var p) s2 = SOME dw /\
   eval_operand value s2 = SOME (abi_decode_load CALLDATALOAD sw s)` by metis_tac[] >>
  `op_taint tn' value = {}` by
    (Cases_on `value` >> fs[op_taint_def] >>
     rename1 `eval_operand (Var x) s1 = _` >>
     `not_fresh_at c1 x` by
       (simp[not_fresh_at_def] >> rpt strip_tac >>
        qpat_x_assum `fresh_vars_wrt c1 s1` mp_tac >>
        simp[fresh_vars_wrt_def] >> qexists_tac `n` >>
        gvs[eval_operand_def, lookup_var_def, FLOOKUP_DEF]) >> metis_tac[]) >>
  `allocas_from lo s2` by
    (qpat_x_assum `allocas_from lo s1` mp_tac >> simp[allocas_from_def]) >>
  drule_all clean_mstore_prefix_framed_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!a z. eval_operand a s = SOME z ==> eval_operand a t = SOME z` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> FLOOKUP H' x = FLOOKUP G x /\
     op_taint u' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `(!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H' u' t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by metis_tac[] >>
  qexistsl_tac [`t`, `H'`, `u'`] >>
  simp[] >>
  suspend "word_sequence"
QED

Resume calldata_clamped_word_prefix_framed_uniform[word_sequence]:
  reverse conj_tac >- metis_tac[SUBSET_TRANS, SUBSET_REFL] >>
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c2.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c2 /\
   sb.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 sb` by
    (drule calldata_clamp_instructions >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[mk_inst_def, is_terminator_def] >> fs[MEM] >>
     Cases_on `signed` >> simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 sb)` by
    (drule emitted_insts_emit_void >> simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts c1 c2) (s1 with vs_inst_idx := s.vs_inst_idx) =
    OK (s2 with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `run_inst_seq (emitted_insts c2 sb) (s2 with vs_inst_idx := s.vs_inst_idx) =
    OK (t with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qspecl_then [`sa`, `c1`, `sb`, `s`, `s1 with vs_inst_idx := s.vs_inst_idx`]
    mp_tac run_inst_seq_chain >> simp[]
QED

Finalise calldata_clamped_word_prefix_framed_uniform

Theorem calldata_clamped_word_prefix_framed:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD sw s) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all calldata_clamped_word_prefix_framed_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >> simp[]
QED

Theorem calldata_unclamped_word_prefix_framed:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord NoClamp) sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s 32 /\
  op_taint tn src = {} /\ fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> irule calldata_clamped_word_prefix_framed >>
  simp[] >> qexists_tac `NoClamp` >> simp[abi_decoder_clamp_valid_def]
QED

Theorem calldata_word_overwrite_prefix_uniform:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\
  ptr_covers G tn p s 32 /\ op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    s' = actual with vs_inst_idx := LENGTH sb.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK actual` (mk_asm "actual_run") >>
  simp_tac (srw_ss()) [compile_abi_decode_to_buf_def, calldata_pos_addr, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  `inst_extends sa c1 /\ inst_extends c2 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `same_blocks sa c1 /\ same_blocks c2 sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa c1 /\ cs_extends c2 sb` by
    (fs[inst_extends_def, same_blocks_def, cs_extends_def] >>
     conj_tac >> qexists_tac `[]` >> simp[]) >>
  `cs_extends c1 c2` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa c1 fn /\ fn_has_code c1 sb fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code c1 c2 fn /\ fn_has_code c2 sb fn` by
    metis_tac[fn_has_code_split] >>
  drule_all calldata_load_overwrite_prefix_uniform >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  rename1 `eval_operand value s1 = SOME _` >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
    (qpat_x_assum `emit_op CALLDATALOAD _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``n <= n + 1``]) >>
  `!x. value = Var x ==> not_fresh_at c1 x` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `emit_op CALLDATALOAD _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       not_fresh_at_def] >> metis_tac[LESS_EQ_ANTISYM]) >>
  `eval_operand (Var p) s1 = SOME dw /\ eval_operand src s1 = SOME sw` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `lookup_var p s1 = lookup_var p s` by
    metis_tac[eval_operand_def, optionTheory.SOME_11] >>
  `ptr_covers H u p s1 32` by metis_tac[ptr_covers_frame] >>
  `allocas_from lo s1` by
    (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  `?mid. run_inst_seq (emitted_insts c1 c2) s1 = OK mid` by
    suspend "clamp_success" >>
  drule_all calldata_clamp_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `s2 = mid with vs_inst_idx := _` >>
  `eval_operand (Var p) s2 = SOME dw /\ eval_operand src s2 = SOME sw /\
   eval_operand value s2 = SOME (abi_decode_load CALLDATALOAD sw s)` by
    (rpt conj_tac >> qpat_assum `!a v. _ ==> eval_operand a s2 = SOME v` irule >>
     simp[]) >>
  `lookup_var p s2 = lookup_var p s1` by
    metis_tac[eval_operand_def, optionTheory.SOME_11] >>
  `ptr_covers G' tn' p s2 32` by metis_tac[ptr_covers_frame] >>
  `op_taint tn' value = {}` by
    (Cases_on `value` >> fs[op_taint_def] >> metis_tac[]) >>
  `allocas_from lo s2` by
    (qpat_x_assum `allocas_from lo s1` mp_tac >> simp[allocas_from_def]) >>
  drule_all clean_mstore_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> FLOOKUP H' x = FLOOKUP G x /\
     op_taint u' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `(!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H' u' t) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)` by metis_tac[] >>
  `run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
    suspend "word_sequence" >>
  pop_assum (mk_asm "ghost_run") >>
  `actual = t with vs_inst_idx := s.vs_inst_idx` by
    (asm "ghost_run" mp_tac >> asm "actual_run" (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) []) >>
  pop_assum SUBST1_TAC >>
  qexistsl_tac [`H'`, `u'`] >>
  asm_x "actual_run" kall_tac >>
  `eval_operand (Var p) t = SOME dw /\ eval_operand src t = SOME sw` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `t with vs_inst_idx := LENGTH sb.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  simp[] >> conj_tac
  >- (asm "ghost_run" mp_tac >> simp[]) >>
  qpat_x_assum `_ SUBSET tn'.t_mem` mp_tac >> simp[]
QED

Resume calldata_word_overwrite_prefix_uniform[word_sequence]:
  qpat_x_assum `s2 = mid with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK mid` kall_tac >>
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c2.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c2 /\
   sb.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 sb` by
    (drule calldata_clamp_instructions >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[mk_inst_def, is_terminator_def] >> fs[MEM] >>
     Cases_on `signed` >> simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c2 sb)` by
    (drule emitted_insts_emit_void >> simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts c1 c2) (s1 with vs_inst_idx := s.vs_inst_idx) =
    OK (s2 with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `run_inst_seq (emitted_insts c2 sb) (s2 with vs_inst_idx := s.vs_inst_idx) =
    OK (t with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qspecl_then [`sa`, `c1`, `sb`, `s`, `s1 with vs_inst_idx := s.vs_inst_idx`]
    mp_tac run_inst_seq_chain >> simp[]
QED

Resume calldata_word_overwrite_prefix_uniform[clamp_success]:
  `c1.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c1 /\
   c2.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 c2 /\
   sb.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 sb` by
    (drule calldata_clamp_instructions >> fs[inst_extends_def]) >>
  `sb.cs_current_insts = c1.cs_current_insts ++ emitted_insts c1 sb` by
    metis_tac[emitted_insts_append, APPEND_ASSOC] >>
  qspecl_then [`sa`, `c1`, `sb`, `s`, `s1 with vs_inst_idx := s.vs_inst_idx`]
    mp_tac run_inst_seq_chain >> simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts c1 sb) (s1 with vs_inst_idx := s.vs_inst_idx) = OK actual` by
    (asm "actual_run" mp_tac >> simp[]) >>
  `emitted_insts c1 sb = emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    metis_tac[emitted_insts_append] >>
  `?z. run_inst_seq (emitted_insts c1 c2)
      (s1 with vs_inst_idx := s.vs_inst_idx) = OK z` by
    (spose_not_then assume_tac >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `emitted_insts c2 sb` mp_tac) >>
     qpat_assum `emitted_insts c1 sb = _ ++ _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_assum `run_inst_seq _ (_ with vs_inst_idx := _) = OK actual`
       (fn th => rewrite_tac[th]) >>
     metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (drule calldata_clamp_instructions >> strip_tac >>
     simp[mk_inst_def, is_terminator_def] >> fs[MEM] >>
     Cases_on `signed` >> simp[mk_inst_def, is_terminator_def]) >>
  qpat_x_assum `run_inst_seq _ (_ with vs_inst_idx := _) = OK z` mp_tac >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, AllCaseEqs()] >>
  strip_tac >> Cases_on `run_inst_seq (emitted_insts c1 c2) s1` >>
  gvs[exec_result_map_def]
QED

Finalise calldata_word_overwrite_prefix_uniform

(* Fixed-bound compatibility interface; witnesses are chosen by the uniform provider. *)
Theorem calldata_word_overwrite_prefix:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\
  ptr_covers G tn p s 32 /\ op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    s' = actual with vs_inst_idx := LENGTH sb.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\ eval_operand src s' = SOME sw /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' 32 /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    mem_word_at (w2n dw) s'.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all calldata_word_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`s'`,`G'`,`tn'`] >> simp[]
QED
