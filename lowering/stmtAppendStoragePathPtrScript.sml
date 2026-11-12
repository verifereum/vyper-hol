(* Counted pointer paths for the storage Append suffix. *)
Theory stmtAppendStoragePathPtr
Ancestors
  appendStorageStageTransportPtr stmtSimAppendStorageCompose fragGasSeqPtr
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs
  fragExec stateFrame venomExecSemantics venomInst venomState
  list rich_list arithmetic fragGasSeqAbort venomInstProofs instIdxIndep
  fragGasPath stmtSimAppendStorage emittedSeqComposePtr ptrDiscipline
  finite_map stmtFragPtr words

Theorem append_storage_word_suffix_no_gas:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sf)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC,
                   rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def]
QED

Theorem append_storage_word_suffix_code:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sb sf) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts sb sf) = LENGTH sf.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode)
      (emitted_insts sb sf)
Proof
  strip_tac >>
  drule append_storage_word_suffix_no_gas >> strip_tac >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND] >>
  conj_tac
  >- (qexists_tac `l` >>
      REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  fs[EVERY_MEM]
QED

(* Unlike the general abort lift, this interface records that no GAS can
   occur in the executed prefix. The unexecuted tail needs no certificate. *)
Theorem run_inst_seq_abort_zero_path_ptr:
  !code s t a G tn G' tn' ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
          (Abort a (t with vs_inst_idx := j))
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `step_prov PG G h u`,
        `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `fn`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexists_tac `j` >>
      drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
      simp[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  drule_all gas_path_ptr_abort >> simp[]
QED

Theorem append_storage_word_abort_path_ptr:
  compile_dynarray_append cenv (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  cap <= w2n (if tr then tload slot s else sload slot s) /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'. gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (Abort Revert_abort t) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sb x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all append_storage_word_suffix_code >> strip_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_dynarray_append_word_parts]) >> strip_tac >>
  `eval_operand (Lit slot) s = SOME slot /\
   (!x. Lit slot = Var x ==> not_fresh_at sb x) /\
   op_taint tn (Lit slot) = {}` by simp[eval_operand_def, op_taint_def] >>
  `~(w2n (if tr then tload slot s else sload slot s) < cap)` by simp[] >>
  drule_all append_storage_guard_abort_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sb s3 /\ inst_extends s3 sf` by
    metis_tac[inst_extends_trans] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb s3)` by
    (`emitted_insts sb sf = emitted_insts sb s3 ++ emitted_insts s3 sf` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     fs[EVERY_MEM]) >>
  `run_inst_seq (emitted_insts sb sf) s = Abort Revert_abort t` by
    (`emitted_insts sb sf = emitted_insts sb s3 ++ emitted_insts s3 sf` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     simp[run_inst_seq_append_err]) >>
  drule_all emitted_inst_seq_ptr_uniform_abort_extend >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sb sf) s G' tn'` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sb sf)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := j`, `G'`, `tn'`] >> simp[]
QED

Theorem append_storage_word_success_path_ptr:
  compile_dynarray_append cenv (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sf.cs_current_insts)) /\
    state_frame t = state_frame
      (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w s)
       else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w s)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_imm = tn.t_imm /\
    (if tr then
       tn'.t_trans = key_update (key_update tn.t_trans (slot+1w+n2w len) {}) slot {} /\
       tn'.t_stor = tn.t_stor
     else
       tn'.t_stor = key_update (key_update tn.t_stor (slot+1w+n2w len) {}) slot {} /\
       tn'.t_trans = tn.t_trans) /\
    (!x. not_fresh_at sb x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all append_storage_word_suffix_code >> strip_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_dynarray_append_word_parts]) >> strip_tac >>
  `eval_operand (Lit slot) s = SOME slot /\
   (!x. Lit slot = Var x ==> not_fresh_at sb x) /\
   op_taint tn (Lit slot) = {} /\
   w2n (if tr then tload slot s else sload slot s) < cap` by
     simp[eval_operand_def, op_taint_def] >>
  drule_all append_storage_guard_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
  `sb.cs_next_var <= s3.cs_next_var` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _` mp_tac >>
     qpat_assum `emit_op LT _ _ = _` mp_tac >>
     qpat_assum `emit_void ASSERT _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >> gvs[]) >>
  `!x. lop = Var x ==> not_fresh_at s3 x` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _` mp_tac >>
     qpat_assum `emit_op LT _ _ = _` mp_tac >>
     qpat_assum `emit_void ASSERT _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >>
     gvs[not_fresh_at_def] >> simp[]) >>
  `!x. Lit slot = Var x \/ lop = Var x \/ op = Var x ==> not_fresh_at s3 x` by
    (simp[] >> metis_tac[not_fresh_at_mono]) >>
  suspend "suffix_inputs"
QED

Resume append_storage_word_success_path_ptr[suffix_inputs]:
  `eval_operand op t = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `op_taint tn' op = {}` by
    (Cases_on `op` >> gvs[op_taint_def]) >>
  `eval_operand (Lit slot) t = SOME slot /\ op_taint tn' (Lit slot) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `~t.vs_call_ctx.cc_static` by
    (qpat_assum `state_frame t = state_frame s` mp_tac >>
     qpat_assum `~s.vs_call_ctx.cc_static` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  drule_all append_storage_suffix_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G'`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume append_storage_word_success_path_ptr[compose]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sb s3 /\ inst_extends s3 sf` by
    metis_tac[inst_extends_trans] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb s3)` by
    (`emitted_insts sb sf = emitted_insts sb s3 ++ emitted_insts s3 sf` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >> fs[EVERY_MEM]) >>
  `run_inst_seq (emitted_insts sb sf) s = OK t'` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`t`, `s3`] >> simp[]) >>
  drule_all emitted_inst_seq_ptr_uniform_compose >> strip_tac >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sb sf) s G9 tn9` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sb sf)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sb sf)) = 0` by
    (simp[LENGTH_NIL, FILTER_EQ_NIL] >> fs[EVERY_MEM]) >>
  qexistsl_tac [`t'`, `G9`, `tn9`] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[ADD_COMM]) >>
  suspend "post"
QED

Resume append_storage_word_success_path_ptr[post]:
  conj_tac
  >- (qpat_assum `state_frame t' = _` mp_tac >>
      qpat_assum `state_frame t = state_frame s` mp_tac >>
      qpat_assum `len = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `tr` >>
      simp[state_frame_def, venom_state_component_equality,
           tstore_def, sstore_def, LET_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qpat_assum `if tr then _ else _` mp_tac >>
      simp[] >> Cases_on `tr` >> simp[] >>
      gvs[]) >>
  conj_tac >> rpt strip_tac >>
  `not_fresh_at s3 x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Finalise append_storage_word_success_path_ptr
