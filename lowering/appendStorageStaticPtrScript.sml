(* Static storage Append certifies only the actually executed prefix. *)
Theory appendStorageStaticPtr
Ancestors
  appendStorageRel appendStorageStageTransportPtr stmtAppendStorageSuffixPtr
  stmtAppendStoragePathPtr stmtSimAppendStorage fragGasCopyLoop fragGasSeqPtr fragExecMem
  fragGasCopySeqLiftProps
  exprLowering emitHelper contextCodegenRel freshWrites
  instMemFrontier emittedSeqComposePtr ptrSafeRun ptrDiscipline
  exprLoweringProps emitHelperProps stateFrame venomInst venomState
  compileEnv loweringStateRelDefs finite_map list rich_list arithmetic
  venomExecSemantics venomInstProps venomInstProofs codegenRel memSafeRun

Theorem append_storage_word_static_origin_path:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then LocTransient else LocStorage) sa = ((),sb) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME w /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  cap < dimword (:256) /\
  w2n (if tr then tload slot s else sload slot s) < cap /\
  s.vs_call_ctx.cc_static /\
  op_taint tn bop = {} /\ op_taint tn vop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u j Gf tf. state_frame u = state_frame s /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (Abort ExHalt_abort
        ((halt_state (set_returndata [] u)) with vs_inst_idx := j),Gf,tf))
Proof
  strip_tac >> drule_all append_storage_word_static_run_actual >> strip_tac >>
  `!D. ?Gf tf. inst_seq_ptr D 0 ctx func PG G tn
      (emitted_insts sa sb) s Gf tf` by suspend "pointer" >>
  `?Gf tf. !D. inst_seq_ptr D 0 ctx func PG G tn
      (emitted_insts sa sb) s Gf tf` by
    metis_tac[inst_seq_ptr_ghost_unique] >>
  drule_all append_storage_word_suffix_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
      i.inst_opcode <> DALLOCA) (emitted_insts sa sb) /\
   run_inst_seq_mem_ok (emitted_insts sa sb) s` by suspend "memory" >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post u. emitted_insts sa sb = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     `MEM i (emitted_insts sa sb)` by simp[] >>
     irule dalloca_no_wrap_non_dalloca >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >> strip_tac >>
  qexistsl_tac [`u`, `j`, `Gf`, `tf`] >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >>
  first_x_assum irule >>
  irule (Q.INST [`lo0` |-> `0`] inst_seq_ptr_lower_bound_transport) >>
  simp[] >> fs[EVERY_MEM]
QED

Resume append_storage_word_static_origin_path[pointer]:
  gen_tac >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_dynarray_append_word_parts]) >> strip_tac >>
  `!x. bop = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all append_storage_guard_actual >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts sa s3) s = OK t3` >>
  rename1 `!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa s3)
      (s with vs_inst_idx := k) G3 tn3` >>
  `sa.cs_next_var <= s3.cs_next_var /\
   (!x. lop = Var x ==> not_fresh_at s3 x)` by
    (qpat_assum `emit_op (if tr then TLOAD else SLOAD) _ _ = _` mp_tac >>
     qpat_assum `emit_op LT _ _ = _` mp_tac >>
     qpat_assum `emit_void ASSERT _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >>
     gvs[not_fresh_at_def] >> simp[]) >>
  `!x. bop = Var x \/ vop = Var x ==> not_fresh_at s3 x` by
    metis_tac[not_fresh_at_mono] >>
  `eval_operand bop t3 = SOME slot /\ eval_operand vop t3 = SOME w` by
    (Cases_on `bop` >> Cases_on `vop` >> gvs[eval_operand_def]) >>
  `op_taint tn3 bop = {} /\ op_taint tn3 vop = {}` by
    (Cases_on `bop` >> Cases_on `vop` >> gvs[op_taint_def]) >>
  `!x. bop = Var x ==> not_fresh_at s3 x` by metis_tac[] >>
  drule_all append_storage_address_stages_actual >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t3` by
    (qpat_assum `state_frame t3 = state_frame s`
       (strip_assume_tac o SRULE [state_frame_def] o Q.AP_TERM `\st. (st.vs_allocas,st.vs_initial_fmp,st.vs_fmp)`) >>
     strip_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` drule >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all append_storage_address_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G3`, `D`] strip_assume_tac) >>
  suspend "store"
QED

Resume append_storage_word_static_origin_path[store]:
  rename1 `run_inst_seq (emitted_insts s5 s6) t5 = OK t6` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends s3 s5 /\ inst_extends s3 s6` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts s3 s5) t3 = OK t5` by
    (irule run_inst_seq_compose_ok >> goal_assum drule >> simp[]) >>
  `run_inst_seq (emitted_insts s3 s6) t3 = OK t6` by
    (irule run_inst_seq_compose_ok >> goal_assum drule >> simp[]) >>
  `writes_fresh s3 (emitted_insts s3 s6)` by
    (irule append_storage_address_writes_fresh >> metis_tac[]) >>
  `eval_operand vop t6 = SOME w` by
    (`eval_operand vop t6 = eval_operand vop t3` by
       (irule writes_fresh_old_operand >> metis_tac[]) >> simp[]) >>
  `state_frame t6 = state_frame s` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t6` by
    (qpat_assum `state_frame t6 = state_frame s`
       (strip_assume_tac o SRULE [state_frame_def] o Q.AP_TERM `\st. (st.vs_allocas,st.vs_initial_fmp,st.vs_fmp)`) >>
     strip_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` drule >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `t6.vs_call_ctx.cc_static` by gvs[state_frame_def] >>
  `op_taint tn6 vop = {}` by
    (`op_taint tn6 vop = op_taint tn3 vop` by
       (irule old_operand_taint_frame >> metis_tac[]) >> simp[]) >>
  `emitted_insts s6 s7 =
     [mk_inst s6.cs_next_id (if tr then TSTORE else SSTORE) [pop;vop] []]` by
    (qpat_assum `emit_void _ [pop;vop] _ = _`
       (mp_then Any mp_tac emitted_insts_emit_void) >> simp[]) >>
  `run_inst_seq (emitted_insts s6 s7) t6 =
     Abort ExHalt_abort (halt_state (set_returndata [] t6))` by
    (Cases_on `tr` >> simp[run_inst_seq_def, step_inst_base_opcode_eqs,
       mk_inst_def, eval_operands_def]) >>
  `!k. inst_seq_ptr D 0 ctx func PG G6 tn6 (emitted_insts s6 s7)
     (t6 with vs_inst_idx := k) G6 tn6` by
    (gen_tac >> Cases_on `tr` >>
     simp[inst_seq_ptr_def, step_inst_base_opcode_eqs, mk_inst_def,
       ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, eval_operands_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  suspend "compose"
QED

Resume append_storage_word_static_origin_path[memory]:
  qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `tr` >>
  simp[compile_dynarray_append_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[EVERY_APPEND, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_dload_in_section_def] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Resume append_storage_word_static_origin_path[compose]:
  `inst_extends sa s3 /\ inst_extends sa s6 /\
   inst_extends sa s7 /\ inst_extends s7 sb` by
    metis_tac[inst_extends_trans] >>
  drule_all append_storage_word_suffix_code >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa s7 ++ emitted_insts s7 sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts sa s7 = emitted_insts sa s6 ++ emitted_insts s6 s7` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts sa s6 = emitted_insts sa s3 ++ emitted_insts s3 s6` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s3) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s6) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s7)` by
    (qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     asm_rewrite_tac[EVERY_APPEND] >> rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa s6)
       (s with vs_inst_idx := k) G6 tn6` by
    (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa s6) s = OK t6` by
    (irule run_inst_seq_compose_ok >> metis_tac[]) >>
  `!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa s7)
       (s with vs_inst_idx := k) G6 tn6` by
    (irule emitted_inst_seq_ptr_uniform_compose >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sa s7) s =
       Abort ExHalt_abort (halt_state (set_returndata [] t6))` by
    metis_tac[run_inst_seq_emit_extend] >>
  `!k. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := k) G6 tn6` by
    (irule emitted_inst_seq_ptr_uniform_abort_extend >> metis_tac[]) >>
  qexistsl_tac [`G6`, `tn6`] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]
QED

Finalise append_storage_word_static_origin_path
