(* Seam 2 joint induction, a family leaf of the call step: pops. *)
Theory bodyIntCallFamCallPop
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore exprSimCopy
  exprSimProps intCallFrame venomState bodyMemPopToplevelSim
  bodyMemPopToplevelPath exprSimPopStorage exprSimTopLevelProps
  exprSimSource exprSimHypsDefs exprSimDefs exprLoweringProps
  exprLowering compileEnv context vyperInterpreter vyperStorageBackend
  vyperStorageLayoutSafety vyperStorage vyperState venomExecSemantics
  venomInst accountsRelProps gasOutcome gasSummary fragGasMode fragGasPathMem
  list words finite_map fragExec bodySimStmtCases exprOpenCases
  supportedExprForms supportedDecls appendStorageSourcePtr fragGasSeq
  fragGasSeqAbort rich_list loweringPosts exprOperandVar supportedExprs

(* A storage operation that keeps memory, allocations, and old variables
   transports the joint continuation once its source and state relations
   have been established. *)
Theorem intcall_expr_cont_memory_frame:
  intcall_frame_ok fp /\
  intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env ee /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  sa.cs_next_var <= sb.cs_next_var /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `(!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s)` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     gvs[eval_operand_def] >>
     `not_fresh_at sa x` by metis_tac[intcall_joint_res_def, intcall_expr_res_def] >> simp[]) >>
  `intcall_expr_res fp ce env ee sb u` by
    (irule intcall_joint_res_frame >>
     simp[] >>
     conj_tac >- (gvs[intcall_joint_res_def, intcall_expr_res_def, allocas_above_def] >> metis_tac[]) >>
     qexistsl [`es`, `s`, `sa`] >> simp[] >>
     rpt strip_tac >>
     drule_all copy_buffer_local_region_frame >> simp[] >> metis_tac[]) >>
  simp[intcall_expr_cont_def] >>
  irule locals_kept_mem >> simp[]
QED

Theorem intcall_pop_storage_path:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand r t = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz) /\
    t = ((if tr then tstore slot (tload slot s - 1w) s
          else sstore slot (sload slot s - 1w) s)
          with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>)
Proof
  strip_tac >>
  drule dynarray_pop_storage_opcodes >> strip_tac >>
  drule dynarray_pop_storage_shape >> strip_tac >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[ALL_DISTINCT] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all tuple_run_inst_seq_gas_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   u.vs_memory = s.vs_memory /\ u.vs_halted = s.vs_halted /\
   u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `u = _ with vs_vars := _` mp_tac >>
     Cases_on `tr` >> simp[tstore_def, sstore_def, LET_THM] >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `gas_path _ _ _ _ _` mp_tac >>
      Cases_on `tr` >>
      simp[gas_marked_path_def, emitted_insts_def, DROP_APPEND, mk_inst_def]) >>
  simp[eval_operand_def, lookup_var_def] >>
  reverse conj_tac
  >- (qpat_x_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[]) >>
  fs[EVERY_MEM, lookup_var_def] >> metis_tac[]
QED

Theorem intcall_pop_toplevel_producer:
  intcall_expr_producer fp (Pop ann (TopLevelNameTarget id))
Proof
  rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  PairCases_on `id` >> gvs[] >>
  `expr_sim_inv ce fp.jc_cx env es /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  drule intcall_supported_pop_form >> strip_tac >> gvs[] >>
  `?ts d. get_module_code fp.jc_cx id0 = SOME ts /\
     find_var_decl_by_name id1 ts = SOME d` by
    (Cases_on `supported_variable_decl fp.jc_tops (id0,id1)` >>
     fs[supported_storage_dynamic_array_def] >>
     rename1 `supported_variable_decl _ _ = SOME info` >>
     PairCases_on `info` >>
     rename1 `supported_variable_decl _ _ = SOME (vis,mut,declared,loc)` >>
     Cases_on `declared` >> fs[] >>
     rename1 `ArrayT elem bound` >> Cases_on `bound` >> fs[] >>
     Cases_on `loc` >> Cases_on `vis` >> Cases_on `mut` >> fs[] >>
     drule supported_variable_decl_runtime_lookup >> simp[] >>
     strip_tac >> gvs[bodySimTheory.body_inv_def] >> metis_tac[]) >>
  `well_typed_expr env (Pop ann (TopLevelNameTarget (id0,id1))) /\
   env_consistent env fp.jc_cx es` by
    (fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  suspend "storage"
QED
Resume intcall_pop_toplevel_producer[storage]:
  drule_all pop_storage_target_facts >> strip_tac >> gvs[] >>
  `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx /\
   ~fp.jc_cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  `elem_size_in_location ce (if tr then LocTransient else LocStorage) ann =
    type_slot_size tv` by (irule pop_storage_element_size >> metis_tac[]) >>
  drule_all compile_expr_pop_storage >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Lit (n2w slot)) 1 (type_slot_size tv)
    ce.ce_is_ctor ce.ce_imm_alloca (if tr then LocTransient else LocStorage) sa` >>
  gvs[] >>
  `declared_storage_region fp.jc_cx id0 id1 [] =
    SOME (tr,n2w slot,ArrayTV tv (Dynamic n))` by
    simp[declared_storage_region_def] >>
  drule_all pop_declared_header_load >> strip_tac >>
  drule_all eval_pop_storage >> strip_tac >>
  Cases_on `lookup_storage (n2w slot) (get_storage fp.jc_cx es tr) = 0w`
  >- (`(if tr then tload (n2w slot) s else sload (n2w slot) s) = 0w` by simp[] >>
      drule_all dynarray_pop_storage_empty_path_mem >>
      disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
      drule gas_marked_path_from_mem >>
      disch_then (qspec_then `F` assume_tac) >>
      simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR (Error (RuntimeError "pop empty storage array"))`,
                `es`, `Abort a t`] >>
      simp[gas_marked_exec_def, exit_result_def, expr_exit_def, LET_THM,
           get_storage_gas_obs]) >>
  suspend "positive"
QED
Resume intcall_pop_toplevel_producer[positive]:
  `(if tr then tload (n2w slot) s else sload (n2w slot) s) <> 0w` by simp[] >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all intcall_pop_storage_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  drule dynarray_pop_storage_shape >> strip_tac >> gvs[] >>
  `0 < w2n (lookup_storage (n2w slot) (get_storage fp.jc_cx es tr))` by
    (Cases_on `lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)` >> gvs[]) >>
  `lookup_storage (n2w slot) (get_storage fp.jc_cx es tr) - 1w =
   n2w (w2n (lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)) - 1)` by
    (Cases_on `lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)` >>
     gvs[GSYM n2w_sub]) >>
  `t = (if tr then tstore (n2w slot)
     (n2w (w2n (lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)) - 1)) s
   else sstore (n2w slot)
     (n2w (w2n (lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)) - 1)) s)
   with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `lookup_var x6 t = SOME (n2w slot + n2w
    (1 + (w2n (lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)) - 1) *
      type_slot_size tv))` by
    (fs[eval_operand_def] >> pure_asm_rewrite_tac [] >>
     pure_rewrite_tac[word_add_n2w, word_mul_n2w, arithmeticTheory.ADD_ASSOC] >>
     AP_TERM_TAC >> once_rewrite_tac[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `lookup_var x6 t = SOME elem` >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ post _` >>
  qabbrev_tac `ee = set_storage fp.jc_cx es tr
    (apply_writes (n2w slot)
      [(0,n2w (w2n (lookup_storage (n2w slot) (get_storage fp.jc_cx es tr)) - 1))]
      (get_storage fp.jc_cx es tr))` >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee t` by
    (simp[Abbr `ee`] >> irule pop_mem_updated_state_rel_cursor >> metis_tac[]) >>
  `eval_expr fp.jc_cx (Pop ann (TopLevelNameTarget (id0,id1))) es =
     (INL (PlaceR (StoragePlace tr elem tv)),ee)` by
    (simp[Abbr `elem`, Abbr `ee`] >>
     AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  `expr_sim_inv ce fp.jc_cx env ee` by
    (drule_all expr_body_pre_eval_result >> simp[]) >>
  suspend "post"
QED
Resume intcall_pop_toplevel_producer[post]:
  `intcall_expr_cont fp ce env es sa s (ee with gas_obs := []) r t` by
    (irule intcall_expr_cont_memory_frame >> simp[] >>
     simp[Abbr `ee`]) >>
  `storage_holds fp.jc_cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
     (ee with gas_obs := []) t` by
    (unabbrev_all_tac >>
     irule (SRULE [get_storage_gas_obs, set_storage_gas_obs]
       (Q.INST [`es` |-> `es with gas_obs := []`]
         (SPEC_ALL pop_mem_positive_holds_cursor))) >>
     simp[get_storage_gas_obs] >>
     conj_tac >- metis_tac[] >>
     qexistsl [`ce`, `fp.jc_ctx`, `env`, `fp.jc_func`, `s`] >>
     simp[] >> Cases_on `tr` >> gvs[]) >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx
     (Pop ann (TopLevelNameTarget (id0,id1))) es sa r s
     (ee with gas_obs := []) (PlaceR (StoragePlace tr elem tv))
     (LocatedValue ann (mk_ptr (Var x6) (if tr then LocTransient else LocStorage))) t` by
    (irule pop_storage_vv_post >> simp[]) >>
  simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl [`INL (PlaceR (StoragePlace tr elem tv))`, `ee`, `OK t`] >>
  simp[gas_marked_exec_def, LET_THM, get_storage_gas_obs,
       set_storage_gas_obs, Abbr `post`] >>
  fs[vv_post_def] >>
  simp[vv_operand_def, mk_ptr_def] >>
  Cases_on `tr` >> simp[] >>
  metis_tac[exprOperandVarTheory.compiler_dynarray_pop_var]
QED
Finalise intcall_pop_toplevel_producer

Theorem intcall_pop_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a tgt. e = Pop a tgt) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >> conj_tac
  >- (rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
      drule intcall_supported_pop_form >> strip_tac >> gvs[] >>
      mp_tac (Q.INST [`ann` |-> `a`] intcall_pop_toplevel_producer) >>
      simp[intcall_expr_producer_def] >>
      disch_then irule >> metis_tac[]) >>
  simp[intcall_map_producer_def, supported_pure_expr_def]
QED
