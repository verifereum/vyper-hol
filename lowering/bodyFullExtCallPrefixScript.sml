(* Successful optional external-code check: exact checked scalar steps. *)
Theory bodyFullExtCallPrefix
Ancestors
  bodyFullExtCallBoundary bodyFullExtCallPrecheckExit
  exprSimSliceExtcode fragGasSeqPtr fragGasOriginPtr ptrDiscipline
  ptrSafeRun memSafeRun venomInst venomState venomExecSemantics
  emitHelper emitHelperProps exprLoweringProps compileEnv fragExec exprSafeOperand
  instMemFrontier unitTransformDefs codegenRel contextCodegenRel loweringStateRelDefs
  pred_set finite_map exprSimAccounts bodyFullGhostFrame exprSimHashBoundary
  exprSimExtCallCase

Theorem extcall_extcodesize_exact_edge:
  emit_op EXTCODESIZE [addr] a = (op,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  ~ctx_has_dalloca ctx ==>
  ?out. op = Var out /\ ~not_fresh_at a out /\
    !D lo. allocas_from lo s ==> gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (update_var out
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
        with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst a.cs_next_id EXTCODESIZE [addr] [out])
         (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s),
       step_taint (mk_inst a.cs_next_id EXTCODESIZE [addr] [out]) s
         (update_var out (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s) tn)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
    SOME (mk_inst a.cs_next_id EXTCODESIZE [addr]
      [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[not_fresh_at_def] >> rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `v = update_var (STRING #"%" (toString a.cs_next_var))
    (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s` >>
  `step_inst_base inst s = OK v` by
    simp[Abbr `inst`, Abbr `v`, slice_extcodesize_step] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (`inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke, Abbr `v`, update_var_def] >>
     simp[Abbr `inst`, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `inst`, mk_inst_def, Abbr `v`]
QED

Theorem extcall_assert_nonzero_edge:
  emit_void ASSERT [op] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand op s = SOME w /\ w <> 0w /\ op_taint tn op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (s with vs_inst_idx := SUC s.vs_inst_idx),G,tn)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id ASSERT [op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  `step_inst_base inst s = OK s` by simp[Abbr `inst`, step_ASSERT_ok] >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (`inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke] >>
     simp[Abbr `inst`, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `inst`, mk_inst_def, step_prov_def, set_prov_def,
    step_taint_def, set_var_taint_def, mem_taint_def, step_writes_def,
    imm_taint_def, new_site_bytes_def, EXTENSION, FLOOKUP_DEF, SF CONJ_ss,
    source_memory_write_ranges_def, written_taint_def, store_taint_def,
    adopt_reset_def, range_bytes_def, DRESTRICT_UNIV] >>
  `<|t_mem := tn.t_mem; t_var := tn.t_var; t_stor := tn.t_stor;
     t_trans := tn.t_trans; t_imm := tn.t_imm|> = tn` by
    simp[taint_component_equality] >> simp[]
QED

Theorem extcall_code_length_nonzero:
  accounts_runtime_well_typed accounts /\ (lookup_account target accounts).code <> [] ==>
  (n2w (LENGTH (lookup_account target accounts).code) : bytes32) <> 0w
Proof
  strip_tac >>
  `LENGTH (lookup_account target accounts).code <= 24576` by
    fs[vyperRuntimeAccountsTheory.accounts_runtime_well_typed_def,
       vyperRuntimeAccountsTheory.account_runtime_well_typed_def] >>
  `LENGTH (lookup_account target accounts).code < dimword (:256)` by
    (simp[wordsTheory.dimword_def] >> decide_tac) >>
  simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  gvs[listTheory.LENGTH_NIL]
QED

Theorem extcall_check_success_path:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) <> 0w /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?out. ~not_fresh_at a out /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (update_var out
        (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
        with vs_inst_idx := s.vs_inst_idx + 2),
       G \\ out, tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
  simp[exprLoweringTheory.compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rename1 `emit_op EXTCODESIZE [addr] a = (sz,sm)` >>
  `cs_extends a sm /\ cs_extends sm b` by
    (conj_tac >- metis_tac[emit_op_extends_next_var] >>
     irule cs_extends_emit_inst >>
     qexistsl_tac [`ASSERT`, `[sz]`, `[]`] >>
     fs[emit_void_def, emit_inst_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all extcall_extcodesize_exact_edge >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >> gvs[] >>
  qexists_tac `out` >> simp[] >> gen_tac >> first_x_assum (qspecl_then [`D`,`lo`] mp_tac) >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
    set_var_taint_def, out_taint_def, mem_taint_def, step_writes_def, imm_taint_def,
    new_site_bytes_def, written_taint_def, source_memory_write_ranges_def,
    store_taint_def, adopt_reset_def, range_bytes_def, mk_inst_def,
    update_var_def, EXTENSION, FLOOKUP_DEF, SF CONJ_ss] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_edge _ _ _ (OK v,_,_)` >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (v,G \\ out,tn with t_var := tn.t_var |+ (out,{})) []
    (OK (v with vs_inst_idx := SUC v.vs_inst_idx),G \\ out,
      tn with t_var := tn.t_var |+ (out,{}))` by
    (irule extcall_assert_nonzero_edge >>
     fs[Abbr `v`, allocas_from_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`sm`,`b`,`Var out`,
       `n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)`] >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def,
        eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]) >>
  `<|t_mem := tn.t_mem; t_var := tn.t_var |+ (out,{});
      t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|> =
    tn with t_var := tn.t_var |+ (out,{})` by simp[taint_component_equality] >>
  fs[] >> gvs[GSYM fmap_domsub] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (v with vs_inst_idx := SUC v.vs_inst_idx),G \\ out,
      tn with t_var := tn.t_var |+ (out,{}))` by
    (`gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (v with vs_inst_idx := SUC v.vs_inst_idx,G \\ out,
        tn with t_var := tn.t_var |+ (out,{})) []
       (OK (v with vs_inst_idx := SUC v.vs_inst_idx),G \\ out,
        tn with t_var := tn.t_var |+ (out,{}))` by
       (irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `v`]) >>
     qpat_x_assum `fn_has_code a b func` kall_tac >>
     qpat_x_assum `Abbrev _` kall_tac >>
     metis_tac[gas_origin_ptr_path_rules, listTheory.APPEND]) >>
  gvs[Abbr `v`, update_var_def, arithmeticTheory.ADD1,
      arithmeticTheory.ADD_ASSOC]
QED

Theorem extcall_fresh_scalar_ghost_frame:
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\ ~not_fresh_at sa out ==>
  ghost_inv_at D lo d cenv cx es (G \\ out)
    (tn with t_var := tn.t_var |+ (out,{}))
    (update_var out w s with vs_inst_idx := idx)
Proof
  strip_tac >> irule ghost_inv_at_exterior_frame >>
  qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >>
  simp[update_var_def] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
       fmap_domsub, FLOOKUP_DRESTRICT]
QED

Theorem extcall_request_fresh_scalar:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\ ~not_fresh_at sp out /\
  sp.cs_next_var <= sb.cs_next_var /\ sp.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = sp.cs_current_bb ==>
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee
    (update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `local_ptrs_reserved cenv sp /\ sa.cs_next_var <= sp.cs_next_var /\
   EVERY (safe_operand sp) [addr;value;gas;buf;off;len;default_op]` by
    fs[extcall_request_ready_def] >>
  `!x. not_fresh_at sp x ==> lookup_var x (update_var out w s) = lookup_var x s` by
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!op. safe_operand sp op ==> eval_operand op (update_var out w s) = eval_operand op s` by
    (Cases >> simp[safe_operand_def, eval_operand_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee (update_var out w s)` by
    (rpt strip_tac >> irule hash_readonly_state_rel >>
     qexistsl_tac [`s`,`sp`] >> simp[update_var_def] >>
     fs[extcall_request_ready_def]) >>
  `!scopes n b sz. local_region cenv scopes (update_var out w s) n b sz <=>
     local_region cenv scopes s n b sz` by
    (simp[local_region_def] >> rpt gen_tac >>
     `!p k. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) k) ==> p <> out` by
       (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  fs[extcall_request_ready_def] >>
  simp[extcall_request_ready_def, stmt_state_rel_inst_idx] >>
  conj_tac >-
    (fs[loweringPostsTheory.wb_frame_def] >>
     simp[loweringPostsTheory.wb_frame_def, update_var_def] >>
     conj_tac >- (rpt strip_tac >>
       `not_fresh_at sp x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
       `x <> out` by metis_tac[] >> fs[lookup_var_def, FLOOKUP_UPDATE]) >>
     conj_tac >- metis_tac[] >>
     irule exprSimPropsTheory.locals_kept_mem_tail >>
     qexists_tac `s` >> simp[]) >>
  `local_ptrs_reserved cenv sb /\
   EVERY (safe_operand sb) [addr;value;gas;buf;off;len;default_op]` by
    (simp[] >> metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
                         exprSafeOperandTheory.safe_operand_mono]) >>
  fs[read_memory_def] >>
  simp[] >>
  conj_tac >-
    (conj_tac >- (qexistsl_tac [`live`,`buf_size`] >> simp[]) >>
     `!n b sz. local_region cenv ee.scopes
        (update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts) n b sz <=>
        local_region cenv ee.scopes (update_var out w s) n b sz` by
       simp[NoAsms, local_region_def, lookup_var_def] >> simp[] >> metis_tac[]) >>
  fs[extcall_default_ready_def, loweringPostsTheory.expr_val_rel_def] >>
  simp[extcall_default_ready_def, loweringPostsTheory.expr_val_rel_def, eval_operand_def,
       lookup_var_def, update_var_def, read_memory_def] >>
  metis_tac[]
QED

Theorem extcall_fresh_scalar_observations:
  ~not_fresh_at sp out /\ sa.cs_next_var <= sp.cs_next_var ==>
  (!x. not_fresh_at sp x ==>
    lookup_var x (update_var out w s with vs_inst_idx := idx) = lookup_var x s /\
    FLOOKUP (G \\ out) x = FLOOKUP G x /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var x) = op_taint tn (Var x)) /\
  (!op. safe_operand sp op ==>
    eval_operand op (update_var out w s with vs_inst_idx := idx) = eval_operand op s /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) op = op_taint tn op /\
    (!x. op = Var x ==> FLOOKUP (G \\ out) x = FLOOKUP G x)) /\
  (ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept_at lo cenv es sa G0 tn0 s0 (G \\ out)
      (tn with t_var := tn.t_var |+ (out,{}))) /\
  (!cx ty v op. safe_operand sp op /\ ptr_mem_ok cx ty v op G tn s ==>
    ptr_mem_ok cx ty v op (G \\ out) (tn with t_var := tn.t_var |+ (out,{}))
      (update_var out w s with vs_inst_idx := idx))
Proof
  strip_tac >>
  `!x. not_fresh_at sp x ==> x <> out` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- (rpt strip_tac >>
    simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
         fmap_domsub, FLOOKUP_DRESTRICT]) >>
  conj_tac >- (Cases >> simp[safe_operand_def, eval_operand_def, update_var_def,
    lookup_var_def, op_taint_def, FLOOKUP_UPDATE, fmap_domsub, FLOOKUP_DRESTRICT] >>
    metis_tac[]) >>
  conj_tac >- (simp[bodyPtrDefsTheory.ghost_kept_at_def] >> rpt strip_tac >>
    fs[op_taint_def, FLOOKUP_UPDATE, fmap_domsub, FLOOKUP_DRESTRICT] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  fs[safe_operand_def, bodyPtrDefsTheory.ptr_mem_ok_def,
     eval_operand_def, update_var_def, lookup_var_def, fmap_domsub, FLOOKUP_DRESTRICT] >>
  `s' <> out` by metis_tac[] >> fs[FLOOKUP_UPDATE]
QED

Theorem extcall_check_alloca_history:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  alloca_history func s /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  alloca_history func (update_var out w s with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  strip_tac >>
  `b.cs_current_bb = a.cs_current_bb /\
   LENGTH b.cs_current_insts = LENGTH a.cs_current_insts + 2 /\
   emitted_insts a b =
     [mk_inst a.cs_next_id EXTCODESIZE [addr]
        [STRING #"%" (toString a.cs_next_var)];
      mk_inst (a.cs_next_id + 1) ASSERT
        [Var (STRING #"%" (toString a.cs_next_var))] []]` by
    (qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_extcodesize_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, exprLoweringPropsTheory.DROP_PREFIX,
       GSYM listTheory.APPEND_ASSOC, mk_inst_def, arithmeticTheory.ADD1]) >>
  `b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b` by
    gvs[exprLoweringTheory.compile_extcodesize_check_def, emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
      fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  fs[allocaHistoryTheory.alloca_history_def, update_var_def] >> rpt strip_tac >>
  Cases_on `k < LENGTH a.cs_current_insts` >- metis_tac[] >>
  `k = LENGTH a.cs_current_insts \/ k = LENGTH a.cs_current_insts + 1` by decide_tac >>
  gvs[] >>
  qpat_x_assum `!i. i < 2 ==> _`
    (fn th => mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >>
  simp[] >> rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem extcall_check_guarded_success:
  compile_extcodesize_check addr a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ w2w aw = target /\ op_taint tn addr = {} /\
  accounts_runtime_well_typed ee.accounts /\
  (lookup_account target ee.accounts).code <> [] /\ ~ctx_has_dalloca ctx /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ allocas_from lo s) ==>
  ?out. ~not_fresh_at a out /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (update_var out
          (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s
          with vs_inst_idx := s.vs_inst_idx + 2),
         G \\ out, tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- (pop_assum strip_assume_tac >>
      `stmt_state_rel H ctx func cenv cx ee s /\ allocas_from lo s` by metis_tac[] >>
      `accounts_agree H cx ee.accounts s.vs_accounts` by
        fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
      drule accountsRelPropsTheory.accounts_agree_lookup >>
      disch_then (qspec_then `target` assume_tac) >>
      ` (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) <> 0w` by
        metis_tac[extcall_code_length_nonzero] >>
      drule_all extcall_check_success_path >>
      disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
      qexists_tac `out` >> simp[]) >>
  qexists_tac `STRING #"%" (toString a.cs_next_var)` >>
  simp[not_fresh_at_def] >> metis_tac[]
QED

Theorem extcall_precheck_success_boundary:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
   else comp_return ()) sp = ((),sb) /\ fn_has_code sp sb func /\
  ~ctx_has_dalloca ctx /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee t /\
  ext_call_precheck_ok skip ret_type target ee.accounts /\
  op_taint tn addr = {} /\ alloca_history func t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t1 G1 tn1.
    extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sb stat
      addr value gas buf off len cap target value_opt calldata has_default
      default_op default_ty default_opt ee t1 /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK t1,G1,tn1)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t1) /\
    t1.vs_memory = t.vs_memory /\ t1.vs_allocas = t.vs_allocas /\
    t1.vs_alloca_next = t.vs_alloca_next /\ tn1.t_mem = tn.t_mem /\
    (!x. not_fresh_at sp x ==> lookup_var x t1 = lookup_var x t /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!op. safe_operand sp op ==> eval_operand op t1 = eval_operand op t /\
      op_taint tn1 op = op_taint tn op /\
      (!x. op = Var x ==> FLOOKUP G1 x = FLOOKUP G x)) /\
    (ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
    (!cx' ty v op. safe_operand sp op /\ ptr_mem_ok cx' ty v op G tn t ==>
      ptr_mem_ok cx' ty v op G1 tn1 t1) /\ alloca_history func t1
Proof
  strip_tac >> Cases_on `ret_type = NoneT /\ ~skip`
  >- (fs[] >>
      `~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
       t.vs_inst_idx = LENGTH sp.cs_current_insts /\
       sa.cs_next_var <= sp.cs_next_var /\ local_ptrs_reserved cenv sp /\
       accounts_runtime_well_typed ee.accounts /\
       ?aw. eval_operand addr t = SOME aw /\ w2w aw = target` by
        fs[extcall_request_ready_def] >>
      `sb.cs_current_bb = sp.cs_current_bb /\
       sp.cs_next_var <= sb.cs_next_var /\ sp.cs_next_id <= sb.cs_next_id /\
       LENGTH sb.cs_current_insts = t.vs_inst_idx + 2` by
        gvs[exprLoweringTheory.compile_extcodesize_check_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
          fresh_id_def, emit_def] >>
      ` (lookup_account target ee.accounts).code <> []` by
        fs[vyperInterpreterTheory.ext_call_precheck_ok_def, vyperInterpreterTheory.ext_call_has_code_def, listTheory.NULL_EQ] >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee t /\ allocas_from lo t` by
        (fs[extcall_request_ready_def, bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
      drule_all extcall_check_guarded_success >>
      disch_then (qspecl_then [`explicit`,`PG`,`G`,`DF`] strip_assume_tac) >>
      qexistsl_tac [`update_var out
        (n2w (LENGTH (lookup_account (w2w aw) t.vs_accounts).code)) t
        with vs_inst_idx := LENGTH sb.cs_current_insts`,
        `G \\ out`, `tn with t_var := tn.t_var |+ (out,{})`] >>
      conj_tac >- metis_tac[extcall_request_fresh_scalar] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (rpt strip_tac >> irule extcall_fresh_scalar_ghost_frame >>
        reverse conj_tac >- metis_tac[] >> qexists_tac `sp` >>
        simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
      drule_all extcall_check_alloca_history >> strip_tac >>
      drule_all extcall_fresh_scalar_observations >> strip_tac >>
      gvs[update_var_def] >> metis_tac[]) >>
  gvs[comp_return_def] >> qexistsl_tac [`t`,`G`,`tn`] >> simp[] >>
  rpt strip_tac >> irule (cj 1 gas_origin_ptr_path_rules) >>
  fs[extcall_request_ready_def]
QED
