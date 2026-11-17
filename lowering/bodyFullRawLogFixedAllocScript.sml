(* One fixed RawLog scratch allocation, uniformly over storage horizons. *)
Theory bodyFullRawLogFixedAlloc
Ancestors
  bodyFullRawLogFixedBoundary exprSimAlloc bodySimFull bodyPtrDefs
  bodyPtrIfExpAllocFrame
  exprLowering exprLoweringProps compileEnv context loweringStateRelDefs
  loweringPosts venomState venomInst venomExecSemantics ptrDiscipline
  fragGasOriginPtr fragGasOriginPtrExec fragGasSeqPtr finite_map words list rich_list
Libs
  pairLib

Theorem raw_log_fixed_alloc_full:
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  compile_call compile_expr cenv ret_ty ty RawLog [topics;data] dflt call_sa = (vv,call_sb) /\
  compile_alloc_buffer 32 sm = (buf,sd) /\ fn_has_code sm sd func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\ return_buf_frame d cenv sm s /\
    alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
  ?u Gu tnu p w. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
    stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gu tnu u /\
    return_buf_frame d cenv sd u /\ alloca_history func u /\
    s.vs_alloca_next <= u.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    buf.buf_operand = Var p /\ not_fresh_at sd p /\
    eval_operand buf.buf_operand u = SOME w /\ ptr_covers Gu tnu p u 32 /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    tnu.t_mem = tn.t_mem UNION new_site_bytes s u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b n. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint (w2n w) 32 b n) /\
    (!name b n. local_region cenv ee.scopes u name b n ==> regions_disjoint (w2n w) 32 b n) /\
    ghost_kept_at lo cenv ee sm G tn s Gu tnu
Proof
  strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- suspend "allocate" >>
  gvs[]
QED

Resume raw_log_fixed_alloc_full[allocate]:
  pop_assum strip_assume_tac >>
  rename1 `valid_horizon cx st0 H0 ee.storage_trace` >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by metis_tac[] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum (drule_at Any) >> simp[]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  suspend "endpoint"
QED

Resume raw_log_fixed_alloc_full[endpoint]:
  `sd.cs_current_bb = sm.cs_current_bb /\
   LENGTH sd.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
   emitted_insts sm sd = [mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]] /\
   sd.cs_current_insts = sm.cs_current_insts ++ [mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]] /\
   p = STRING #"%" (toString sm.cs_next_var)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND, not_fresh_at_def]) >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [p]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK t` >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sd.cs_current_insts`,
    `step_prov PG G inst t`, `step_taint inst s t tn`, `p`, `w`] >>
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    return_buf_frame d cenv sm s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` by metis_tac[] >>
  conj_tac >- suspend "path" >>
  suspend "post"
QED

Resume raw_log_fixed_alloc_full[path]:
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule_all fragExecTheory.fn_has_code_same_block >> simp[]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`, ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def,
       taint_ok_def, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def, step_inst_non_invoke] >>
     conj_tac >- gvs[ghost_inv_at_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds,
       combinTheory.K_THM, opcode_case_def] >>
     simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
     rpt strip_tac >>
     gvs[step_inst_base_opcode_eqs, mk_inst_def,
       exec_alloca_def, AllCaseEqs(), update_var_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def,
      codegenRelTheory.source_memory_write_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def] >>
  drule_all straight_line_origin_ptr_edge >>
  simp[Abbr `inst`, mk_inst_def] >> strip_tac >>
  `~t.vs_halted` by
    metis_tac[venomInstPropsTheory.step_preserves_halted, step_inst_non_invoke] >>
  qpat_x_assum `!explicit PG. gas_origin_ptr_edge _ _ _ _`
    (qspecl_then [`explicit`, `PG`] assume_tac) >>
  drule_at Any (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Resume raw_log_fixed_alloc_full[post]:
  `stmt_state_rel H ctx func cenv cx ee t` by
    (drule_all literal_alloc_buffer_run >> strip_tac >>
     gvs[]) >>
  `t.vs_current_bb = s.vs_current_bb /\
   t.vs_halted = s.vs_halted /\
   s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Abbr `inst`, step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
       AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  simp[] >>
  conj_tac >- simp[stmt_state_rel_inst_idx] >>
  conj_tac >- suspend "ghost" >>
  conj_tac
  >- (`sm.cs_next_var <= sd.cs_next_var` by
        (qspec_then `32` (qspec_then `sm` mp_tac) ci_mono_compile_alloc_buffer >>
         gvs[ci_mono_def]) >>
      Cases_on `d` >> gvs[return_buf_frame_def] >>
      PairCases_on `x` >> gvs[return_buf_frame_def] >>
      conj_tac
      >- (simp[lookup_var_def] >>
          metis_tac[lookup_var_def]) >>
      gvs[not_fresh_at_def] >> decide_tac) >>
  conj_tac >- suspend "history" >>
  suspend "coverage_and_frame"
QED

Resume raw_log_fixed_alloc_full[history]:
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule_all fragExecTheory.fn_has_code_same_block >> simp[]) >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  drule_all allocaHistoryTheory.alloca_history_base_step >>
  simp[Abbr `inst`, mk_inst_def, is_terminator_def]
QED

Resume raw_log_fixed_alloc_full[coverage_and_frame]:
  conj_tac
  >- (`ptr_covers (step_prov PG G inst t) (step_taint inst s t tn) p t 32` by
        (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
           (mp_then Any mp_tac allocationPtrTheory.alloca_step_ptr_covers) >>
         simp[Abbr `inst`] >>
         disch_then irule >> gvs[]) >>
      gvs[ptr_covers_def, lookup_var_def]) >>
  conj_tac
  >- simp[Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
       written_taint_def, new_site_bytes_def, mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (simp[local_region_def, lookup_var_def] >> metis_tac[local_region_def, lookup_var_def]) >>
  suspend "kept"
QED

Resume raw_log_fixed_alloc_full[ghost]:
  suspend "ghost_fields"
QED

Resume raw_log_fixed_alloc_full[kept]:
  `!x. not_fresh_at sm x ==> x <> p` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `lo <= s.vs_alloca_next` by gvs[ghost_inv_at_def] >>
  `!i. i < s.vs_alloca_next ==> i NOTIN new_site_bytes s t` by
    (fs[Abbr `inst`] >> Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`
     >- (qpat_assum `step_inst_base _ _ = OK t`
           (mp_then Any mp_tac allocationPtrTheory.fresh_alloca_new_site_bytes) >> simp[]) >>
     rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME site` >> PairCases_on `site` >>
     qpat_x_assum `step_inst_base _ _ = OK t` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >> strip_tac >>
     gvs[new_site_bytes_def, update_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
  simp[ghost_kept_at_def] >> conj_tac
  >- (gen_tac >> strip_tac >> `x <> p` by metis_tac[] >>
      Cases_on `out_prov PG G inst t` >>
      gvs[Abbr `inst`, step_prov_def, set_prov_def,
        step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def, FLOOKUP_UPDATE,
        FLOOKUP_DRESTRICT]) >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  `!name b n. local_region cenv ee.scopes s name b n ==>
     local_region cenv ee.scopes t name b n` by
    (simp[local_region_def] >> rpt strip_tac >>
     goal_assum (drule_at Any) >>
     gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
       written_taint_def, mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `off + sz <= s.vs_alloca_next` by
        (gvs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
      `i < s.vs_alloca_next` by decide_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `b + sz <= s.vs_alloca_next` by
        (`local_ptrs_rel func cenv ee.scopes s` by
           (qpat_x_assum `!H'. valid_horizon _ _ _ _ ==> _`
              (qspec_then `H0` mp_tac) >>
            simp[stmt_state_rel_def, state_rel_def] >> strip_tac >> simp[]) >>
         qpat_x_assum `local_ptrs_rel _ _ _ s` mp_tac >>
         qpat_x_assum `local_region _ _ s _ _ _` mp_tac >>
         simp[local_region_def, local_ptrs_rel_def] >>
         rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]) >>
      `i < s.vs_alloca_next` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> `i < s.vs_alloca_next` by decide_tac >> metis_tac[]
QED

Resume raw_log_fixed_alloc_full[ghost_fields]:
  `!x. not_fresh_at sm x ==> x <> p` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `!x. not_fresh_at sm x ==>
     FLOOKUP (step_prov PG G inst t) x = FLOOKUP G x /\
     op_taint (step_taint inst s t tn) (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >> `x <> p` by metis_tac[] >>
     Cases_on `out_prov PG G inst t` >>
     gvs[Abbr `inst`, step_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ s` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  simp[ghost_inv_at_def] >> conj_tac >- suspend "ghost_locals" >>
  suspend "ghost_rest"
QED

Resume raw_log_fixed_alloc_full[ghost_locals]:
  rpt gen_tac >> strip_tac >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var q) sz)` >>
  `not_fresh_at sm q` by metis_tac[local_ptrs_reserved_def] >>
  `q <> p` by metis_tac[] >>
  qpat_x_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _`
    (qspecl_then [`name`, `entry`, `q`, `sz`] mp_tac) >>
  simp[] >> strip_tac >> conj_tac
  >- (`ptr_covers (step_prov PG G inst t) (step_taint inst s t tn) q t sz` by
        (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
          (mp_then Any mp_tac allocationPtrTheory.alloca_step_old_ptr_covers) >>
         simp[Abbr `inst`] >> disch_then irule >> gvs[]) >>
      gvs[ptr_covers_def, lookup_var_def]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var q s = SOME w'` by gvs[lookup_var_def] >>
  `local_ptrs_rel func cenv ee.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ s` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum (qspecl_then [`name`, `entry`, `q`, `sz`] mp_tac) >>
  simp[] >> strip_tac >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  fs[Abbr `inst`] >>
  qpat_assum `step_inst_base _ s = OK t`
    (mp_then Any mp_tac alloca_step_robust_below_frontier) >>
  simp[] >> disch_then irule >>
  simp[] >> metis_tac[]
QED

Resume raw_log_fixed_alloc_full[ghost_rest]:
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rb) slot_size)` >>
      `not_fresh_at sm rb` by metis_tac[] >>
      `rb <> p` by metis_tac[] >>
      simp[lookup_var_def] >>
      `ptr_covers (step_prov PG G inst t) (step_taint inst s t tn) rb t x1` by
        (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
          (mp_then Any mp_tac allocationPtrTheory.alloca_step_old_ptr_covers) >>
         simp[Abbr `inst`] >> disch_then irule >> gvs[]) >>
      gvs[ptr_covers_def, lookup_var_def]) >>
  conj_tac >- suspend "ghost_storage" >>
  suspend "ghost_low"
QED

Resume raw_log_fixed_alloc_full[ghost_storage]:
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Abbr `inst`, step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
       AllCaseEqs(), update_var_def] >> rpt strip_tac >> gvs[]) >>
  gvs[stor_taint_ok_at_def, Abbr `inst`, step_taint_def,
    store_taint_def, imm_taint_def, mk_inst_def, adopt_reset_def]
QED

Resume raw_log_fixed_alloc_full[ghost_low]:
  conj_tac
  >- (`!i. i < s.vs_alloca_next ==> i NOTIN new_site_bytes s t` by
        (fs[Abbr `inst`] >> Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`
         >- (qpat_assum `step_inst_base _ _ = OK t`
               (mp_then Any mp_tac allocationPtrTheory.fresh_alloca_new_site_bytes) >> simp[]) >>
         rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME site` >> PairCases_on `site` >>
         qpat_x_assum `step_inst_base _ _ = OK t` mp_tac >>
         simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >> strip_tac >>
         gvs[new_site_bytes_def, update_var_def, FLOOKUP_DEF] >> metis_tac[]) >>
      simp[Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
        written_taint_def, mk_inst_def,
        codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
      rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> metis_tac[]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Abbr `inst`, step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
    AllCaseEqs(), update_var_def] >> rpt strip_tac >>
  gvs[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Finalise raw_log_fixed_alloc_full

