(* Constructor TopLevelName copies retain translated, rather than clean, taint. *)
Theory bodyFullToplevelCodeCtorExecution
Ancestors
  bodyFullToplevelCodeAllocation bodyFullUnwrapCodeCopy exprPtrCtorCodeLoad bufferAllocationExecution
  exprPtrUnwrapAllocEntry exprPtrUnwrapAllocation exprPtrUnwrapAllocationFrame
  exprPtrUnwrapAllocSeparation exprPtrUnwrapCodeCopyShape exprSimCopy
  exprLoweringProps context compileEnv ptrDiscipline loweringPosts exprSimMemUnwrap entrySinkExtraction bodyFullUnwrapRun
  venomState venomInst venomMemDefs fragExec fragGasSeqPtr fragGasOriginPtr list rich_list words finite_map

Theorem toplevel_code_ctor_execution_full:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_alloc_buffer nb sm = (buf,mid) /\
  compile_imm_copy_to_memory T imm src buf.buf_operand n 0 mid = ((),sb) /\
  fn_has_code sm mid func /\ fn_has_code mid sb func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword(:256) /\ 32*n <= nb /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sm x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    copy_old_operand sm region /\ op_taint tn region = {} /\ op_prov G region = NONE) /\
  w2n p + 32*n <= lo ==>
  ?root u a Gm tm Gf tnf z d.
    buf.buf_operand = Var root /\ buf.buf_size = nb /\
    u = update_var root (n2w (buffer_allocation_base s sm.cs_next_id))
      (buffer_allocation_fields s sm.cs_next_id nb) /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
    w2n d+nb < dimword(:256) /\ copy_runtime_frame mid a sb z /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)) /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    ptr_covers Gf tnf root z nb /\ lookup_var root a = SOME d /\
    (!x. x IN tnf.t_mem <=>
      if w2n d <= x /\ x < w2n d+32*n
      then w2n p + (x-w2n d) IN tm.t_mem else x IN tm.t_mem) /\
    tnf.t_stor = tm.t_stor /\ tnf.t_trans = tm.t_trans /\ tnf.t_imm = tm.t_imm /\
    (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x /\
      op_taint tnf (Var x) = op_taint tm (Var x)) /\
    allocas_from lo z
Proof
  strip_tac >> drule_all toplevel_code_allocation_full >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  `!x. src = Var x ==> x <> root` by
    metis_tac[unwrap_alloc_old_operand_distinct] >>
  drule_all unwrap_alloc_old_operand_ghost >>
  disch_then (qspecl_then [`tn`,`SUC s.vs_inst_idx`,`PG`,`G`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  qabbrev_tac `d:bytes32 = n2w (buffer_allocation_base s sm.cs_next_id)` >>
  `w2n d+nb < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> simp[Abbr `d`]) >>
  `lookup_var root a = SOME d` by
    (qpat_x_assum `eval_operand buf.buf_operand a = _` mp_tac >>
     simp[eval_operand_def, Abbr `d`]) >>
  `eval_operand src a = SOME p /\ op_taint tm src = {} /\ op_prov Gm src = NONE` by fs[] >>
  `allocas_from lo a /\ ~a.vs_halted /\ s.vs_alloca_next <= a.vs_alloca_next` by
    (simp[allocas_from_def, buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >>
     qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def] >>
     disch_then drule >> simp[]) >>
  `w2n d + 32*n <= a.vs_alloca_next` by
    (drule_all toplevel_code_allocation_frontier >>
     simp[Abbr `d`, update_var_def]) >>
  `lo <= w2n d` by
    (`buffer_allocation_base s sm.cs_next_id < dimword(:256)` by
       (drule_all unwrap_alloc_site_bound >> decide_tac) >>
     simp[Abbr `d`, w2n_n2w] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     fs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> fs[] >> metis_tac[]) >>
  suspend "copy"
QED

Resume toplevel_code_ctor_execution_full[copy]:
  `!region. imm = SOME region ==> eval_operand region a = SOME 0w /\
    copy_old_operand mid region /\ op_taint tm region = {} /\ op_prov Gm region = NONE` by
    (rpt gen_tac >> disch_tac >>
     `eval_operand region s = SOME 0w /\ copy_old_operand sm region /\
      op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
     `!x. region = Var x ==> not_fresh_at sm x` by fs[copy_old_operand_def] >>
     `!x. region = Var x ==> x <> root` by metis_tac[unwrap_alloc_old_operand_distinct] >>
     drule_all allocated_copy_operands_old >> strip_tac >>
     drule_all unwrap_alloc_old_operand_ghost >>
     disch_then (qspecl_then [`tn`,`SUC s.vs_inst_idx`,`PG`,`G`] mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >> simp[]) >>
  `compile_imm_copy_to_memory T imm src (Var root) n 0 mid = ((),sb)` by
    (qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `w2n p+0+32*n <= lo /\ 0+32*n <= nb /\
   w2n p+0+32*n <= a.vs_alloca_next /\ w2n d+0+32*n <= a.vs_alloca_next /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by gvs[] >>
  drule_all code_copy_ctor_range_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`ARB`] strip_assume_tac) >>
  `copy_old_operand mid (Var root) /\ eval_operand (Var root) a = SOME d` by
    simp[copy_old_operand_def, eval_operand_def] >>
  `w2n d+0+32*n < dimword(:256) /\ w2n p+0+32*n < dimword(:256)` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts mid sb) a` by
    (irule body_ctor_copy_mem_ok >> metis_tac[]) >>
  drule code_ctor_copy_insts >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode) (emitted_insts mid sb)` by
    (fs[emitted_insts_def, DROP_APPEND, EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq (emitted_insts mid sb) a = OK t /\
   sb.cs_current_bb = mid.cs_current_bb /\
   sb.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid sb` by
    fs[copy_runtime_frame_def, same_blocks_def] >>
  `t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted` by
    (drule run_inst_seq_preserves_entry_control >>
     impl_tac >- fs[EVERY_MEM] >> simp[]) >>
  suspend "paths"
QED

Resume toplevel_code_ctor_execution_full[paths]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,Gm,tm) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >> drule_all code_copy_ctor_range_ptr >>
     disch_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) >>
     `Gf' = Gf /\ tnf' = tnf` by
       (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
     `inst_seq_ptr D lo ctx func PG Gm tm (emitted_insts mid sb) a Gf tnf` by
       (qpat_x_assum `!k. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
         (qspec_then `a.vs_inst_idx` mp_tac) >> simp[]) >>
     irule emitted_origin_ptr_path >>
     simp[] >> qexistsl [`emitted_insts mid sb`,`mid`] >> gvs[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`a`,`Gm`,`tm`] mp_tac) >>
     pure_rewrite_tac[] >> disch_then (qspec_then `[]` mp_tac) >>
     simp[NoAsms] >> disch_then irule >> simp[]) >>
  `ptr_covers Gf tnf root t nb` by metis_tac[] >>
  qexistsl [`root`,`u`,`a`,`Gm`,`tm`,`Gf`,`tnf`,`t`,`d`] >>
  gvs[Abbr `d`]
QED

Finalise toplevel_code_ctor_execution_full
