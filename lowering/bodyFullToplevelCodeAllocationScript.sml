(* A TopLevelName runtime buffer allocation on one joint execution. *)
Theory bodyFullToplevelCodeAllocation
Ancestors
  bodyFullToplevelCodeRange exprPtrUnwrapAllocEntry exprPtrUnwrapAllocation
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation bodyMemEcArithPrefix
  exprPtrUnwrapCodeCopyShape exprPtrCodeCopyEndpoint exprPtrCodeCopyFrame bufferAllocationExecution
  fragGasOriginPtr fragGasSeqPtr bodyFullUnwrapRun exprSimCopy exprSimAlloc exprLoweringProps context compileEnv
  ptrDiscipline loweringPosts venomState venomInst venomMemDefs fragExec list rich_list words finite_map

Theorem toplevel_code_allocation_full:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?root u Gm tm a.
    buf.buf_operand = Var root /\ buf.buf_size = nb /\
    u = update_var root (n2w (buffer_allocation_base s sm.cs_next_id))
      (buffer_allocation_fields s sm.cs_next_id nb) /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a,Gm,tm)) /\
    a.vs_current_bb = mid.cs_current_bb /\
    a.vs_inst_idx = LENGTH mid.cs_current_insts /\
    ptr_covers Gm tm root a nb /\
    eval_operand buf.buf_operand a = SOME (n2w (buffer_allocation_base s sm.cs_next_id))
Proof
  strip_tac >> drule_all unwrap_alloc_entry >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  qpat_x_assum `out' = _` SUBST_ALL_TAC >>
  `run_inst_seq (emitted_insts sm mid) s = OK u` by
    simp[run_inst_seq_def] >>
  `u.vs_requests = s.vs_requests` by
    (simp[update_var_def, buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  `mid.cs_current_bb = sm.cs_current_bb` by
    metis_tac[unwrap_alloc_current_block] >>
  `run_inst_seq_mem_ok (emitted_insts sm mid) s` by
    metis_tac[ec_alloc_buffer_mem_ok] >>
  qexistsl [`STRING #"%" (toString sm.cs_next_var)`,`u`,`Gf`,`tnf`,`a`] >> asm_rewrite_tac[] >> gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm mid) s Gf tnf` by
    (simp[inst_seq_ptr_def] >> irule unwrap_alloc_ptr_check >>
     simp[buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH mid.cs_current_insts),Gf,tnf)` by
    (irule emitted_origin_ptr_path >> conj_tac >- (simp[]) >>
     qexistsl [`emitted_insts sm mid`,`sm`] >>
     simp[ec_alloc_buffer_mem_ok, mk_inst_def, is_terminator_def]) >>
  `LENGTH mid.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `a = u with vs_inst_idx := LENGTH mid.cs_current_insts` by simp[] >>
  gvs[]
QED

Theorem toplevel_code_allocation_frontier:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\
  nb < dimword(:256) /\ 32*n <= nb ==>
  w2n (n2w (buffer_allocation_base s sm.cs_next_id):bytes32) + 32*n <=
    (buffer_allocation_fields s sm.cs_next_id nb).vs_alloca_next
Proof
  strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  simp[buffer_allocation_base_def, buffer_allocation_fields_def] >>
  Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]
  >- (`s.vs_alloca_next MOD dimword(:256) <= s.vs_alloca_next` by
        simp[arithmeticTheory.MOD_LESS_EQ] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME site` >>
  PairCases_on `site` >> fs[alloca_next_valid_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> strip_tac >>
  `site0 MOD dimword(:256) <= site0` by simp[arithmeticTheory.MOD_LESS_EQ] >>
  first_x_assum drule >> decide_tac
QED

Theorem toplevel_code_runtime_execution_full:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_alloc_buffer nb sm = (buf,mid) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 mid = ((),sb) /\
  fn_has_code sm mid func /\ fn_has_code mid sb func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword(:256) /\ 32*n <= nb /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sm x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} /\
  w2n p + 32*n <= LENGTH s.vs_data_section /\
  w2n p + 32*n < dimword(:256) ==>
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
    tnf.t_mem = tm.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
    tnf.t_stor = tm.t_stor /\ tnf.t_trans = tm.t_trans /\ tnf.t_imm = tm.t_imm /\
    (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x /\
      op_taint tnf (Var x) = op_taint tm (Var x)) /\
    allocas_from lo z /\
    (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory)
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
  `eval_operand src a = SOME p /\ op_taint tm src = {}` by fs[] >>
  `allocas_from lo a /\ ~a.vs_halted /\ a.vs_data_section = s.vs_data_section` by
    (simp[allocas_from_def, buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >>
     qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def] >>
     disch_then drule >> simp[]) >>
  `w2n d + 32*n <= a.vs_alloca_next` by
    (drule_all toplevel_code_allocation_frontier >>
     simp[Abbr `d`, update_var_def]) >>
  `compile_imm_copy_to_memory F imm src (Var root) n 0 mid = ((),sb)` by
    (qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `0+32*n <= nb /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
   w2n d+0+32*n <= a.vs_alloca_next /\
   w2n p+0+32*n <= LENGTH a.vs_data_section /\
   w2n p+0+32*n < dimword(:256)` by gvs[] >>
  drule_all toplevel_code_runtime_range_full >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `ptr_covers Gf tnf root t nb` by metis_tac[] >>
  `copy_old_operand mid (Var root) /\ eval_operand (Var root) a = SOME d` by
    simp[copy_old_operand_def, eval_operand_def] >>
  `w2n d+32*n < dimword(:256)` by decide_tac >>
  `!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len a.vs_memory` by
    (rpt strip_tac >> irule code_copy_endpoint_exterior >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
     qexistsl [`p`,`d`] >> asm_rewrite_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (gen_tac >>
     qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`a`,`Gm`,`tm`] mp_tac) >>
     pure_rewrite_tac[] >> disch_then (qspec_then `[]` mp_tac) >>
     simp[NoAsms] >> disch_then irule >> simp[]) >>
  qexistsl [`root`,`u`,`a`,`Gm`,`tm`,`Gf`,`tnf`,`t`,`d`] >>
  gvs[Abbr `d`] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
