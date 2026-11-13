(* A TopLevelName runtime buffer allocation on one joint execution. *)
Theory bodyFullToplevelCodeAllocation
Ancestors
  bodyFullToplevelCodeRange exprPtrUnwrapAllocEntry exprPtrUnwrapAllocation
  exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation bodyMemEcArithPrefix
  exprPtrUnwrapCodeCopyShape exprPtrCodeCopyEndpoint bufferAllocationExecution
  fragGasSeqPtr bodyFullUnwrapRun exprSimCopy exprSimAlloc exprLoweringProps context compileEnv
  ptrDiscipline loweringPosts venomState venomInst fragExec list rich_list words finite_map

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
