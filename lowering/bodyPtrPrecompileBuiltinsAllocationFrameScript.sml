Theory bodyPtrPrecompileBuiltinsAllocationFrame
Ancestors bodyPtrPrecompileBuiltinsStaging exprSimLiteralBuffer
          ptrDiscipline venomExecSemantics venomState venomInst finite_map
          loweringHalt contextCodegenRelProps pred_set compileEnv emitHelper
          context list rich_list fragExec fragGasSeqPtr exprLoweringProps

Theorem alloca_ghost_frames:
  (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_mem =
    tn.t_mem UNION new_site_bytes s t /\
  (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_imm = tn.t_imm /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit sz] [out]) t) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn) (Var p) =
      op_taint tn (Var p))
Proof
  simp[step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       mk_inst_def, step_prov_def, set_prov_def, set_var_taint_def,
       op_taint_def] >>
  Cases_on `out_prov PG G (mk_inst id ALLOCA [Lit sz] [out]) t` >>
  gvs[mk_inst_def] >>
  simp[set_prov_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem alloca_taint_exterior:
  i NOTIN new_site_bytes s t ==>
  (i IN (step_taint (mk_inst id ALLOCA [Lit sz] [out]) s t tn).t_mem <=>
   i IN tn.t_mem)
Proof
  simp[alloca_ghost_frames]
QED

Theorem alloca_runtime_frames:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  (!p. p <> out ==> lookup_var p t = lookup_var p s)
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem emitted_allocation_singleton:
  compile_alloc_buffer n sa = (buf,sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]]
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, emitted_insts_def, DROP_APPEND1] >>
  strip_tac >> gvs[DROP_APPEND1]
QED

Theorem singleton_ghost_result[local]:
  inst_seq_ptr D 0 ctx fn PG G tn [i] s Gf tnf /\
  step_inst_base i s = OK t ==>
  Gf = step_prov PG G i t /\ tnf = step_taint i s t tn
Proof
  strip_tac >> gvs[inst_seq_ptr_def]
QED

Theorem emitted_allocation_frames:
  compile_alloc_buffer n sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?out G' tn'. buf.buf_operand = Var out /\ not_fresh_at sb out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' out t n /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    tn'.t_mem = tn.t_mem UNION new_site_bytes s t /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all emitted_allocation_checked_cursors >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  drule emitted_allocation_singleton >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (Cases_on `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s` >>
     gvs[run_inst_seq_def]) >>
  drule alloca_runtime_frames >> strip_tac >>
  qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >>
  gvs[] >> drule_all singleton_ghost_result >> strip_tac >> gvs[] >>
  qexistsl [`step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
                 [STRING #"%" (toString sa.cs_next_var)]) t`,
            `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
                 [STRING #"%" (toString sa.cs_next_var)]) s t tn`] >>
  simp[alloca_ghost_frames] >> gen_tac >> strip_tac >>
  `p <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[]) >> simp[alloca_ghost_frames]
QED
