(* Counted buffer allocation at its actual (possibly reused) base. *)
Theory bodyIntCallReuseAllocation
Ancestors
  bodyIntCallStorageAllocate exprSimAlloc storageCopyGasPath
  exprSimStorageCopy exprSimAggregateChildren stmtReasonLitFragMemory
  loweringHalt exprLoweringProps venomState venomExecSemantics
  venomInst compileEnv context finite_map words rich_list venomMemDefs

Theorem intcall_reuse_allocation:
  compile_alloc_buffer nb sm = (buf,si) /\ fn_has_code sm si func /\
  nb < dimword(:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u x b.
    buf.buf_operand = Var x /\ not_fresh_at si x /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [x]) (fn_insts func) /\
    sm.cs_next_id < si.cs_next_id /\ local_ptrs_reserved ce si /\
    (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    ~u.vs_halted /\ u.vs_current_bb = si.cs_current_bb /\
    u.vs_inst_idx = LENGTH si.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,nb) /\
    b + nb < dimword(:256) /\ b + nb <= u.vs_alloca_next /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid off sz. aid < sm.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
      regions_disjoint b nb off sz) /\
    (!name off sz. local_region ce es.scopes u name off sz ==>
      regions_disjoint b nb off sz)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  `t.vs_alloca_next >= s.vs_alloca_next /\
   (t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
     vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     simp[AllCaseEqs(), update_var_def] >> rpt strip_tac >>
     gvs[venom_state_component_equality]) >>
  `w2n w + nb <= t.vs_alloca_next` by
    (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP t.vs_allocas _ = _ ==> _`
       (qspec_then `sm.cs_next_id` mp_tac) >> simp[]) >>
  `si.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm si` by
    metis_tac[prefix_drop_equiv, emitted_insts_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH si.cs_current_insts))` by
    (mp_tac (Q.SPECL [`emitted_insts sm si`,`s`,`t`,`F`,`ctx`,`func`,`bb`]
       storage_copy_seq_path) >>
     simp[mk_inst_def, is_terminator_def] >>
     impl_tac >- (qpat_x_assum `isPREFIX _ _` mp_tac >> simp[mk_inst_def]) >>
     simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH si.cs_current_insts`,
    `x`,`w2n w`] >>
  gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
      n2w_w2n, local_region_def] >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _;
        vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (qpat_x_assum `t with <|vs_vars := _; vs_inst_idx := _;
        vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!aid b len. aid < _ /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` irule >>
  qexists_tac `name` >> metis_tac[]
QED
