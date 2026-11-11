(* A declared pointer's ALLOCA, including re-entry of a registered site. *)
Theory bodyIntCallDeclarationAlloc
Ancestors
  bodyIntCallDeclarationRegions stmtSimDeclPath loweringSlice intCallFrame
  fragGasMode fragGasSeq fragExec compileEnv exprLoweringProps emitHelperProps
  emitHelper venomExecSemantics venomState venomInst venomMemProps
  stmtSimDefs exprSimDefs instIdxIndep list rich_list

Theorem declared_alloca_resources:
  emit_inst ALLOCA [Lit bytes] [p] sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit bytes] [p]) (fn_insts func) /\
  stmt_state_rel ctx func ce cx es s /\ not_local_ptr ce es.scopes p /\
  allocas_above lo s /\
  (!op. reserved op ==> op <> Var p) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,w2n bytes) /\
    lo <= w2n w /\ allocas_above lo t /\
    t.vs_memory = s.vs_memory /\
    (!op. reserved op ==> eval_operand op t = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
   inst.inst_operands = [Lit bytes] /\ inst.inst_id = sa.cs_next_id` by
    simp[Abbr `inst`, mk_inst_def] >>
  `?u. exec_alloca inst s bytes = OK u` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- simp[exec_alloca_def] >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME region` >>
     PairCases_on `region` >> simp[exec_alloca_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  `allocas_above lo u` by
    (drule (INST_TYPE [alpha |-> ``:256``] exec_alloca_allocas_above) >> disch_then (qspecl_then [`inst`,`bytes`] mp_tac) >>
     simp[result_allocas_above_def]) >>
  `lo <= w2n w` by (fs[allocas_above_def] >> metis_tac[]) >>
  drule_all exec_alloca_frames >> strip_tac >>
  drule_all exec_alloca_memory >> strip_tac >>
  drule exec_alloca_operand_frame >> simp[] >> disch_tac >>
  drule_all exec_alloca_alloca_next_mono >> disch_tac >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[Lit bytes]`, `ALLOCA`, `[p]`, `sa`, `sb`] >>
     gvs[is_terminator_def, step_inst_base_def, mk_inst_def, Abbr `inst`]) >>
  drule gas_marked_path_exec >> strip_tac >>
  drule fragGasPathTheory.gas_path_normal >> strip_tac >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `w`] >>
  simp[stmt_state_rel_inst_idx, lookup_var_def, allocas_above_def,
       instIdxIndepTheory.eval_op_inst_idx] >>
  gvs[lookup_var_def, allocas_above_def] >>
  conj_tac
  >- (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
      simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      rpt strip_tac >> gvs[] >>
      gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, emit_def]) >>
  gvs[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, emit_def] >>
  first_assum ACCEPT_TAC
QED
