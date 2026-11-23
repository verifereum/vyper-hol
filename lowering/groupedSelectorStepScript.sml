(* Execution of the grouped comparison's EQ and direct JNZ. *)
Theory groupedSelectorStep
Ancestors
  entryDispatchPtr entryPrefixPtr fragGasOriginPtrLoop fragGasOriginPtr ptrSafeRun
  ptrDiscipline fragExec venomExecSemantics venomInst venomState
  codegenRel contextCodegenRel unitTransformDefs memSafeRun moduleLoweringProps
  compileEnv emitHelperProps list finite_map words

Theorem grouped_comparison_origin_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [mid; Lit (n2w sel)] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id' JNZ [Var out; Label yes; Label no] []) /\
  ~s.vs_halted /\ eval_operand mid s = SOME m /\ op_taint tn mid = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    vars_pc_only s t /\ t.vs_current_bb = (if m = n2w sel then yes else no) /\
    t.vs_inst_idx = 0 /\
    (!sa sb. fresh_vars_wrt sa s /\ sa.cs_next_var < sb.cs_next_var /\
      out = STRING #"%" (toString sa.cs_next_var) ==> fresh_vars_wrt sb t) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D fuel. ptr_safe_blocks D lo fuel ctx func PG
        (entry_prov func t G') (entry_taint_vars func t tn') t ==>
      ptr_safe_run D lo fuel ctx func PG G tn s) /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `v = bool_to_word (m = n2w sel)` >>
  qabbrev_tac `u = update_var out v s` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `i = mk_inst id EQ [mid; Lit (n2w sel)] [out]` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `step_inst 0 ctx i s = OK u` by
    simp[Abbr `i`, Abbr `u`, Abbr `v`, step_inst_non_invoke, mk_inst_def,
         step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK s1,G1,tn1)` by
    (rpt gen_tac >> simp[Abbr `s1`] >> irule step_origin_ptr_path >>
     simp[] >>
     `ptr_safe_step D lo 0 ctx func PG G tn i s` by
       (simp[Abbr `i`] >> irule ptr_safe_dispatch_scalar_step >>
        simp[op_taint_def] >> simp[Abbr `u`, update_var_def]) >>
     `ghost_step 0 ctx PG G tn i s = (G1,tn1)` by
       (mp_tac (Q.SPECL [`0`,`ctx`,`PG`,`G`,`tn`,`i`,`s`,`u`]
          ghost_step_non_invoke) >> simp[Abbr `i`, Abbr `G1`, Abbr `tn1`]) >>
     gvs[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_write_ranges_def, source_memory_read_ranges_def]) >>
  `op_taint tn1 (Var out) = {}` by
    (simp[Abbr `tn1`, Abbr `i`] >> irule dispatch_scalar_output_clean >> simp[op_taint_def]) >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = SUC s.vs_inst_idx /\
    ~s1.vs_halted /\ eval_operand (Var out) s1 = SOME v /\
    allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (fs[Abbr `s1`, Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
        FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  qabbrev_tac `lbl = if m = n2w sel then yes else no` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G1,tn1) []
     (OK (jump_to lbl s1),G1,tn1)` by
    (rpt gen_tac >> mp_tac (Q.INST [`s` |-> `s1`, `G` |-> `G1`, `tn` |-> `tn1`,
       `cond` |-> `Var out`, `l1` |-> `yes`, `l2` |-> `no`,
       `w` |-> `v`, `iid` |-> `id'`, `bb` |-> `bb`] jnz_origin_ptr_path) >>
     simp[Abbr `lbl`, Abbr `v`, bool_to_word_def]) >>
  `!D fuel. ptr_safe_blocks D lo fuel ctx func PG
      (entry_prov func (jump_to lbl s1) G1)
      (entry_taint_vars func (jump_to lbl s1) tn1) (jump_to lbl s1) ==>
    ptr_safe_run D lo fuel ctx func PG G tn s` by
    (rpt strip_tac >>
     `step_inst fuel ctx i s = OK u` by
       simp[Abbr `i`, Abbr `u`, Abbr `v`, step_inst_non_invoke, mk_inst_def,
            step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
     `ptr_safe_step D lo fuel ctx func PG G tn i s` by
       (simp[Abbr `i`] >> irule ptr_safe_dispatch_scalar_step >>
        simp[op_taint_def] >> simp[Abbr `u`, update_var_def]) >>
     irule ptr_safe_run_scalar_continuation >> qexistsl_tac [`bb`,`i`,`u`] >>
     simp[Abbr `i`, is_terminator_def, mk_inst_def, Abbr `u`, update_var_def] >>
     `ptr_safe_run D lo fuel ctx func PG G1 tn1 s1` suffices_by simp[] >>
     mp_tac (Q.INST [`s` |-> `s1`, `fn` |-> `func`, `G` |-> `G1`, `tn` |-> `tn1`,
       `op` |-> `Var out`, `yes` |-> `yes`, `no` |-> `no`, `v` |-> `v`,
       `id` |-> `id'`, `bb` |-> `bb`] ptr_safe_cond_jump_continuation) >>
     simp[Abbr `lbl`, Abbr `v`, bool_to_word_def]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp[Abbr `tn1`, Abbr `i`] >>
     irule dispatch_scalar_taint_frame >>
     simp[Abbr `u`, vars_pc_only_update_var, vars_pc_only_refl]) >>
  `!sa sb. fresh_vars_wrt sa s /\ sa.cs_next_var < sb.cs_next_var /\
    out = STRING #"%" (toString sa.cs_next_var) ==>
    fresh_vars_wrt sb (jump_to lbl s1)` by
    (rpt gen_tac >> simp[Abbr `s1`, Abbr `u`, control_moves_keep_vars] >> strip_tac >>
     irule fresh_vars_wrt_advance >>
     qexistsl_tac [`sa.cs_next_var`, `sa`] >> simp[]) >>
  qexistsl [`jump_to lbl s1`,`G1`,`tn1`] >>
  conj_tac >-
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
  rpt conj_tac >> (TRY (first_assum ACCEPT_TAC)) >>
  simp[vars_pc_only_def, Abbr `s1`, Abbr `u`, jump_to_def, update_var_def,
       venom_state_component_equality, Abbr `G1`, Abbr `tn1`, Abbr `i`,
       lookup_var_def, FLOOKUP_UPDATE, step_taint_single_output_preserves_other_operand,
       step_prov_def, out_prov_def, set_prov_def, FLOOKUP_DRESTRICT, mk_inst_def]
QED
