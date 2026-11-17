(* A deterministic SLOAD/TLOAD endpoint, shared by all finite horizons. *)
Theory augAssignFullLoadStorageStep
Ancestors
  decoderNavigationPtr decoderGhostFramePtr
  emitHelperProps exprLoweringProps instMemFrontier memSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState stateFrame codegenRel
  loweringStateRelDefs compileEnv finite_map words pred_set list arithmetic

val load_steps = LIST_CONJ (List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``SLOAD``, ``TLOAD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs));

Theorem augassign_storage_load_joint_step:
  !K DF lo explicit ctx func PG sa arg slot s G tn old sb tr x opc i w raw u G1 tn1.
    x = STRING #"%" (toString sa.cs_next_var) /\
    opc = (if tr then TLOAD else SLOAD) /\
    i = mk_inst sa.cs_next_id opc [arg] [x] /\
    w = (if tr then tload slot s else sload slot s) /\
    raw = update_var x w s /\
    u = (raw with vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G i raw /\
    tn1 = step_taint i s raw tn /\
    emit_op opc [arg] sa = (old,sb) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand arg s = SOME slot /\
    (!q. arg = Var q ==> not_fresh_at sa q) /\
    op_taint tn arg = {} /\
    (!b. (slot,b) NOTIN (if tr then tn.t_trans else tn.t_stor)) /\
    (!H. K H ==> ptr_inst_ok (DF H) lo 0 ctx func G tn i s)
    ==>
    (!H. K H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,G1,tn1)) /\
    eval_operand old u = SOME w /\ eval_operand arg u = SOME slot /\
    op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s /\
         FLOOKUP G1 q = FLOOKUP G q /\ op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >>
  simp_tac bool_ss [GSYM AND_IMP_INTRO] >>
  ntac 8 (disch_then SUBST1_TAC) >>
  pure_rewrite_tac [AND_IMP_INTRO] >>
  qabbrev_tac `x = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [arg] [x]` >>
  qabbrev_tac `raw = update_var x (if tr then tload slot s else sload slot s) s` >>
  qabbrev_tac `u = raw with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i raw` >>
  qabbrev_tac `tn1 = step_taint i s raw tn` >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `!q. not_fresh_at sa q ==> q <> x` by
    (simp[not_fresh_at_def, Abbr `x`] >> metis_tac[LESS_EQ_REFL]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `s.vs_inst_idx = _` (fn th => pure_rewrite_tac [GSYM th]) >>
      simp_tac bool_ss [Abbr `G1`, Abbr `tn1`] >>
      irule navigation_instruction_origin >> goal_assum (drule_at Any) >>
      Cases_on `tr` >>
      simp[Abbr `i`, mk_inst_def, is_terminator_def,
        below_frontier_no_ranges, inst_dload_in_section_other,
        load_steps, exec_read1_def, Abbr `raw`] >>
      qexistsl_tac [`sa`,`sb`] >> simp[Abbr `x`, mk_inst_def]) >>
  `op_taint tn1 (Var x) = {} /\ tn1.t_mem = tn.t_mem` by
    (Cases_on `tr` >>
     gvs[Abbr `tn1`, Abbr `i`, Abbr `raw`, step_taint_def,
       op_taint_def, set_var_taint_def, out_taint_def, key_taint_def,
       mk_inst_def, FLOOKUP_UPDATE, mem_taint_def, new_site_bytes_def,
       update_var_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, EXTENSION, FLOOKUP_DEF] >>
     metis_tac[]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (Cases_on `tr` >> simp[Abbr `tn1`, Abbr `i`, step_taint_nonmemory_frame, mk_inst_def]) >>
  `op_prov G1 (Var x) = NONE` by
    (Cases_on `tr` >> simp[Abbr `G1`, Abbr `i`, op_prov_def, step_prov_def,
      out_prov_def, set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT]) >>
  `eval_operand arg (raw with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)) = SOME slot` by
    (Cases_on `arg` >>
     gvs[eval_operand_def, Abbr `raw`, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[Abbr `raw`, Abbr `x`, eval_operand_def, lookup_var_def,
    update_var_def, state_frame_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `i`, step_prov_other_output,
    step_taint_other_output, mk_inst_def]
QED
