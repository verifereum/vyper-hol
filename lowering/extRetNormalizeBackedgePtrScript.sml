Theory extRetNormalizeBackedgePtr
Ancestors
  extRetCopyCountedPtr extRetAbiBytesArithPtr fragGasSeqPtr fragGasPathPtr
  exprSimPtrProps bodyPtrBopRawArm fragExec venomExecSemantics venomInstProofs
  venomInst venomState ptrSafeRun ptrDiscipline compileEnv emitHelper
  finite_map words list arithmetic wordLoadStorePtr typedCopyPtr codegenRel pred_set ghostPcTransportPtr

(* The jump path stops at block entry, before PHIs. Thus no target-block or
   no-PHI premise is necessary here. A consumer continuing in cond must supply
   its own entry/no-PHI facts. In particular se is the actual child exit. *)
Theorem normalize_array_backedge_counted_ptr:
  lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH se.cs_current_insts) =
    SOME (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) /\
  get_instruction bb (LENGTH se.cs_current_insts+1) =
    SOME (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) /\
  get_instruction bb (LENGTH se.cs_current_insts+2) =
    SOME (mk_inst (id+2) JMP [Label cond] []) /\
  s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\ ~s.vs_halted /\
  ctr <> tmp /\ lookup_var ctr s = SOME (n2w i) /\
  op_taint tn (Var ctr) = {} /\ i < N /\ N < dimword(:256) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = cond /\ sf.vs_inst_idx = 0 /\
    sf.vs_prev_bb = SOME se.cs_current_bb /\ ~sf.vs_halted /\
    lookup_var ctr sf = SOME (n2w (i+1)) /\ op_taint tnf (Var ctr) = {} /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. p <> tmp /\ p <> ctr ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `a = update_var tmp (n2w i+1w) s` >>
  qabbrev_tac `s1 = a with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `b = update_var ctr (n2w i+1w) s1` >>
  qabbrev_tac `s2 = b with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) a` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) s a tn` >>
  qabbrev_tac `G2 = step_prov PG G1 (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) b` >>
  qabbrev_tac `tn2 = step_taint (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) s1 b tn1` >>
  `step_inst_base (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) s = OK a` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def, Abbr `a`]) >>
  `tn1 = tn with t_var := tn.t_var |+ (tmp,{})` by
    (simp[Abbr `tn1`, Abbr `a`, step_taint_def, mk_inst_def,
      out_taint_def, op_taint_def, set_var_taint_def, mem_taint_def,
      imm_taint_def, adopt_reset_def, update_var_def, new_site_bytes_def,
      step_writes_def, written_taint_def, store_taint_def, range_bytes_def,
      source_memory_write_ranges_def, eval_operand_def, FLOOKUP_DEF,
      EXTENSION, taint_component_equality] >> metis_tac[]) >>
  `step_inst_base (mk_inst (id+1) ASSIGN [Var tmp] [ctr]) s1 = OK b` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure1_def, eval_operand_def, Abbr `s1`,
       Abbr `a`, Abbr `b`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `tn2 = tn1 with t_var := tn1.t_var |+ (ctr,{})` by
    (simp[Abbr `tn2`, Abbr `b`, step_taint_def, mk_inst_def,
      out_taint_def, op_taint_def, set_var_taint_def, mem_taint_def,
      imm_taint_def, adopt_reset_def, update_var_def, new_site_bytes_def,
      step_writes_def, written_taint_def, store_taint_def, range_bytes_def,
      source_memory_write_ranges_def, eval_operand_def, FLOOKUP_DEF,
      EXTENSION, taint_component_equality, FLOOKUP_UPDATE,
      Abbr `s1`, Abbr `a`, lookup_var_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`, NoAsms] >>
     irule gas_path_ptr_one_step >>
     simp[mk_inst_def, is_terminator_def, Abbr `a`, update_var_def] >>
     rewrite_tac[GSYM mk_inst_def] >>
     irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` by
    (simp[Abbr `G2`, Abbr `tn2`, Abbr `s2`, NoAsms] >>
     irule gas_path_ptr_one_step >>
     simp[mk_inst_def, is_terminator_def, Abbr `s1`, Abbr `a`, update_var_def, ADD1] >>
     rewrite_tac[GSYM mk_inst_def] >>
     conj_tac >- simp[Abbr `b`, update_var_def] >>
     irule bop_assign_ptr_inst_ok >> simp[op_taint_def,FLOOKUP_UPDATE]) >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G2 tn2 (OK (jump_to cond s2))` by
    (irule jump_gas_path_ptr >>
     conj_tac >- simp[Abbr `s2`, Abbr `b`, Abbr `s1`, Abbr `a`, update_var_def] >>
     qexistsl_tac [`bb`,`mk_inst (id+2) JMP [Label cond] []`] >>
     simp[Abbr `s2`, Abbr `s1`, Abbr `b`, Abbr `a`, update_var_def,
       mk_inst_def, is_terminator_def, ADD1] >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       eval_operand_def, allocas_from_def, source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       op_taint_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       jump_to_def]) >>
  qexistsl_tac [`G2`,`tn2`,`jump_to cond s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  simp[Abbr `s2`, Abbr `b`, Abbr `s1`, Abbr `a`, jump_to_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def,
    GSYM word_add_n2w] >>
  conj_tac
  >- (qpat_x_assum `s.vs_current_bb = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_x_assum `s.vs_inst_idx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      simp[NoAsms]) >>
  rpt strip_tac >>
  simp[Abbr `G2`, Abbr `G1`, step_prov_def, mk_inst_def,
    set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
