(* Recover the actual post-PHI point of a successful LowerDload JMP. *)
Theory gasFocusLowerDloadJumpContinuation
Ancestors
  gasFocusLowerDloadCutGuards gasCount lowerDloadSafetyControlCoverage
  lowerDloadReturnAlignment lowerDloadReturnOrdinary lowerDloadSafetyAmbient
  lowerDloadSafetyRelation lowerDloadSafetyKernel o1SafeUpto contextCodegenRel
  concretizeLayoutCutSafe venomExecProofs venomExecSemantics venomState venomInst
  list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_successful_jump_entry:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  inst.inst_opcode = JMP /\ step_inst k C' inst t = OK q /\ ~q.vs_halted /\
  lookup_block q.vs_current_bb (ld_image f).fn_blocks = SOME bb' /\
  eval_phis q bb'.bb_instructions = OK tp /\
  run_block_non_phis m C' bb'
    (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  ?lbl H' G' ni s1 g Y.
    q = jump_to lbl t /\ step_inst k C inst s = OK (jump_to lbl s) /\
    enters_block fn (jump_to lbl s) s1 /\
    g = f with <|lf_src := s1;
                 lf_tgt := tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions;
                 lf_H := H'; lf_tv := (entry_taint_vars fn (jump_to lbl s) tn).t_var|> /\
    ld_sync lo P C vs stk PG G' (entry_taint_vars fn (jump_to lbl s) tn)
      fn ni s1 (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
      A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs) /\
    ld_image g = ld_image f /\
    ld_envelope g.lf_supply fn s1 s1.vs_inst_idx Y
      (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_inst_idx /\
    ld_prefix C' (ld_image f) Y
      (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_inst_idx 0
      (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
      (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
    lookup_block (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_current_bb
      (ld_image f).fn_blocks = SOME bb' /\
    0 < LENGTH Y /\
    get_instruction bb' (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_inst_idx =
      SOME (HD Y) /\
    ld_return_cont C fn cs s1 /\ gas_cut n vs s1 /\
    s1.vs_gas_readings = (tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions).vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH s1.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `t1 = tp with vs_inst_idx := phi_prefix_length bb'.bb_instructions` >>
  `enters_block (ld_image f) q t1` by
    (simp[enters_block_def, Abbr `t1`] >> qexistsl_tac [`bb'`,`tp`] >> simp[]) >>
  `gas_cut n vs t1` by
    (qspecl_then [`m`,`C'`,`bb'`,`t1`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs t` by metis_tac[ld_block_entry_cut_back] >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings /\ s.vs_halted = t.vs_halted` by fs[ld_nonghost_def] >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `taint_ok fn tn inst s` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  `lookup_block t1.vs_current_bb (ld_image f).fn_blocks = SOME bb'` by
    (drule eval_phis_preserves_current_bb >> simp[Abbr `t1`]) >>
  `?ti. get_instruction bb' t1.vs_inst_idx = SOME ti` by
    (irule (BETA_RULE ld_successful_body_fetch) >> qexistsl_tac [`C'`,`m`] >> metis_tac[]) >>
  `active_inst (ld_image f) ti t1` by
    (simp[active_inst_def] >> qexists_tac `bb'` >>
     qpat_assum `get_instruction _ _ = _`
       (strip_assume_tac o SRULE [get_instruction_def, AllCaseEqs()]) >>
     simp[] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all ld_sync_control_entry >>
  disch_then (qx_choose_then `lbl` (qx_choose_then `H'` (qx_choose_then `G'`
    (qx_choose_then `ni` (qx_choose_then `s1` (qx_choose_then `g`
    (qx_choose_then `Y` strip_assume_tac))))))) >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (`fs0 = fs` by fs[] >>
     `g.lf_serial = f.lf_serial` by simp[] >>
     `f.lf_serial = f0.lf_serial` by fs[HD] >>
     `g.lf_serial = f0.lf_serial` by (irule EQ_TRANS >> qexists_tac `f.lf_serial` >> asm_rewrite_tac []) >>
     qpat_x_assum `g = _` kall_tac >>
     BETA_TAC >> asm_rewrite_tac [HD, TL, NOT_CONS_NIL]) >>
  `ld_return_cont C fn cs s1` by
    (irule ld_return_cont_block >> conj_tac
     >- metis_tac[ld_sync_fn_shape, o1_fn_shape_components] >>
     qexistsl_tac [`inst`,`k`,`jump_to lbl s`,`s`] >>
     `~(jump_to lbl s).vs_halted` by fs[jump_to_def] >>
     simp[is_terminator_def]) >>
  `s1.vs_gas_readings = s.vs_gas_readings` by
    (qpat_assum `enters_block fn (jump_to lbl s) s1`
       (mp_tac o MATCH_MP enters_block_readings) >> simp[jump_to_def]) >>
  `t1.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `enters_block (ld_image f) q t1`
       (mp_tac o MATCH_MP enters_block_readings) >> simp[jump_to_def]) >>
  `0 < LENGTH Y` by metis_tac[ld_prefix_bound] >>
  `get_instruction bb' t1.vs_inst_idx = SOME (HD Y)` by metis_tac[] >>
  `ld_image g = ld_image f` by metis_tac[] >>
  `gas_cut n vs s1` by fs[gas_cut_def] >>
  `s1.vs_gas_readings = t1.vs_gas_readings` by simp[] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH s1.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (qpat_x_assum `EVERY (\a. a.lf_src.vs_gas_readings = _ /\ _) (f::fs)` mp_tac >>
     simp[EVERY_DEF]) >>
  qexistsl_tac [`lbl`,`H'`,`G'`,`ni`,`s1`,`g`,`Y`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
