(* Advance a singleton scalar or binding instruction at the actual successor fetch. *)
Theory gasFocusLowerDloadArithmeticBindingPoint
Ancestors
  o1SafeUpto gasCount lowerDloadArithmeticPointEffect lowerDloadSafetyAssignSteps
  lowerDloadSafetyRetpcEffects lowerDloadSafetyParamCoverage lowerDloadSafetyAdvance
  lowerDloadReturnOrdinary lowerDloadSafetyAmbient lowerDloadSafetyLocations
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadOracleCallAssembly
  ptrDiscipline o1PassContract codegenRel contextCodegenRel venomEffects
  venomExecProps venomExecSemantics venomInst finite_map list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_arithmetic_binding_point_next:
  let q = u with vs_inst_idx := SUC t.vs_inst_idx in
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  (MEM inst.inst_opcode
     [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
      ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; ADD; SUB; SHL; SHR; SAR] \/
   MEM inst.inst_opcode [ASSIGN; RETPC_PARAM; PARAM]) /\
  step_inst fuel C' inst t = OK u /\ active_inst (ld_image f) j q /\ gas_cut n vs q ==>
  ?ss H' g i Y.
    let s1 = ss with vs_inst_idx := SUC s.vs_inst_idx in
    step_inst 0 C inst s = OK ss /\
    g = (f with <|lf_src := s1; lf_tgt := q; lf_H := H';
                  lf_tv := (step_taint inst s ss tn).t_var|>) /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn i s1 q A (g::fs) N /\
    ld_global lo A (g::fs) /\ ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs) /\
    ld_envelope g.lf_supply fn s1 s1.vs_inst_idx Y q.vs_inst_idx /\
    ld_prefix C' (ld_image g) Y q.vs_inst_idx 0 q q /\ 0 < LENGTH Y /\ j = EL 0 Y /\
    s1.vs_gas_readings = q.vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
      LENGTH s1.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule ld_sync_ptr_ok >> strip_tac >>
  drule_all ld_sync_fn_shape >> disch_then (strip_assume_tac o MATCH_MP o1_fn_shape_components) >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode _ \/ MEM inst.inst_opcode _` mp_tac >>
     simp[NoAsms] >> strip_tac >>
     simp[is_terminator_def, is_alloca_op_def, write_effects_def, empty_effects_def,
          source_memory_write_ranges_def]) >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP] >> decide_tac) >>
  `?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    suspend "effect" >>
  suspend "advance"
QED

Resume ld_focus_arithmetic_binding_point_next[effect]:
  qpat_x_assum `MEM inst.inst_opcode _ \/ MEM inst.inst_opcode _` strip_assume_tac
  >- (`gas_cut n vs s` by
        (qpat_x_assum `gas_cut n vs _` mp_tac >>
         qpat_x_assum `LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings` mp_tac >>
         simp[gas_cut_def, Abbr `q`] >> decide_tac) >>
      `taint_ok fn tn inst s` by
        (qpat_x_assum `o1_safe_upto _ _ _ _ _` mp_tac >>
         simp[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
         metis_tac[]) >>
      drule_all ld_sync_arithmetic_effect_at >> disch_then ACCEPT_TAC) >>
  `step_inst_base inst t = OK u` by metis_tac[step_inst_non_invoke] >>
  (Cases_on `inst.inst_opcode = PARAM`
   >- (drule_all ld_sync_param_effect >> disch_then ACCEPT_TAC)) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by metis_tac[ld_global_selected, MEM] >>
  (Cases_on `inst.inst_opcode = ASSIGN`
   >- (drule (Q.INST [`PG` |-> `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`] ld_assign_effect) >>
       disch_then (qspecl_then [`u`,`tn`,`lo`,`inst`] mp_tac) >>
       simp[] >> strip_tac >>
       qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs
         (first_prov f.lf_H inst.inst_operands)`] >>
       simp[step_inst_non_invoke] >> metis_tac[ld_set_first_prov_in_domain])) >>
  `inst.inst_opcode = RETPC_PARAM` by fs[MEM] >>
  drule ld_retpc_param_effect >>
  disch_then (qspecl_then [`u`,`tn`,`lo`,`inst`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[step_inst_non_invoke] >>
  gen_tac >> strip_tac >> irule ld_set_prov_selected >>
  qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]
QED

Resume ld_focus_arithmetic_binding_point_next[advance]:
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
                            lf_tv := (step_taint inst s ss tn).t_var|>` >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH [inst] /\
   s1.vs_inst_idx = SUC s.vs_inst_idx` by simp[Abbr `q`, Abbr `s1`, ADD1] >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i s1 /\ ld_envelope f.lf_supply fn s1 s1.vs_inst_idx Y q.vs_inst_idx /\
          0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[Abbr `s1`, Abbr `q`, ADD1, Excl "EL"]) >>
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr `g`, Abbr `s1`, Abbr `q`]) >>
  `q.vs_inst_idx = SUC p` by simp[Abbr `q`] >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn i s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[markerTheory.Abbrev_def]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = s1 /\ g.lf_tgt = q /\ ld_image g = ld_image f` by
    simp[Abbr `g`, ld_image_def] >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (qpat_assum `fs0 = fs` SUBST_ALL_TAC >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >> metis_tac[]) >>
  suspend "package"
QED

Resume ld_focus_arithmetic_binding_point_next[package]:
  `step_inst 0 C inst s = OK ss` by metis_tac[step_inst_non_invoke] >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `s1.vs_gas_readings = q.vs_gas_readings` by simp[Abbr `s1`, Abbr `q`] >>
  `LENGTH s1.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    simp[Abbr `s1`, Abbr `q`] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
            LENGTH s1.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (simp[] >>
     qpat_x_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     simp[EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[LESS_EQ_TRANS]) >>
  `ld_prefix C' (ld_image g) Y q.vs_inst_idx 0 q q` by
    (pure_rewrite_tac[ld_prefix_zero, REFL_CLAUSE, AND_CLAUSES] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  `ld_envelope g.lf_supply fn s1 (SUC s.vs_inst_idx) Y q.vs_inst_idx` by
    metis_tac[] >>
  `ss.vs_gas_readings = q.vs_gas_readings` by simp[Abbr `q`] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
            LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs` by
    (qpat_assum `EVERY (\a. _ /\ LENGTH s1.vs_gas_readings <= _) (g::fs)` mp_tac >>
     simp[NoAsms, Abbr `s1`]) >>
  `!a w. MEM a fs0 /\ MEM (SOME w) a.lf_Q ==> w IN ld_slots A fs0` by metis_tac[] >>
  qexistsl_tac [`ss`,`H'`,`i`,`Y`] >>
  qpat_assum `Abbrev (s1 = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (g = _)` (SUBST1_TAC o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_x_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `MEM inst.inst_opcode _ \/ MEM inst.inst_opcode _` kall_tac >>
  fs[] >> metis_tac[]
QED

Finalise ld_focus_arithmetic_binding_point_next
