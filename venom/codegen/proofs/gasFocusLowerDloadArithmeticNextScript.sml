(* Resume the actual successful LowerDload body after a singleton arithmetic step. *)
Theory gasFocusLowerDloadArithmeticNext
Ancestors
  o1SafeUpto gasCount lowerDloadArithmeticPointEffect
  lowerDloadSafetyAdvance lowerDloadReturnOrdinary lowerDloadReturnAlignment
  lowerDloadSafetyAmbient lowerDloadSafetyLocations lowerDloadSafetyRelation
  lowerDloadSafetyKernel ptrDiscipline o1PassContract codegenRel contextCodegenRel
  venomEffects venomExecProps venomExecSemantics venomInst list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem arithmetic_ordinary_unwritten[local]:
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR] ==>
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
  source_memory_write_ranges inst s = []
Proof
  simp[] >> strip_tac >>
  simp[is_terminator_def, is_alloca_op_def, write_effects_def, empty_effects_def,
       source_memory_write_ranges_def]
QED

Theorem arithmetic_body_cut_back[local]:
  s.vs_gas_readings = t.vs_gas_readings /\ step_inst fuel C' inst t = OK u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  gas_cut n vs s /\ LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `run_block_non_phis fuel C' bb q` >>
  `q.vs_gas_readings = u.vs_gas_readings` by simp[Abbr `q`] >>
  qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
  simp[gas_count_suffix_def] >> disch_tac >>
  qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
  qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
  simp[gas_count_suffix_def] >> disch_tac >>
  qpat_x_assum `gas_cut n vs _` mp_tac >>
  simp[gas_cut_def, LENGTH_DROP] >> decide_tac
QED

Theorem ld_focus_arithmetic_body_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR] /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ step_inst fuel C' inst t = OK u /\
  run_block_non_phis fuel C' bb (u with vs_inst_idx := SUC t.vs_inst_idx) = z /\
  ((?v. z = OK v /\ gas_cut n vs v) \/ (?rt v. z = IntRet rt v /\ gas_cut n vs v)) ==>
  ?ss g i Y.
    step_inst 0 C inst s = OK ss /\ g.lf_fn = fn /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx) /\ ld_image g = ld_image f /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (u with vs_inst_idx := SUC t.vs_inst_idx) A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs) /\
    ld_envelope g.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx) /\
    ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0
      (u with vs_inst_idx := SUC t.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb /\
    0 < LENGTH Y /\ get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y) /\
    ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    ss.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ld_global lo A (f::fs)` by fs[] >>
  drule ld_sync_memory >> strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  drule_all arithmetic_body_cut_back >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  `taint_ok fn tn inst s` by
    (qpat_x_assum `o1_safe_upto _ _ _ _ _` mp_tac >>
     simp[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
     metis_tac[]) >>
  drule_all ld_sync_arithmetic_effect_at >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by metis_tac[arithmetic_ordinary_unwritten] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all ld_sync_fn_shape >> disch_then (strip_assume_tac o MATCH_MP o1_fn_shape_components) >>
  qmatch_asmsub_abbrev_tac `run_block_non_phis fuel C' bb q` >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH [inst]` by
    simp[Abbr `q`, ADD1] >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists_tac `bb` >> fs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
         ld_envelope f.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
           (SUC s.vs_inst_idx) Y (SUC p) /\
         0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1, Excl "EL"]) >>
  suspend "advance"
QED

Resume ld_focus_arithmetic_body_next[advance]:
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
                           lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr `g`, Abbr `s1`, Abbr `q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn i s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[markerTheory.Abbrev_def]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = s1 /\ g.lf_tgt = q /\ ld_image g = ld_image f` by
    simp[Abbr `g`, ld_image_def] >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (`fs0 = fs` by fs[] >> qpat_assum `fs0 = fs` SUBST_ALL_TAC >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >> metis_tac[]) >>
  `step_inst 0 C inst s = OK ss` by metis_tac[step_inst_non_invoke] >>
  `ld_return_cont C fn cs s1` by
    (simp[Abbr `s1`] >> irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by simp[] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
            LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (simp[Abbr `s1`, Abbr `q`] >>
     qpat_x_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     simp[EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[LESS_EQ_TRANS]) >>
  `ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0 q q` by
    (pure_rewrite_tac[ld_prefix_zero, REFL_CLAUSE, AND_CLAUSES] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >>
     qpat_assum `j = EL 0 Y` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y)` by
    (`q.vs_inst_idx = SUC t.vs_inst_idx` by simp[Abbr `q`] >>
     qpat_assum `q.vs_inst_idx = SUC t.vs_inst_idx` (SUBST1_TAC o SYM) >>
     simp[]) >>
  qpat_x_assum `t.vs_inst_idx = p` (SUBST_ALL_TAC o SYM) >>
  qexistsl_tac [`ss`,`g`,`i`,`Y`] >>
  qpat_assum `Abbrev (s1 = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (q = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)`
    (mp_tac o BETA_RULE) >>
  qpat_x_assum `EVERY (\a. _ /\ LENGTH ss.vs_gas_readings <= _) (g::fs)` mp_tac >>
  simp[] >> metis_tac[]
QED

Finalise ld_focus_arithmetic_body_next
