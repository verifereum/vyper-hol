(* Resume the actual successful body after a singleton classified read or comparison. *)
Theory gasFocusLowerDloadClassifiedReadNext
Ancestors
  o1SafeUpto gasCount concretizeLayoutCutSafe lowerDloadClassifiedReadPointEffect
  lowerDloadFrontier ctxLookupAgree
  lowerDloadSafetyAllocBounds lowerDloadSafetyAdvance lowerDloadReturnOrdinary
  lowerDloadReturnAlignment lowerDloadSafetyAmbient lowerDloadSafetyLocations
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadOracleCallAssembly
  lowerDloadDefs ptrDiscipline o1PassContract codegenRel contextCodegenRelProps
  venomEffects venomExecProps venomExecSemantics venomInst venomWf finite_map
  pred_set words list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_classified_read_body_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  ir_supply_covers_fn f.lf_supply fn /\
  MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] /\
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
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >> pure_rewrite_tac[MEM] >> strip_tac >>
     simp[is_terminator_def, is_alloca_op_def, write_effects_def, empty_effects_def,
          source_memory_write_ranges_def]) >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs s` by
    (irule gas_cut_readings_mono >> qexists_tac `q` >> simp[Abbr `q`]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
      b+sz <= dyn_floor C vs /\ c+sz < dimword(:256)` by suspend "slots" >>
  `MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s` by suspend "guard" >>
  suspend "successor"
QED

Resume ld_focus_classified_read_body_next[slots]:
  `mem_inv dload_headroom_ok C vs` by fs[o1_safe_upto_def] >>
  drule_all ld_sync_source_mem_inv >> strip_tac >>
  `s.vs_initial_fmp = vs.vs_initial_fmp` by
    (drule_all ld_frame_raw_reachable >> metis_tac[raw_reachable_initial_fmp]) >>
  drule ld_sync_frontier >> strip_tac >>
  `t.vs_alloca_next <= dyn_floor C vs` by
    (simp[dyn_floor_def] >> IF_CASES_TAC >>
     gvs[dload_headroom_ok_def, ctx_has_dalloca_def] >> decide_tac) >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_target_headroom] >>
  drule ld_sync_slots >> strip_tac >>
  drule ld_sync_maps >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all ld_alloc_frontiers >> simp[] >> decide_tac
QED

Resume ld_focus_classified_read_body_next[guard]:
  disch_tac >>
  `run_block_non_phis fuel C' bb t = z` by
    (simp[Once run_block_non_phis_def] >> gvs[Abbr `q`]) >>
  `EVERY inst_wf (fn_insts fn)` by
    (fs[fn_inst_wf_def, EVERY_MEM, fn_insts_def] >> metis_tac[fn_insts_blocks_MEM]) >>
  `lower_dload_function_supply f.lf_supply fn =
    (ld_image f, SND (lower_dload_function_supply f.lf_supply fn))` by simp[ld_image_def] >>
  `^ld_probe_guard C' fuel bb t` by (BETA_TAC >> metis_tac[]) >>
  irule (Q.INST [`h` |-> `0`, `X` |-> `[inst]`] (BETA_RULE ld_guarded_source_non_revert)) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume ld_focus_classified_read_body_next[successor]:
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs` by metis_tac[] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
  drule_all ld_sync_classified_read_effect_at >> strip_tac >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  `step_inst 0 C inst s = OK ss` by metis_tac[step_inst_non_invoke] >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `q.vs_current_bb = t.vs_current_bb /\ q.vs_inst_idx = p + LENGTH [inst]` by
    simp[Abbr `q`, ADD1] >>
  `active_inst (ld_image f) j q` by metis_tac[lookup_instruction_active] >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  qabbrev_tac `ss1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  `?i Y. active_inst fn i ss1 /\ ld_envelope f.lf_supply fn ss1 (SUC s.vs_inst_idx) Y (SUC p) /\
         0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1, Abbr `ss1`]) >>
  qabbrev_tac `g = f with <|lf_src := ss1; lf_tgt := q; lf_H := H';
                            lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_vars P A g` by
    (mp_tac (Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`] ld_vars_inst_indices) >>
     simp[Abbr `g`, Abbr `ss1`, Abbr `q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn i ss1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[]) >>
  suspend "assemble"
QED

Resume ld_focus_classified_read_body_next[assemble]:
  `g.lf_serial = f.lf_serial /\ g.lf_fn = fn /\
   g.lf_Q = f.lf_Q /\ g.lf_supply = f.lf_supply /\
   g.lf_src = ss1 /\ g.lf_tgt = q /\ ld_image g = ld_image f` by
    simp[Abbr `g`, ld_image_def] >>
  `ld_return_cont C fn cs ss1` by
    (simp[Abbr `ss1`] >> irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs` by
    (pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> qx_gen_tac `a` >> disch_tac >>
     qpat_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)`
       (qspec_then `a` (mp_tac o BETA_RULE) o REWRITE_RULE [EVERY_MEM]) >>
     (impl_tac >- simp[]) >> strip_tac >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `ss.vs_gas_readings = u.vs_gas_readings` SUBST1_TAC >>
     irule LESS_EQ_TRANS >> qexists_tac `LENGTH t.vs_gas_readings` >>
     conj_tac >> gvs[]) >>
  `j = HD Y` by fs[CONJUNCT1 EL] >>
  `ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0 q q` by
    (simp[ld_prefix_zero, CONJUNCT1 EL] >> metis_tac[]) >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (qpat_assum `fs0 = fs` SUBST1_TAC >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >> metis_tac[]) >>
  `get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y)` by
    (`q.vs_inst_idx = SUC t.vs_inst_idx` by simp[Abbr `q`] >>
     qpat_assum `q.vs_inst_idx = SUC t.vs_inst_idx` (SUBST1_TAC o SYM) >>
     qpat_assum `j = HD Y` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb` by
    (qpat_assum `u.vs_current_bb = t.vs_current_bb` SUBST1_TAC >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `ld_envelope g.lf_supply fn ss1 (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >>
     qpat_assum `t.vs_inst_idx = p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `(ss with vs_inst_idx := SUC s.vs_inst_idx) = ss1` by simp[Abbr `ss1`] >>
  `(u with vs_inst_idx := SUC t.vs_inst_idx) = q` by simp[Abbr `q`] >>
  qexistsl_tac [`ss`,`g`,`i`,`Y`] >>
  qpat_assum `(ss with vs_inst_idx := SUC s.vs_inst_idx) = ss1` SUBST1_TAC >>
  qpat_assum `(u with vs_inst_idx := SUC t.vs_inst_idx) = q` SUBST1_TAC >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qpat_x_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)`
       (strip_assume_tac o SRULE [] o BETA_RULE) >>
     `!a. MEM a fs0 ==> !v. MEM (SOME v) a.lf_Q ==> v IN ld_slots A fs0` by
       (qpat_assum `!a. MEM a fs0 ==> FRANGE a.lf_H SUBSET ld_slots A fs0 /\ _` mp_tac >>
        metis_tac[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `t.vs_inst_idx = p` (SUBST1_TAC o SYM) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >> simp[Abbr `ss1`, Abbr `q`]
QED

Finalise ld_focus_classified_read_body_next
