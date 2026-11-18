(* Continue at the actual next instruction after a cached original ALLOCA. *)
Theory gasFocusLowerDloadCachedAllocaNext
Ancestors lowerDloadOrdinaryEndpoint[qualified,ignore_grammar] lowerDloadSafetyAdvance[qualified,ignore_grammar] lowerDloadExpansionEndpoint[qualified,ignore_grammar] lowerDloadSafetyOrdinaryCoverage[qualified,ignore_grammar] marker[qualified,ignore_grammar] fcgDefs[qualified,ignore_grammar]
  o1SafeUpto lowerDloadSafetyAllocation lowerDloadSafetyUpdates
  lowerDloadReturnOrdinary lowerDloadReturnAlignment lowerDloadSafetyAmbient
  lowerDloadSafetyLocations lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadOracleCallAssembly o1LowerDloadClosure ptrDiscipline pointerConfinedDefs
  o1PassContract codegenRel contextCodegenRel
  venomExecProps venomExecSemantics venomState venomWf venomInst finite_map pred_set
  list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_cached_alloca_body_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  inst.inst_opcode = ALLOCA /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,m) /\
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
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `inst_wf inst` by
    (qpat_assum `fn_inst_wf fn` mp_tac >>
     qpat_assum `MEM inst (fn_insts fn)` mp_tac >>
     pure_rewrite_tac[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `?out. inst.inst_outputs = [out]` by
    (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >> (gvs[])) >>
  `MEM out (fn_ir_vars fn)` by
    (irule ld_inst_output_ir >> qexists_tac `inst` >> simp[]) >>
  `out IN fn_pv P fn` by
    (mp_tac ptr_roots_subset_fn_pv >>
     simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def] >>
     disch_then irule >> disj1_tac >> disj1_tac >> qexists_tac `inst` >>
     simp[inst_output_def]) >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  drule_all ld_cached_alloca_endpoint >> strip_tac >>
  `ss.vs_current_bb = s.vs_current_bb /\ ss.vs_gas_readings = s.vs_gas_readings` by
    (qpat_assum `step_inst 0 C inst s = OK ss` mp_tac >>
     simp[ld_alloca_step, exec_alloca_def, update_var_def] >> strip_tac >>
     qpat_assum `_ = ss` (SUBST1_TAC o SYM) >> simp[]) >>
  `?c. FLOOKUP t.vs_allocas inst.inst_id = SOME (c,m)` by
    (`FLOOKUP f.lf_src.vs_allocas inst.inst_id = SOME (b,m)` by simp[] >>
     drule_all ld_maps_original >> simp[] >> metis_tac[]) >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qpat_assum `step_inst fuel C' inst t = OK u` mp_tac >>
     simp[ld_alloca_step, exec_alloca_def, update_var_def] >> strip_tac >>
     qpat_assum `_ = u` (SUBST1_TAC o SYM) >> simp[]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = fn /\ g.lf_fn = f.lf_fn /\
   g.lf_Q = f.lf_Q /\ g.lf_supply = f.lf_supply /\
   g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx)` by simp[ADD1] >>
  qpat_x_assum `g = _` kall_tac >>
  suspend "continuation"
QED

Resume ld_focus_cached_alloca_body_next[continuation]:
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = SUC p` by simp[Abbr `q`] >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists_tac `bb` >> fs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i g.lf_src /\
         ld_envelope f.lf_supply fn g.lf_src (SUC s.vs_inst_idx) Y (SUC p) /\
         0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1]) >>
  `ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[is_terminator_def]) >>
  `ld_image g = ld_image f` by simp[ld_image_def] >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (simp[Abbr `q`] >> gvs[]) >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (qpat_assum `fs0 = fs` SUBST_ALL_TAC >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >> metis_tac[]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
     g.lf_src g.lf_tgt A (g::fs) N` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `j = HD Y` by
    (qpat_assum `j = EL 0 Y` (ACCEPT_TAC o PURE_REWRITE_RULE [CONJUNCT1 EL])) >>
  `ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0 q q` by
    (simp[ld_prefix_zero, CONJUNCT1 EL] >> metis_tac[]) >>
  qexistsl_tac [`ss`,`g`,`i`,`Y`] >>
  unabbrev_all_tac >> gvs[] >> first_assum ACCEPT_TAC
QED

Finalise ld_focus_cached_alloca_body_next
