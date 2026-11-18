(* Resume a successful LowerDload block body after a singleton environment read. *)
Theory gasFocusLowerDloadEnvironmentNext
Ancestors
  o1SafeUpto gasCount lowerDloadSafetyEnvironmentReadEffects
  lowerDloadSafetyAdvance lowerDloadReturnOrdinary lowerDloadReturnAlignment
  lowerDloadSafetyAmbient lowerDloadSafetyLocations lowerDloadSafetyRelation
  lowerDloadSafetyKernel lowerDloadOracleCallAssembly
  ptrDiscipline o1PassContract codegenRel contextCodegenRel venomEffects venomExecProps
  venomExecSemantics venomInst finite_map list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_environment_body_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  ld_return_cont C fn cs s /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  MEM inst.inst_opcode
    [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
     TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
     CALLDATASIZE;RETURNDATASIZE;CODESIZE] /\
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
  drule ld_sync_ptr_ok >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_x_assum `MEM inst.inst_opcode _` mp_tac >> pure_rewrite_tac[MEM] >> strip_tac >>
     simp[is_terminator_def, is_alloca_op_def, write_effects_def, empty_effects_def,
          source_memory_write_ranges_def]) >>
  `s.vs_gas_readings = t.vs_gas_readings` by fs[ld_nonghost_def] >>
  `gas_cut n vs q` by
    (qspecl_then [`fuel`,`C'`,`bb`,`q`] mp_tac (CONJUNCT1 (CONJUNCT2 gas_count_suffix)) >>
     qpat_x_assum `(?v. z = OK v /\ _) \/ _` strip_assume_tac >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs v` mp_tac >> simp[gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `gas_cut n vs s` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def] >> disch_tac >>
     qpat_x_assum `gas_cut n vs q` mp_tac >>
     simp[Abbr `q`, gas_cut_def, LENGTH_DROP] >> decide_tac) >>
  `taint_ok fn tn inst s` by
    (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
     metis_tac[]) >>
  `step_inst_base inst t = OK u` by metis_tac[step_inst_non_invoke] >>
  qpat_assum `ld_vars P A f`
    (mp_then Any mp_tac (Q.INST [`PG` |-> `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`]
       ld_environment_read_effect)) >>
  disch_then (qspecl_then [`u`,`tn`,`lo`,`inst`] mp_tac) >> simp[] >> strip_tac >>
  `step_inst 0 C inst s = OK ss /\ step_inst fuel C inst s = OK ss` by
    simp[step_inst_non_invoke] >>
  qabbrev_tac `H' = set_prov f.lf_H inst.inst_outputs NONE` >>
  qabbrev_tac `ss1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := ss1; lf_tgt := q; lf_H := H';
                            lf_tv := (step_taint inst s ss tn).t_var|>` >>
  `ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss)` by
    (irule ld_sync_ghost_step >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  `!a. a IN FRANGE H' ==> a IN FDOM A` by
    (qpat_assum `!a. a IN FRANGE f.lf_H ==> a IN FDOM A`
       (mp_then Any mp_tac (Q.INST [`q` |-> `NONE`, `outs` |-> `inst.inst_outputs`]
         lowerDloadOracleCallAssemblyTheory.ld_set_prov_selected)) >>
     simp[Abbr `H'`] >> metis_tac[]) >>
  `ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory` by
    (irule ld_sync_dyn_agree_unwritten >> goal_assum (drule_at Any) >> simp[] >>
     (metis_tac[])) >>
  `?j. get_instruction bb q.vs_inst_idx = SOME j` by
    (irule (BETA_RULE ld_successful_body_fetch) >> metis_tac[]) >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = SUC p` by simp[Abbr `q`] >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists_tac `bb` >> fs[get_instruction_def] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i ss1 /\ ld_envelope f.lf_supply fn ss1 (SUC s.vs_inst_idx) Y (SUC p) /\
          0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1, Abbr `ss1`]) >>
  suspend "advance"
QED

Resume ld_focus_environment_body_next[advance]:
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr `g`, Abbr `ss1`, Abbr `q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn i ss1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
   g.lf_Q = f.lf_Q /\ g.lf_supply = f.lf_supply /\
   g.lf_src = ss1 /\ g.lf_tgt = q` by simp[Abbr `g`] >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (qpat_assum `fs0 = fs` (SUBST_ALL_TAC) >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >> metis_tac[]) >>
  `ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[]) >>
  `ld_image g = ld_image f` by simp[ld_image_def] >>
  `ss.vs_gas_readings = u.vs_gas_readings` by fs[ld_nonghost_def] >>
  `LENGTH u.vs_gas_readings <= LENGTH t.vs_gas_readings` by
    (qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP] >> decide_tac) >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs` by
    (qpat_x_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     simp[EVERY_MEM] >> strip_tac >> qx_gen_tac `a` >> disch_tac >>
     qpat_assum `!a. MEM a fs ==> _` (qspec_then `a` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `LENGTH u.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings` by
       (irule LESS_EQ_TRANS >> qexists_tac `LENGTH t.vs_gas_readings` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `(ss with vs_inst_idx := SUC s.vs_inst_idx) = ss1` by simp[Abbr `ss1`] >>
  `ld_prefix C' (ld_image g) Y (SUC t.vs_inst_idx) 0 q q` by
    (pure_rewrite_tac[ld_prefix_zero, REFL_CLAUSE, AND_CLAUSES] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >>
     qpat_assum `j = EL 0 Y` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `get_instruction bb (SUC p) = SOME (EL 0 Y)` by
    (qpat_assum `q.vs_inst_idx = SUC p` (SUBST1_TAC o SYM) >>
     qpat_assum `j = EL 0 Y` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `lookup_block u.vs_current_bb (ld_image g).fn_blocks = SOME bb` by
    (qpat_assum `u.vs_current_bb = t.vs_current_bb` SUBST1_TAC >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `(u with vs_inst_idx := SUC t.vs_inst_idx) = q` by simp[Abbr `q`] >>
  `g.lf_src.vs_gas_readings = ss.vs_gas_readings /\
   g.lf_tgt.vs_gas_readings = u.vs_gas_readings` by simp[Abbr `ss1`, Abbr `q`] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH ss.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by simp[] >>
  `ld_envelope g.lf_supply fn ss1 (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (qpat_assum `g.lf_supply = f.lf_supply` SUBST1_TAC >>
     qpat_assum `t.vs_inst_idx = p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `get_instruction bb (SUC t.vs_inst_idx) = SOME (HD Y)` by
    (qpat_assum `t.vs_inst_idx = p` SUBST1_TAC >>
     qpat_assum `get_instruction bb (SUC p) = SOME (EL 0 Y)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [CONJUNCT1 EL])) >>
  qpat_assum `ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx)`
    (mp_tac) >>
  qpat_assum `(ss with vs_inst_idx := SUC s.vs_inst_idx) = ss1` SUBST1_TAC >>
  disch_tac >> qexistsl_tac [`ss`,`g`,`i`,`Y`] >>
  qpat_assum `(ss with vs_inst_idx := SUC s.vs_inst_idx) = ss1` SUBST1_TAC >>
  qpat_assum `(u with vs_inst_idx := SUC t.vs_inst_idx) = q` SUBST1_TAC >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qpat_assum `g.lf_fn = f.lf_fn` SUBST1_TAC >> first_assum ACCEPT_TAC)) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qpat_x_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)`
       (strip_assume_tac o SRULE [] o BETA_RULE) >>
     `!a. MEM a fs ==> !v. MEM (SOME v) a.lf_Q ==> v IN ld_slots A fs` by
       (qpat_assum `!a. MEM a fs0 ==> FRANGE a.lf_H SUBSET ld_slots A fs0 /\ _` mp_tac >>
        qpat_assum `fs0 = fs` SUBST1_TAC >> metis_tac[]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `t.vs_inst_idx = p` (SUBST1_TAC o SYM) >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise ld_focus_environment_body_next
