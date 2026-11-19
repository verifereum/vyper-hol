(* Synchronize LOG and storage writes at the actual next target fetch. *)
Theory gasFocusLowerDloadLogStorePoint
Ancestors
  o1SafeUpto gasCount lowerDloadSafetyHashLog lowerDloadSafetyStorageWriteCoverage
  lowerDloadSafetyAdvance lowerDloadReturnOrdinary lowerDloadSafetyAmbient
  lowerDloadSafetyLocations lowerDloadSafetyRelation lowerDloadSafetyKernel
  ptrDiscipline o1PassContract codegenRel contextCodegenRel venomEffects venomExecProps
  venomExecSemantics venomInst finite_map list rich_list arithmetic
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_log_store_point_next:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\ t.vs_inst_idx = p /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
             LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (f::fs) /\
  MEM inst.inst_opcode [LOG;SSTORE;TSTORE] /\ step_inst fuel C' inst t = OK u /\
  active_inst (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  gas_cut n vs (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?ss H' g i Y.
    step_inst 0 C inst s = OK ss /\
    g = (f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                  lf_tgt := u with vs_inst_idx := SUC t.vs_inst_idx;
                  lf_H := H'; lf_tv := (step_taint inst s ss tn).t_var|>) /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i
      (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (u with vs_inst_idx := SUC t.vs_inst_idx) A (g::fs) N /\
    ld_global lo A (g::fs) /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs) /\
    ld_envelope g.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
      (ss with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx Y
      (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx /\
    ld_prefix C' (ld_image g) Y (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx 0
      (u with vs_inst_idx := SUC t.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    0 < LENGTH Y /\ j = EL 0 Y /\
    (ss with vs_inst_idx := SUC s.vs_inst_idx).vs_gas_readings =
      (u with vs_inst_idx := SUC t.vs_inst_idx).vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
               LENGTH (ss with vs_inst_idx := SUC s.vs_inst_idx).vs_gas_readings <=
                 LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_abbrev_tac `goal` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `fs0 = fs /\ ld_global lo A (f::fs)` by fs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   ~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode _` mp_tac >> pure_rewrite_tac[MEM] >> strip_tac >>
     simp[is_terminator_def, is_alloca_op_def, write_effects_def, empty_effects_def,
          source_memory_write_ranges_def]) >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (drule ld_sync_memory >> simp[ld_nonghost_def]) >>
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
    (Cases_on `inst.inst_opcode = LOG`
     >- (drule_all ld_sync_log_effect >> strip_tac >> qexistsl [`ss`,`H'`] >> simp[]) >>
     `MEM inst.inst_opcode [SSTORE;TSTORE]` by fs[MEM] >>
     `gas_cut n vs s` by
       (qpat_x_assum `gas_cut n vs q` mp_tac >> simp[Abbr `q`, gas_cut_def] >> decide_tac) >>
     `taint_ok fn tn inst s` by
       (fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >> metis_tac[]) >>
     drule_all ld_sync_storage_write_effect_at >> simp[]) >>
  `step_inst 0 C inst s = OK ss` by metis_tac[step_inst_non_invoke] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
                            lf_tv := (step_taint inst s ss tn).t_var|>` >>
  suspend "advance"
QED

Resume ld_focus_log_store_point_next[advance]:
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = SUC p` by simp[Abbr `q`] >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i s1 /\ ld_envelope f.lf_supply fn s1 (SUC s.vs_inst_idx) Y (SUC p) /\
          0 < LENGTH Y /\ j = EL 0 Y` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`) ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`ld_image f`] mp_tac) >>
     simp[ADD1, Abbr `s1`]) >>
  `ld_vars P A g` by
    (mp_tac (ld_vars_inst_indices |> Q.INST
       [`f` |-> `f with <|lf_src := ss; lf_tgt := u; lf_H := H';
                         lf_tv := (step_taint inst s ss tn).t_var|>`,
        `i` |-> `SUC s.vs_inst_idx`, `j` |-> `SUC t.vs_inst_idx`]) >>
     simp[Abbr `g`, Abbr `s1`, Abbr `q`]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn i s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule ld_sync_ordinary_advance >> metis_tac[]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_Q = f.lf_Q /\
   g.lf_supply = f.lf_supply /\ ld_image g = ld_image f /\
   g.lf_src = s1 /\ g.lf_tgt = q` by simp[Abbr `g`, ld_image_def] >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (qpat_assum `fs0 = fs` SUBST_ALL_TAC >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (qexists_tac `f` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     first_assum ACCEPT_TAC) >>
  suspend "package"
QED

Resume ld_focus_log_store_point_next[package]:
  `s1.vs_gas_readings = q.vs_gas_readings` by
    fs[Abbr `s1`, Abbr `q`, ld_nonghost_def] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
              LENGTH s1.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)` by
    (simp[] >> qpat_x_assum `EVERY (\a. _ /\ LENGTH s.vs_gas_readings <= _) (f::fs)` mp_tac >>
     simp[EVERY_MEM, Abbr `q`] >> strip_tac >> qx_gen_tac `a` >> disch_tac >>
     first_x_assum drule >> strip_tac >>
     metis_tac[LESS_EQ_TRANS]) >>
  `ld_prefix C' (ld_image g) Y q.vs_inst_idx 0 q q` by
    (pure_rewrite_tac[ld_prefix_zero, REFL_CLAUSE, AND_CLAUSES] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `ld_image g = ld_image f` SUBST1_TAC >>
     qpat_assum `j = EL 0 Y` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `ld_envelope g.lf_supply fn s1 s1.vs_inst_idx Y q.vs_inst_idx` by
    simp[Abbr `s1`] >>
  qunabbrev_tac `goal` >> qexistsl [`ss`,`H'`,`g`,`i`,`Y`] >>
  `ss with vs_inst_idx := SUC s.vs_inst_idx = s1` by simp[Abbr `s1`] >>
  `u with vs_inst_idx := SUC t.vs_inst_idx = q` by simp[Abbr `q`] >>
  qpat_assum `ss with vs_inst_idx := SUC s.vs_inst_idx = s1` SUBST1_TAC >>
  qpat_assum `u with vs_inst_idx := SUC t.vs_inst_idx = q` SUBST1_TAC >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- simp[Abbr `g`]) >>
  qpat_x_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)`
    (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ld_focus_log_store_point_next
