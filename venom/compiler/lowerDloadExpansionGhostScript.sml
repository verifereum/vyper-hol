(* Ghost observations at a completed expansion, independent of successor location. *)
Theory lowerDloadExpansionGhost
Ancestors
  lowerDloadExpansionExit lowerDloadSafetyUpdates lowerDloadSafetyValues
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadSafetyAllocation
  venomExecSemantics venomState ptrDiscipline finite_map pred_set list

Theorem ld_vars_observation_cong:
  ld_vars P A f /\ s.vs_vars = f.lf_src.vs_vars /\
  s.vs_params = f.lf_src.vs_params /\ t.vs_params = f.lf_tgt.vs_params /\
  (!v. MEM v (fn_ir_vars f.lf_fn) ==>
    FLOOKUP t.vs_vars v = FLOOKUP f.lf_tgt.vs_vars v) ==>
  ld_vars P A (f with <|lf_src := s; lf_tgt := t|>)
Proof
  strip_tac >> gvs[ld_vars_def] >> rpt conj_tac
  >- (simp[fmap_eq_flookup, FLOOKUP_DRESTRICT] >> gen_tac >>
      Cases_on `x IN set (fn_ir_vars f.lf_fn)` >> simp[] >>
      Cases_on `x IN FDOM f.lf_src.vs_vars` >> gvs[SUBSET_DEF] >>
      metis_tac[FLOOKUP_DRESTRICT, fmap_eq_flookup])
  >- (rpt strip_tac >> first_x_assum drule >>
      Cases_on `v IN FDOM t.vs_vars` >>
      Cases_on `v IN FDOM f.lf_tgt.vs_vars` >> simp[FLOOKUP_DEF])
  >> rpt strip_tac >>
  `MEM v (fn_ir_vars f.lf_fn)` by
    (gvs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_expansion_step_nonghost:
  MEM inst.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD] /\
  ld_nonghost tn s t /\ step_inst fuel C inst t = OK u ==>
  ld_nonghost tn s u /\ u.vs_params = t.vs_params /\
  u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb
Proof
  strip_tac >> gvs[MEM]
  >- (drule_all ld_alloca_step >> strip_tac >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      gvs[ld_nonghost_def]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def] >>
  simp[exec_pure2_def, exec_read1_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[update_var_def, write_memory_with_expansion_def, ld_nonghost_def]
QED

Theorem ld_expansion_prefix_nonghost:
  !h t. ld_prefix C fn X p h t0 t /\ ld_nonghost tn s t0 /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD]) X ==>
  ld_nonghost tn s t /\ t.vs_params = t0.vs_params /\
  t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb
Proof
  Induct_on `h`
  >- simp[ld_prefix_zero] >>
  rpt strip_tac >> dxrule ld_prefix_predecessor >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac)) >>
  first_x_assum drule_all >> strip_tac >>
  `MEM (EL h X).inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD]` by
    (drule ld_prefix_bound >> strip_tac >> gvs[EVERY_EL]) >>
  drule_all ld_expansion_step_nonghost >> strip_tac >>
  gvs[ld_nonghost_def]
QED

Theorem ld_dload_expansion_ghost_exit:
  X = [<|inst_id := ai; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := [a]|>;
       <|inst_id := zi; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [Var a; Var z; Lit 32w]; inst_outputs := []|>;
       <|inst_id := mi; inst_opcode := MLOAD;
         inst_operands := [Var a]; inst_outputs := [out]|>] /\
  a <> z /\ out <> a /\ out <> z /\ off <> Var a /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  eval_operand off s = SOME ow /\ eval_operand off t0 = SOME ow /\
  code_layout_valid s /\
  eval_operand (Label "code_end") s = SOME basew /\
  eval_operand (Label "code_end") t0 = SOME basew /\
  t0.vs_code = s.vs_code /\
  w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword (:256) /\
  t0.vs_inst_idx = p /\ ld_prefix C' fn' X p 3 t0 t /\
  step_inst fuel C' (EL 3 X) t = OK u /\
  f.lf_src = s /\ f.lf_tgt = t0 /\ f.lf_tv = tn.t_var /\
  ld_vars P A f /\ ld_nonghost tn s t0 /\
  MEM out (fn_ir_vars f.lf_fn) /\
  ~MEM a (fn_ir_vars f.lf_fn) /\ ~MEM z (fn_ir_vars f.lf_fn) ==>
  ?ss. step_inst 0 C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H [out] NONE;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_erase A o_f set_prov f.lf_H [out] NONE =
      step_prov PG (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_params = s.vs_params /\ ss.vs_current_bb = s.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ss.vs_inst_idx = s.vs_inst_idx /\
    u.vs_params = t0.vs_params /\ u.vs_current_bb = t0.vs_current_bb /\
    u.vs_prev_bb = t0.vs_prev_bb /\ u.vs_inst_idx = p+3 /\
    FLOOKUP u.vs_vars out = FLOOKUP ss.vs_vars out
Proof
  strip_tac >>
  drule_all ld_dload_expansion_value_exit >>
  disch_then (qspec_then `C` (qx_choose_then `ss` strip_assume_tac)) >>
  `ld_nonghost tn s t /\ t.vs_params = t0.vs_params /\
    t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb` by
    (irule ld_expansion_prefix_nonghost >> simp[] >>
     goal_assum (drule_at (Pat `ld_prefix _ _ _ _ _ _ _`)) >> simp[]) >>
  `ld_nonghost tn s u /\ u.vs_params = t.vs_params /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (irule ld_expansion_step_nonghost >> simp[] >>
     goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[]) >>
  qexists_tac `ss` >> simp[] >>
  qpat_x_assum `step_inst 0 C inst s = OK ss` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_read1_def] >>
  disch_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `update_var out w f.lf_src` >>
  simp[step_taint_def, out_taint_def, ld_erase_set_prov, step_prov_def,
       out_prov_def] >>
  conj_tac
  >- (qabbrev_tac `g = f with <|
        lf_src := update_var out w f.lf_src;
        lf_tgt := update_var out w f.lf_tgt;
        lf_H := set_prov f.lf_H [out] NONE;
        lf_tv := set_var_taint tn.t_var [out] {}|>` >>
      `ld_vars P A g` by
        (simp[Abbr `g`, update_var_def] >> irule ld_vars_write >>
         simp[set_var_taint_def, FLOOKUP_UPDATE, ld_word_agree_empty]) >>
      `ld_vars P A (g with <|lf_src := update_var out w f.lf_src;
                             lf_tgt := u|>)` suffices_by simp[Abbr `g`] >>
      irule ld_vars_observation_cong >> simp[Abbr `g`, update_var_def] >>
      gen_tac >> strip_tac >> Cases_on `v = out` >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  qpat_x_assum `ld_nonghost tn f.lf_src u` mp_tac >>
  simp[ld_nonghost_def, update_var_def, store_taint_def,
       adopt_reset_def, imm_taint_def] >> strip_tac >> gvs[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "expansion ghost boundary has hypotheses")
  [ld_vars_observation_cong, ld_expansion_step_nonghost,
   ld_expansion_prefix_nonghost, ld_dload_expansion_ghost_exit];
