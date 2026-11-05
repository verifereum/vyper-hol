Theory lowerDloadSafetyCreate
Ancestors
  lowerDloadExternalBoundary lowerDloadSafetyHashLog
  lowerDloadOracleCallAssembly lowerDloadSafetyUpdates lowerDloadSafetyKernel
  ptrDiscipline venomExecSemantics venomCallOracleDefs venomState
  codegenRel contextCodegenRel memLocDefs finite_map pred_set list words

(* Separate request observation from the finite CREATE outcome consumption. *)
Theorem ld_create_exec_steps:
  venom_create_request s value off sz salt = rq /\
  venom_create_request t value off' sz salt = rq /\
  s.vs_outcomes = t.vs_outcomes /\
  exec_create inst t value off' sz salt = OK ts ==>
  ?out w ss rs rt. inst.inst_outputs = [out] /\
    consume_create_outcome rq s = (w,rs) /\
    consume_create_outcome rq t = (w,rt) /\
    ss = update_var out w rs /\ ts = update_var out w rt /\
    exec_create inst s value off sz salt = OK ss
Proof
  strip_tac >>
  qpat_x_assum `exec_create _ t _ _ _ _ = _` mp_tac >>
  simp[exec_create_def, Excl "consume_create_outcome_eq", AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `consume_create_outcome rq s` >>
  Cases_on `consume_create_outcome rq t` >>
  gvs[Excl "consume_create_outcome_eq"] >>
  `q = q'` by gvs[consume_create_outcome_eq] >>
  simp[]
QED

Theorem ld_create_taint:
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  ss.vs_allocas = s.vs_allocas /\ ss.vs_fmp = s.vs_fmp ==>
  step_taint inst s ss tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  gvs[step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
      range_bytes_def, source_memory_write_ranges_def, store_taint_def,
      adopt_reset_def, imm_taint_def, written_taint_def,
      taint_component_equality] >>
  rpt (CASE_TAC >> gvs[]) >>
  simp[FLOOKUP_DEF] >> SET_TAC[]
QED

Theorem ld_create_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  MEM inst (fn_insts f.lf_fn) /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  venom_create_request f.lf_src value off sz salt = rq /\
  venom_create_request f.lf_tgt value off' sz salt = rq /\
  exec_create inst f.lf_tgt value off' sz salt = OK ts ==>
  ?ss. exec_create inst f.lf_src value off sz salt = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    step_prov PG (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `f.lf_src.vs_outcomes = f.lf_tgt.vs_outcomes` by fs[ld_nonghost_def] >>
  drule_all ld_create_exec_steps >> strip_tac >>
  `w = w /\ ld_memory lo A tn rs rt /\ ld_nonghost tn rs rt /\
   rs.vs_vars = f.lf_src.vs_vars /\ rt.vs_vars = f.lf_tgt.vs_vars /\
   rs.vs_allocas = f.lf_src.vs_allocas /\ rt.vs_allocas = f.lf_tgt.vs_allocas /\
   rs.vs_alloca_next = f.lf_src.vs_alloca_next /\ rt.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
   rs.vs_current_bb = f.lf_src.vs_current_bb /\ rt.vs_current_bb = f.lf_tgt.vs_current_bb /\
   rs.vs_prev_bb = f.lf_src.vs_prev_bb /\ rt.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
   rs.vs_inst_idx = f.lf_src.vs_inst_idx /\ rt.vs_inst_idx = f.lf_tgt.vs_inst_idx` by
    (irule ld_consume_create_effect >> metis_tac[]) >>
  `rs.vs_fmp = f.lf_src.vs_fmp` by gvs[consume_create_outcome_eq] >>
  `step_taint inst f.lf_src (update_var out w rs) tn =
   tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst f.lf_src)` by
    (irule ld_create_taint >> simp[update_var_def]) >>
  qexists `update_var out w rs` >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >-
    (`rs.vs_params = f.lf_src.vs_params /\ rt.vs_params = f.lf_tgt.vs_params` by
       gvs[consume_create_outcome_eq] >>
     simp[update_var_def] >> irule ld_oracle_call_vars >> simp[] >>
     (conj_tac >- (qexists `w` >> simp[])) >>
     irule ld_inst_output_ir >> qexists `inst` >> simp[])) >>
  gvs[ld_memory_def, ld_nonghost_def, update_var_def,
      step_prov_def, ld_erase_set_prov, out_prov_def] >> metis_tac[]
QED

Theorem ld_create_observed_bytes:
  ld_memory lo A tn s t /\
  access_ok lo (ld_erase A o_f H) fn inst s /\
  taint_ok fn tn inst s /\ ~about_to_revert fn inst s /\
  ~in_revert_forward fn s /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;off;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;off;len;salt])) /\
  eval_operand value s = SOME v /\
  (inst.inst_opcode = CREATE2 ==> ?sw. eval_operand salt s = SOME sw) /\
  eval_operand off s = SOME x /\ eval_operand len s = SOME n /\
  (op_prov H off = NONE ==> x = y) /\
  (!k. op_prov H off = SOME k ==> ld_wordrel A (SOME k) x y) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  read_memory (w2n x) (w2n n) s = read_memory (w2n y) (w2n n) t
Proof
  strip_tac >> (gvs[] >>
  `mem_read_ops inst = SOME <|iao_ofst := off; iao_size := SOME len;
                             iao_max_size := SOME len|>` by
    simp[mem_read_ops_def] >>
  `MEM (w2n x,w2n n) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  irule ld_observed_memory_read >> simp[] >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`H`,`fn`,`lo`,`tn`] >> simp[])
QED
