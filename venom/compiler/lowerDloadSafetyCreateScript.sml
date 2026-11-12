Theory lowerDloadSafetyCreate
Ancestors
  lowerDloadExternalBoundary lowerDloadSafetyHashLog
  lowerDloadOracleCallAssembly lowerDloadSafetyUpdates lowerDloadSafetyKernel
  lowerDloadSafetyValues lowerDloadSafetyAssemblyPremises
  lowerDloadSafetyRelation lowerDloadSafetyAmbient lowerDloadSafetyAllocBounds
  ptrDiscipline venomExecSemantics venomCallOracleDefs venomState
  pointerConfinedDefs codegenRel contextCodegenRel memLocDefs finite_map pred_set list words

(* Separate request observation from the finite CREATE outcome consumption. *)
Theorem ld_create_exec_steps:
  venom_create_request s value off sz salt =
    venom_create_request t value off' sz salt /\
  s.vs_outcomes = t.vs_outcomes /\
  exec_create inst t value off' sz salt = OK ts ==>
  ?out w ss rs rt. inst.inst_outputs = [out] /\
    consume_create_outcome (venom_create_request t value off' sz salt) s = (w,rs) /\
    consume_create_outcome (venom_create_request t value off' sz salt) t = (w,rt) /\
    ss = update_var out w rs /\ ts = update_var out w rt /\
    exec_create inst s value off sz salt = OK ss
Proof
  strip_tac >>
  qpat_x_assum `exec_create _ t _ _ _ _ = _` mp_tac >>
  simp[exec_create_def, Excl "consume_create_outcome_eq", AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `consume_create_outcome (venom_create_request t value off' sz salt) s` >>
  Cases_on `consume_create_outcome (venom_create_request t value off' sz salt) t` >>
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
  venom_create_request f.lf_src value off sz salt =
    venom_create_request f.lf_tgt value off' sz salt /\
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

Theorem ld_create_scalar_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;off;len] /\
    MEM op [value;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;off;len;salt] /\
    MEM op [value;len;salt])) /\ op = Var v ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >> (
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >> disch_tac >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_use_ok_def] >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  gvs[AllCaseEqs()])
QED

Theorem ld_create_scalar_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;off;len] /\
    MEM op [value;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;off;len;salt] /\
    MEM op [value;len;salt])) ==>
  eval_operand op f.lf_src = eval_operand op f.lf_tgt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM op inst.inst_operands` by (gvs[] >> gvs[]) >>
  `!v. op = Var v ==> v NOTIN fn_pv P f.lf_fn` by
    metis_tac[ld_create_scalar_nonpointer] >>
  `op_prov f.lf_H op = NONE` by
    (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  irule ld_vars_operand_equal >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule ld_inst_input_ir >> metis_tac[]) >> conj_tac
  >- (irule ld_numeric_operand_nonopaque >> simp[] >>
      qexists `inst` >> gvs[]) >>
  `op_taint tn op = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl [`f.lf_fn`,`inst`,`f.lf_src`] >> gvs[]) >>
  gvs[op_taint_def]
QED

Theorem ld_create_dispatch:
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst_base inst t = OK ts ==>
  ?value off len salt v y n sw.
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;off;len] /\ sw = NONE) \/
     (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;off;len;salt] /\
      ?w. eval_operand salt t = SOME w /\ sw = SOME w)) /\
    eval_operand value t = SOME v /\ eval_operand off t = SOME y /\
    eval_operand len t = SOME n /\ ~t.vs_call_ctx.cc_static /\
    exec_create inst t v y n sw = OK ts
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  gvs[] >> simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_create_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?value off len salt v x y n sw.
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;off;len] /\ sw = NONE) \/
     (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;off;len;salt] /\
      ?w. eval_operand salt f.lf_src = SOME w /\ sw = SOME w)) /\
    eval_operand value f.lf_src = SOME v /\
    eval_operand off f.lf_src = SOME x /\
    eval_operand off f.lf_tgt = SOME y /\
    eval_operand len f.lf_src = SOME n /\
    (op_prov f.lf_H off = NONE ==> x = y) /\
    (!k. op_prov f.lf_H off = SOME k ==> ld_wordrel A (SOME k) x y) /\
    ~f.lf_tgt.vs_call_ctx.cc_static /\
    exec_create inst f.lf_tgt v y n sw = OK ts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_create_dispatch >> strip_tac >>
  `!op. MEM op [value;len] \/ (inst.inst_opcode = CREATE2 /\ op = salt) ==>
    eval_operand op f.lf_src = eval_operand op f.lf_tgt` by
    (rpt strip_tac >> irule ld_create_scalar_equal >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexists `inst` >> simp[] >>
     gvs[] >> metis_tac[]) >>
  `op_taint tn off = {}` by
    (irule ld_numeric_operand_untainted >>
     qexistsl [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[]) >>
  `?x. eval_operand off f.lf_src = SOME x /\
    (op_prov f.lf_H off = NONE ==> x = y) /\
    (!k. op_prov f.lf_H off = SOME k ==> ld_wordrel A (SOME k) x y)` by
    (irule ld_numeric_operand_observation >> simp[] >>
     (conj_tac >- (qexists `tn` >> simp[])) >>
     (conj_tac >- (qexists `inst` >> simp[] >>
       qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[])) >>
     qexists `P` >> simp[]) >>
  qexistsl [`value`,`off`,`len`,`salt`,`v`,`x`,`y`,`n`,`sw`] >>
  simp[] >> metis_tac[]
QED

Theorem ld_create_step:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
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
  drule_all ld_create_operands >> strip_tac >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by
    (fs[taint_ok_def] >> metis_tac[]) >>
  `~about_to_revert f.lf_fn inst f.lf_src` by
    (fs[MEM] >> gvs[about_to_revert_def]) >>
  `read_memory (w2n x) (w2n n) f.lf_src = read_memory (w2n y) (w2n n) f.lf_tgt` by
    (irule ld_create_observed_bytes >>
     qpat_assum `access_ok _ _ _ _ _` (irule_at Any) >>
     qpat_assum `taint_ok _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `venom_create_request f.lf_src v x n sw = venom_create_request f.lf_tgt v y n sw` by
    (irule ld_create_request_equal >> metis_tac[]) >>
  drule_all ld_create_effect >> disch_then (qspec_then `PG` strip_assume_tac) >>
  qexists `ss` >> simp[] >>
  `f.lf_src.vs_call_ctx = f.lf_tgt.vs_call_ctx` by fs[ld_nonghost_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  gvs[] >> simp[eval_operands_def]
QED

Theorem ld_sync_create_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  ptr_discipline lo C vs0 /\ mem_inv dload_headroom_ok C vs0 /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb /\
    ss.vs_inst_idx = s.vs_inst_idx /\ ts.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ld_sync_access_ok, ld_sync_taint_ok] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_sync_active >> simp[] >> strip_tac >>
     metis_tac[ld_alloc_target_no_wrap, HD]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  gvs[step_inst_non_invoke] >>
  `tn.t_var = f.lf_tv` by simp[] >>
  `MEM inst.inst_opcode [CREATE;CREATE2]` by simp[] >>
  drule_all ld_create_step >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  qexistsl [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[] >>
  qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
  gen_tac >> strip_tac >> irule ld_set_prov_selected >>
  qexistsl [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]
QED

val _ = if null (hyp ld_sync_create_effect) then ()
        else raise Fail "CREATE producer has hypotheses";
