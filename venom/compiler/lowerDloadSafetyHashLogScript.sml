Theory lowerDloadSafetyHashLog
Ancestors
  lowerDloadOracleCallAssembly lowerDloadSafetyPublicCopy lowerDloadSafetyWriteAssembly
  lowerDloadSafetyUpdates lowerDloadSafetyValues lowerDloadSafetyKernel
  lowerDloadSafetyAmbient lowerDloadSafetyAssemblyPremises lowerDloadSafetyAllocBounds
  o1LowerDloadOpaque o1LowerDloadJointInternalEffects
  lowerDloadSafetyRelation ptrDiscipline venomExecSemantics venomState
  venomInst venomWf codegenRel contextCodegenRel memLocDefs pointerConfinedDefs finite_map pred_set list words

(* Operational boundary: the bytes are precisely those consumed by SHA3. *)
Theorem ld_sha3_steps:
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [off;len] /\
  eval_operand off s = SOME x /\ eval_operand off t = SOME y /\
  eval_operand len s = eval_operand len t /\
  (!n. eval_operand len s = SOME n ==>
    TAKE (w2n n) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n n) 0w) =
    TAKE (w2n n) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n n) 0w)) /\
  step_inst_base inst t = OK ts ==>
  ?out h. inst.inst_outputs = [out] /\ ts = update_var out h t /\
    step_inst_base inst s = OK (update_var out h s)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst t = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> metis_tac[]
QED

Theorem ld_sha3_taint:
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [off;len] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, written_taint_def, FLOOKUP_DEF,
       taint_component_equality] >> SET_TAC[]
QED

Theorem ld_sha3_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  MEM inst (fn_insts f.lf_fn) /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [off;len] /\
  eval_operand off f.lf_src = SOME x /\ eval_operand off f.lf_tgt = SOME y /\
  eval_operand len f.lf_src = eval_operand len f.lf_tgt /\
  (!n. eval_operand len f.lf_src = SOME n ==>
    TAKE (w2n n) (DROP (w2n x) f.lf_src.vs_memory ++ REPLICATE (w2n n) 0w) =
    TAKE (w2n n) (DROP (w2n y) f.lf_tgt.vs_memory ++ REPLICATE (w2n n) 0w)) /\
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
  drule_all ld_sha3_steps >> strip_tac >>
  `step_taint inst f.lf_src (update_var out h f.lf_src) tn =
   tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst f.lf_src)` by
    (irule ld_sha3_taint >> simp[]) >>
  qexists `update_var out h f.lf_src` >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (simp[update_var_def] >> irule ld_vars_write >>
     simp[set_var_taint_def, FLOOKUP_UPDATE, word_agree_except_def] >>
     irule ld_inst_output_ir >> qexists `inst` >> simp[])) >>
  gvs[ld_memory_def, ld_nonghost_def, update_var_def,
      step_prov_def, ld_erase_set_prov, out_prov_def] >> metis_tac[]
QED

Theorem ld_sha3_length_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [off;len] /\
  len = Var v ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >> disch_tac >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_use_ok_def] >>
  disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `v` mp_tac)) >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `off = Var v` >> gvs[AllCaseEqs()]
QED

Theorem ld_sha3_length_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [off;len] ==>
  eval_operand len f.lf_src = eval_operand len f.lf_tgt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `MEM len inst.inst_operands` by simp[] >>
  `!v. len = Var v ==> v NOTIN fn_pv P f.lf_fn` by
    metis_tac[ld_sha3_length_nonpointer] >>
  `op_prov f.lf_H len = NONE` by
    (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  irule ld_vars_operand_equal >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule ld_inst_input_ir >> metis_tac[]) >> conj_tac
  >- (irule ld_numeric_operand_nonopaque >> simp[] >>
      qexists `inst` >> simp[]) >>
  `op_taint tn len = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[]) >>
  gvs[op_taint_def]
QED

Theorem ld_sha3_target_shape:
  inst.inst_opcode = SHA3 /\ step_inst_base inst t = OK ts ==>
  ?off len y n. inst.inst_operands = [off;len] /\
    eval_operand off t = SOME y /\ eval_operand len t = SOME n
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst t = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_sha3_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)) /\
  inst.inst_opcode = SHA3 /\ step_inst_base inst f.lf_tgt = OK ts ==>
  ?off len x y. inst.inst_operands = [off;len] /\
    eval_operand off f.lf_src = SOME x /\ eval_operand off f.lf_tgt = SOME y /\
    eval_operand len f.lf_src = eval_operand len f.lf_tgt /\
    (!n. eval_operand len f.lf_src = SOME n ==>
      TAKE (w2n n) (DROP (w2n x) f.lf_src.vs_memory ++ REPLICATE (w2n n) 0w) =
      TAKE (w2n n) (DROP (w2n y) f.lf_tgt.vs_memory ++ REPLICATE (w2n n) 0w))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_sha3_target_shape >> strip_tac >>
  `?x. eval_operand off f.lf_src = SOME x` by
    (irule ld_write_operand_defined >> simp[] >>
     conj_tac >- (qexists `inst` >> simp[]) >> metis_tac[]) >>
  `eval_operand len f.lf_src = eval_operand len f.lf_tgt` by
    (irule ld_sha3_length_equal >> simp[] >>
     conj_tac >- metis_tac[] >> qexistsl [`inst`,`off`,`tn`] >> simp[]) >>
  `op_taint tn off = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[]) >>
  `(op_prov f.lf_H off = NONE ==> x = y) /\
   (!k. op_prov f.lf_H off = SOME k ==> ld_wordrel A (SOME k) x y)` by
    (irule ld_write_address_observation >> simp[] >>
     conj_tac >- (qexists `tn` >> simp[]) >>
     conj_tac >- (qexists `inst` >> simp[]) >> metis_tac[]) >>
  `~about_to_revert f.lf_fn inst f.lf_src` by simp[about_to_revert_def] >>
  `eval_operand len f.lf_src = SOME n` by simp[] >>
  drule_all ld_sha3_observed_bytes >> disch_tac >>
  qexistsl [`off`,`len`,`x`,`y`] >> simp[]
QED

Theorem ld_sync_sha3_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ~in_revert_forward fn s /\ t.vs_alloca_next < dimword(:256) /\
  inst.inst_opcode = SHA3 /\ step_inst fuel C' inst t = OK ts ==>
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `access_ok lo G fn inst s` by metis_tac[ld_sync_access_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    (qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ld_sync_def] >> simp[EVERY_MEM] >>
     strip_tac >> metis_tac[]) >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[] >> metis_tac[]) >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  drule_all ld_sha3_operands >> strip_tac >>
  drule_all ld_sha3_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  qexistsl [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >> simp[] >>
  qpat_assum `FDOM A = ld_slots A (f::fs)`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  gen_tac >> strip_tac >> irule ld_set_prov_selected >>
  qexistsl [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]
QED

Theorem ld_log_steps:
  inst.inst_opcode = LOG /\ s.vs_call_ctx = t.vs_call_ctx /\
  (!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))) /\
  step_inst_base inst t = OK ts ==>
  ?ss logs logt. step_inst_base inst s = OK ss /\
    ss = s with vs_logs := logs /\ ts = t with vs_logs := logt
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> simp[]) >>
  qpat_x_assum `step_inst_base inst t = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `?a b tail. REVERSE rest = a::b::tail` by
    (`2 <= LENGTH (REVERSE rest)` by simp[] >>
     Cases_on `REVERSE rest` >> gvs[] >>
     rename1 `2 <= SUC (LENGTH tail)` >> Cases_on `tail` >> gvs[]) >>
  `MEM a rest /\ MEM b rest /\ (!op. MEM op tail ==> MEM op rest)` by
    (pure_once_rewrite_tac[GSYM MEM_REVERSE] >>
     qpat_assum `REVERSE rest = _` (fn th => pure_rewrite_tac[th, MEM]) >>
     metis_tac[MEM_REVERSE]) >>
  `IS_SOME (eval_operand a s) /\ IS_SOME (eval_operand b s)` by
    (gvs[] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  `IS_SOME (eval_operands tail t)` by gvs[] >>
  `IS_SOME (eval_operands tail s)` by
    (gvs[ld_eval_operands_defined, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand b s` >> gvs[] >>
  Cases_on `eval_operands tail s` >> gvs[] >>
  simp[venom_state_component_equality] >> metis_tac[optionTheory.IS_SOME_DEF]
QED

Theorem ld_log_taint:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] ==>
  step_taint inst s (s with vs_logs := logs) tn = tn
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- simp[written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- simp[written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- simp[written_taint_def] >>
     Cases_on `more` >> simp[written_taint_def]) >>
  simp[step_taint_def, mem_taint_def, set_var_taint_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, FLOOKUP_DEF, DRESTRICT_UNIV,
       taint_component_equality] >> SET_TAC[]
QED

Theorem ld_log_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_outputs = [] /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt /\
  inst.inst_opcode = LOG /\ step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := f.lf_H;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase A o_f f.lf_H /\
    ss.vs_allocas = f.lf_src.vs_allocas /\ ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\ ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\ ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\ ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\ ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `f.lf_src.vs_call_ctx = f.lf_tgt.vs_call_ctx` by fs[ld_nonghost_def] >>
  `!op. MEM op inst.inst_operands ==>
    (IS_SOME (eval_operand op f.lf_src) <=> IS_SOME (eval_operand op f.lf_tgt))` by
    (rpt strip_tac >> irule ld_vars_operand_defined >> simp[] >>
     conj_tac >- (rpt strip_tac >> metis_tac[ld_inst_input_ir]) >>
     metis_tac[]) >>
  drule_all ld_log_steps >> strip_tac >>
  `step_taint inst f.lf_src (f.lf_src with vs_logs := logs) tn = tn` by
    (irule ld_log_taint >> simp[]) >>
  qexists `ss` >>
  gvs[ld_vars_def, ld_memory_def, ld_nonghost_def,
      step_prov_def, set_prov_def, DRESTRICT_UNIV] >> metis_tac[]
QED

Theorem ld_sync_log_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  inst.inst_opcode = LOG /\ step_inst fuel C' inst t = OK ts ==>
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `inst_wf inst` by
    (drule ld_sync_source >> simp[active_inst_def] >> strip_tac >>
     fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by
    (fs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  drule_all ld_log_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  qexistsl [`ss`,`f.lf_H`] >> simp[]
QED

val _ = if List.all (null o hyp)
  [ld_sync_sha3_effect, ld_sync_log_effect, ld_log_steps, ld_sha3_effect]
  then () else raise Fail "hash/log effects have hypotheses";
