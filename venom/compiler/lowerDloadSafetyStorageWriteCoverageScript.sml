Theory lowerDloadSafetyStorageWriteCoverage
Ancestors
  lowerDloadSafetyStorageWriteEffects lowerDloadSafetyOrdinaryCoverage
  lowerDloadOracleCallAssembly lowerDloadSafetyWriteAssembly
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyValues
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadSafetyAmbient
  ptrDiscipline venomWf memLocDefs pointerConfinedDefs venomExecSemantics
  venomState venomInst finite_map pred_set list

Theorem ld_storage_operand_observation[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ MEM inst.inst_opcode [SSTORE;TSTORE] /\
  MEM op inst.inst_operands /\ tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y ==>
  word_agree_except (op_taint tn op) x y
Proof
  strip_tac >>
  `!v. op = Var v ==> v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> disch_tac >> irule ld_ptr_use_scalar >>
     simp[] >> qexists_tac `inst` >> gvs[MEM, mem_read_ops_def, mem_write_ops_def,
       is_pointer_preserving_op_def]) >>
  `op_prov f.lf_H op = NONE` by metis_tac[ld_vars_nonpointer_provenance] >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >>
     simp[] >> qexists_tac `inst` >> gvs[MEM]) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
      ld_word_agree_empty] >>
  drule_all ld_vars_value >> simp[]
QED

Theorem ld_storage_operands[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\ inst_wf inst /\
  MEM inst (fn_insts f.lf_fn) /\ MEM inst.inst_opcode [SSTORE;TSTORE] /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?a v key x y. inst.inst_operands = [a;v] /\ inst.inst_outputs = [] /\
    eval_operand a f.lf_src = SOME key /\ eval_operand a f.lf_tgt = SOME key /\
    eval_operand v f.lf_src = SOME x /\ eval_operand v f.lf_tgt = SOME y /\
    word_agree_except (op_taint tn v) x y
Proof
  strip_tac >>
  `LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = []` by
    (fs[inst_wf_def] >> rpt strip_tac >> gvs[] >>
     Cases_on `inst.inst_outputs` >> gvs[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> rename1 `inst.inst_operands = [a;v]` >>
  `?key y. eval_operand a f.lf_tgt = SOME key /\
           eval_operand v f.lf_tgt = SOME y` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >>
     simp[exec_write2_def, eval_operands_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  `?src_key. eval_operand a f.lf_src = SOME src_key` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  `?x. eval_operand v f.lf_src = SOME x` by
    (irule ld_write_operand_defined >> simp[] >> conj_tac
     >- (qexists_tac `inst` >> simp[]) >> metis_tac[]) >>
  `op_taint tn a = {}` by
    (spose_not_then assume_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     pure_rewrite_tac[taint_ok_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspec_then `a` mp_tac) >> gvs[MEM]) >>
  `word_agree_except (op_taint tn a) src_key key` by
    (irule ld_storage_operand_observation >> metis_tac[MEM]) >>
  `word_agree_except (op_taint tn v) x y` by
    (irule ld_storage_operand_observation >> metis_tac[MEM]) >>
  gvs[ld_word_agree_empty]
QED

Theorem ld_sync_storage_write_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  MEM inst.inst_opcode [SSTORE;TSTORE] /\
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
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_shape_ok fn /\ fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  `MEM inst.inst_opcode [SSTORE;TSTORE]` by simp[] >>
  drule_all ld_storage_operands >> strip_tac >>
  (Q.SUBGOAL_THEN `inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE`
    assume_tac >- gvs[MEM]) >>
  drule_all ld_storage_write_effect >> strip_tac >>
  qexistsl_tac [`ss`,`f.lf_H`] >>
  simp[] >>
  `f with <|lf_src := ss; lf_tgt := ts; lf_H := f.lf_H;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|> =
   f with <|lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var|>` by
    simp[ld_frame_component_equality] >> simp[]
QED

Theorem ld_sync_storage_write_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  MEM inst.inst_opcode [SSTORE;TSTORE] /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ld_pair lo P names Sigma C C' vs0 (ld_image f) ti
    (ts with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_sync_storage_write_effect >> strip_tac >>
  irule ld_sync_ordinary_coverage >> metis_tac[]
QED
