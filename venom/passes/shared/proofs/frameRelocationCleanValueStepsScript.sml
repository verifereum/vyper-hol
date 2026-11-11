Theory frameRelocationCleanValueSteps
Ancestors frameRelocationScalarSteps frameRelocationTaintOrder
  frameRelocationCopyTaint frameRelocationLocal frameRelocationDemand
  frameRelocationMemory frameRelocationGuardedValues frameRelocationGhostCopy
  frameOriginUpdates ptrDiscipline venomExecSemantics venomState
  finite_map pred_set words list

Definition clean_value_shape_def:
  clean_value_shape inst <=>
    ((inst.inst_opcode = ISZERO \/ inst.inst_opcode = NOT) /\
      LENGTH inst.inst_operands = 1) \/
    (scalar_binary_opcode inst.inst_opcode /\ LENGTH inst.inst_operands = 2) \/
    ((inst.inst_opcode = ADDMOD \/ inst.inst_opcode = MULMOD) /\
      LENGTH inst.inst_operands = 3)
End

Theorem relocation_clean_write_taint:
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  relocation_taint_le next (tn with t_var := tn.t_var |+ (v,{}))
    (un with t_var := un.t_var |+ (v,{}))
Proof
  simp[relocation_taint_le_def, op_taint_def, FLOOKUP_UPDATE] >>
  strip_tac >> conj_tac
  >- (fs[demand_taint_def] >> metis_tac[]) >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem guarded_clean_write_restrict:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  (!a b. next a b ==> R a b) ==>
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) next
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v z s) (update_var v z t)
Proof
  strip_tac >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) R
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v z s) (update_var v z t)` by
    (irule guarded_equal_write >> goal_assum (drule_at Any) >>
     simp[update_var_def, dead_result_rel_def]) >>
  fs[local_rel_def, demand_agree_def] >> metis_tac[]
QED

Theorem clean_value_taint:
  clean_value_shape inst /\ inst.inst_outputs = [v] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >>
  Cases_on `scalar_binary_opcode inst.inst_opcode`
  >- (`LENGTH inst.inst_operands = 2` by
        (gvs[clean_value_shape_def, scalar_binary_opcode_def]) >>
      Cases_on `inst.inst_operands` >> fs[] >>
      Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >>
      metis_tac[scalar_binary_taint]) >>
  `new_site_bytes s (update_var v x s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  fs[clean_value_shape_def] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `t'` >> fs[] >> Cases_on `t` >> fs[]
QED

Theorem clean_value_prov:
  clean_value_shape inst /\ inst.inst_outputs = [v] /\
  (!w. MEM (Var w) inst.inst_operands ==> clean_scalar Opaque rv tn w) ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE)
Proof
  strip_tac >>
  Cases_on `scalar_binary_opcode inst.inst_opcode`
  >- (`LENGTH inst.inst_operands = 2` by
        (gvs[clean_value_shape_def, scalar_binary_opcode_def]) >>
      Cases_on `inst.inst_operands` >> fs[] >>
      Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >>
      irule scalar_binary_prov_erasure >> simp[] >>
      metis_tac[clean_scalar_def]) >>
  fs[clean_value_shape_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       origin_set_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem clean_value_execution:
  clean_value_shape inst /\ inst.inst_outputs = [v] /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  s.vs_labels = t.vs_labels /\
  (!w. MEM (Var w) inst.inst_operands ==> clean_scalar Opaque rv tn w) /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule guarded_scalar_operand >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `scalar_binary_opcode inst.inst_opcode`
  >- (`LENGTH inst.inst_operands = 2` by
        (gvs[clean_value_shape_def, scalar_binary_opcode_def]) >>
      gvs[LENGTH_EQ_NUM_compute] >>
      drule scalar_binary_dispatch >> strip_tac >>
      `exec_pure2 f inst s = OK post` by metis_tac[] >>
      `eval_operand h s = eval_operand h t /\
       eval_operand h' s = eval_operand h' t` by metis_tac[] >>
      qpat_x_assum `!st. step_inst_base inst st = _` (fn th => rewrite_tac[th]) >>
      gvs[exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  fs[clean_value_shape_def] >>
  gvs[LENGTH_EQ_NUM_compute] >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> strip_tac >>
  gvs[exec_pure1_def, exec_pure3_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem guarded_clean_value_step:
  clean_value_shape inst /\ inst.inst_outputs = [v] /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  s.vs_labels = t.vs_labels /\
  (!w. MEM (Var w) inst.inst_operands ==> clean_scalar Opaque rv tn w) /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (step_taint inst s post tn)) next
      (\s t. dead_result_rel D (Halt s) (Halt t))
      post (update_var v z t) /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le next (step_taint inst s post tn)
      (step_taint inst t (update_var v z t) un)
Proof
  strip_tac >> drule_all clean_value_execution >> strip_tac >>
  qexists_tac `z` >> simp[] >>
  `step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    metis_tac[clean_value_taint] >>
  `step_taint inst t (update_var v z t) un =
     un with t_var := un.t_var |+ (v,{})` by
    metis_tac[clean_value_taint] >>
  simp[] >> conj_tac
  >- (gvs[] >> irule guarded_clean_write_restrict >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule clean_value_prov >> simp[] >>
      qexistsl_tac [`Opaque`, `tn`] >> simp[]) >>
  simp[clean_value_taint] >>
  irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]
QED
