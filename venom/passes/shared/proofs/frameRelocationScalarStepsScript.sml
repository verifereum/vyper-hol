Theory frameRelocationScalarSteps
Ancestors frameRelocationGuardedValues frameRelocationGhostCopy
  frameRelocationLocal frameRelocationValues frameOriginUpdates
  venomExecSemantics venomState ptrDiscipline finite_map pred_set

Theorem guarded_equal_write:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  (!a b x. Obs a b ==> Obs (update_var v x a) (update_var v x b)) ==>
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) R Obs
    (update_var v z s) (update_var v z t)
Proof
  strip_tac >> irule local_rel_update_observation_invariant >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, op_taint_def, FLOOKUP_UPDATE, word_agree_except_def] >>
  qexistsl_tac [`guarded_bytes Opaque rv tn`, `\u. F`, `guarded_ptr Opaque L rv`] >>
  simp[guarded_ptr_other, guarded_bytes_other] >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, op_taint_def, FLOOKUP_UPDATE, word_agree_except_def]
QED

Theorem guarded_purebinary:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [v] /\
  s.vs_labels = t.vs_labels /\
  (!w. a = Var w \/ b = Var w ==> clean_scalar Opaque rv tn w) /\
  (!s t v x. Obs s t ==> Obs (update_var v x s) (update_var v x t)) /\
  exec_pure2 f inst s = OK s' ==>
  ?x y. eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
    eval_operand a t = SOME x /\ eval_operand b t = SOME y /\
    s' = update_var v (f x y) s /\
    exec_pure2 f inst t = OK (update_var v (f x y) t) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (tn with t_var := tn.t_var |+ (v,{}))) R Obs
      s' (update_var v (f x y) t)
Proof
  strip_tac >>
  `eval_operand a s = eval_operand a t` by
    (irule guarded_scalar_operand >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand b s = eval_operand b t` by
    (irule guarded_scalar_operand >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  irule guarded_equal_write >> goal_assum (drule_at Any) >> simp[]
QED

(* Clean scalar binary family; shifts have a distinct taint rule. *)
Definition scalar_binary_opcode_def:
  scalar_binary_opcode opc <=>
    MEM opc [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp;
             EQ; LT; GT; SLT; SGT; AND; OR; XOR; SIGNEXTEND; BYTE]
End

Theorem scalar_binary_dispatch:
  scalar_binary_opcode inst.inst_opcode ==>
  ?f. !s. step_inst_base inst s = exec_pure2 f inst s
Proof
  simp[scalar_binary_opcode_def] >> strip_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> metis_tac[]
QED

Theorem scalar_binary_prov_erasure:
  scalar_binary_opcode inst.inst_opcode /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [v] /\
  (!w. a = Var w \/ b = Var w ==> FLOOKUP rv w = NONE) ==>
  step_prov PG (SND o_f rv) inst s' =
    SND o_f (origin_set rv [v] NONE)
Proof
  strip_tac >>
  `op_prov (SND o_f rv) a = NONE /\ op_prov (SND o_f rv) b = NONE` by
    (Cases_on `a` >> Cases_on `b` >>
     simp[op_prov_def, FLOOKUP_o_f] >> metis_tac[]) >>
  gvs[scalar_binary_opcode_def] >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       origin_set_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  qx_gen_tac `u` >> Cases_on `u = v` >> simp[]
QED

Theorem scalar_binary_update_taint:
  scalar_binary_opcode inst.inst_opcode /\ inst.inst_outputs = [v] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,out_taint tn inst s)
Proof
  strip_tac >>
  `{i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
       (aid IN FDOM s.vs_allocas /\ s.vs_allocas ' aid = (b,sz)) /\
       b <= i /\ i < b + sz} = {}` by (simp[EXTENSION] >> metis_tac[]) >>
  gvs[scalar_binary_opcode_def] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, update_var_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, FLOOKUP_DEF, EXTENSION] >>
  simp[taint_component_equality] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem scalar_binary_taint:
  scalar_binary_opcode inst.inst_opcode /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [v] /\
  (inst.inst_opcode = MUL ==> op_taint tn a = {} /\ op_taint tn b = {}) ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >>
  `{i | ?aid b sz. aid NOTIN FDOM s.vs_allocas /\
       (aid IN FDOM s.vs_allocas /\ s.vs_allocas ' aid = (b,sz)) /\
       b <= i /\ i < b + sz} = {}` by (simp[EXTENSION] >> metis_tac[]) >>
  gvs[scalar_binary_opcode_def] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def, update_var_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, out_taint_def,
       set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       FLOOKUP_DEF, EXTENSION] >>
  simp[taint_component_equality] >> Cases_on `eval_operand a s` >> simp[]
QED

Theorem guarded_scalar_binary_step:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  scalar_binary_opcode inst.inst_opcode /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [v] /\
  s.vs_labels = t.vs_labels /\
  (!w. a = Var w \/ b = Var w ==> clean_scalar Opaque rv tn w) /\
  (!s t v x. Obs s t ==> Obs (update_var v x s) (update_var v x t)) /\
  step_inst_base inst s = OK s' ==>
  ?t'. step_inst_base inst t = OK t' /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (step_taint inst s s' tn)) R Obs s' t' /\
    step_taint inst s s' tn = tn with t_var := tn.t_var |+ (v,{}) /\
    step_taint inst t t' tn = tn with t_var := tn.t_var |+ (v,{}) /\
    step_prov PG (SND o_f rv) inst s' =
      SND o_f (origin_set rv [v] NONE)
Proof
  strip_tac >> drule scalar_binary_dispatch >> strip_tac >>
  `op_taint tn a = {} /\ op_taint tn b = {}` by
    (Cases_on `a` >> Cases_on `b` >>
     fs[op_taint_def, clean_scalar_def] >> metis_tac[]) >>
  `exec_pure2 f inst s = OK s'` by metis_tac[] >>
  drule_all guarded_purebinary >> strip_tac >>
  `step_prov PG (SND o_f rv) inst s' =
     SND o_f (origin_set rv [v] NONE)` by
    (irule scalar_binary_prov_erasure >> simp[] >>
     metis_tac[frameRelocationGuardedValuesTheory.clean_scalar_def]) >>
  qexists_tac `update_var v (f x y) t` >>
  gvs[] >>
  `step_taint inst s (update_var v (f x y) s) tn =
     tn with t_var := tn.t_var |+ (v,{})` by
    (irule scalar_binary_taint >> simp[]) >>
  `step_taint inst t (update_var v (f x y) t) tn =
     tn with t_var := tn.t_var |+ (v,{})` by
    (irule scalar_binary_taint >> simp[]) >>
  simp[]
QED
