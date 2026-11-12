(* Masked keyed storage updates. *)
Theory lowerDloadSafetyStorageWriteEffects
Ancestors
  lowerDloadSafetyKernel ptrDiscipline venomState vfmState
  finite_map pred_set combin list venomExecSemantics venomInst
  lowerDloadSafetyRelation memLocDefs codegenRel contextCodegenRel

Theorem ld_storage_agree_update:
  storage_agree_except X st st' /\ word_agree_except M x y ==>
  storage_agree_except (key_update X key M)
    (update_storage key x st) (update_storage key y st')
Proof
  simp[storage_agree_except_def, word_agree_except_def,
       key_taint_def, key_update_def, update_storage_def] >>
  rpt strip_tac >> Cases_on `k = key` >> gvs[APPLY_UPDATE_THM]
QED

Theorem ld_nonghost_sstore:
  ld_nonghost tn s t /\ word_agree_except M x y ==>
  ld_nonghost (tn with t_stor := key_update tn.t_stor key M)
    (sstore key x s) (sstore key y t)
Proof
  simp[ld_nonghost_def, sstore_def, lookup_account_def] >>
  strip_tac >>
  qpat_assum `!a. (_ with storage := _) = _ /\ _`
    (qspec_then `t.vs_call_ctx.cc_address` strip_assume_tac) >>
  gvs[account_state_component_equality] >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `a = t.vs_call_ctx.cc_address` >>
  gvs[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[ld_storage_agree_update]
QED

Theorem ld_nonghost_tstore:
  ld_nonghost tn s t /\ word_agree_except M x y ==>
  ld_nonghost (tn with t_trans := key_update tn.t_trans key M)
    (tstore key x s) (tstore key y t)
Proof
  simp[ld_nonghost_def, tstore_def] >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >>
  Cases_on `a = t.vs_call_ctx.cc_address` >>
  gvs[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[ld_storage_agree_update]
QED

Theorem ld_storage_write_step[local]:
  (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) /\
  inst.inst_operands = [a;v] /\ ~s.vs_call_ctx.cc_static /\
  eval_operand a s = SOME key /\ eval_operand v s = SOME x ==>
  step_inst_base inst s = OK
    (if inst.inst_opcode = SSTORE then sstore key x s else tstore key x s)
Proof
  strip_tac >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_write2_def, eval_operands_def]
QED

Theorem ld_storage_write_taint[local]:
  (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) /\
  inst.inst_operands = [a;v] /\ inst.inst_outputs = [] /\
  eval_operand a s = SOME key ==>
  step_taint inst s
    (if inst.inst_opcode = SSTORE then sstore key x s else tstore key x s) tn =
  if inst.inst_opcode = SSTORE then
    tn with t_stor := key_update tn.t_stor key (op_taint tn v)
  else tn with t_trans := key_update tn.t_trans key (op_taint tn v)
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       new_site_bytes_def, source_memory_write_ranges_def, range_bytes_def,
       sstore_def, tstore_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       FLOOKUP_DEF, DRESTRICT_UNIV] >> SET_TAC[]
QED

Theorem ld_storage_write_effect:
  ld_vars P A f /\ tn.t_var = f.lf_tv /\
  (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) /\
  inst.inst_operands = [a;v] /\ inst.inst_outputs = [] /\
  eval_operand a f.lf_src = SOME key /\
  eval_operand a f.lf_tgt = SOME key /\
  eval_operand v f.lf_src = SOME x /\
  eval_operand v f.lf_tgt = SOME y /\
  word_agree_except (op_taint tn v) x y /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
      (ld_erase A o_f f.lf_H) inst ss = ld_erase A o_f f.lf_H /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ss.vs_labels = f.lf_src.vs_labels /\
    ss.vs_return_pc_token = f.lf_src.vs_return_pc_token /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx /\
    ts.vs_labels = f.lf_tgt.vs_labels /\
    ts.vs_return_pc_token = f.lf_tgt.vs_return_pc_token
Proof
  strip_tac >>
  `~f.lf_tgt.vs_call_ctx.cc_static` by
    (spose_not_then strip_assume_tac >>
     qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >> gvs[eval_operands_def]) >>
  `~f.lf_src.vs_call_ctx.cc_static` by fs[ld_nonghost_def] >>
  `step_inst_base inst f.lf_src = OK
    (if inst.inst_opcode = SSTORE then sstore key x f.lf_src
     else tstore key x f.lf_src)` by (irule ld_storage_write_step >> simp[]) >>
  `step_inst_base inst f.lf_tgt = OK
    (if inst.inst_opcode = SSTORE then sstore key y f.lf_tgt
     else tstore key y f.lf_tgt)` by (irule ld_storage_write_step >> simp[]) >>
  `step_taint inst f.lf_src
    (if inst.inst_opcode = SSTORE then sstore key x f.lf_src
     else tstore key x f.lf_src) tn =
    (if inst.inst_opcode = SSTORE then
       tn with t_stor := key_update tn.t_stor key (op_taint tn v)
     else tn with t_trans := key_update tn.t_trans key (op_taint tn v))` by
    (irule ld_storage_write_taint >> simp[]) >>
  qexists_tac `if inst.inst_opcode = SSTORE then sstore key x f.lf_src
              else tstore key x f.lf_src` >>
  gvs[] >>
  (conj_tac >- gvs[ld_vars_def, sstore_def, tstore_def] >>
   conj_tac >- (gvs[ld_memory_def, sstore_def, tstore_def] >> metis_tac[]) >>
   conj_tac >- metis_tac[ld_nonghost_sstore, ld_nonghost_tstore] >>
   simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, sstore_def, tstore_def])
QED
