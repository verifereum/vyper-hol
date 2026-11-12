(* ILOAD observes ordinary memory, with a statically scalar offset. *)
Theory lowerDloadSafetyIloadEffects
Ancestors
  lowerDloadSafetyKernel lowerDloadSafetyBytes lowerDloadSafetyReadSteps
  lowerDloadSafetyMemoryReadSteps lowerDloadSafetyUpdates lowerDloadSafetyValues
  ptrDiscipline venomExecSemantics venomState venomInst unitShapeDefs
  memLocDefs codegenRel contextCodegenRel pointerConfinedDefs finite_map list pred_set words

Theorem ld_iload_operands[local]:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\
  f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = ILOAD ==>
  eval_operands inst.inst_operands f.lf_src =
  eval_operands inst.inst_operands f.lf_tgt
Proof
  strip_tac >> irule ld_vars_numeric_operands_equal >> simp[] >>
  reverse conj_tac >- (qexists_tac `tn` >> simp[]) >>
  qexistsl_tac [`A`, `P`] >> simp[] >>
  gen_tac >> strip_tac >> conj_tac >- metis_tac[ld_inst_input_ir] >>
  gvs[fn_ptr_ok_def] >> metis_tac[]
QED

Theorem ld_iload_vars[local]:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\
  f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = ILOAD /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)) ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs (out_taint tn inst f.lf_src) |> )
Proof
  strip_tac >> drule_all ld_iload_operands >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rename1 `eval_operand op1 f.lf_tgt = SOME addr` >>
  `eval_operand op1 f.lf_src = SOME addr` by
    gvs[eval_operands_def, AllCaseEqs()] >>
  `op_prov f.lf_H op1 = NONE` by
    (irule ld_vars_nonpointer_provenance >> simp[] >>
     qexistsl_tac [`A`, `P`] >> simp[] >>
     gvs[fn_ptr_ok_def] >> metis_tac[MEM]) >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n addr))
    (mload (w2n addr) f.lf_src) (mload (w2n addr) f.lf_tgt)` by
    (irule ld_memory_mload_access >> simp[] >>
     qexistsl_tac [`A`, `f.lf_H`, `f.lf_fn`, `inst`, `lo`] >>
     simp[mem_read_ops_def, source_memory_read_ranges_def, eval_operand_def] >>
     metis_tac[]) >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def] >>
  pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE, out_taint_def] >>
  irule ld_inst_output_ir >> metis_tac[MEM]
QED

Theorem ld_iload_effect:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\
  f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = ILOAD /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)) ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE =
      step_prov PG (ld_erase A o_f f.lf_H) inst ss /\
    ss.vs_allocas = f.lf_src.vs_allocas /\
    ss.vs_alloca_next = f.lf_src.vs_alloca_next /\
    ss.vs_params = f.lf_src.vs_params /\
    ss.vs_current_bb = f.lf_src.vs_current_bb /\
    ss.vs_prev_bb = f.lf_src.vs_prev_bb /\
    ss.vs_inst_idx = f.lf_src.vs_inst_idx /\
    ts.vs_allocas = f.lf_tgt.vs_allocas /\
    ts.vs_alloca_next = f.lf_tgt.vs_alloca_next /\
    ts.vs_params = f.lf_tgt.vs_params /\
    ts.vs_current_bb = f.lf_tgt.vs_current_bb /\
    ts.vs_prev_bb = f.lf_tgt.vs_prev_bb /\
    ts.vs_inst_idx = f.lf_tgt.vs_inst_idx
Proof
  strip_tac >> drule_all ld_iload_vars >> strip_tac >>
  `MEM inst.inst_opcode [MLOAD;ILOAD]` by simp[] >>
  drule_all ld_memory_read_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_memory_read_success >> strip_tac >> gvs[] >>
  `step_taint inst f.lf_src (update_var out x f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs
       (out_taint tn inst f.lf_src)` by
    (irule ld_memory_read_taint >> simp[MEM]) >>
  simp[] >>
  conj_tac >- (irule ld_memory_update_var >> simp[]) >>
  conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
  simp[ld_erase_set_prov, step_prov_def, out_prov_def, update_var_def]
QED
