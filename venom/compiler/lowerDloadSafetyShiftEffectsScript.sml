(* Shifts and selector MUL retain masked data: a shift consumes an exact scalar
   cnt, a MUL an untainted 0w/1w selector. *)
Theory lowerDloadSafetyShiftEffects
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues lowerDloadSafetyRelation
  lowerDloadSafetyKernel ptrDiscipline unitShapeDefs venomState venomInst
  venomExecSemantics pointerConfinedDefs memLocDefs codegenRel
  finite_map list pred_set words

Theorem ld_shift_cnt_untainted[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [cnt;data] ==>
  op_taint tn cnt = {}
Proof
  simp[taint_ok_def] >> rpt strip_tac >>
  Cases_on `op_taint tn cnt = {}` >> simp[] >>
  qpat_x_assum `!op. _` (qspec_then `cnt` mp_tac) >> gvs[MEM]
QED

Theorem ld_shift_operand[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ MEM inst.inst_opcode [MUL; SHL; SHR; SAR] /\
  MEM op inst.inst_operands /\ eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x /\
      word_agree_except (op_taint tn op) x y
Proof
  strip_tac >>
  `!v. op = Var v ==> v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> disch_tac >> irule ld_ptr_use_scalar >>
     simp[] >> qexists_tac `inst` >> gvs[MEM] >>
     simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
  `op_prov f.lf_H op = NONE` by
    (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  `!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_input_ir] >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >>
     simp[] >> qexists_tac `inst` >> gvs[MEM] >> metis_tac[]) >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >> simp[] >> metis_tac[]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[] >>
  drule_all ld_vars_operand_agree >> simp[]
QED

Theorem ld_shift_vars[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [MUL; SHL; SHR; SAR] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs (out_taint tn inst f.lf_src) |> )
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = MUL`
  >- (qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
      pure_once_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[opcode_case_def] >>
      simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
      rename1 `eval_operand op1 f.lf_tgt = SOME y` >>
      rename1 `eval_operand op2 f.lf_tgt = SOME w` >>
      `?x. eval_operand op1 f.lf_src = SOME x /\
           word_agree_except (op_taint tn op1) x y` by
        (irule ld_shift_operand >> simp[] >>
         conj_tac >- (qexists_tac `inst` >> simp[]) >>
         qexistsl_tac [`A`, `P`] >> simp[]) >>
      `?z. eval_operand op2 f.lf_src = SOME z /\
           word_agree_except (op_taint tn op2) z w` by
        (irule ld_shift_operand >> simp[] >>
         conj_tac >- (qexists_tac `inst` >> simp[]) >>
         qexistsl_tac [`A`, `P`] >> simp[]) >>
      simp[] >> pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
      simp[set_var_taint_def, FLOOKUP_UPDATE] >>
      reverse conj_tac >- (irule ld_inst_output_ir >> metis_tac[MEM]) >>
      strip_tac >>
      Cases_on `op_taint tn op1 = {}`
      >- (Cases_on `op_taint tn op2 = {}`
          >- gvs[ld_word_agree_empty, out_taint_def] >>
          `x = 0w \/ x = 1w` by
            (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
             simp[taint_ok_def] >> strip_tac >>
             qpat_x_assum `!op. _` (qspec_then `op2` mp_tac) >>
             gvs[] >> strip_tac >> gvs[]) >>
          gvs[ld_word_agree_empty] >>
          gvs[out_taint_def, word_agree_except_def,
              wordsTheory.WORD_MULT_CLAUSES]) >>
      `op_taint tn op2 = {} /\ (z = 0w \/ z = 1w)` by
        (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
         simp[taint_ok_def] >> strip_tac >>
         qpat_x_assum `!op. _` (qspec_then `op1` mp_tac) >>
         gvs[] >> strip_tac >> gvs[]) >>
      gvs[ld_word_agree_empty] >>
      gvs[out_taint_def, word_agree_except_def,
          wordsTheory.WORD_MULT_CLAUSES]) >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  `inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR`
    by gvs[MEM] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
  (gvs[] >>
   qpat_x_assum `eval_operand op1 f.lf_tgt = SOME _` mp_tac >>
   qmatch_goalsub_rename_tac `SOME cnt_value` >> strip_tac >>
   qpat_x_assum `eval_operand op2 f.lf_tgt = SOME _` mp_tac >>
   qmatch_goalsub_rename_tac `SOME data_value` >> strip_tac >>
   `?x. eval_operand op1 f.lf_src = SOME x /\
        word_agree_except (op_taint tn op1) x cnt_value` by
     (irule ld_shift_operand >> simp[] >>
      conj_tac >- (qexists_tac `inst` >> simp[]) >>
      qexistsl_tac [`A`, `P`] >> simp[]) >>
   `?y. eval_operand op2 f.lf_src = SOME y /\
        word_agree_except (op_taint tn op2) y data_value` by
     (irule ld_shift_operand >> simp[] >>
      conj_tac >- (qexists_tac `inst` >> simp[]) >>
      qexistsl_tac [`A`, `P`] >> simp[]) >>
   `op_taint tn op1 = {}` by
     (irule ld_shift_cnt_untainted >> qexistsl_tac [`op2`, `f.lf_fn`, `inst`, `f.lf_src`] >> simp[]) >>
   gvs[ld_word_agree_empty] >>
   pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
   simp[set_var_taint_def, FLOOKUP_UPDATE, out_taint_def] >>
   reverse conj_tac >- (irule ld_inst_output_ir >> metis_tac[MEM]) >>
   strip_tac >>
   FIRST [irule word_agree_except_shl, irule word_agree_except_shr,
          irule word_agree_except_sar] >> simp[])
QED

Theorem ld_shift_success[local]:
  MEM inst.inst_opcode [MUL; SHL; SHR; SAR] /\
  step_inst_base inst s = OK s' ==>
  ?out x. inst.inst_outputs = [out] /\ s' = update_var out x s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_shift_taint[local]:
  MEM inst.inst_opcode [MUL; SHL; SHR; SAR] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  `inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> MSTORE /\
   inst.inst_opcode <> ISTORE /\ inst.inst_opcode <> SSTORE /\
   inst.inst_opcode <> TSTORE` by (gvs[MEM] >> simp[]) >>
  `written_taint tn inst s = {}` by
    (namedCases_on `inst.inst_operands` ["", "a rest"]
     >- simp[written_taint_def] >>
     namedCases_on `rest` ["", "b tail"]
     >- simp[written_taint_def] >>
     namedCases_on `tail` ["", "c more"]
     >- (gvs[MEM] >> simp[written_taint_def]) >>
     Cases_on `more` >> simp[written_taint_def]) >>
  `source_memory_write_ranges inst s = []` by
    (gvs[MEM] >> simp[source_memory_write_ranges_def]) >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, update_var_def,
       new_site_bytes_def, step_writes_def, range_bytes_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       FLOOKUP_DEF, taint_component_equality] >> SET_TAC[]
QED

Theorem ld_masked_scalar_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [MUL; SHL; SHR; SAR] /\
  step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  ld_nonghost tn f.lf_src f.lf_tgt ==>
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
  strip_tac >> drule_all ld_shift_vars >> strip_tac >>
  drule_all ld_shift_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_shift_success >> strip_tac >> gvs[] >>
  (`step_taint inst f.lf_src (update_var out x f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs
       (out_taint tn inst f.lf_src)` by
    (irule ld_shift_taint >> simp[]) >>
   simp[] >>
   conj_tac >- (irule ld_memory_update_var >> simp[]) >>
   conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
   simp[ld_erase_set_prov, step_prov_def, out_prov_def])
QED
