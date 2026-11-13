(* Affine arithmetic preserves selected allocation identities modulo words. *)
Theory lowerDloadSafetyAffineEffects
Ancestors
  lowerDloadSafetyUpdates lowerDloadSafetyValues lowerDloadSafetyRelation
  lowerDloadSafetyKernel lowerDloadPointerClosure ptrDiscipline unitShapeDefs
  venomState venomInst venomExecSemantics pointerConfinedDefs
  finite_map list pred_set words unitLabelMapIdentity memLocDefs codegenRel

Theorem ld_affine_operand[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [ADD; SUB] /\ MEM op inst.inst_operands /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x /\
    ld_wordrel A (op_prov f.lf_H op) x y
Proof
  strip_tac >>
  `!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_input_ir] >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >>
     simp[] >> qexists_tac `inst` >> gvs[MEM] >> metis_tac[]) >>
  `op_taint tn op = {}` by
    (irule ld_numeric_operand_untainted >>
     qexistsl_tac [`f.lf_fn`, `inst`, `f.lf_src`] >> gvs[MEM]) >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >> simp[] >> metis_tac[]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[] >>
  drule_all ld_vars_operand_agree >>
  Cases_on `op_prov f.lf_H op` >> simp[ld_wordrel_def, ld_word_agree_empty]
QED

Theorem ld_affine_restriction[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [a;b] ==>
  ~(?v w. a = Var v /\ b = Var w /\
       v IN fn_pv P fn /\ w IN fn_pv P fn) /\
  (inst.inst_opcode = SUB ==> !v. b = Var v ==> v NOTIN fn_pv P fn)
Proof
  simp[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def, fn_insts_MEM] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem ld_affine_provenance[local]:
  ld_vars P A f /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ MEM inst.inst_opcode [ADD; SUB] /\
  inst.inst_operands = [a;b] ==>
  (op_prov f.lf_H a <> NONE ==> op_prov f.lf_H b = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov f.lf_H b = NONE)
Proof
  strip_tac >> drule_all ld_affine_restriction >> strip_tac >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[op_prov_def, ld_vars_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_affine_selected_output[local]:
  ld_vars P A f /\ MEM inst (fn_insts f.lf_fn) /\
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [a;b] /\
  MEM out inst.inst_outputs /\ first_prov f.lf_H [a;b] = SOME k ==>
  out IN fn_pv P f.lf_fn
Proof
  strip_tac >>
  `?v. MEM (Var v) [a;b] /\ v IN fn_pv P f.lf_fn` by
    (Cases_on `a` >> Cases_on `b` >>
     gvs[first_prov_def, op_prov_def, AllCaseEqs(), ld_vars_def,
         SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[fn_pv_def] >> irule ld_pointer_preserving_output >>
  qexistsl_tac [`inst`, `v`] >> gvs[MEM, is_pointer_preserving_op_def]
QED

Theorem ld_affine_vars:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [ADD; SUB] /\
  step_inst_base inst f.lf_tgt = OK ts ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs
        (first_prov f.lf_H inst.inst_operands);
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {} |> )
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB` by gvs[MEM] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
  (gvs[] >>
   `?x. eval_operand op1 f.lf_src = SOME x /\
        ld_wordrel A (op_prov f.lf_H op1) x v1` by
     (irule ld_affine_operand >> simp[] >> conj_tac
      >- metis_tac[] >> qexistsl_tac [`inst`, `tn`] >> simp[]) >>
   `?y. eval_operand op2 f.lf_src = SOME y /\
        ld_wordrel A (op_prov f.lf_H op2) y v2` by
     (irule ld_affine_operand >> simp[] >> conj_tac
      >- metis_tac[] >> qexistsl_tac [`inst`, `tn`] >> simp[]) >>
   qexists_tac `update_var out
      (if inst.inst_opcode = ADD then x + y else x - y) f.lf_src` >>
   simp[update_var_def] >> irule ld_vars_write >>
   simp[set_var_taint_def, FLOOKUP_UPDATE] >>
   conj_tac
   >- (rpt strip_tac >> irule ld_affine_selected_output >>
       reverse conj_tac >- metis_tac[] >>
       qexistsl_tac [`op1`, `op2`, `inst`, `a`] >> simp[]) >>
   reverse conj_tac
   >- (irule ld_inst_output_ir >> metis_tac[MEM]) >>
   disch_tac >>
   `MEM inst.inst_opcode [ADD; SUB]` by simp[] >>
   drule_all ld_affine_provenance >> strip_tac >>
   Cases_on `op_prov f.lf_H op1` >>
   Cases_on `op_prov f.lf_H op2` >>
   gvs[first_prov_def, ld_word_agree_empty] >>
   metis_tac[ld_wordrel_affine, WORD_ADD_COMM])
QED

Theorem ld_erase_first_prov:
  first_prov (ld_erase A o_f H) ops =
    OPTION_MAP (ld_erase A) (first_prov H ops)
Proof
  Induct_on `ops` >> simp[first_prov_def, ld_erase_op_prov] >>
  Cases_on `op_prov H h` >> simp[]
QED

Theorem ld_affine_success[local]:
  MEM inst.inst_opcode [ADD; SUB] /\ step_inst_base inst s = OK s' ==>
  ?a b out x. inst.inst_operands = [a;b] /\ inst.inst_outputs = [out] /\
    s' = update_var out x s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_affine_taint[local]:
  MEM inst.inst_opcode [ADD; SUB] /\ inst.inst_operands = [a;b] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >>
  `out_taint tn inst s = {}` by
    (Cases_on `eval_operand a s` >> gvs[MEM] >> simp[out_taint_def]) >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, update_var_def, new_site_bytes_def,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       FLOOKUP_DEF, taint_component_equality] >> SET_TAC[]
QED

Theorem ld_affine_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  MEM inst.inst_opcode [ADD; SUB] /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\ ld_nonghost tn f.lf_src f.lf_tgt ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs (first_prov f.lf_H inst.inst_operands);
      lf_tv := (step_taint inst f.lf_src ss tn).t_var |> ) /\
    ld_memory lo A (step_taint inst f.lf_src ss tn) ss ts /\
    ld_nonghost (step_taint inst f.lf_src ss tn) ss ts /\
    ld_erase A o_f set_prov f.lf_H inst.inst_outputs (first_prov f.lf_H inst.inst_operands) =
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
  strip_tac >> drule_all ld_affine_vars >> strip_tac >>
  drule_all ld_affine_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_affine_success >> strip_tac >> gvs[] >>
  (`step_taint inst f.lf_src (update_var out x f.lf_src) tn =
      tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}` by
     (irule ld_affine_taint >> simp[] >> metis_tac[]) >>
   simp[] >> conj_tac
   >- (irule ld_memory_update_var >> simp[]) >>
   conj_tac
   >- (irule ld_nonghost_update_var >> simp[]) >>
   simp[ld_erase_set_prov, step_prov_def, out_prov_def, ld_erase_first_prov, update_var_def])
QED
