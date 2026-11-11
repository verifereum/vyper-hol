(* MLOAD effects consume masked observations in source coordinates. *)
Theory lowerDloadSafetyMloadEffects
Ancestors
  lowerDloadSafetyBytes lowerDloadSafetyReadSteps lowerDloadSafetyUpdates
  lowerDloadSafetyMemoryReadSteps
  lowerDloadSafetyValues ptrDiscipline venomExecSemantics venomState venomInst
  unitShapeDefs memLocDefs codegenRel contextCodegenRel finite_map list pred_set words

Theorem ld_mload_operand[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [op] /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x /\
    (op_prov f.lf_H op = NONE ==> x = y) /\
    (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  strip_tac >>
  `!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn)` by
    metis_tac[ld_inst_input_ir, MEM] >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> strip_tac >> irule ld_numeric_operand_nonopaque >>
     simp[] >> qexists_tac `inst` >> gvs[MEM]) >>
  `op_taint tn op = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >>
     qexistsl_tac [`f.lf_fn`, `inst`, `f.lf_src`] >> simp[]) >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >> simp[] >> metis_tac[]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[] >>
  conj_tac
  >- (strip_tac >> irule ld_vars_operand_scalar >>
      simp[] >> qexistsl_tac [`A`, `P`, `f`, `op`] >> simp[] >>
      rpt strip_tac >> gvs[op_taint_def]) >>
  rpt strip_tac >> irule ld_vars_operand_selected >> metis_tac[]
QED

Theorem ld_mload_vars[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = MLOAD /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_memory lo A tn f.lf_src f.lf_tgt /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)) ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs (out_taint tn inst f.lf_src) |> )
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  simp[Once step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `?x. eval_operand op1 f.lf_src = SOME x /\
    (op_prov f.lf_H op1 = NONE ==> x = addr) /\
    (!a. op_prov f.lf_H op1 = SOME a ==> ld_wordrel A (SOME a) x addr)` by
    (irule ld_mload_operand >> simp[] >> conj_tac
     >- (qexists_tac `P` >> simp[]) >>
     qexistsl_tac [`inst`, `tn`] >> simp[]) >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) f.lf_src) (mload (w2n addr) f.lf_tgt)` by
    (irule ld_memory_mload_access >> simp[] >>
     qexistsl_tac [`A`, `f.lf_H`, `f.lf_fn`, `inst`, `lo`] >>
     simp[mem_read_ops_def, source_memory_read_ranges_def, eval_operand_def] >>
     metis_tac[]) >>
  simp[Once step_inst_base_def, exec_read1_def] >>
  pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE, out_taint_def] >>
  irule ld_inst_output_ir >> metis_tac[MEM]
QED

Theorem ld_mload_success[local]:
  inst.inst_opcode = MLOAD /\ step_inst_base inst s = OK s' ==>
  ?out x. inst.inst_outputs = [out] /\ s' = update_var out x s
Proof
  metis_tac[ld_memory_read_success, MEM]
QED

Theorem ld_mload_taint[local]:
  inst.inst_opcode = MLOAD ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >> irule ld_memory_read_taint >> simp[MEM]
QED

Theorem ld_mload_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  inst.inst_opcode = MLOAD /\ step_inst_base inst f.lf_tgt = OK ts /\
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
  strip_tac >> drule_all ld_mload_vars >> strip_tac >>
  drule_all ld_mload_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_mload_success >> strip_tac >> gvs[] >>
  `step_taint inst f.lf_src (update_var out x f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs
       (out_taint tn inst f.lf_src)` by
    (irule ld_mload_taint >> simp[]) >>
  simp[] >>
  conj_tac >- (irule ld_memory_update_var >> simp[]) >>
  conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
  simp[ld_erase_set_prov, step_prov_def, out_prov_def]
QED
