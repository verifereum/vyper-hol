(* Unsigned comparisons observe translated positive allocation sites. *)
Theory lowerDloadSafetyComparisonEffects
Ancestors
  lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  lowerDloadSafetyUpdates venomExecSemantics unitShapeDefs codegenRel contextCodegenRel
  pointerConfinedDefs memLocDefs ptrDiscipline venomState venomInst irSupply unitLabelMapIdentity
  finite_map pred_set list arithmetic words

Theorem ld_comparison_pointer_syntax[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [LT;GT;EQ] /\
  MEM (Var v) inst.inst_operands /\ v IN fn_pv P fn ==>
  ?u w. inst.inst_operands = [Var u;Var w]
Proof
  simp[fn_ptr_ok_def, ptr_use_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (fn_insts fn) ==> _`
    (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!v. MEM (Var v) inst.inst_operands /\ _ ==> _`
    (qspec_then `v` mp_tac) >>
  gvs[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  metis_tac[]
QED

Theorem ld_selected_erased_site[local]:
  ld_vars P A f /\ ~retpc_var f.lf_fn v /\
  eval_operand (Var v) f.lf_src = SOME x /\
  eval_operand (Var v) f.lf_tgt = SOME y /\
  FLOOKUP (ld_erase A o_f f.lf_H) v = SOME (b,n) /\ 0 < n ==>
  ?a c. FLOOKUP f.lf_H v = SOME a /\
    FLOOKUP A a = SOME (b,c,n) /\ ld_wordrel A (SOME a) x y
Proof
  simp[FLOOKUP_o_f] >> strip_tac >>
  Cases_on `FLOOKUP f.lf_H v` >> gvs[] >> rename1 `ld_erase A a = (b,n)` >>
  `ld_wordrel A (SOME a) x y` by
    (irule ld_vars_operand_selected >> qexistsl_tac [`P`, `f`, `Var v`] >>
     simp[op_prov_def]) >>
  gvs[ld_wordrel_SOME, ld_erase_def] >> metis_tac[]
QED

Theorem ld_comparison_selected[local]:
  ld_vars P A f /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [Var u;Var w] /\
  (u IN FDOM f.lf_H \/ w IN FDOM f.lf_H) /\
  ~retpc_var f.lf_fn u /\ ~retpc_var f.lf_fn w /\
  eval_operand (Var u) f.lf_tgt = SOME y1 /\
  eval_operand (Var w) f.lf_tgt = SOME y2 /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword (:256)) ==>
  ?x1 x2. eval_operand (Var u) f.lf_src = SOME x1 /\
    eval_operand (Var w) f.lf_src = SOME x2 /\
    ((y1=y2) <=> (x1=x2)) /\
    ((w2n y1 < w2n y2) <=> (w2n x1 < w2n x2)) /\
    ((w2n y2 < w2n y1) <=> (w2n x2 < w2n x1))
Proof
  strip_tac >>
  `?b n x1 x2.
    FLOOKUP (ld_erase A o_f f.lf_H) u = SOME (b,n) /\
    FLOOKUP (ld_erase A o_f f.lf_H) w = SOME (b,n) /\ 0 < n /\
    eval_operand (Var u) f.lf_src = SOME x1 /\
    eval_operand (Var w) f.lf_src = SOME x2 /\
    b <= w2n x1 /\ w2n x1 <= b+n /\
    b <= w2n x2 /\ w2n x2 <= b+n` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     simp[access_ok_def] >> strip_tac >>
     gvs[] >> metis_tac[]) >>
  `?a c. FLOOKUP f.lf_H u = SOME a /\ FLOOKUP A a = SOME (b,c,n) /\
    ld_wordrel A (SOME a) x1 y1` by
    (irule ld_selected_erased_site >> metis_tac[]) >>
  `?a' c'. FLOOKUP f.lf_H w = SOME a' /\ FLOOKUP A a' = SOME (b,c',n) /\
    ld_wordrel A (SOME a') x2 y2` by
    (irule ld_selected_erased_site >> metis_tac[]) >>
  `a = a'` by (irule ld_positive_source_identity >> metis_tac[]) >> gvs[] >>
  irule ld_wordrel_site_comparisons >> metis_tac[]
QED

Theorem ld_comparison_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [op1;op2] /\
  eval_operand op1 f.lf_tgt = SOME y1 /\
  eval_operand op2 f.lf_tgt = SOME y2 /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword (:256)) ==>
  ?x1 x2. eval_operand op1 f.lf_src = SOME x1 /\
    eval_operand op2 f.lf_src = SOME x2 /\
    ((y1=y2) <=> (x1=x2)) /\
    ((w2n y1 < w2n y2) <=> (w2n x1 < w2n x2)) /\
    ((w2n y2 < w2n y1) <=> (w2n x2 < w2n x1))
Proof
  strip_tac >>
  `!op v. MEM op inst.inst_operands /\ op = Var v ==>
    MEM v (fn_ir_vars f.lf_fn) /\ ~retpc_var f.lf_fn v /\
    (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {}` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- metis_tac[ld_inst_input_ir] >> conj_tac
     >- (irule ld_numeric_operand_nonopaque >> simp[] >> qexists_tac `inst` >> gvs[])
     >> `op_taint tn (Var v) = {}` by
       (irule ld_numeric_operand_untainted >>
        qexistsl_tac [`f.lf_fn`, `inst`, `f.lf_src`] >> gvs[]) >>
     gvs[op_taint_def]) >>
  Cases_on `op_prov f.lf_H op1 = NONE /\ op_prov f.lf_H op2 = NONE`
  >- (`eval_operand op1 f.lf_src = eval_operand op1 f.lf_tgt` by
        (irule ld_vars_operand_equal >> metis_tac[listTheory.MEM]) >>
      `eval_operand op2 f.lf_src = eval_operand op2 f.lf_tgt` by
        (irule ld_vars_operand_equal >> metis_tac[listTheory.MEM]) >>
      metis_tac[]) >>
  `?v. MEM (Var v) inst.inst_operands /\ v IN FDOM f.lf_H` by
    (Cases_on `op1` >> Cases_on `op2` >>
     gvs[op_prov_def, FLOOKUP_DEF] >> metis_tac[]) >>
  `v IN fn_pv P f.lf_fn` by (gvs[ld_vars_def, SUBSET_DEF] >> metis_tac[]) >>
  `?u w. inst.inst_operands = [Var u;Var w]` by
    (irule ld_comparison_pointer_syntax >> metis_tac[]) >>
  `op1 = Var u /\ op2 = Var w` by metis_tac[listTheory.CONS_11] >> gvs[] >>
  irule ld_comparison_selected >> simp[] >> metis_tac[]
QED

Theorem ld_comparison_success[local]:
  MEM inst.inst_opcode [LT;GT;EQ] /\ step_inst_base inst s = OK s' ==>
  ?op1 op2 y1 y2 out z.
    inst.inst_operands = [op1;op2] /\ inst.inst_outputs = [out] /\
    eval_operand op1 s = SOME y1 /\ eval_operand op2 s = SOME y2 /\
    s' = update_var out z s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_comparison_taint[local]:
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [op1;op2] ==>
  step_taint inst s (update_var v x s) tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >> gvs[MEM] >> Cases_on `eval_operand op1 s` >>
  simp[step_taint_def, out_taint_def, written_taint_def, mem_taint_def,
       update_var_def, new_site_bytes_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       imm_taint_def, FLOOKUP_DEF, taint_component_equality] >> SET_TAC[]
QED

Theorem ld_comparison_vars[local]:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword (:256)) ==>
  ?ss. step_inst_base inst f.lf_src = OK ss /\
    ld_vars P A (f with <| lf_src := ss; lf_tgt := ts;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := set_var_taint f.lf_tv inst.inst_outputs {} |> )
Proof
  strip_tac >> drule_all ld_comparison_success >> strip_tac >>
  qpat_x_assum `ts = update_var _ _ _` kall_tac >>
  drule_all ld_comparison_observation >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  gvs[MEM] >> pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def, exec_pure2_def, GREATER_DEF] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac[update_var_def] >> irule ld_vars_write >>
  simp[set_var_taint_def, FLOOKUP_UPDATE, ld_word_agree_empty] >>
  drule ld_inst_output_ir >> simp[]
QED

Theorem ld_comparison_effect:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  tn.t_var = f.lf_tv /\ fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ taint_ok f.lf_fn tn inst f.lf_src /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ step_inst_base inst f.lf_tgt = OK ts /\
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword (:256)) /\
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
  strip_tac >> drule_all ld_comparison_vars >> strip_tac >>
  drule_all ld_comparison_success >> strip_tac >>
  qpat_x_assum `step_inst_base inst f.lf_tgt = OK ts` mp_tac >>
  strip_tac >> drule_all ld_comparison_success >> strip_tac >> gvs[] >>
  (`step_taint inst f.lf_src (update_var out z f.lf_src) tn =
     tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}` by
    (irule ld_comparison_taint >> simp[] >> metis_tac[]) >>
   simp[] >>
   conj_tac >- (irule ld_memory_update_var >> simp[]) >>
   conj_tac >- (irule ld_nonghost_update_var >> simp[]) >>
   simp[ld_erase_set_prov, step_prov_def, out_prov_def, update_var_def])
QED
