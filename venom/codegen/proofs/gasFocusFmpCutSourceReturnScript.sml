(* A target RET and successful bind determine the source return arity.
   The resumed instruction is fetched in the actual saved source caller. *)
Theory gasFocusFmpCutSourceReturn
Ancestors
  fnFrameBoundaryGenRet fnFrameBoundaryInvoke concretizePtrOwnerPath
  o1ContractSimplifyCfgSrcFrame o1LowerDloadReadiness o1PassContract
  venomExecSemantics venomInstProofs1 venomState venomInst list rich_list

Theorem source_saved_continuation[local]:
  o1_ctx_shape C /\
  frame_reachable root C (f::stk) PG G tn fn ri s /\
  bind_outputs f.cf_inst.inst_outputs r.iret_values
    (adopt_return_fmp r (merge_callee_state f.cf_state se)) = SOME sb ==>
  ?i. active_inst f.cf_fn i (sb with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  drule scfg_frame_reachable_functions >> simp[] >> strip_tac >>
  drule ptr_owner_frame_active >> simp[] >> strip_tac >>
  `wf_function f.cf_fn` by fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
  `sb.vs_current_bb = f.cf_state.vs_current_bb` by
    (qspec_then `\u. u.vs_current_bb` mp_tac bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >>
     Cases_on `r.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  irule ld_nonterminator_successor >> simp[] >>
  qexists `f.cf_inst` >> simp[is_terminator_def]
QED

Theorem focus_fmp_cut_source_return:
  o1_ctx_shape C /\
  frame_reachable root C (f::stk) PG G tn fn ri s /\
  active_inst fn ri s /\ ~s.vs_halted /\ ri.inst_opcode = RET /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) ri.inst_operands ==> IS_SOME (lookup_var v s)) /\
  j.inst_outputs = f.cf_inst.inst_outputs /\
  step_inst kt C' ri t = IntRet rt te /\
  bind_outputs j.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state tc te)) = SOME tt ==>
  ?r se sb i.
    step_inst ks C ri s = IntRet r se /\
    bind_outputs f.cf_inst.inst_outputs r.iret_values
      (adopt_return_fmp r (merge_callee_state f.cf_state se)) = SOME sb /\
    active_inst f.cf_fn i (sb with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> drule_all ret_source_values >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `ys` strip_assume_tac)) >>
  `IS_SOME (eval_operands ri.inst_operands s)` by
    (`IS_SOME (eval_operands ri.inst_operands t)` by simp[] >>
     fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     rpt strip_tac >> Cases_on `op` >> fs[eval_operand_def] >>
     metis_tac[eval_operand_def]) >>
  Cases_on `eval_operands ri.inst_operands s` >> fs[] >>
  rename1 `eval_operands ri.inst_operands s = SOME xs` >>
  `LENGTH xs = LENGTH ys` by metis_tac[eval_operands_some_length] >>
  `xs <> []` by (Cases_on `xs` >> Cases_on `ys` >> fs[]) >>
  `LENGTH f.cf_inst.inst_outputs = LENGTH (FRONT xs)` by
    gvs[bind_outputs_def, LENGTH_FRONT] >>
  qabbrev_tac `r = <| iret_values := FRONT xs; iret_adopt_fmp := NONE |>` >>
  `step_inst ks C ri s = IntRet r s` by
    (Cases_on `xs` >> gvs[] >>
     simp[Abbr `r`, step_inst_non_invoke, step_inst_base_def]) >>
  `?sb. bind_outputs f.cf_inst.inst_outputs r.iret_values
      (adopt_return_fmp r (merge_callee_state f.cf_state s)) = SOME sb` by
    simp[Abbr `r`, bind_outputs_def] >>
  drule_all source_saved_continuation >> strip_tac >>
  qexistsl [`r`, `s`, `sb`, `i`] >> simp[]
QED
