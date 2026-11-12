Theory acLiveEmissionProofs
Ancestors
  acMergeRuntimeDefs acMergeCursorDefs acMergeSimulationProofs
  acMergeStepProofs acChainProofs acAbortRelProofs
  stateEquiv stateEquivProps venomExecSemantics venomExecProofs
  venomState venomInst assertCombinerDefs analysisSimDefs
  finite_map list words pred_set basePtrProofs

(* Only the selected operand is retained across an untouched emission. *)
Theorem ac_live_selected_step:
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  ac_merge_operand_origin xs dfg X n p /\ n < LENGTH xs /\
  (!v. MEM v (EL n xs).inst_outputs ==> v NOTIN X) /\
  step_inst fuel ctx (EL n xs) t = OK t' ==>
  eval_operand p t' = eval_operand p t
Proof
  rpt strip_tac >> fs[ac_merge_operand_origin_def]
  >- (gvs[eval_operand_def] >> irule step_inst_preserves_lookup >> metis_tac[]) >>
  metis_tac[ac_merge_runtime_laws_prior_operand]
QED

Theorem ac_live_emission_contract:
  ac_merge_cursor_laws xs dfg cs X su0 shape pending /\
  ac_merge_runtime_laws xs dfg fuel ctx cert /\
  (!c q v. ac_get_iszero_operand dfg {} c = SOME q /\ q = Var v ==>
     v NOTIN X) ==>
  ac_live_emission_contract xs cs fuel ctx
    (state_equiv X) (execution_equiv UNIV) ac_abort_equiv
    (ac_merge_live X cert shape pending)
    (ac_merge_revert_deferred X cert shape pending)
Proof
  rpt strip_tac >> simp[ac_live_emission_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `shape (SUC n) mp' su' /\
   ac_merge_emission_form dfg X (EL n xs)
      (pending n mp su) (pending (SUC n) mp' su') out` by
    (fs[ac_merge_live_def, ac_merge_cursor_laws_def] >> metis_tac[]) >>
  `cert n s /\ state_equiv X s t /\
    (!j p. pending n mp su = SOME (j,p) ==> eval_operand p t = SOME 0w)` by
    fs[ac_merge_live_def] >>
  `!v. MEM (Var v) (EL n xs).inst_operands ==> v NOTIN X` by
    (fs[ac_merge_cursor_laws_def] >> metis_tac[EL_MEM]) >>
  `!v. MEM v (EL n xs).inst_outputs ==> v NOTIN X` by
    (fs[ac_merge_cursor_laws_def] >> metis_tac[EL_MEM]) >>
  fs[ac_merge_emission_form_def]
  >- suspend "unchanged"
  >- suspend "removed"
  >- suspend "equal"
  >> suspend "generated"
QED

Resume ac_live_emission_contract[unchanged]:
  `lift_result (state_equiv X) (execution_equiv UNIV) ac_abort_equiv
     (step_inst fuel ctx (EL n xs) s)
     (step_inst fuel ctx (EL n xs) t)` by
    (irule ac_unchanged_step >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `step_inst fuel ctx (EL n xs) t` >> gvs[lift_result_def] >>
      rename1 `step_inst fuel ctx (EL n xs) t = OK t'` >>
      `cert (SUC n) s'` by metis_tac[ac_merge_runtime_laws_step] >>
      simp[run_insts_def, ac_merge_live_def] >>
      rpt strip_tac >>
      `ac_merge_operand_origin xs dfg X n p` by
        (fs[ac_merge_live_def, ac_merge_cursor_laws_def] >> metis_tac[]) >>
      metis_tac[ac_live_selected_step]) >>
  Cases_on `step_inst fuel ctx (EL n xs) s` >>
  Cases_on `step_inst fuel ctx (EL n xs) t` >>
  gvs[lift_result_def, run_insts_def]
QED
Resume ac_live_emission_contract[removed]:
  drule_all ac_merge_runtime_laws_query >> strip_tac >>
  `eval_operand q t = SOME w` by metis_tac[eval_operand_equiv] >>
  `step_inst fuel ctx (EL n xs) s =
    if w = 0w then OK s else
      Abort Revert_abort (revert_state (set_returndata [] s))` by
    (irule ac_assert_predicate >> metis_tac[]) >>
  `cert (SUC n) s` by metis_tac[ac_merge_runtime_laws_skip_assert] >>
  `run_insts fuel ctx
    [EL n xs with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>] t = OK t` by
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `w = 0w` >>
  gvs[ac_merge_live_def, ac_merge_revert_deferred_def, ac_merge_deferred_def] >>
  metis_tac[ac_abort_equiv_refl]
QED
Resume ac_live_emission_contract[equal]:
  drule_all ac_merge_runtime_laws_query >> strip_tac >>
  `eval_operand q t = SOME w` by metis_tac[eval_operand_equiv] >>
  `w = 0w` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `step_inst fuel ctx (EL n xs) s = OK s` by
    (irule step_assert_ok >> simp[bool_to_word_def] >> metis_tac[]) >>
  `eval_operand c t = SOME (bool_to_word T)` by
    metis_tac[eval_operand_equiv, MEM] >>
  `step_inst fuel ctx (EL n xs) t = OK t` by
    (irule step_assert_ok >> simp[bool_to_word_def] >> metis_tac[]) >>
  `cert (SUC n) s` by metis_tac[ac_merge_runtime_laws_skip_assert] >>
  Cases_on `more` >>
  gvs[run_insts_def, ac_merge_live_def] >>
  `step_inst fuel ctx
      (EL n xs with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|>) t = OK t` by
    simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[run_insts_def, ac_merge_live_def]
QED
Resume ac_live_emission_contract[generated]:
  drule_all ac_merge_runtime_laws_query >> strip_tac >>
  `eval_operand q t = SOME w` by metis_tac[eval_operand_equiv] >>
  `eval_operand p t = SOME 0w` by metis_tac[] >>
  `step_inst fuel ctx (EL n xs) s =
    if w = 0w then OK s else
      Abort Revert_abort (revert_state (set_returndata [] s))` by
    (irule ac_assert_predicate >> metis_tac[]) >>
  `cert (SUC n) s` by metis_tac[ac_merge_runtime_laws_skip_assert] >>
  `state_equiv X s
    (update_var zv (bool_to_word (0w = 0w /\ w = 0w))
       (update_var ov (word_or 0w w) t))` by
    (qpat_assum `state_equiv X s t`
       (mp_then (Pos hd) mp_tac ac_or_iszero_frame) >>
     disch_then (qspecl_then [`ov`,`zv`,`0w`,`w`] mp_tac) >> simp[]) >>
  `run_insts fuel ctx
    [instruction oi OR [p;q] [ov]; instruction zi ISZERO [Var ov] [zv]] t =
    OK (update_var zv (bool_to_word (w = 0w)) (update_var ov (word_or 0w w) t))` by
    (qpat_assum `eval_operand p t = SOME 0w`
       (mp_then (Pos hd) mp_tac ac_or_iszero_prefix) >>
     simp[]) >>
  Cases_on `more`
  >- suspend "generated_more"
  >> suspend "generated_last"
QED
Resume ac_live_emission_contract[generated_more]:
  `run_insts fuel ctx out t =
    OK (update_var zv (bool_to_word (w = 0w)) (update_var ov (word_or 0w w) t))` by
    (gvs[] >> pure_rewrite_tac[run_insts_three] >>
     simp[run_insts_def, step_inst_non_invoke, step_inst_base_def]) >>
  Cases_on `w = 0w` >>
  gvs[ac_merge_live_def, ac_merge_revert_deferred_def, ac_merge_deferred_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[ac_abort_equiv_refl, word_or_eq_0w]
QED
Resume ac_live_emission_contract[generated_last]:
  `run_insts fuel ctx out t =
    if w = 0w then
      OK (update_var zv (bool_to_word (w = 0w)) (update_var ov (word_or 0w w) t))
    else Abort Revert_abort (revert_state (set_returndata []
      (update_var zv (bool_to_word (w = 0w)) (update_var ov (word_or 0w w) t))))` by
    (gvs[] >> pure_rewrite_tac[run_insts_three] >>
     simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          bool_to_word_def] >> Cases_on `w = 0w` >> simp[bool_to_word_def]) >>
  `ac_abort_equiv s t` by
    (irule execution_equiv_ac_abort_equiv >>
     fs[state_equiv_def] >> metis_tac[execution_equiv_weaken_UNIV]) >>
  Cases_on `w = 0w` >> gvs[ac_merge_live_def] >>
  irule ac_abort_equiv_revert_returndata >> simp[]
QED
Finalise ac_live_emission_contract
