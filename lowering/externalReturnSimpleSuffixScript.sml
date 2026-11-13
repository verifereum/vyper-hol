Theory externalReturnSimpleSuffix
Ancestors
  vyperLoweringCorrect rawReturnCorrect rawReturnHeader runFromGasPath
  fragExec fragGasPath compileEnv compileVyper vyperState

Theorem return_exiting_fragment_path:
  frag_exec ctx st st' P (\s. F) R /\
  fn_has_code st st' fn /\ P s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?n r. gas_path ctx fn s n r /\ exit_result r /\ R r
Proof
  strip_tac >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pat `exit_result _`) run_from_gas_path >> simp[] >> metis_tac[]
QED

Theorem return_none_suffix_path:
  ~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_stmt cenv lctx ty (Return NONE) st = (x,st') /\
  cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
  cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
  fn_has_code st st' fn /\ state_rel func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?n r. gas_path ctx fn s n r /\ exit_result r /\
    external_call_result_rel tops NoneT tx
      (INL NoneV, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests) r
Proof
  Cases_on `x` >> strip_tac >>
  `frag_exec ctx st st' (\s. state_rel func cenv cx es s) (\s. F)
    (external_call_result_rel tops NoneT tx
      (INL NoneV, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests))` by
    (irule external_return_none_result_rel >> simp[] >> metis_tac[]) >>
  drule return_exiting_fragment_path >>
  disch_then (qspecl_then [`s`, `fn`] mp_tac) >> simp[]
QED

Theorem return_word_suffix_path:
  ~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  word_value v0 /\
  fn_has_code st st' fn /\ state_rel func cenv cx es s /\
  eval_operand op s = SOME (val_to_w256 v0) /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?n r. gas_path ctx fn s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests) r
Proof
  Cases_on `x` >> strip_tac >>
  `frag_exec ctx st st'
    (\s. state_rel func cenv cx es s /\
         eval_operand op s = SOME (val_to_w256 v0)) (\s. F)
    (external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests))` by
    (irule external_return_word_result_rel >> simp[] >> metis_tac[]) >>
  drule return_exiting_fragment_path >>
  disch_then (qspecl_then [`s`, `fn`] mp_tac) >> simp[]
QED

Theorem return_raw_suffix_path:
  lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) prim T ei msz F nkey ut iv st = (x,st') /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  evaluate_type (type_env tops) ret = SOME tv /\
  safe_cast tv v0 = SOME v /\ is_bytestring_type ret /\
  fn_has_code st st' fn /\ state_rel func cenv cx es s /\
  eval_operand op s = SOME p /\ val_in_memory tv v0 (w2n p) s.vs_memory /\
  w2n p + val_footprint tv v0 <= dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?n r. gas_path ctx fn s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests) r
Proof
  Cases_on `x` >> strip_tac >>
  `frag_exec ctx st st'
    (\s. state_rel func cenv cx es s /\
      (?p. eval_operand op s = SOME p /\
           val_in_memory tv v0 (w2n p) s.vs_memory /\
           w2n p + val_footprint tv v0 <= dimword (:256))) (\s. F)
    (external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests))` by
    (irule external_return_raw_unlock_result_rel >>
     simp[vyperStateTheory.return_def] >>
     goal_assum (drule_at Any) >> simp[vyperStateTheory.return_def]) >>
  drule return_exiting_fragment_path >>
  disch_then (qspecl_then [`s`, `fn`] mp_tac) >> simp[] >> metis_tac[]
QED
