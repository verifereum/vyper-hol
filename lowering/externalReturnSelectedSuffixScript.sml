(* Successful-read external return consumers. *)
Theory externalReturnSelectedSuffix
Ancestors externalReturnSelectedResources externalReturnSiteSemantics
  externalReturnConsumerFit externalReturnSimpleSuffix vyperLoweringCorrect
  typedMemoryCopy loweringPosts exprLoweringProps fragExec compileEnv
  valueCopyBytes valueTypingMemoryProps exprSimProps stmtSimReturn
  externalReturnConsumerProbe externalReturnCopyAlloc externalReturnSuffixResult
  externalReturnBufferlessAlloc externalReturnIntcallMetadata vyperTypeSystem
  externalReturnBufferlessNormalize vyperTypeContract supportedDecls supportedProgram
  vyperInterpreter

(* Word destinations force the annotation to be exactly the destination.
   Use typed encoding, including address and bytesN, not word_value. *)
Theorem return_site_word_operand:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  is_word_type ret ==>
  ?tv. evaluate_type (get_tenv cx) ret = SOME tv /\
    safe_cast tv v = SOME v /\
    stmt_state_rel ctx func ce cx ee s /\
    eval_operand op s = SOME (typed_val_to_w256 tv v)
Proof
  strip_tac >> drule_all return_site_value_semantics >> strip_tac >>
  `expr_type e = ret` by metis_tac[typed_copy_word_widening] >>
  gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem return_prim_suffix_path:
  ~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) T F ei msz F nkey ut iv st = (x,st') /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  is_word_type ret /\
  fn_has_code st st' fn /\ state_rel func cenv cx es s /\
  eval_operand op s = SOME (typed_val_to_w256 tv v0) /\ ~s.vs_halted /\
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
         eval_operand op s = SOME (typed_val_to_w256 tv v0)) (\s. F)
    (external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests))` by
    (irule external_return_prim_result_rel >> simp[] >> metis_tac[]) >>
  drule return_exiting_fragment_path >>
  disch_then (qspecl_then [`s`, `fn`] mp_tac) >> simp[]
QED

Theorem return_site_nonraw_word_path:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  is_word_type ret /\ ~ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  ce.ce_nonreentrant = (F,nkey,ut,iv) /\
  get_tenv cx = type_env tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  return_consumer_suffix ce ret sty op sb = (u,sf) /\
  (!y. op = Var y ==> not_fresh_at sb y) /\
  fn_has_code sb sf func /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_site_word_operand >> strip_tac >>
  `compile_external_return (SOME op) T F ce.ce_ret_enc_info
     ce.ce_max_return_size F nkey ut iv sb = (u,sf)` by
    (qpat_x_assum `return_consumer_suffix _ _ _ _ _ = _` mp_tac >>
     gvs[return_consumer_suffix_def, comp_bind_def, comp_return_def]) >>
  `state_rel func ce cx ee s` by
    fs[stmt_state_rel_def] >>
  `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`
    by fs[] >>
  drule_all return_prim_suffix_path >> strip_tac >>
  first_x_assum (qspecl_then [`am.exports`, `ctx`] strip_assume_tac) >>
  qexistsl_tac [`n`, `r`] >> simp[] >> metis_tac[]
QED

(* A bytes/string widening changes capacity, but not the actual footprint
   or its ownership witness. *)
Theorem return_bytestring_val_at:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  expr_val_at ce cx sty sa sb ee v op s ==>
  expr_val_at ce cx dty sa sb ee v op s
Proof
  strip_tac >>
  `val_footprint stv v = val_footprint dtv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_wf dtv v` by metis_tac[value_has_type_memory_wf] >>
  `~is_word_type sty` by metis_tac[is_bytestring_word_type] >>
  `?sbt. stv = BaseTV sbt` by metis_tac[bytestring_type_value] >>
  `?dbt. dtv = BaseTV dbt` by metis_tac[bytestring_type_value] >>
  fs[expr_val_at_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]
QED

Theorem return_site_nocopy_memory:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  ~is_word_type ret /\
  (expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)) ==>
  ?tv w. evaluate_type (get_tenv cx) ret = SOME tv /\
    safe_cast tv v = SOME v /\ val_wf tv v /\
    stmt_state_rel ctx func ce cx ee s /\
    eval_operand op s = SOME w /\
    val_in_memory tv v (w2n w) s.vs_memory /\
    expr_val_at ce cx ret sa sb ee v op s /\
    w2n w + val_footprint tv v < dimword (:256)
Proof
  strip_tac >> drule_all return_site_value_semantics >> strip_tac >>
  `expr_val_rel cx ret v op s /\ expr_val_at ce cx ret sa sb ee v op s` by
    (fs[expr_post_def] >>
     (conj_tac
      >- (`~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
          fs[expr_val_rel_def] >>
          drule_all bytestring_val_in_memory_transfer >> simp[])) >>
     drule_all return_bytestring_val_at >> simp[]) >>
  `stmt_state_rel ctx func ce cx ee s` by fs[expr_post_def] >>
  fs[expr_val_rel_def] >>
  (conj_tac
   >- (qpat_x_assum `!tv. evaluate_type _ ret = SOME tv ==> _`
         (qspec_then `dtv` mp_tac) >> simp[])) >>
  drule_all expr_val_at_bound >> simp[]
QED

Theorem return_site_raw_bytes_path:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  is_bytestring_type ret /\ ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  ce.ce_nonreentrant = (F,nkey,ut,iv) /\
  get_tenv cx = type_env tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  lowered_value_type ce e = expr_type e /\
  return_consumer_suffix ce ret (lowered_value_type ce e) op sb = (u,sf) /\
  (!y. op = Var y ==> not_fresh_at sb y) /\
  fn_has_code sb sf func /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_site_value_semantics >> strip_tac >>
  `is_bytestring_type (expr_type e)` by metis_tac[typed_copy_bytestring_source] >>
  `~is_word_type ret` by metis_tac[is_bytestring_word_type] >>
  (Q.SUBGOAL_THEN `expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)` assume_tac
    >- simp[]) >>
  drule_all return_site_nocopy_memory >> strip_tac >>
  `compile_external_return (SOME op) F T ce.ce_ret_enc_info
     ce.ce_max_return_size F nkey ut iv sb = (u,sf)` by
    (qpat_x_assum `return_consumer_suffix _ _ _ _ _ = _` mp_tac >>
     gvs[return_consumer_suffix_def, comp_bind_def, comp_return_def]) >>
  `state_rel func ce cx ee s` by fs[stmt_state_rel_def] >>
  `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`
    by fs[] >>
  `w2n w + val_footprint tv v <= dimword (:256)` by simp[] >>
  `evaluate_type (type_env tops) ret = SOME tv` by metis_tac[] >>
  drule_all return_raw_suffix_path >> strip_tac >>
  first_x_assum (qspecl_then [`am.exports`, `ctx`] strip_assume_tac) >>
  qexistsl_tac [`n`, `r`] >> simp[] >> metis_tac[]
QED

Theorem return_selected_nocopy_window:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  ~is_word_type ret /\ ret <> NoneT /\
  (expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)) ==>
  ?tv w ct rv. evaluate_type (type_env tops) ret = SOME tv /\
    safe_cast tv v = SOME v /\
    stmt_state_rel ctx func ce cx ee s /\
    eval_operand op s = SOME w /\
    abi_encoder_admissible ce.ce_ret_enc_info /\
    abi_encoder_window_input ce.ce_ret_enc_info ct rv (w2n w)
      (val_footprint tv v) s.vs_memory /\
    return_bytes tops ret v (enc ct rv) /\
    LENGTH (enc ct rv) <= ce.ce_max_return_size /\
    (0 < val_footprint tv v ==>
      (?aid b len. aid < sb.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) /\
        b <= w2n w /\ w2n w + val_footprint tv v <= b + len) \/
      (?name b len. local_region ce ee.scopes s name b len /\
        b <= w2n w /\ w2n w + val_footprint tv v <= b + len))
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  (Q.SUBGOAL_THEN `expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)` assume_tac
    >- simp[]) >>
  drule_all return_site_nocopy_memory >> strip_tac >>
  qpat_x_assum `ret <> NoneT ==> _` mp_tac >> simp[] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) ret = SOME dtv` >>
  `evaluate_type (type_env tops) ret = SOME dtv` by metis_tac[] >>
  drule_all return_consumer_window >> strip_tac >>
  `tv = dtv` by fs[] >>
  qpat_x_assum `tv = dtv` SUBST_ALL_TAC >>
  qexistsl_tac [`ct`, `rv`] >> simp[] >> strip_tac >>
  drule_all return_expr_normalize_source >> simp[]
QED

(* Execute the real nonraw ABI allocation/encode/RETURN suffix. *)
Theorem return_abi_suffix_path:
  compile_external_return (SOME src) F F ei msz F nkey ut iv st = (x,sf) /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  msz < dimword (:256) /\ LENGTH (enc ct rv) <= msz /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei ct rv (w2n w) cap s.vs_memory /\
  eval_operand src s = SOME w /\
  (!y. src = Var y ==> not_fresh_at st y) /\
  (0 < cap ==>
    (?aid b len. aid < st.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      b <= w2n w /\ w2n w + cap <= b + len) \/
    (?name b len. local_region ce ee.scopes s name b len /\
      b <= w2n w /\ w2n w + cap <= b + len)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  ~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
  return_bytes tops ret v (enc ct rv) ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts ee),
       ee.requests) r
Proof
  strip_tac >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[stmtLoweringTheory.compile_external_return_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  `cs_extends st cs'` by
    (drule loweringHaltTheory.compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends cs' cs''` by
    (drule abiEncoderAppendTheory.cs_extends_abi_encode >> simp[]) >>
  `cs_extends cs'' sf` by (drule cs_extends_emit_inst >> simp[]) >>
  `fn_has_code st cs' func /\ fn_has_code cs' cs'' func /\
   fn_has_code cs'' sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `eval_operand src s = SOME (n2w (w2n w))` by simp[] >>
  `?fuel. external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts ee),
     ee.requests) (run_from fuel ctx func s)` by
    (irule return_output_alloc_encoder_result_rel >>
     simp[] >>
     qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `exit_result (run_from fuel ctx func s)` by
    (Cases_on `run_from fuel ctx func s` >>
     fs[external_call_result_rel_def, exit_result_def]) >>
  drule_at (Pat `exit_result _`) runFromGasPathTheory.run_from_gas_path >> simp[] >> metis_tac[]
QED

Theorem return_selected_nocopy_path:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  ~is_word_type ret /\ ret <> NoneT /\ ~ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  lowered_value_type ce e = expr_type e /\
  (expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)) /\
  return_consumer_suffix ce ret (lowered_value_type ce e) op sb = (u,sf) /\
  (!y. op = Var y ==> not_fresh_at sb y) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sb /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  (Q.SUBGOAL_THEN `expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)` assume_tac
    >- simp[]) >>
  drule_all return_selected_nocopy_window >> strip_tac >>
  `ce.ce_max_return_size < dimword (:256)` by
    (drule_all return_site_output_buffer_bound >> simp[]) >>
  `compile_external_return (SOME op) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sb = (u,sf)` by
    (qpat_x_assum `return_consumer_suffix _ _ _ _ _ = _` mp_tac >>
     gvs[return_consumer_suffix_def, comp_bind_def, comp_return_def]) >>
  `?n r. gas_path ctx func s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts ee),
       ee.requests) r` by
    (irule return_abi_suffix_path >>
     qpat_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `r`] >> simp[] >> metis_tac[]
QED

(* Typing rules exclude the apparent valued-None return corner case. *)
Theorem return_site_valued_not_none:
  IS_SOME (type_stmt env ret (Return (SOME e))) ==> ret <> NoneT
Proof
  simp[vyperTypeSystemTheory.type_stmt_def] >> rpt strip_tac >> gvs[]
QED

(* A normalized allocation supplies actual-footprint ownership.  Semantic
   typing is still derived from the successful source read, not assumed. *)
Theorem return_selected_allocated_path:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  ~is_word_type ret /\ ~ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sb = (u,sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sb /\ stmt_state_rel ctx func ce cx ee s /\
  (!y. op = Var y ==> not_fresh_at sb y) /\
  evaluate_type (get_tenv cx) ret = SOME dtv /\
  eval_operand op s = SOME w /\ val_in_memory dtv v (w2n w) s.vs_memory /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size dtv) /\
  aid < sb.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  drule_all return_site_value_semantics >> strip_tac >>
  drule return_site_valued_not_none >> strip_tac >>
  `ce.ce_max_return_size < dimword (:256)` by
    (drule_all return_site_output_buffer_bound >> simp[]) >>
  qpat_x_assum `ret <> NoneT ==> _` mp_tac >> simp[] >> strip_tac >>
  `evaluate_type (type_env tops) ret = SOME dtv` by metis_tac[] >>
  `safe_cast dtv v = SOME v` by gvs[] >>
  drule_all return_consumer_window >> strip_tac >>
  `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by fs[] >>
  `val_footprint dtv v <= type_memory_size dtv` by
    (irule externalReturnCopyTransportTheory.return_footprint_le_layout >> gvs[]) >>
  `?n r. gas_path ctx func s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts ee),
       ee.requests) r` by
    (irule return_abi_suffix_path >>
     qpat_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> qexistsl_tac [`cx`, `ce`] >> simp[] >>
     strip_tac >> disj1_tac >>
     qexistsl_tac [`aid`, `w2n w`, `type_memory_size dtv`] >> simp[]) >>
  qexistsl_tac [`n`, `r`] >> simp[] >> gvs[] >> metis_tac[]
QED

(* Convert a checked normalizing prefix plus exiting counted continuation. *)
Theorem return_normalizing_prefix_path:
  frag_exec ctx sa sb (\z. z = s) Q (\r. F) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?n r. gas_path ctx func t n r /\ exit_result r /\ R r) ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\ R r
Proof
  strip_tac >> qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all fragGasPathTheory.gas_path_exit >> strip_tac >>
  `!err. run_from fuel ctx func s' <> Error err` by
    metis_tac[exit_result_not_error] >>
  qpat_x_assum `!fuel. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all runFromGasPathTheory.run_from_gas_path >> metis_tac[]
QED

Theorem return_normalize_compiler_context:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dst src sty sm = ((),sn) /\
  compile_external_return (SOME buf.buf_operand) F F ei msz F nk ut iv sn = (u,sf) /\
  fn_has_code sa sf func /\ local_ptrs_reserved ce sa ==>
  fn_has_code sa sn func /\ fn_has_code sn sf func /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  local_ptrs_reserved ce sn /\ sa.cs_next_id < sn.cs_next_id /\
  (!y. buf.buf_operand = Var y ==> not_fresh_at sn y)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qspecl_then [`sz`, `sa`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sn` by
    (`ci_mono sm (SND (compile_store_memory_typed ce buf.buf_operand dst src sty sm))`
      by simp[cj 1 ci_mono_typed_memory_family] >> gvs[]) >>
  `ci_mono sn sf` by
    (`ci_mono sn (SND (compile_external_return (SOME buf.buf_operand) F F ei msz F nk ut iv sn))`
      by simp[cj 3 stmtLoweringMonoTheory.ci_mono_return_helpers] >> gvs[]) >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `sa.cs_next_id < sn.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  fs[ci_mono_def] >>
  metis_tac[fn_has_code_split, cs_extends_trans, freshWritesTheory.not_fresh_at_mono]
QED

Theorem return_selected_located_normalize_path:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es se sa s0 ee v src s /\
  ~is_word_type ret /\ ~is_word_type (expr_type e) /\ ~ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  compile_alloc_buffer (type_memory_bytes ce ret) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ret src (expr_type e) sm = ((),sn) /\
  compile_external_return (SOME buf.buf_operand) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sn = (u,sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!y. src = Var y ==> not_fresh_at sa y) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  drule_all return_site_value_semantics >> strip_tac >>
  drule return_site_copy_metadata >> strip_tac >>
  drule_all return_normalize_compiler_context >> strip_tac >>
  `type_memory_bytes ce ret = type_memory_size dtv` by
    (irule return_site_memory_size >> metis_tac[]) >>
  `type_memory_size dtv < dimword (:256)` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`sty` |-> `expr_type e`]
    return_consumer_located_normalize)) >> strip_tac >>
  drule return_normalizing_prefix_path >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >>
  disch_then ho_match_mp_tac >>
  rpt strip_tac >>
  drule_all return_selected_allocated_path >>
  gvs[] >> metis_tac[]
QED

Theorem return_selected_bufferless_normalize_path:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  ce.ce_func_info name = (0,0,pvs) /\ phy = ce.ce_func_return_type name /\
  type_widens_to (get_tenv cx) phy (expr_type e) /\
  evaluate_type (get_tenv cx) phy = SOME stv /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  stmt_state_rel ctx func ce cx ee s /\
  ~is_word_type ret /\ ~ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  compile_alloc_buffer (type_memory_bytes ce ret) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ret (Lit 0w) phy sm = ((),sn) /\
  compile_external_return (SOME buf.buf_operand) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sn = (u,sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  drule return_site_copy_metadata >> strip_tac >>
  drule_all return_normalize_compiler_context >> strip_tac >>
  drule_all return_selected_bufferless >> disch_tac >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  (Q.SUBGOAL_THEN `(phy = NoneT \/ type_memory_bytes ce phy = 0)` assume_tac
    >- metis_tac[]) >>
  drule_all return_bufferless_site_zero_semantics >> strip_tac >>
  `type_widens_to (get_tenv cx) phy ret` by
    metis_tac[typedCopyCompatibilityTheory.type_widens_to_trans] >>
  `compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm)` by metis_tac[] >>
  drule_all return_alloc_zero_value_run >> strip_tac >>
  drule_all return_selected_allocated_path >> strip_tac >>
  drule_all fragGasPathTheory.gas_path_exit >> strip_tac >>
  `!err. run_from fuel ctx func t <> Error err` by
    metis_tac[exit_result_not_error] >>
  qpat_x_assum `!fuel r. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all runFromGasPathTheory.run_from_gas_path >> metis_tac[]
QED

Theorem return_selected_bufferless_nocopy_path:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE fname External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  ce.ce_func_info name = (0,0,pvs) /\ phy = ce.ce_func_return_type name /\
  type_widens_to (get_tenv cx) phy (expr_type e) /\
  evaluate_type (get_tenv cx) phy = SOME stv /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  stmt_state_rel ctx func ce cx ee s /\
  ~is_word_type ret /\ ~ce.ce_raw_return /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME (Lit 0w)) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sb = (u,sf) /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sb /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  drule return_site_copy_metadata >> strip_tac >>
  drule_all return_selected_bufferless >> disch_tac >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  (Q.SUBGOAL_THEN `(phy = NoneT \/ type_memory_bytes ce phy = 0)` assume_tac
    >- metis_tac[]) >>
  drule_all return_bufferless_site_zero_semantics >> strip_tac >>
  drule return_site_valued_not_none >> strip_tac >>
  `ce.ce_max_return_size < dimword (:256)` by
    (drule_all return_site_output_buffer_bound >> simp[]) >>
  qpat_x_assum `ret <> NoneT ==> _` mp_tac >> simp[] >> strip_tac >>
  `evaluate_type (type_env tops) ret = SOME dtv` by metis_tac[] >>
  `val_in_memory dtv v (w2n (0w:bytes32)) s.vs_memory` by
    metis_tac[return_zero_wf_memory] >>
  drule_all return_consumer_window >> strip_tac >>
  `val_footprint dtv v <= type_memory_size dtv` by
    (irule externalReturnCopyTransportTheory.return_footprint_le_layout >> simp[]) >>
  `val_footprint dtv v = 0` by decide_tac >>
  `?n r. gas_path ctx func s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts ee),
       ee.requests) r` by
    (irule return_abi_suffix_path >>
     qpat_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`n`, `r`] >> simp[] >> gvs[] >> metis_tac[]
QED

Theorem selected_check_raw_bytes[local]:
  !in_deploy layouts addr mods art src tls vis mut nr name args defaults ret body.
  check_contract in_deploy layouts addr mods = SOME art /\
  MEM (src,tls) mods /\
  MEM (FunctionDecl vis mut nr T name args defaults ret body) tls ==>
  ?n. ret = BaseT (BytesT (Dynamic n))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x mods ==> check_module _ _ _ _ _ _ x` drule >>
  simp[check_module_def, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!x. MEM x tls ==> check_toplevel_decl _ _ _ x` drule >>
  simp[check_toplevel_decl_def, function_header_ok_def]
QED

Theorem selected_lookup_external_raw[local]:
  !ts ambient name mut nr args defaults ret body.
  EVERY (supported_declaration_header ambient) ts /\
  lookup_function (NONE : num option) name External ts =
    SOME (mut,nr,args,defaults,ret,body) ==>
  ?rr. MEM (FunctionDecl External mut nr rr name args defaults ret body) ts /\
       lookup_raw_return (NONE : num option) name External ts = SOME rr
Proof
  Induct_on `ts` >- simp[lookup_function_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM] >>
      Cases_on `s = name /\ f = External` >> gvs[] >> metis_tac[])
  >- (Cases_on `v` >>
      simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
           listTheory.MEM, supported_public_variables_rejected] >>
      metis_tac[])
  >- (simp[listTheory.EVERY_DEF, supported_hashmap_header_contract] >>
      strip_tac >> gvs[lookup_function_def, lookup_raw_return_def,
                      listTheory.MEM] >> metis_tac[])
  >> simp[listTheory.EVERY_DEF, lookup_function_def, lookup_raw_return_def,
          listTheory.MEM] >> metis_tac[]
QED

Theorem return_selected_raw_bytes:
  !tops am tx mut nr args defaults ret body.
  source_typing_ok tops am tx /\ supported_program tops /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,defaults,ret,body) /\
  lookup_raw_return_or_F (NONE:num option) tx.function_name External tops ==>
  is_bytestring_type ret
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  drule_all selected_lookup_external_raw >> strip_tac >>
  gvs[lookup_raw_return_or_F_def, e2eDefsTheory.source_typing_ok_def] >>
  `?n. ret = BaseT (BytesT (Dynamic n))` by
    (drule selected_check_raw_bytes >> simp[listTheory.MEM] >> metis_tac[]) >>
  simp[is_bytestring_type_def]
QED

Theorem selected_word_fits_eq[local]:
  (!sty ty. arg_type_fits sty ty /\ is_word_type sty ==> sty = ty) /\
  (!stys tys. arg_types_fit stys tys /\ EVERY is_word_type stys ==>
    stys = tys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_word_type_def] >> gvs[]
QED

Theorem selected_source_word_eq[local]:
  is_word_type sty /\ type_widens_to tenv sty ty ==> sty = ty
Proof
  simp[type_widens_to_def] >> metis_tac[cj 1 selected_word_fits_eq]
QED

Theorem return_selected_located_suffix:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es se sa s0 ee v op s /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  lowered_value_type ce e = expr_type e /\
  return_consumer_suffix ce ret (lowered_value_type ce e) op sa = (u,sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ (!y. op = Var y ==> not_fresh_at sa y) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  drule return_site_valued_not_none >> strip_tac >>
  Cases_on `ce.ce_raw_return`
  >- (`lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by fs[] >>
      drule_all return_selected_raw_bytes >> strip_tac >>
      drule_all return_site_raw_bytes_path >> simp[]) >>
  Cases_on `is_word_type ret`
  >- (drule_all return_site_nonraw_word_path >> simp[]) >>
  Cases_on `expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)`
  >- (drule_all return_selected_nocopy_path >> simp[]) >>
  `~is_word_type (expr_type e)` by
    (drule_all return_site_value_semantics >> strip_tac >>
     metis_tac[selected_source_word_eq]) >>
  `~(is_bytestring_type ret /\ is_bytestring_type (lowered_value_type ce e)) /\
    lowered_value_type ce e <> ret` by metis_tac[] >>
  drule_all return_consumer_normalize_split >> strip_tac >>
  `compile_store_memory_typed ce buf.buf_operand ret op (expr_type e) sm = ((),sn)`
    by metis_tac[] >>
  `compile_external_return (SOME buf.buf_operand) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sn = (u,sf)` by gvs[] >>
  drule_all return_selected_located_normalize_path >> simp[]
QED

Theorem selected_zero_not_scalar[local]:
  type_memory_bytes ce ty = 0 ==>
  ~is_word_type ty /\ ~is_bytestring_type ty
Proof
  Cases_on `ty` >> simp[is_word_type_def, is_bytestring_type_def, type_memory_bytes_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, is_bytestring_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, is_bytestring_type_def, type_memory_bytes_def]
QED

Theorem return_selected_bufferless_suffix:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  ce.ce_func_info name = (0,0,pvs) /\ phy = ce.ce_func_return_type name /\
  lowered_value_type ce e = phy /\
  type_widens_to (get_tenv cx) phy (expr_type e) /\
  evaluate_type (get_tenv cx) phy = SOME stv /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  stmt_state_rel ctx func ce cx ee s /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  return_consumer_suffix ce ret (lowered_value_type ce e) (Lit 0w) sa = (u,sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac >> drule_all return_selected_consumer_resources >> strip_tac >>
  drule return_site_copy_metadata >> strip_tac >>
  drule_all return_selected_bufferless >> disch_tac >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  (Q.SUBGOAL_THEN `(phy = NoneT \/ type_memory_bytes ce phy = 0)` assume_tac
    >- metis_tac[]) >>
  drule_all return_bufferless_site_zero_semantics >> strip_tac >>
  `~is_word_type ret /\ ~is_bytestring_type ret` by
    metis_tac[selected_zero_not_scalar] >>
  `~ce.ce_raw_return` by
    (Cases_on `ce.ce_raw_return` >> simp[] >>
     `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by fs[] >>
     drule_all return_selected_raw_bytes >> simp[]) >>
  Cases_on `phy = ret`
  >- (`compile_external_return (SOME (Lit 0w)) F F ce.ce_ret_enc_info
         ce.ce_max_return_size F nkey F (mut = View) sa = (u,sf)` by
        (qpat_x_assum `return_consumer_suffix _ _ _ _ _ = _` mp_tac >>
         gvs[return_consumer_suffix_def, comp_bind_def, comp_return_def]) >>
      drule_all return_selected_bufferless_nocopy_path >> simp[]) >>
  `~(is_bytestring_type ret /\ is_bytestring_type (lowered_value_type ce e)) /\
    lowered_value_type ce e <> ret` by metis_tac[] >>
  drule_all return_consumer_normalize_split >> strip_tac >>
  `compile_store_memory_typed ce buf.buf_operand ret (Lit 0w) phy sm = ((),sn)`
    by metis_tac[] >>
  `compile_external_return (SOME buf.buf_operand) F F ce.ce_ret_enc_info
    ce.ce_max_return_size F nkey F (mut = View) sn = (u,sf)` by gvs[] >>
  drule_all return_selected_bufferless_normalize_path >> simp[]
QED
