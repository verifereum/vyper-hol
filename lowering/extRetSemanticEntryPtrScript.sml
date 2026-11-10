Theory extRetSemanticEntryPtr
Ancestors
  extRetInternalCallTypingPtr exprSimHypsDefs memoryLocalRhsProps
  vyperAST vyperInterpreter vyperTyping vyperTypeInvariants vyperTypeCallGraph
  vyperTypeEvalSoundness vyperTypeSystem exprLowering finite_map loweringPosts typedCopyPtr bodyPtrStructLitUniformTypes
  bodyPtrIfExpStoreContract bodyPtrDefs fragGasPathPtr gasSummary
  stmtAbortPtr venomExecSemantics venomInstProofs vyperState exprSimDefs
  emitHelperProps fragExec
Libs
  monadsyntax

Theorem ext_ret_internal_call_lowered_runtime_typed:
  !ce cx env es ann id args drv sig v er.
    expr_sim_inv ce cx env es /\
    well_typed_expr env (Call ann (IntCall id) args drv) /\
    call_evaluation_safe cx (int_calls_expr (Call ann (IntCall id) args drv)) /\
    FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v,er) ==>
    value_runtime_typed env
      (lowered_value_type ce (Call ann (IntCall id) args drv)) v
Proof
  rpt strip_tac >>
  drule_all ext_ret_internal_call_read_signature_typed >> strip_tac >>
  `ce.ce_func_return_type (nsid_to_string id) = sig.ret_ty` by
    gvs[expr_sim_inv_def] >>
  simp[lowered_value_type_def]
QED

Theorem ext_ret_internal_call_lowered_runtime_layout:
  !ce cx env es ann id args drv sig v er.
    expr_sim_inv ce cx env es /\
    well_typed_expr env (Call ann (IntCall id) args drv) /\
    call_evaluation_safe cx (int_calls_expr (Call ann (IntCall id) args drv)) /\
    FLOOKUP env.fn_sigs id = SOME sig /\
    (do r <- eval_expr cx (Call ann (IntCall id) args drv);
        read_result cx r od) es = (INL v,er) ==>
    ?tv. evaluate_type (get_tenv cx)
           (lowered_value_type ce (Call ann (IntCall id) args drv)) = SOME tv /\
         value_has_type tv v /\
         type_memory_bytes ce (lowered_value_type ce
           (Call ann (IntCall id) args drv)) = type_memory_size tv
Proof
  rpt strip_tac >>
  drule_all ext_ret_internal_call_lowered_runtime_typed >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem ext_ret_read_post_runtime_typed:
  !ce cx env e es v er.
    expr_sim_inv ce cx env es /\ well_typed_expr env e /\
    call_evaluation_safe cx (int_calls_expr e) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,er) ==>
    value_runtime_typed env (post_value_type ce e) v
Proof
  rpt strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
      disch_then (qspec_then `env` mp_tac) >>
      gvs[expr_sim_inv_def]) >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >> gvs[] >>
  `?sig. FLOOKUP env.fn_sigs fid = SOME sig` by
    (Cases_on `fid` >> gvs[well_typed_expr_def]) >>
  drule_all ext_ret_internal_call_lowered_runtime_typed >>
  gvs[post_value_type_def, expr_type_def] >>
  Cases_on `is_word_type ty \/ is_bytestring_type ty` >> gvs[]
QED

Theorem ext_ret_read_post_runtime_layout:
  !ce cx env e es v er.
    expr_sim_inv ce cx env es /\ well_typed_expr env e /\
    call_evaluation_safe cx (int_calls_expr e) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,er) ==>
    ?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
         value_has_type tv v /\
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tv
Proof
  rpt strip_tac >>
  drule_all ext_ret_read_post_runtime_typed >> strip_tac >>
  drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem ext_ret_return_post_runtime_layout:
  !ce cx env e es v er ret.
    expr_sim_inv ce cx env es /\
    IS_SOME (type_stmt env ret (Return (SOME e))) /\
    call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,er) ==>
    ?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
         value_has_type tv v /\
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tv
Proof
  rpt strip_tac >>
  gvs[type_stmt_return_some_iff, int_calls_stmt_def, int_calls_expr_def] >>
  drule_all ext_ret_read_post_runtime_layout >> simp[]
QED

Theorem ext_ret_aggregate_lowered_post_type:
  !ce e env.
    well_typed_expr env e /\ ~is_word_type (expr_type e) /\
    ~is_bytestring_type (expr_type e) ==>
    lowered_value_type ce e = post_value_type ce e
Proof
  rpt strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- metis_tac[structlit_uniform_nonword_lowered_type] >>
  `?ty fid args drv. e = Call ty (IntCall fid) args drv` by
    metis_tac[post_value_type_not_int_call] >>
  gvs[post_value_type_def, expr_type_def]
QED

Theorem ext_ret_aggregate_return_runtime_layout:
  !ce cx env e es v er ret.
    expr_sim_inv ce cx env es /\
    IS_SOME (type_stmt env ret (Return (SOME e))) /\
    call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
    ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,er) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\
         type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv
Proof
  rpt strip_tac >>
  drule_all ext_ret_return_post_runtime_layout >>
  `well_typed_expr env e` by gvs[type_stmt_return_some_iff] >>
  drule_all ext_ret_aggregate_lowered_post_type >> simp[]
QED

(* The global-metadata rejection is itself a permitted pointer endpoint for
   a successful source Return. No functional-return agreement is claimed. *)
Theorem ext_ret_invalid_normalize_outcome:
  !D ctx fn PG ce dst dty src sty sa sb s G tn es v tops Q.
    ~is_word_type dty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
    ~acyclic_struct_metadata ce.ce_struct_fields /\
    compile_store_memory_typed ce dst dty src sty sa = ((),sb) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr D tops (ctx,fn) PG (raise (ReturnException v))
      (es,s,G,tn) Q (\res ee gt r. stmt_exit_ptr (\v es gt r. T) ee res gt r)
Proof
  rpt strip_tac >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id INVALID [] []) s = Abort a t` by
    metis_tac[step_invalid] >>
  drule_all store_memory_typed_invalid_counted >> strip_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, raise_def] >>
  qexistsl_tac [`INR (ReturnException v)`, `es`, `G`, `tn`, `Abort a t`] >>
  simp[stmt_exit_ptr_def, exit_result_def]
QED
