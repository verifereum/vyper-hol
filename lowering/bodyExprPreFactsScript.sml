(* Shared expression-call and body-precondition boundaries. *)
Theory bodyExprPreFacts
Ancestors
  exprSimHypsDefs gasContext vyperABI
  supportedExprTraverse supportedExprs supportedDecls supportedStmts
  vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState compileEnv allocLimits
Libs
  monadsyntax

(* An expression with no internal call in it has no internal calls to
   make.  Reasons and conditions are pure (supported_pure_no_internal_call). *)
Theorem no_internal_call_int_calls:
  (!e. ~supported_expr_exists expr_internal_call_root e ==>
       int_calls_expr e = []) /\
  (!t. ~supported_target_exists expr_internal_call_root t ==>
       int_calls_target t = []) /\
  (!es. ~supported_exprs_exists expr_internal_call_root es ==>
        int_calls_exprs es = []) /\
  (!eo. ~supported_opt_exists expr_internal_call_root eo ==>
        int_calls_opt eo = []) /\
  (!kes. ~supported_fields_exists expr_internal_call_root kes ==>
         int_calls_named_exprs kes = [])
Proof
  ho_match_mp_tac int_calls_expr_ind >>
  rw[int_calls_expr_def, supported_expr_exists_def,
     expr_internal_call_root_def]
QED

Theorem supported_pure_int_calls:
  !tops e. supported_pure_expr tops e ==> int_calls_expr e = []
Proof
  metis_tac[supported_pure_no_internal_call, expr_has_internal_call_def,
            no_internal_call_int_calls]
QED

(* supported_function_decl finds only the main module's functions. *)
Theorem supported_function_decl_main[local]:
  !tops id vis. IS_SOME (supported_function_decl tops id vis) ==> FST id = NONE
Proof
  Cases >> rpt gen_tac >> PairCases_on `id` >>
  simp[supported_function_decl_def] >>
  Cases_on `id0` >> simp[]
QED

(* An expression with no effect in it has no internal calls to make. *)
Theorem no_effect_int_calls[local]:
  (!e. ~supported_expr_exists expr_effect_root e ==> int_calls_expr e = []) /\
  (!es. ~supported_exprs_exists expr_effect_root es ==>
        int_calls_exprs es = [])
Proof
  `!x. expr_internal_call_root x ==> expr_effect_root x` by
    (Cases >> simp[expr_internal_call_root_def, expr_effect_root_def]) >>
  conj_tac >> rpt strip_tac
  >- (irule (cj 1 no_internal_call_int_calls) >>
      metis_tac[supported_expr_exists_mono]) >>
  irule (cj 3 no_internal_call_int_calls) >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_pure_forms_int_calls[local]:
  (!tops e. supported_pure_expr tops e ==> int_calls_expr e = []) /\
  (!tops es. supported_pure_exprs tops es ==> int_calls_exprs es = []) /\
  (!tops e. supported_place_expr tops e ==> int_calls_expr e = [])
Proof
  metis_tac[no_effect_int_calls, supported_pure_no_effect]
QED

Theorem supported_effect_main_int_calls[local]:
  (!tops e. supported_effect_expr tops e ==>
      EVERY (\c. FST c = NONE) (int_calls_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
      EVERY (\c. FST c = NONE) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def, int_calls_expr_def] >>
  imp_res_tac supported_pure_forms_int_calls >>
  imp_res_tac supported_function_decl_main >> gvs[]
QED

(* A supported expression runs no EVM code, and its internal calls are to
   the main module, as expr_body_pre asks. *)
Theorem supported_expr_body_calls:
  !tops e. supported_expr tops e ==>
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[supported_expr_no_evm_run] >>
  pop_assum mp_tac >> simp[supportedExprsTheory.supported_expr_def] >> strip_tac >>
  imp_res_tac supported_pure_int_calls >>
  imp_res_tac supported_effect_main_int_calls >> gvs[]
QED

(* The same for a reason, which may also be a string literal. *)
Theorem supported_string_reason_body_calls:
  !tops e. supported_string_reason tops e ==>
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?t str. e = Literal t (StringL str)`
  >- gvs[expr_has_evm_run_def, supported_expr_exists_def,
         expr_evm_run_root_def, int_calls_expr_def] >>
  irule supported_expr_body_calls >> qexists_tac `tops` >>
  simp[supportedExprsTheory.supported_expr_def] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def]
QED

(* A statement's expression meets expr_body_pre. *)
Theorem stmt_expr_body_pre:
  !cenv cx env e es calls.
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    ~supported_expr_exists
       (\e. ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e /\
    call_evaluation_safe cx (int_calls_expr e ++ calls) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    (int_calls_expr e <> [] ==>
     ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops) /\
    (!target. supported_expr_exists
       (expr_abi_decode_target_root target) e ==>
       occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `byte_widths_expr e /\ alloc_limits_expr cenv e` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> metis_tac[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    metis_tac[call_evaluation_safe_append_left] >>
  simp[expr_body_pre_def] >>
  Cases_on `int_calls_expr e` >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_EXPRESSION_PRE_AUDIT OK\n"
     else raise Fail "body expression precondition inherited admission"
  end) [no_internal_call_int_calls, supported_pure_int_calls,
        supported_expr_body_calls, supported_string_reason_body_calls,
        stmt_expr_body_pre];
