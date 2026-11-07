(*
 * The pointer twin of bodySimMain's induction: the cases for the external calls and the effectful builtins.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_send_case_ptr
 *   body_extcall_case_ptr
 *   body_raw_call_case_ptr
 *   body_raw_call_calldata_case_ptr
 *   body_raw_log_case_ptr
 *   body_raw_revert_case_ptr
 *   body_selfdestruct_case_ptr
 *   body_create_case_ptr
 *)
Theory bodyPtrCallCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list bodyPtrCallResidual
  bodyPtrCallCalldata exprSendPtr bodyWordArgsReady typedWordArgsReadyPtr
  exprSimSend exprSimPrecompiles exprSimHypsDefs rawCallExpressionPtr

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_send_case_ptr:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Call v12 (Send has_gas) es v13)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[body_expr_ptr_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >>
  `body_exprs_ptr_ok cx es` by
    (first_x_assum irule >>
     simp[type_check_def, check_def, assert_def] >> metis_tac[]) >>
  `!e s. MEM e es /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >> fs[EVERY_MEM]) >>
  `typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) es` by
    (irule body_word_args_ready >> simp[] >> metis_tac[]) >>
  `ptr_args_ready d ctx PG func cenv cx expr_type (expr_sim_inv cenv cx env) es` by
    (irule body_exprs_ptr_ok_ready >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule send_expr_sim_ptr >> qexists_tac `env` >> simp[]) >>
  irule send_expr_vv_sim_ptr >> qexists_tac `env` >> simp[]
QED

(* bodyPtrCallResidual's residual, until extcall's lowering port and the
   decoder's compare are settled. *)
Theorem body_extcall_case_ptr:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ptr_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ptr_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ptr_ok cx (TAKE 1 es) ==>
    body_expr_ptr_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  ACCEPT_TAC extcall_case_ptr_residual
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_raw_call_case_ptr:
  !cx ty flags es v18.
    body_exprs_ptr_ok cx es ==>
    body_expr_ptr_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule raw_call_sim_ptr >> metis_tac[]) >>
  irule raw_call_vv_sim_ptr >> metis_tac[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_raw_call_calldata_case_ptr:
  !cx ty flags es v19.
    body_exprs_ptr_ok cx es ==>
    body_expr_ptr_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  (* Vacuous: its DALLOCA contradicts ~ctx_has_dalloca (bodyPtrCallCalldata). *)
  rw[body_expr_ptr_ok_def] >>
  fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  drule raw_call_calldata_ptr_vacuous >> simp[]
QED

(* bodyPtrCallResidual's residual, until RawLog's lowering lands. *)
Theorem body_raw_log_case_ptr:
  !cx v20 es v21.
    body_exprs_ptr_ok cx es ==> body_expr_ptr_ok cx (Call v20 RawLog es v21)
Proof
  ACCEPT_TAC raw_log_case_ptr_residual
QED

(* bodyPtrCallResidual's residual, until RawRevert's lowering lands. *)
Theorem body_raw_revert_case_ptr:
  !cx v22 es v23.
    body_exprs_ptr_ok cx es ==> body_expr_ptr_ok cx (Call v22 RawRevert es v23)
Proof
  ACCEPT_TAC raw_revert_case_ptr_residual
QED

(* Vacuous: expr_body_pre excludes selfdestruct (expr_evm_run_root). *)
Theorem body_selfdestruct_case_ptr:
  !cx v24 es v25.
    body_exprs_ptr_ok cx es ==>
    body_expr_ptr_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rw[body_expr_ptr_ok_def] >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      supportedExprTraverseTheory.expr_evm_run_root_def]
QED

(* Vacuous: expr_body_pre excludes the creates, which the source runs on
   the EVM (expr_evm_run_root). *)
Theorem body_create_case_ptr:
  !cx ty kind has_salt rof v26 es v27.
    (!raw_args s'' prefix t s'3' code_size t'.
       kind = CreateFromBlueprint raw_args /\
       eval_exprs cx (TAKE (if has_salt then 4 else 3) es) s'' =
       (INL prefix,t) /\
       check_create_blueprint has_salt prefix s'3' = (INL code_size,t') ==>
       body_results_ptr_ok cx (DROP (if has_salt then 4 else 3) es)) /\
    (!raw_args.
       kind = CreateFromBlueprint raw_args ==>
       body_exprs_ptr_ok cx (TAKE (if has_salt then 4 else 3) es)) /\
    (!s'' prefix t ctor_es nargs s'3' results t' s'4' args t''.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) /\
       eval_expr_results cx (TAKE nargs ctor_es) s'3' = (INL results,t') /\
       read_results cx results s'4' = (INL args,t'') ==>
       body_exprs_ptr_ok cx (DROP nargs ctor_es)) /\
    (!s'' prefix t ctor_es nargs.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) ==>
       body_results_ptr_ok cx (TAKE nargs ctor_es)) /\
    (kind = CreateCopyOf ==> body_exprs_ptr_ok cx es) /\
    (kind = CreateMinimalProxy ==> body_exprs_ptr_ok cx es) /\
    (kind = RawCreate ==> body_exprs_ptr_ok cx (TAKE 2 es)) ==>
    body_expr_ptr_ok cx (Call ty (CreateTarget kind has_salt rof v26) es v27)
Proof
  rw[body_expr_ptr_ok_def] >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      supportedExprTraverseTheory.expr_evm_run_root_def]
QED
