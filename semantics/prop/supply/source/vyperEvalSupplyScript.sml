(* TOP-LEVEL: eval_source_supply_mutual for all nine evaluator forms.
 * Helpers: indexed monadic decomposition and guarded IH matching.
 *)
Theory vyperEvalSupply
Ancestors
  list pair option vyperMisc vyperSourceSupplyDefs vyperSourcePrimitiveSupply
  vyperSourceCompoundSupply vyperSourceOracleSupply vyperSourceTransferSupply
  vyperSourceCallSupply vyperSourceCreateSupply vyperSupplyBoundary
  vyperAccountSupply vyperAdapterSupply vyperInterpreter vyperCreate
  vyperState vyperCallOutcome extCallOracle
Libs
  vyperSupplyProofLib

val supply_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [source_supply_reads, source_supply_field_updates, source_supply_locals,
   source_supply_locks, source_supply_action_return, source_supply_action_raise,
   source_supply_action_write_storage, source_supply_action_set_storage_backend,
   source_supply_action_set_global, source_supply_assignment,
   source_supply_handlers, source_supply_create_soft_failure,
   source_supply_check_create_blueprint, source_supply_action_raw_call,
   source_supply_action_ext_call, source_supply_action_send,
   source_supply_action_create, source_supply_action_transfer,
   source_supply_action_read, source_supply_action_take]);

val supply_net = vyperSupplyProofLib.fact_net supply_facts
  [source_supply_action_bind, source_supply_action_finally,
   source_supply_action_finally_unless_halt,
   source_supply_action_try,
   source_supply_action_accounts_const, source_supply_action_adopt];

val SUPPLY_STEP = FIRST [
  first_assum ACCEPT_TAC,
  MATCH_ACCEPT_TAC source_supply_action_selfdestruct_effect,
  vyperSupplyProofLib.solve supply_net,
  CONV_TAC (HO_REWR_CONV FORALL_PROD), gen_tac,
  CONV_TAC (RAND_CONV (CHANGED_CONV vyperSupplyProofLib.head_conv)),
  CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
  CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
  strip_tac, conj_tac, vyperSupplyProofLib.case_tac];

val SUPPLY_FINISH_TAC = simp_tac bool_ss [FST, SND] >>
  vyperSupplyProofLib.finish_goal;
val SUPPLY_TAC = rpt SUPPLY_STEP >> SUPPLY_FINISH_TAC;

fun SUPPLY_SUSPEND_CASE (goal as (_,w)) =
  let
    fun cname tm = #Name (dest_thy_const (fst (strip_comb tm)));
    val (f,args) = strip_comb (rand w);
    val (c,cargs) = strip_comb (List.last args);
    val name = cname c;
    val tag = cname f ^ "_" ^ name ^
      (if name = "Return" orelse name = "Raise" then
         "_" ^ cname (List.hd cargs)
       else if name = "Assert" then "_" ^ cname (List.last cargs)
       else if name = "Call" then "_" ^ cname (List.nth (cargs,1))
       else "");
  in suspend tag goal end;


Theorem eval_source_supply_mutual:
  (!cx s. source_supply_action (eval_stmt cx s)) /\
  (!cx ss. source_supply_action (eval_stmts cx ss)) /\
  (!cx it. source_supply_action (eval_iterator cx it)) /\
  (!cx target. source_supply_action (eval_target cx target)) /\
  (!cx targets. source_supply_action (eval_targets cx targets)) /\
  (!cx bt. source_supply_action (eval_base_target cx bt)) /\
  (!cx tyv name body values. source_supply_action (eval_for cx tyv name body values)) /\
  (!cx e. source_supply_action (eval_expr cx e)) /\
  (!cx es. source_supply_action (eval_exprs cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY strip_tac >> SUPPLY_SUSPEND_CASE
QED

Resume eval_source_supply_mutual[eval_expr_Call_ExtCall]:
  simp[Once evaluate_def] >> rpt SUPPLY_STEP >>
  SUPPLY_FINISH_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Pass]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Continue]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Break]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Return_NONE]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Return_SOME]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Raise_RaiseBare]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Raise_RaiseUnreachable]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Raise_RaiseReason]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Assert_AssertBare]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Assert_AssertUnreachable]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Assert_AssertReason]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Log]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_AnnAssign]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Append]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Assign]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_AugAssign]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_If]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_For]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmt_Expr]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmts_NIL]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_stmts_CONS]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_iterator_Array]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_iterator_Range]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_target_BaseTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_target_TupleTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_targets_NIL]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_targets_CONS]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_base_target_NameTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_base_target_TopLevelNameTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_base_target_AttributeTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_base_target_SubscriptTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_for_NIL]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_for_CONS]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Name]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_TopLevelName]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_FlagMember]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_IfExp]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Literal]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_StructLit]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Subscript]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Attribute]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Builtin]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Pop]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_TypeBuiltin]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_Send]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_IntCall]:
  simp[Once evaluate_def] >> rpt SUPPLY_STEP >>
  SUPPLY_FINISH_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_RawCallTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_RawCallCalldataTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_RawLog]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_RawRevert]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_SelfDestructTarget]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_expr_Call_CreateTarget]:
  Cases_on `kind` >> Cases_on `has_salt` >> gvs[] >>
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_exprs_NIL]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Resume eval_source_supply_mutual[eval_exprs_CONS]:
  simp[Once evaluate_def] >> SUPPLY_TAC
QED

Finalise eval_source_supply_mutual

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperEvalSupply");
