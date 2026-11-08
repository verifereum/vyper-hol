(* Body memory safety at the actual frame entry and continuing landings.

   body_mem_mutual: by evaluate_ind, every statement, statement list and
   expression of a frame simulates with memory (bodyMemoryPreds'
   predicates), the memory twin of bodySimMain's body_sim_mutual.  Each
   case is a proved memory case lemma of the body*Memory theories, a
   bodyMem* leaf theory's case lemma, or a short tactic below; the
   per-constructor lemmas below split an expression case between the
   proved subcases and its leaf.

   TOP-LEVEL:
     body_mem_mutual    - the predicates, by evaluate_ind
     body_stmts_sim_mem - the statement-list judgment it gives *)
Theory bodyMemory
Ancestors
  bodyMemoryDefs stmtMemory stmtSimJumpMem stmtRaiseMemory stmtIfMemory
  stmtAssertMemory fragLoopMemory
  allocaHistoryFragment builtinBytesMemory concatMemory
  bodySimMain bodySimStmtCases bodySimDeclCases
  bodySim exprSimHyps stmtLoweringProps exprLoweringProps supportedProgram
  vyperInterpreter vyperTypeSystem vyperState vyperContext supportedStmts
  bodyMemoryPreds bodyReturnMemory bodyExprStmtMemory bodySeqMemory
  bodyFlagMemberMemory bodyCalldataMemory bodyLiteralForceMemory
  exprSimOperators
  bodyMemRaiseReason bodyMemAssert bodyMemAssertReason bodyMemLog
  bodyMemAnnAssign bodyMemAppend bodyMemAssign bodyMemAssignTuple
  bodyMemAugAssign bodyMemIf bodyMemFor bodyMemName bodyMemToplevel
  bodyMemIfExp bodyMemLiteralOther bodyMemStructLit bodyMemSubscript
  bodyMemAttribute bodyMemBop bodyMemBopInLiteral bodyMemMakeArray
  bodyMemEcArith bodyMemBuiltinUnary bodyMemBuiltinRest bodyMemPopName
  bodyMemPopNested bodyMemTypeBuiltin bodyMemSend bodyMemExtCall
  bodyMemIntCall bodyMemRawCall bodyMemRawCallCalldata bodyMemRawLog
  bodyMemRawRevert bodyMemSelfDestruct bodyMemCreate

val _ = Parse.hide "body";

val body_mem_ind = evaluate_ind
  |> Q.SPECL [`body_stmt_mem_ok`, `body_stmts_mem_ok`, `body_iterator_mem_ok`,
              `body_for_mem_ok`, `body_expr_mem_ok`, `body_exprs_mem_ok`,
              `body_base_target_mem_ok`, `body_base_target_mem_ok`,
              `body_tuple_target_mem_ok`, `body_tuple_targets_mem_ok`,
              `body_results_mem_ok`];

(* ===== Expression cases split between proved subcases and a leaf ===== *)

Theorem body_literal_mem_ok:
  !cx ann l. body_expr_mem_ok cx (Literal ann l)
Proof
  metis_tac[body_literal_word_mem_case, body_literal_other_mem_case]
QED

Theorem body_builtin_mem_ok:
  !cx ty bt es.
    (!s'' x t v code_ty addr s3 tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = SOME v /\ v = (code_ty,addr) /\
       eval_exprs cx (TL es) s3 = (INL tail_vs,t') ==>
       body_exprs_mem_ok cx [addr]) /\
    (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = SOME v /\ v = (code_ty,addr) ==>
       body_exprs_mem_ok cx (TL es)) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas /\
       code_slice_source bt es = NONE ==>
       body_exprs_mem_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_mem_ok cx (HD es)) ==>
    body_expr_mem_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  (* A code slice reads x.code without evaluating it; the operand list as a
     whole is still memory-safe, since a bare x.code is (body_acc_code_mem). *)
  `!s'' x t.
     type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
     (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
     body_exprs_mem_ok cx es` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `code_slice_source bt es`
     >- (first_x_assum irule >> metis_tac[]) >>
     rename1 `code_slice_source bt es = SOME v` >> PairCases_on `v` >>
     `body_exprs_mem_ok cx (TL es)` by metis_tac[] >>
     gvs[vyperInterpreterTheory.code_slice_source_SOME] >>
     simp[Once body_exprs_mem_ok_def, bodyMemBiAccTheory.body_acc_code_mem]) >>
  qpat_x_assum `!s'' x t v code_ty addr s3 tail_vs t'. _` kall_tac >>
  qpat_x_assum `!s'' x t v code_ty addr. _` kall_tac >>
  qpat_x_assum `!s'' x t. _ /\ _ /\ _ /\ code_slice_source bt es = NONE ==> _` kall_tac >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len /\ bt <> Env MsgGas ==>
   body_exprs_mem_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `?bop. bt = Bop bop`
  >- (gvs[] >> Cases_on `?e1 e2. es = [e1; e2]`
      >- (gvs[builtin_args_length_ok_def] >>
          Cases_on `(bop = In \/ bop = NotIn) /\
                    ?a t n elems. e2 = Builtin a (MakeArray t n) elems`
          >- (gvs[] >> irule body_bop_in_literal_mem_case >> simp[]) >>
          irule body_bop_mem_case >> gvs[]) >>
      simp[body_expr_mem_ok_def] >> metis_tac[expr_body_pre_bop_args]) >>
  Cases_on `?t n. bt = MakeArray t n`
  >- (gvs[] >> irule body_make_array_mem_case >> gvs[]) >>
  Cases_on `bt = ECAdd`
  >- (gvs[] >> irule body_ec_arith_mem_case >> gvs[]) >>
  Cases_on `bt = ECMul`
  >- (gvs[] >> irule body_ec_arith_mem_case >> gvs[]) >>
  Cases_on `bt = CalldataLen` >- simp[body_calldatalen_mem_case] >>
  Cases_on `?e. es = [e] /\ (bt = Neg \/ bt = Abs \/ bt = Not)`
  >- (gvs[] >> irule body_builtin_unary_mem_case >>
      gvs[builtin_args_length_ok_def, body_exprs_mem_ok_def]) >>
  irule body_builtin_rest_mem_case >> gvs[] >> metis_tac[]
QED

Theorem body_pop_mem_ok:
  !cx ann bt. body_base_target_mem_ok cx bt ==> body_expr_mem_ok cx (Pop ann bt)
Proof
  rpt strip_tac >>
  Cases_on `(?id. bt = NameTarget id) \/ (?nid. bt = TopLevelNameTarget nid)`
  >- metis_tac[body_pop_name_mem_case] >>
  irule body_pop_nested_mem_case >> gvs[]
QED

(* ===== The induction ===== *)

Theorem body_mem_mutual:
  (!cx s. body_stmt_mem_ok cx s) /\ (!cx ss. body_stmts_mem_ok cx ss) /\
  (!cx it. body_iterator_mem_ok cx it) /\
  (!cx tyv nm body vs. body_for_mem_ok cx tyv nm body vs) /\
  (!cx e. body_expr_mem_ok cx e) /\ (!cx es. body_exprs_mem_ok cx es) /\
  (!cx t. body_base_target_mem_ok cx t) /\
  (!cx g v. body_tuple_target_mem_ok cx g v) /\
  (!cx gs vs. body_tuple_targets_mem_ok cx gs vs) /\
  (!cx es. body_results_mem_ok cx es)
Proof
  mp_tac body_mem_ind >> impl_tac
  >- (rpt conj_tac >| [
    (* 0 *) MATCH_ACCEPT_TAC body_pass_mem_ok,
    (* 1 *) MATCH_ACCEPT_TAC body_continue_mem_ok,
    (* 2 *) MATCH_ACCEPT_TAC body_break_mem_ok,
    (* 3 *) MATCH_ACCEPT_TAC body_return_none_mem_ok,
    (* 4 *) MATCH_ACCEPT_TAC body_return_mem_ok,
    (* 5 *) rw[body_stmt_mem_ok_def] >> irule compile_raise_frag_mem >> simp[],
    (* 6 *) rw[body_stmt_mem_ok_def] >> irule compile_raise_frag_mem >> simp[],
    (* 7 *) MATCH_ACCEPT_TAC body_raise_reason_mem_case,
    (* 8 *) rw[body_stmt_mem_ok_def, supported_stmt_def,
               supported_raise_reason_def],
    (* 9 *) rpt strip_tac >> irule body_assert_mem_case >> simp[],
    (* 10 *) rpt strip_tac >> irule body_assert_mem_case >> simp[],
    (* 11 *) MATCH_ACCEPT_TAC body_assert_reason_mem_case,
    (* 12 *) rw[body_stmt_mem_ok_def, supported_stmt_def,
                supported_assert_reason_def],
    (* 13 *) MATCH_ACCEPT_TAC body_log_mem_case,
    (* 14 *) MATCH_ACCEPT_TAC body_annassign_mem_case,
    (* 15 *) MATCH_ACCEPT_TAC body_append_mem_case,
    (* 16 *) MATCH_ACCEPT_TAC body_assign_mem_case,
    (* 17 *) MATCH_ACCEPT_TAC body_assign_tuple_mem_case,
    (* 18 *) MATCH_ACCEPT_TAC body_augassign_mem_case,
    (* 19 *) MATCH_ACCEPT_TAC body_if_mem_ok,
    (* 20 *) MATCH_ACCEPT_TAC body_for_mem_case,
    (* 21 *) MATCH_ACCEPT_TAC body_expr_stmt_mem_case,
    (* 22 *) MATCH_ACCEPT_TAC body_nil_mem_ok,
    (* 23 *) MATCH_ACCEPT_TAC body_stmts_cons_mem_case,
    (* 24 *) simp[body_iterator_mem_ok_def],
    (* 25 *) rw[body_iterator_mem_ok_def] >> metis_tac[],
    (* 26 *) simp[body_for_mem_ok_def],
    (* 27 *) rw[body_for_mem_ok_def] >> first_x_assum irule >>
             simp[push_scope_with_var_def, return_def],
    (* 28 *) simp[body_name_mem_ok],
    (* 29 *) simp[body_toplevel_mem_ok],
    (* 30 *) simp[body_flag_member_mem_case],
    (* 31 *) MATCH_ACCEPT_TAC body_ifexp_mem_ok,
    (* 32 *) simp[body_literal_mem_ok],
    (* 33 *) MATCH_ACCEPT_TAC body_structlit_mem_case,
    (* 34 *) MATCH_ACCEPT_TAC body_subscript_mem_case,
    (* 35 *) MATCH_ACCEPT_TAC body_attribute_mem_ok,
    (* 36 *) MATCH_ACCEPT_TAC body_builtin_mem_ok,
    (* 37 *) MATCH_ACCEPT_TAC body_pop_mem_ok,
    (* 38 *) MATCH_ACCEPT_TAC body_type_builtin_mem_case,
    (* 39 *) MATCH_ACCEPT_TAC body_send_mem_case,
    (* 40 *) MATCH_ACCEPT_TAC body_extcall_mem_case,
    (* 41 *) MATCH_ACCEPT_TAC body_intcall_mem_case,
    (* 42 *) MATCH_ACCEPT_TAC body_raw_call_mem_case,
    (* 43 *) MATCH_ACCEPT_TAC body_raw_call_calldata_mem_case,
    (* 44 *) MATCH_ACCEPT_TAC body_raw_log_mem_case,
    (* 45 *) MATCH_ACCEPT_TAC body_raw_revert_mem_case,
    (* 46 *) MATCH_ACCEPT_TAC body_selfdestruct_mem_case,
    (* 47 *) MATCH_ACCEPT_TAC body_create_mem_case,
    (* 48 *) simp[body_exprs_mem_ok_def],
    (* 49 *) rw[body_exprs_mem_ok_def] >> metis_tac[],
    (* 50 *) simp[body_base_target_mem_ok_def],
    (* 51 *) simp[body_base_target_mem_ok_def],
    (* 52 *) simp[body_base_target_mem_ok_def],
    (* 53 *) rw[body_base_target_mem_ok_def] >> metis_tac[],
    (* 54 *) simp[],
    (* 55 *) simp[body_tuple_target_mem_ok_def],
    (* 56 *) simp[body_tuple_target_mem_ok_def],
    (* 57 *) simp[body_tuple_target_mem_ok_def],
    (* 58 *) rw[body_tuple_target_mem_ok_def] >> metis_tac[],
    (* 59 *) simp[body_tuple_target_mem_ok_def],
    (* 60 *) simp[body_tuple_target_mem_ok_def],
    (* 61 *) simp[body_results_mem_ok_def],
    (* 62 *) rw[body_results_mem_ok_def] >> metis_tac[]
  ]) >>
  simp[]
QED

(* ===== The judgment it gives ===== *)

Theorem body_stmts_sim_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
Proof
  ACCEPT_TAC (MATCH_MP body_stmts_mem_projection
                (CONJUNCT1 (CONJUNCT2 body_mem_mutual)))
QED
