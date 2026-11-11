(*
 * Statement simulation: an augmented assignment to a word local (#637)
 *
 * AugAssign over stmt_frag (stmtSim) for x op= e where x is a local held
 * through its pointer and of a type whose values are word_values.  x op= e
 * is x = x op e on both sides: the source reads x, evaluates e, runs the
 * operator and writes x, as evaluating the expression x op e annotated with
 * x's type and then writing x would, and the lowering is x op e's lowering
 * at x's type (an MLOAD of the pointer, e, compile_binop) and then an
 * MSTORE at the pointer.  So the expression side is compile_bop_word_case's
 * (exprSimOperators), the checked operators' aborts (overflow, division by
 * zero) among its exits, and ** and the narrow or negative shifts rest on
 * exprSimBinopFrag's cheats (#572).  The store is stmtSimAssignStore's.
 *
 * TOP-LEVEL:
 *   compile_augassign_local_case      — x op= e on a word local, for every
 *                                       outcome, given e's expr_sim_case
 *   compile_augassign_local_stmt_frag — the same, given e's expr_sim_ok
 *   eval_augassign_local_bop          — x op= e evaluates as x op e, then
 *                                       writes x
 *   augassign_local_code_bop          — its code is x op e's, then MSTORE
 *)

Theory stmtSimAugAssign
Ancestors
  exprBopSimDefs exprBopSimProps
  exprSimSource gasContext gasExemptCert gasSummary gasSummaryCompose
  fragGasMode fragGasPath fragGasPathMem fragGasSeq gasCount
  exprSimName exprSimNameWord
  stmtSimProps
  exprSimHypsDefs
  stmtSimDefs
  exprSimDefs
  loweringPosts
  allocLimits
  list rich_list finite_map pred_set
  fragExec localPtrsProps  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimOperators exprSimLeaves loweringSlice  stmtSimDecl
  stmtSimDeclStore stmtSimAssignStore stmtSimDeclPath stmtSimDeclCompose exprOpenPrimitives
  exprLowering exprBopLowering stmtLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs valueEncoding
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperTypeSystem vyperTyping vyperTypeEnv
  vyperTypeInvariants vyperTypeBuiltins vyperTypeStatePreservation vyperTypeCallGraph vyperLookup vyperAST
  venomExecSemantics venomExecProofs venomInst venomState
Libs
  monadsyntax intLib

(* ===== The source side ===== *)

(* A local in scope: its target place, the value there and its type. *)
Theorem eval_target_place_local:
  !cx id es entry.
    lookup_scopes id es.scopes = SOME entry ==>
    eval_target_place cx (NameTarget id) es = (INL (MemoryPlace id []), es) /\
    read_place cx (MemoryPlace id []) es = (INL entry.value, es) /\
    place_type_value cx (MemoryPlace id []) es = (INL entry.type, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, get_place_def, return_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, get_place_def] >>
  simp[read_place_def, place_type_value_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, read_memory_path_def,
       evaluate_subscripts_def, subscripts_type_def, lift_sum_def]
QED

(* x op= e on a local x in scope: x's place, its value and its type are read
   without changing the state, e is evaluated, then the operator runs on
   x's value and e's, and the result is written to x. *)
Theorem eval_augassign_local:
  !cx ty id bop e es res es' entry.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry ==>
    ?r1 es1.
      (do tv <- eval_expr cx e; read_result cx tv od) es = (r1, es1) /\
      case r1 of
        INR ex => res = INR ex /\ es' = es1
      | INL v =>
          case evaluate_binop
                 (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
                 entry.type bop entry.value v of
            INR err => res = INR (Error err) /\ es' = es1
          | INL r => write_place cx (MemoryPlace id []) r es1 = (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspec_then `cx` strip_assume_tac) eval_target_place_local >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, LET_THM] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r0, st0)` >>
  Cases_on `r0` >> simp[] >>
  rename1 `eval_expr cx e es = (INL raw, st0)` >>
  Cases_on `read_result cx raw st0` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  qmatch_goalsub_abbrev_tac `evaluate_binop u entry.type bop entry.value v1` >>
  Cases_on `evaluate_binop u entry.type bop entry.value v1` >>
  simp[lift_sum_def, return_def, raise_def]
QED

(* The operator's type argument matters only for in and not in on an
   array. *)
Theorem evaluate_binop_tv:
  !u tv tv' bop v1 v2.
    bop <> In /\ bop <> NotIn ==>
    evaluate_binop u tv bop v1 v2 = evaluate_binop u tv' bop v1 v2
Proof
  rpt strip_tac >> Cases_on `bop` >> gvs[] >>
  ONCE_REWRITE_TAC [evaluate_binop_def] >> simp[] >>
  ONCE_REWRITE_TAC [evaluate_binop_def] >> simp[]
QED

(* Pointwise source boundary, used for counted runs, not certificates. *)
Theorem eval_augassign_local_forced:
  lookup_scopes id es.scopes = SOME entry ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        entry.type bop entry.value v);
      write_place cx (MemoryPlace id []) r od) es
Proof
  strip_tac >>
  drule_then (qspec_then `cx` strip_assume_tac) eval_target_place_local >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_rhs_admissible:
  lookup_scopes id es.scopes = SOME entry /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_stmt cx (AugAssign ty (NameTarget id) bop e)
     (es with gas_obs := gs) = (INR ex, ee)` by
    (`lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule eval_augassign_local_forced >>
     disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
     simp[bind_def]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem augassign_rhs_exception:
  lookup_scopes id es.scopes = SOME entry /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (INR ex, ee)
Proof
  strip_tac >> drule eval_augassign_local_forced >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[bind_def]
QED

Theorem augassign_rhs_normal:
  lookup_scopes id es.scopes = SOME entry /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    entry.type bop entry.value v))
    (write_place cx (MemoryPlace id [])) ee
Proof
  strip_tac >> drule eval_augassign_local_forced >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem augassign_rhs_exempt:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_exec memory (ctx,func) (eval_target_place cx (NameTarget id))
    (es,s0) [] (INL (MemoryPlace id [])) es (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) (return ()) =
   do p <- eval_target_place cx (NameTarget id);
      cur <- read_place cx p;
      ptv <- place_type_value cx p;
      v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        ptv bop cur v);
      ignore_bind (write_place cx p r) (return ()) od` by
    (simp[Once evaluate_def, ignore_bind_def, bind_assoc]) >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  `gas_marked_exec memory (ctx,func) (read_place cx (MemoryPlace id []))
     (es with gas_obs := [],t) [] (INL entry.value)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> irule (cj 2 eval_target_place_local) >> simp[]) >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[lift_option_type_def, subscripts_type_def, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* ===== The code ===== *)

(* x op= e on a local x held through its pointer p: no declaration, x's
   target is p itself with no code, then MLOAD, e lowered at x's type, the
   operator and MSTORE. *)
Theorem augassign_local_code_parts:
  !cenv lctx ty0 ty id bop e sa c sf p sz.
    stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op MLOAD [Var p] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void MSTORE [Var p; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       compile_get_target_ptr_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `emit_op MLOAD [Var p] sa` >> rename1 `_ = (cur_op, s1)` >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs_op, s2)` >> simp[] >>
  Cases_on `compile_binop bop cur_op rhs_op ty NONE
              (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `_ = (res_op, s3)` >> simp[] >>
  Cases_on `emit_void MSTORE [Var p; res_op] s3` >> simp[oneTheory.one]
QED

(* A saved lhs load exposes the existing word-name post, including frames. *)
Theorem augassign_local_load:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  is_word_type ty /\ lookup_scopes id es.scopes = SOME entry /\
  word_value entry.value /\ emit_op MLOAD [Var p] sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_exec F (ctx,func) (eval_target_place cx (NameTarget id))
        (es,s0) [] (INL (MemoryPlace id [])) es (OK t) /\
      expr_post ctx func cenv cx (Name ty id) es sa sb s0
        (es with gas_obs := []) entry.value op t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      local_ptrs_reserved cenv sb /\
      (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
      (?out. op = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >>
  `lower_value compile_expr cenv ty (Name ty id) sa = (op,sb)` by
    simp[lower_value_def, compile_expr_def, comp_bind_def, compile_name_vv_def,
         unwrap_value_def, contextTheory.compile_ptr_load_def,
         contextTheory.mk_ptr_def, comp_return_def, vyperASTTheory.expr_type_def] >>
  drule_all compile_name_word_path >> strip_tac >> gvs[] >>
  qexists_tac `update_var out (val_to_w256 entry.value)
    (s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      gen_tac >> irule (cj 1 eval_target_place_local) >> simp[]) >>
  conj_tac >- (irule name_word_post >> simp[] >> metis_tac[]) >>
  simp[update_var_def] >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[lookup_var_def, FLOOKUP_UPDATE, not_fresh_at_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

(* ===== The operator ===== *)

(* The types the type checker allows for x op= e, with op neither in nor
   not in (type_stmt), are word_value_types. *)
Theorem well_typed_binop_augassign_word:
  !ty bop t2.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn ==>
    word_value_type ty /\ word_value_type t2
Proof
  Cases_on `bop` >> rw[well_typed_binop_def, word_value_type_def] >> gvs[]
QED

(* The source's operator on x's value and e's is the operator of the
   expression x op e annotated with x's type: the builtin reads its type
   argument from e's type, x op= e from x's place, and neither matters
   but for in and not in. *)
Theorem bop_result_augassign:
  !cx ty bop t2 v1 v2 es tv.
    bop <> In /\ bop <> NotIn ==>
    bop_result cx ty bop [ty; t2] v1 v2 es =
    case evaluate_binop
           (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
           tv bop v1 v2 of
      INL v => INL v
    | INR err => INR (Error err)
Proof
  rpt strip_tac >> simp[bop_result_def, evaluate_builtin_def] >>
  metis_tac[evaluate_binop_tv]
QED

(* ===== x op= e is x = x op e ===== *)

(* The source: x op= e on a local x in scope evaluates as the expression
   x op e annotated with x's type would, then writes its value to x. *)
Theorem eval_augassign_local_bop:
  !cx ty id bop e es res es' entry.
    eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (res, es') /\
    lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn ==>
    ?r es1.
      (do tv <- eval_expr cx (Builtin ty (Bop bop) [Name ty id; e]);
          read_result cx tv od) es = (r, es1) /\
      case r of
        INR ex => res = INR ex /\ es' = es1
      | INL v => write_place cx (MemoryPlace id []) v es1 = (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_augassign_local >> strip_tac >>
  Cases_on `(do tv <- eval_expr cx (Builtin ty (Bop bop) [Name ty id; e]);
                read_result cx tv od) es` >>
  rename1 `bind (eval_expr cx (Builtin _ _ _)) _ es = (rr, es2)` >> simp[] >>
  `!ann. (do r0 <- eval_expr cx (Name ann id); read_result cx r0 od) es =
          (INL entry.value, es)` by metis_tac[eval_name_word] >>
  drule eval_expr_bop_cases >> simp[] >> strip_tac >>
  `!w st. bop_result cx ty bop [ty; expr_type e] entry.value w st =
          case evaluate_binop
                 (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
                 entry.type bop entry.value w of
            INL v => INL v
          | INR err => INR (Error err)` by
    (rpt gen_tac >> irule bop_result_augassign >> simp[]) >>
  gvs[vyperASTTheory.expr_type_def] >>
  Cases_on `evaluate_binop
              (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
              entry.type bop entry.value v2` >> gvs[]
QED

(* The code: x op= e on a local held through its pointer is the lowering
   of x op e at x's type, then an MSTORE of its result at the pointer. *)
Theorem augassign_local_code_bop:
  !cenv lctx ty0 ty id bop e sa c sf p sz.
    stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e) sa = (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    word_value_type ty /\ bop <> In /\ bop <> NotIn ==>
    c = cenv /\
    ?s3 res_op.
      lower_value compile_expr cenv ty (Builtin ty (Bop bop) [Name ty id; e])
        sa = (res_op, s3) /\
      emit_void MSTORE [Var p; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all augassign_local_code_parts >> strip_tac >> simp[] >>
  `is_word_type ty /\ ~is_bytestring_type ty` by
    metis_tac[word_value_type_word] >>
  Cases_on `lower_value compile_expr cenv ty
              (Builtin ty (Bop bop) [Name ty id; e]) sa` >>
  rename1 `_ = (op', s')` >>
  drule lower_value_bop >> simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  drule_all lower_value_name_word >> strip_tac >>
  gvs[expr_int_literal_def]
QED

(* A well-formed type's width is whole bytes: Vyper's int widths are
   multiples of 8, and decimal and every other type are 168 or 256 bits. *)
Theorem well_formed_type_bits:
  !tenv ty. well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  Cases_on `ty` >> simp[type_bits_def] >> rename1 `BaseT bt` >>
  Cases_on `bt` >>
  rw[type_bits_def, well_formed_type_def, vyperValueTheory.evaluate_type_def]
QED

(* The checked augmented operand satisfies the ordinary builtin gate too. *)
Theorem augassign_builtin_operands:
  augassign_operand_ok ty bop e ==>
  builtin_operands_ok ty (Bop bop) [lhs; e]
Proof
  Cases_on `bop` >>
  simp[augassign_operand_ok_def, builtin_operands_ok_def,
       power_operands_ok_def, int_literal_value_def] >>
  Cases_on `e` >> simp[power_exponent_ok_def] >>
  rename1 `Literal ann lit` >> Cases_on `lit` >> simp[power_exponent_ok_def]
QED

(* The checked augmented operand gives the exponent and shift-amount facts
   the field-target statement lemmas take. *)
Theorem augassign_operand_ok_operands:
  augassign_operand_ok ty bop e ==>
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e)
Proof
  Cases_on `bop` >> simp[augassign_operand_ok_def] >>
  Cases_on `e` >> simp[power_exponent_ok_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  simp[power_exponent_ok_def, nonneg_int_literal_def, int_literal_value_def]
QED


(* ===== The statement ===== *)

(* A local the typing environment knows: it is held through a pointer
   variable, it is in scope, and its entry's type is its type's. *)
Theorem expr_sim_inv_local:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (?entry. lookup_scopes id es.scopes = SOME entry) /\
    !entry. lookup_scopes id es.scopes = SOME entry ==>
            evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  rpt gen_tac >> strip_tac >>
  fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
  qpat_x_assum `!id ty. _ ==> IS_SOME _` drule >>
  qpat_x_assum `!id ty. _ ==> ?p sz. _` drule >>
  simp[optionTheory.IS_SOME_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ _ ==> _` drule_all >> simp[]
QED

Theorem augassign_binop_admissible:
  lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] entry.value v ee)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty; expr_type e] entry.value v ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     entry.type bop entry.value v of
       INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     entry.type bop entry.value v` >- simp[expr_res_ok_def] >>
  rename1 `_ = INR err` >>
  `eval_stmt cx (AugAssign ty (NameTarget id) bop e)
    (es with gas_obs := gs) = (INR (Error err), ee)` by
    (`lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule_all augassign_rhs_normal >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, raise_def]) >>
  `stmt_res_ok lctx (INR (Error err))` by metis_tac[gas_admissible_result] >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_current_store_layout:
  expr_sim_inv cenv cx env ee /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME etv /\ word_value_type ty /\
  value_has_type etv w ==>
  !current. lookup_scopes id ee.scopes = SOME current ==>
    store_lays_out etv current.type w
Proof
  strip_tac >> rpt strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME current.type` by
    metis_tac[expr_sim_inv_local] >>
  `current.type = etv` by gvs[] >> simp[] >>
  irule store_lays_out_typed >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ty`, `get_tenv cx`] >> simp[word_value_type_word]
QED

Theorem augassign_write_admissible:
  lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) /\
  bop_result cx ty bop [ty; expr_type e] entry.value v ee = INL w /\
  write_place cx (MemoryPlace id []) w ee = (res, fin) ==>
  !m. res <> INR (Error (TypeError m))
Proof
  strip_tac >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     entry.type bop entry.value v = INL w` by
    (`bop_result cx ty bop [ty; expr_type e] entry.value v ee =
       case evaluate_binop
         (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
         entry.type bop entry.value v of
         INL x => INL x | INR err => INR (Error err)` by
       (irule bop_result_augassign >> simp[]) >>
     gvs[AllCaseEqs()]) >>
  `eval_stmt cx (AugAssign ty (NameTarget id) bop e)
     (es with gas_obs := gs) = (res, fin)` by
    (`lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule_all augassign_rhs_normal >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, return_def]) >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  fs[stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_binop_ready:
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME ty /\
  lookup_scopes id es.scopes = SOME entry /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  expr_sim_inv cenv cx env ee /\
  (!w. bop_result cx ty bop [ty; expr_type e] entry.value v est = INL w ==>
       value_has_type entry.type w) /\
  binop_frag ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty; expr_type e] entry.value v est
Proof
  strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type] >>
  `well_formed_type env.type_defs ty` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >> gvs[] >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  conj_tac
  >- (gen_tac >>
      `bop_result cx ty bop [ty; expr_type e] entry.value v est =
       case evaluate_binop
         (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
         entry.type bop entry.value v of
           INL w => INL w | INR err => INR (Error err)` by
        (irule bop_result_augassign >> simp[]) >>
      pop_assum SUBST1_TAC >>
      simp[AllCaseEqs()] >> strip_tac >>
      irule well_typed_binop_success_type >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`ty`, `expr_type e`, `get_tenv cx`, `entry.type`, `tyv`, `ty`] >> simp[]) >>
  irule binop_frag_word_typed >> simp[] >> conj_tac
  >- (strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
      Cases_on `expr_int_literal e` >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`expr_type e`, `get_tenv cx`, `entry.type`, `tyv`] >> simp[]
QED

Theorem stmt_post_expr_entry_frame:
  expr_post ctx func cenv cx e es sa sm s0 em v op t /\
  sa.cs_next_var <= sm.cs_next_var /\
  stmt_post ctx func cx lctx old c sm sf t res ee last ==>
  stmt_post ctx func cx lctx old c sa sf s0 res ee last
Proof
  strip_tac >> irule stmt_post_entry_frame >>
  qexistsl_tac [`t`, `sm`] >> fs[expr_post_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem gas_marked_exec_observation:
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r ==>
  source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (res, ee with gas_obs := tail)
Proof
  simp[gas_marked_exec_def]
QED

(* A zero-observation target prefix does not change the source observations. *)
Theorem gas_marked_exec_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) source (es with gas_obs := [],t)
    marks res ee r ==>
  gas_marked_exec F (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `gas_explicit marks s0.vs_gas_readings =
   gas_explicit marks t.vs_gas_readings` by
    (drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_suffix >> simp[gasCountTheory.gas_count_suffix_def]) >>
  gvs[gas_marked_exec_def] >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem augassign_rhs_exception_exec:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_rhs_exception >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem augassign_rhs_normal_exec:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      entry.type bop entry.value v)) (write_place cx (MemoryPlace id [])))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >>
  drule_all gas_marked_exec_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `lookup_scopes id (es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail).scopes = SOME entry`
        by simp[] >>
      drule_all augassign_rhs_normal >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

Theorem write_place_local_gas_obs:
  !cx id v es res es' obs.
    write_place cx (MemoryPlace id []) v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) ==>
    res = INL () /\
    write_place cx (MemoryPlace id []) v (es with gas_obs := obs) =
      (res, es' with gas_obs := obs)
Proof
  rpt strip_tac >> drule_all write_place_local >> strip_tac >> gvs[] >>
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       replace_memory_entry_def, evaluate_subscripts_def,
       assign_subscripts_def, set_scopes_def, return_def, raise_def]
QED

Theorem local_word_pointer_live:
  stmt_state_rel ctx func cenv cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  ?w. lookup_var p s = SOME w
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  rpt strip_tac >> first_x_assum drule_all >> metis_tac[]
QED

Theorem augassign_store_continuation_exec:
  br = INL w /\
  write_place cx (MemoryPlace id []) w ee = (res, fin) /\
  (!m. res <> INR (Error (TypeError m))) /\
  gas_marked_path F ctx func u 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [])))
    (ee,u) [] res fin r
Proof
  strip_tac >> drule_all write_place_local_gas_obs >> strip_tac >>
  simp[gas_marked_exec_def, lift_sum_def, bind_def, return_def]
QED

Theorem augassign_error_continuation_exec:
  br = INR err /\ gas_marked_path F ctx func u 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [])))
    (ee,u) [] (INR (Error err)) ee r
Proof
  simp[gas_marked_exec_def, lift_sum_def, bind_def, raise_def]
QED

(* A live-local store: the counted instruction and the complete statement post.
   Prefix frames are relative to the original statement entry. *)
Theorem local_word_store_post_path:
  !ctx func cenv cx lctx es s id p sz w v etv res es' op st sf sa s0.
    emit_void MSTORE [Var p; op] st = ((), sf) /\
    fn_has_code st sf func /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    eval_operand op s = SOME (typed_val_to_w256 etv v) /\
    write_place cx (MemoryPlace id []) v es = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) /\
    (!entry. lookup_scopes id es.scopes = SOME entry ==>
             store_lays_out etv entry.type v) /\
    (!x wd. not_fresh_at sa x /\ lookup_var x s0 = SOME wd ==>
            lookup_var x s = SOME wd) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) ==>
    ?t. res = INL () /\
        gas_marked_path F ctx func s 0 (OK t) /\
        stmt_post ctx func cx lctx cenv cenv sa sf s0 res es' t
Proof
  rpt strip_tac >>
  drule_all write_place_local >> strip_tac >> gvs[] >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `store_lays_out etv entry.type v` by simp[] >>
  drule_all stmt_state_rel_write_local_store >> strip_tac >>
  drule_all emit_mstore_marked_path >> strip_tac >>
  `sf.cs_current_bb = st.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> simp[is_terminator_def]) >>
  qexists_tac `mstore (w2n w) (typed_val_to_w256 etv v) s with
                vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_post_def, stmt_lands_def] >>
  simp[cenv_top_ext_refl, stmt_state_rel_inst_idx, mstore_def, LET_THM,
       lookup_var_def] >>
  gvs[lookup_var_def]
QED

(* x op= e on a word local x, for every outcome, given e's expr_sim_case
   (so e may make internal calls unless nocalls): x op e's errors exit,
   the checked operators' aborts among them, and on a value the MSTORE
   writes it to x's region. *)
(* Why it holds.  The source reads x, evaluates e and runs the operator,
   which is how x op e evaluates (eval_augassign_local_bop), and the code
   is x op e's lowering then the MSTORE (augassign_local_code_bop); x op e
   meets expr_body_pre where e does, so its expr_sim is compile_bop_word_case's.
   The scopes at the write hold x at the type ty evaluates to
   (expr_sim_inv at the state after e), so the result's typed word is the
   word the store lays out at x's type (store_lays_out_word_value). *)
(* Under the counted judgment (source-action stmt_frag): gas_exempt_cert is
   syntactic over the source term, so the exempt branch cannot come from the
   expression x op e's own outcome by a pointwise source equality.  The
   statement's certificate can be built from e's own certificate with the
   existing rules: the place, the read of x and its type are pure at es
   (lookup_scopes id es.scopes = SOME entry), place_type_value unfolds to a
   get_scopes bind, and e's action is the first non-pure bind.  *)
(* Historical fixed-result proof, retained for reference only.
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  drule_all augassign_local_code_bop >> strip_tac >>
  rename1 `emit_void MSTORE [Var p; res_op] s3 = _` >>
  drule_all eval_augassign_local_bop >>
  disch_then (qx_choosel_then [`r`, `es1`] strip_assume_tac) >>
  `expr_body_pre cenv cx env (Builtin ty (Bop bop) [Name ty id; e]) es` by
    (irule expr_body_pre_augassign >> simp[] >> metis_tac[]) >>
  `expr_sim_case nocalls ctx func cenv cx
     (Builtin ty (Bop bop) [Name ty id; e])` by
    (irule augassign_bop_case >> simp[]) >>
  `expr_sim ctx func cenv cx ty (Builtin ty (Bop bop) [Name ty id; e]) es` by
    (irule expr_sim_case_apply >> simp[int_calls_expr_def] >> metis_tac[]) >>
  qspecl_then [`cenv`, `cx`, `env`, `Builtin ty (Bop bop) [Name ty id; e]`,
               `es`, `r`, `es1`] mp_tac expr_body_pre_word_result >>
  impl_tac >- simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `Builtin ty (Bop bop) [Name ty id; e]`,
               `es`, `ty`, `sa`, `res_op`, `s3`] mp_tac
    expr_body_pre_lower_value_word_shape >>
  impl_tac >- simp[vyperASTTheory.expr_type_def] >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  Cases_on `r`
  >~ [`INR ex`]
  >- (gvs[] >> drule_all expr_sim_error_run >> strip_tac >>
      drule exit_result_not_error >> strip_tac >>
      disj2_tac >> simp[stmt_exit_def] >> metis_tac[]) >>
  fs[vyperASTTheory.expr_type_def] >>
  rename1 `write_place cx (MemoryPlace id []) v es1 = (res, es')` >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all write_place_local >> strip_tac >>
  rename1 `find_containing_scope id es1.scopes = SOME (pre, env1, entry1, rest)` >>
  `lookup_scopes id es1.scopes = SOME entry1` by
    metis_tac[find_containing_scope_lookup] >>
  `evaluate_type (get_tenv cx) ty = SOME entry1.type` by
    metis_tac[expr_sim_inv_local] >>
  gvs[vyperASTTheory.expr_type_def] >>
  (* x op e, from s0 to its end u *)
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s3`, `res_op`, `INL v`, `es1`, `s0`]
                mp_tac) >>
  impl_tac >- simp[expr_res_ok_def] >>
  simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  rename1 `expr_post ctx func cenv cx _ es sa s3 s0 es1 v res_op u` >>
  qpat_x_assum `expr_post ctx _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def, vyperASTTheory.expr_type_def] >>
  strip_tac >>
  `eval_operand res_op u = SOME (typed_val_to_w256 entry1.type v)` by
    gvs[] >>
  `store_lays_out entry1.type entry1.type v` by
    (irule store_lays_out_word_value >>
     metis_tac[word_value_type_memory_size, evaluate_word_memory_type]) >>
  drule_all assign_local_store_run >>
  strip_tac >>
  disj1_tac >> qexists_tac `t` >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
      simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
           fresh_id_def, emit_def, comp_return_def] >>
      strip_tac >> Cases_on `s3.cs_current_insts` >>
      gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
          venomInstTheory.mk_inst_def, is_terminator_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func t = r /\ _ ==> _`
    (qspecl_then [`fuel`, `run_from fuel ctx func t`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func u <> Error e) ==> _`
    (qspec_then `fuel'` mp_tac) >>
  simp[] >> metis_tac[]
QED
*)
Theorem compile_augassign_local_case:
  !nocalls ctx func cx lctx RetQ cenv ty0 env ty id bop e es.
    expr_sim_case nocalls ctx func cenv cx e /\
    expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
    FLOOKUP env.var_types id = SOME ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type] >>
  `word_value entry.value` by metis_tac[word_value_type_typed] >>
  drule_all augassign_local_code_parts >> strip_tac >> gvs[] >>
  suspend "code_and_outcome"
QED

Resume compile_augassign_local_case[code_and_outcome]:
  `cs_extends sa s1` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  drule_all augassign_local_load >> strip_tac >>
  suspend "rhs_outcome"
QED

Resume compile_augassign_local_case[rhs_outcome]:
  `expr_sim ctx func cenv cx ty e (es with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac
     >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with gas_obs := [])` by
    (simp[] >> irule augassign_rhs_admissible >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by
    fs[expr_post_def] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs_op`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_rhs_exempt >> conj_tac
  >- (qexists_tac `entry` >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Resume compile_augassign_local_case[rhs_summary]:
  `gas_marked_path F ctx func s0 0 (OK t)` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
       mp_tac >> simp[gas_marked_exec_def]) >>
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gasSummary$gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule augassign_rhs_exception_exec >> conj_tac
      >- (qexists_tac `entry` >> simp[]) >>
      qexists_tac `t` >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_local_case[rhs_normal]:
  gvs[] >>
  rename1 `expr_post ctx func cenv cx e _ s1 s2 t (ee with gas_obs := []) v rhs_op u` >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL v, ee with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all augassign_binop_ready >>
  disch_then (qspecl_then [`func`, `ee with gas_obs := []`, `ctx`] strip_assume_tac) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] entry.value v ee)` by
    (`expr_res_ok (bop_result cx ty bop [ty; expr_type e]
        entry.value v (ee with gas_obs := []))` suffices_by simp[] >>
     irule augassign_binop_admissible >>
     simp[] >>
     qexistsl_tac [`es`, `gas_explicit marks t.vs_gas_readings`, `id`, `lctx`] >>
     simp[]) >>
  suspend "binop_ready"
QED

Resume compile_augassign_local_case[binop_ready]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `eval_operand (Var out) t = SOME (val_to_w256 entry.value) /\
   eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (conj_tac >> irule expr_val_rel_word >>
     fs[expr_post_def] >> goal_assum (drule_at Any) >>
     simp[expr_type_def, word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 entry.value)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_def, binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `Var out`, `rhs_op`, `res_op`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_local_case[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  `bop_result cx ty bop [ty; expr_type e] entry.value v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       entry.type bop entry.value v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     entry.type bop entry.value v = INL result` by gvs[AllCaseEqs()] >>
  Cases_on `write_place cx (MemoryPlace id []) result (ee with gas_obs := [])` >>
  rename1 `_ = (wr, fin)` >>
  `!m. wr <> INR (Error (TypeError m))` by
    (`bop_result cx ty bop [ty; expr_type e] entry.value v
        (ee with gas_obs := []) = INL result` by simp[] >>
     drule_all augassign_write_admissible >> simp[]) >>
  suspend "write_safe"
QED

Resume compile_augassign_local_case[write_safe]:
  drule_all write_place_local_gas_obs >>
  disch_then (qspec_then `[]` strip_assume_tac) >> gvs[] >>
  `expr_sim_inv cenv cx env (ee with gas_obs := [])` by simp[] >>
  `?current. lookup_scopes id (ee with gas_obs := []).scopes = SOME current` by
    metis_tac[expr_sim_inv_local] >>
  `?ptr. lookup_var p s = SOME ptr` by
    (`lookup_scopes id ee.scopes = SOME current` by fs[] >>
     metis_tac[local_word_pointer_live]) >>
  `!current. lookup_scopes id (ee with gas_obs := []).scopes = SOME current ==>
     store_lays_out entry.type current.type result` by
    (drule_all augassign_current_store_layout >> simp[]) >>
  `eval_operand res_op s = SOME (typed_val_to_w256 entry.type result)` by
    simp[exprSimPropsTheory.typed_val_to_w256_word_value] >>
  `?last. (INL () : unit + exception) = INL () /\
     gas_marked_path F ctx func s 0 (OK last) /\
     stmt_post ctx func cx lctx cenv cenv s3 sb s (INL ()) fin last` by
    (match_mp_tac local_word_store_post_path >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "store_post"
QED

Resume compile_augassign_local_case[store_post]:
  `stmt_post ctx func cx lctx cenv cenv s2 sb u (INL ()) fin last` by
    (irule stmt_post_entry_frame >> qexistsl_tac [`s`, `s3`] >> simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `stmt_post ctx func cx lctx cenv cenv s1 sb t (INL ()) fin last` by
    (irule stmt_post_expr_entry_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `stmt_post ctx func cx lctx cenv cenv sa sb s0 (INL ()) fin last` by
    (irule stmt_post_expr_entry_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >>
     drule emitted_insts_emit_op >> simp[]) >>
  `gas_marked_path F ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`INL ()`, `fin`, `OK last`] >> simp[] >>
  reverse conj_tac
  >- (disj1_tac >>
      qpat_x_assum `fin = fin with gas_obs := []` (fn th => rewrite_tac[GSYM th]) >>
      simp[]) >>
  irule augassign_rhs_normal_exec >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule augassign_store_continuation_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume compile_augassign_local_case[operator_exit]:
  `bop_result cx ty bop [ty; expr_type e] entry.value v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       entry.type bop entry.value v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       entry.type bop entry.value v`
  >- (gvs[] >> fs[expr_exit_def, exit_result_def]) >>
  gvs[] >>
  qexistsl_tac [`INR (Error y)`, `ee with gas_obs := []`, `r`] >>
  conj_tac
  >- (irule augassign_rhs_normal_exec >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      irule augassign_error_continuation_exec >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise compile_augassign_local_case

(* compile_augassign_local_case for an operand with no internal call. *)
Theorem compile_augassign_local_stmt_frag:
  !ctx func cx lctx RetQ cenv ty0 env ty id bop e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\ augassign_operand_ok ty bop e /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  rpt strip_tac >> drule augassign_operand_ok_operands >> strip_tac >>
  fs[expr_sim_pre_body, expr_sim_ok_case] >>
  irule (Q.SPEC `T` compile_augassign_local_case) >> simp[] >> metis_tac[]
QED

(* Integrity gate: the source and code sides and the store carry no
   admission; the statement itself inherits exprSimBinopFrag's (#572). *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "AUGASSIGN_AUDIT OK\n"
     else raise Fail "augmented assignment inherited admission"
  end) [eval_augassign_local_bop, augassign_local_code_bop,
        expr_sim_inv_local, assign_local_store_run];
