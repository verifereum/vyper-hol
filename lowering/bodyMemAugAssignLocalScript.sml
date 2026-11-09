(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a local (S1's body_augassign_local).  The
   lowering loads x through its pointer p, lowers e at x's type, runs the
   operator and stores the result at p.  The pieces compose one after the
   other as in S1's compile_augassign_local_case: the load of a live local
   (bodyNameWordMemory), e's memory simulation, the operator's
   binop_frag_val_mem (bodyBinopFamiliesMemory) and the store into x's
   region (bodyMemAssignLocalWord).  x op= e is not literally x = x op e at
   the counted level, since an exemption certificate is syntactic in the
   source action; the statement's certificate is built from e's.

   The *_mem_src helpers are copies of S1 source-side lemmas that live only
   on the S1 branch (stmtSimAugAssign there), generalised over the memory
   flag where S1's fix it to F. *)
Theory bodyMemAugAssignLocal
Ancestors
  bodySim vyperTypeCallGraph
  bodyMemoryPreds bodyMemoryDefs bodyMemAssignLocalWord bodyNameWordMemory
  bodyBinopFamiliesMemory bodyBinopFragMemory
  allocaFootprint exprSimMemDefs exprSimSource exprSimHyps bodyExprPreFacts
  stmtSimAugAssign
  exprBopSimDefs exprBopSimProps
  gasOutcome gasContext gasExemptCert gasSummary gasSummaryCompose
  fragGasMode fragGasPath fragGasPathMem fragGasSeq
  exprSimName exprSimNameWord stmtSimProps exprSimHypsDefs stmtSimDefs
  exprSimDefs loweringPosts allocLimits
  fragExec fragExecMem localPtrsProps exprSimOps exprSimBinopFrag
  exprSimOperators exprSimLeaves loweringSlice stmtSimDecl
  stmtSimDeclStore stmtSimAssignStore stmtSimDeclPath stmtSimDeclCompose
  exprOpenPrimitives exprOperandVar
  exprLowering exprBopLowering stmtLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs valueEncoding
  supportedStmtTraverse supportedStmts supportedExprs
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperTypeSystem vyperTyping vyperTypeEnv
  vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTypeBuiltins vyperTypeStatePreservation
  vyperLookup vyperAST
  venomExecSemantics venomExecProofs venomInst venomState
  list rich_list finite_map pred_set
Libs
  monadsyntax

(* ===== The source side (S1 copies) ===== *)

(* S1 stmtSimAugAssign's eval_augassign_local_forced. *)
Theorem eval_augassign_local_forced_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        entry.type bop entry.value v);
      write_place cx (MemoryPlace id []) r od) es
Proof
  strip_tac >>
  drule_then (qspec_then `cx` strip_assume_tac)
    stmtSimAugAssignTheory.eval_target_place_local >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

(* S1 stmtSimAugAssign's augassign_rhs_admissible. *)
Theorem augassign_rhs_admissible_mem_src[local]:
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
     drule eval_augassign_local_forced_mem_src >>
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

(* S1 stmtSimAugAssign's augassign_rhs_exception. *)
Theorem augassign_rhs_exception_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (INR ex, ee)
Proof
  strip_tac >> drule eval_augassign_local_forced_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[bind_def]
QED

(* S1 stmtSimAugAssign's augassign_rhs_normal. *)
Theorem augassign_rhs_normal_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    entry.type bop entry.value v))
    (write_place cx (MemoryPlace id [])) ee
Proof
  strip_tac >> drule eval_augassign_local_forced_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

(* S1 stmtSimAugAssign's augassign_rhs_exempt. *)
Theorem augassign_rhs_exempt_mem_src[local]:
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
     >- (gen_tac >>
         irule (cj 2 stmtSimAugAssignTheory.eval_target_place_local) >>
         simp[]) >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[lift_option_type_def, subscripts_type_def, bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* S1 stmtSimAugAssign's augassign_binop_admissible. *)
Theorem augassign_binop_admissible_mem_src[local]:
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
     drule_all augassign_rhs_normal_mem_src >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, raise_def]) >>
  `stmt_res_ok lctx (INR (Error err))` by metis_tac[gas_admissible_result] >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

(* S1 stmtSimAugAssign's augassign_write_admissible. *)
Theorem augassign_write_admissible_mem_src[local]:
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
     drule_all augassign_rhs_normal_mem_src >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, return_def]) >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  fs[stmt_res_ok_def, expr_res_ok_def]
QED

(* S1 stmtSimAugAssign's gas_marked_exec_zero_prefix, at either memory
   flag. *)
Theorem gas_marked_exec_zero_prefix_mem_src[local]:
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) source (es with gas_obs := [],t)
    marks res ee r ==>
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `gas_explicit marks s0.vs_gas_readings =
   gas_explicit marks t.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  gvs[gas_marked_exec_def] >>
  drule_all gas_marked_path_then >> simp[]
QED

(* S1 stmtSimAugAssign's augassign_rhs_exception_exec, at either memory
   flag. *)
Theorem augassign_rhs_exception_exec_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix_mem_src >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_rhs_exception_mem_src >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* S1 stmtSimAugAssign's augassign_rhs_normal_exec, at either memory
   flag. *)
Theorem augassign_rhs_normal_exec_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      entry.type bop entry.value v)) (write_place cx (MemoryPlace id [])))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >>
  drule_all gas_marked_exec_zero_prefix_mem_src >> strip_tac >>
  gvs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `lookup_scopes id (es with gas_obs :=
        gas_explicit marks s0.vs_gas_readings ++ tail).scopes = SOME entry`
        by simp[] >>
      drule_all augassign_rhs_normal_mem_src >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

(* S1 stmtSimAugAssign's write_place_local_gas_obs. *)
Theorem write_place_local_gas_obs_mem_src[local]:
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

(* S1 stmtSimAugAssign's augassign_store_continuation_exec, at either
   memory flag. *)
Theorem augassign_store_continuation_exec_mem_src[local]:
  br = INL w /\
  write_place cx (MemoryPlace id []) w ee = (res, fin) /\
  (!m. res <> INR (Error (TypeError m))) /\
  gas_marked_path memory ctx func u 0 r ==>
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [])))
    (ee,u) [] res fin r
Proof
  strip_tac >> drule_all write_place_local_gas_obs_mem_src >> strip_tac >>
  simp[gas_marked_exec_def, lift_sum_def, bind_def, return_def]
QED

(* S1 stmtSimAugAssign's augassign_error_continuation_exec, at either
   memory flag. *)
Theorem augassign_error_continuation_exec_mem_src[local]:
  br = INR err /\ gas_marked_path memory ctx func u 0 r ==>
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [])))
    (ee,u) [] (INR (Error err)) ee r
Proof
  simp[gas_marked_exec_def, lift_sum_def, bind_def, raise_def]
QED

(* ===== The load of x ===== *)

(* stmtSimAugAssign's well_typed_binop_augassign_alloc_ok, which is local
   there. *)
Theorem well_typed_binop_augassign_alloc_ok_mem_src[local]:
  !cenv ty bop t2. well_typed_binop ty bop ty t2 ==> type_alloc_ok cenv ty
Proof
  rpt strip_tac >>
  Cases_on `bop = In`
  >- gvs[well_typed_binop_def, type_alloc_ok_def, is_word_type_def] >>
  Cases_on `bop = NotIn`
  >- gvs[well_typed_binop_def, type_alloc_ok_def, is_word_type_def] >>
  drule_all well_typed_binop_augassign_word >> strip_tac >>
  imp_res_tac exprSimSourceTheory.word_value_type_word >>
  simp[type_alloc_ok_def]
QED

(* x itself meets the expression precondition where e does. *)
Theorem augassign_name_sim_pre[local]:
  expr_body_pre cenv cx env e es /\ FLOOKUP env.var_types id = SOME ty /\
  well_typed_binop ty bop ty (expr_type e) ==>
  expr_sim_pre cenv cx env (Name ty id) es
Proof
  rpt strip_tac >>
  drule expr_body_pre_var_types_well_formed >>
  disch_then drule >> strip_tac >>
  drule well_formed_type_bits >> strip_tac >>
  drule well_typed_binop_augassign_alloc_ok_mem_src >> strip_tac >>
  gvs[expr_sim_pre_body, expr_body_pre_def, well_typed_expr_def,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedProgramTheory.expr_abi_decode_target_root_def] >>
  irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
  qexists_tac `int_calls_expr e` >> simp[]
QED

(* The MLOAD of a live word local, on a memory-safe path: x's place is
   taken with no code, and the load gives the word-name post. *)
Theorem augassign_local_load_mem[local]:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  expr_sim_pre cenv cx env (Name ty id) es /\ word_value_type ty /\
  lookup_scopes id es.scopes = SOME entry /\
  emit_op MLOAD [Var p] sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  local_ptrs_reserved cenv sa /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_exec T (ctx,func) (eval_target_place cx (NameTarget id))
        (es,s0) [] (INL (MemoryPlace id [])) es (OK t) /\
      expr_post ctx func cenv cx (Name ty id) es sa sb s0
        (es with gas_obs := []) entry.value op t /\
      word_value entry.value /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      local_ptrs_reserved cenv sb /\ alloca_history func t /\
      t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
      (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
      (?out. op = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `lower_value compile_expr cenv ty (Name ty id) sa = (op,sb)` by
    simp[lower_value_def, compile_expr_def, comp_bind_def, compile_name_vv_def,
         unwrap_value_def, contextTheory.compile_ptr_load_def,
         contextTheory.mk_ptr_def, comp_return_def, vyperASTTheory.expr_type_def] >>
  drule_all body_name_word_counted >> strip_tac >> gvs[] >>
  qexists_tac `update_var out (val_to_w256 entry.value)
    (s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
      >- (gen_tac >>
          irule (cj 1 stmtSimAugAssignTheory.eval_target_place_local) >>
          simp[]) >>
      simp[gas_marked_path_def]) >>
  conj_tac
  >- (irule name_word_post >> simp[] >> qexists_tac `p` >> simp[]) >>
  `out = STRCAT "%" (toString sa.cs_next_var) /\
   sb.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

(* ===== The statement ===== *)

Theorem compile_augassign_local_mem[local]:
  !d ctx func cx lctx RetQ cenv ty0 env ty id bop e es.
    (!gs. expr_sim_mem ctx func cenv cx ty e (es with gas_obs := gs)) /\
    expr_body_pre cenv cx env e es /\
    FLOOKUP env.var_types id = SOME ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0 (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[] >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type] >>
  `well_formed_type env.type_defs ty` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `expr_sim_pre cenv cx env (Name ty id) es` by
    metis_tac[augassign_name_sim_pre] >>
  drule_all augassign_local_code_parts >> strip_tac >> gvs[] >>
  suspend "code"
QED

Resume compile_augassign_local_mem[code]:
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
  drule_all augassign_local_load_mem >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with gas_obs := [])` by
    (simp[] >> irule augassign_rhs_admissible_mem_src >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by
    fs[expr_post_def] >>
  qpat_x_assum `!gs. expr_sim_mem _ _ _ _ _ _ _`
    (qspec_then `[]` (mp_tac o REWRITE_RULE [expr_sim_mem_def])) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs_op`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_rhs_exempt_mem_src >> conj_tac
  >- (qexists_tac `entry` >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Resume compile_augassign_local_mem[rhs_summary]:
  `gas_marked_path T ctx func s0 0 (OK t)` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
       mp_tac >> simp[gas_marked_exec_def]) >>
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule augassign_rhs_exception_exec_mem_src >> conj_tac
      >- (qexists_tac `entry` >> simp[]) >>
      qexists_tac `t` >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_local_mem[rhs_normal]:
  gvs[] >>
  rename1 `expr_post ctx func cenv cx e _ s1 s2 t (ee with gas_obs := []) v rhs_op u` >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] entry.value v
     (ee with gas_obs := []))` by
    (irule augassign_binop_admissible_mem_src >> simp[] >>
     qexistsl_tac [`es`, `gas_explicit marks t.vs_gas_readings`, `id`, `lctx`] >>
     simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  rename1 `value_has_type etv v` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    (disch_then (fn th =>
       qpat_x_assum `_ ==> shift_amount_ok e` (assume_tac o C MP th)) >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  suspend "binop"
QED

Resume compile_augassign_local_mem[binop]:
  `binop_frag_val_mem ctx func cenv cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE)
     [ty; expr_type e] entry.value v (ee with gas_obs := [])` by
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ty`, `Name ty id`, `e`,
       `entry.value`, `v`, `ee with gas_obs := []`, `entry.type`, `etv`]
       mp_tac binop_frag_typed_mem >>
     simp[vyperASTTheory.expr_type_def, expr_int_literal_def] >>
     disch_then irule >>
     strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  `eval_operand (Var out) t = SOME (val_to_w256 entry.value) /\
   eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (conj_tac >> irule expr_val_rel_word >>
     fs[expr_post_def] >> goal_assum (drule_at Any) >>
     simp[vyperASTTheory.expr_type_def, word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 entry.value)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `Var out`, `rhs_op`, `res_op`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_local_mem[operator_normal]:
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
     drule_all augassign_write_admissible_mem_src >> simp[]) >>
  drule_all write_place_local >> strip_tac >> gvs[] >>
  rename1 `find_containing_scope id ee.scopes = SOME (pre, env1, cur, rest)` >>
  `lookup_scopes id ee.scopes = SOME cur` by
    metis_tac[find_containing_scope_lookup] >>
  `evaluate_type (get_tenv cx) ty = SOME cur.type` by
    (`expr_sim_inv cenv cx env (ee with gas_obs := [])` by simp[] >>
     drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> simp[]) >>
  `cur.type = entry.type` by gvs[] >>
  `value_has_type entry.type result` by
    (mp_tac (Q.INST [`t1` |-> `ty`, `t2` |-> `expr_type e`,
       `tenv` |-> `get_tenv cx`, `result_tv` |-> `entry.type`,
       `tv1` |-> `entry.type`, `tv2` |-> `etv`, `tv` |-> `entry.type`,
       `v1` |-> `entry.value`, `v2` |-> `v`, `v` |-> `result`,
       `u` |-> `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`]
       well_typed_binop_success_type) >> simp[]) >>
  `store_lays_out entry.type cur.type result` by
    (simp[] >> irule store_lays_out_typed >>
     simp[] >> qexistsl_tac [`ty`, `get_tenv cx`] >> simp[]) >>
  `eval_operand res_op s = SOME (typed_val_to_w256 entry.type result)` by
    simp[exprSimPropsTheory.typed_val_to_w256_word_value] >>
  suspend "store"
QED

Resume compile_augassign_local_mem[store]:
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ee with gas_obs := []`, `s`, `id`,
    `p`, `sz`, `pre`, `env1`, `cur`, `rest`, `result`, `entry.type`, `res_op`,
    `s3`, `sb`] mp_tac assign_local_word_store_path_mem >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_marked_path T ctx func s 0 (OK last)` >>
  `gas_marked_path T ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`INL ()`,
    `ee with <|scopes :=
       pre ++ (env1 |+ (id, cur with <|value := result; popped := []|>)) ::
       rest; gas_obs := []|>`, `OK last`] >>
  conj_tac
  >- (irule augassign_rhs_normal_exec_mem_src >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      irule augassign_store_continuation_exec_mem_src >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> simp[] >>
  suspend "post"
QED

Resume compile_augassign_local_mem[post]:
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_x_assum `emit_op _ _ sa = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[]) >>
  `s3.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `s3.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono,
                 arithmeticTheory.LESS_EQ_TRANS] >>
     `lookup_var x u = SOME w` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def]) >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME b` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]
QED

Resume compile_augassign_local_mem[operator_exit]:
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
  >- (irule augassign_rhs_normal_exec_mem_src >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      irule augassign_error_continuation_exec_mem_src >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise compile_augassign_local_mem

Theorem body_augassign_local_mem:
  !cx ty id bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings
      (AugAssign ty (NameTarget id) bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
             is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target))` by
    (`cx_tops cx = tops` by
       (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
     fs[body_inv_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supportedExprTraverseTheory.supported_expr_exists_def,
         int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `FLOOKUP env.var_types id = SOME ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
         DISJ_IMP_THM, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_types id` >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[]) >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >>
     metis_tac[stmtSimAugAssignTheory.eval_target_place_local]) >>
  irule compile_augassign_local_mem >> simp[DISJ_IMP_THM] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `body_expr_mem_ok cx e`
        (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
      disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`,
        `es with gas_obs := gs`] mp_tac) >>
      simp[]) >>
  qexists_tac `env` >> simp[]
QED
