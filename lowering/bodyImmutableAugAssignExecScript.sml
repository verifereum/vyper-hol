Theory bodyImmutableAugAssignExec
Ancestors
  bodyImmutableAugAssignFacts bodyImmutableAugAssignStore
  stmtSimAugAssignStorage stmtSimAugAssign gasContext gasExemptCert gasSummary
  fragGasMode fragGasPath fragGasPathMem fragGasSeq vyperExprNoControl exprSimDefs stmtSimDefs
  vyperInterpreter vyperState
Libs
  monadsyntax

Theorem immutable_augassign_prefix_obs:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = NONE /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v0) ==>
  !gs. eval_target_place cx (TopLevelNameTarget (src,id))
         (es with gas_obs := gs) =
         (INL (ImmutablePlace src id []),es with gas_obs := gs) /\
       read_place cx (ImmutablePlace src id []) (es with gas_obs := gs) =
         (INL v0,es with gas_obs := gs) /\
       place_type_value cx (ImmutablePlace src id []) (es with gas_obs := gs) =
         (INL tv,es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >> irule immutable_augassign_source_prefix >> simp[] >>
  metis_tac[]
QED

(* Pointwise replay is kept separate from syntactic certificates. *)
Theorem immutable_augassign_forced:
  eval_target_place cx (TopLevelNameTarget nsid) es = (INL p,es) /\
  read_place cx p es = (INL v0,es) /\
  place_type_value cx p es = (INL tv,es) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e) es =
    (do v <- bind (eval_expr cx e) (read_result cx);
        r <- lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          tv bop v0 v);
        write_place cx p r od) es
Proof
  strip_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem immutable_augassign_rhs_exception:
  eval_target_place cx (TopLevelNameTarget nsid) es = (INL p,es) /\
  read_place cx p es = (INL v0,es) /\
  place_type_value cx p es = (INL tv,es) /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex,ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e) es = (INR ex,ee)
Proof
  strip_tac >> drule_all immutable_augassign_forced >>
  disch_then (qspecl_then [`ty`,`e`,`bop`] mp_tac) >> simp[Once bind_def]
QED

Theorem immutable_augassign_rhs_normal:
  eval_target_place cx (TopLevelNameTarget nsid) es = (INL p,es) /\
  read_place cx p es = (INL v0,es) /\
  place_type_value cx p es = (INL tv,es) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e) es =
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop v0 v)) (write_place cx p) ee
Proof
  strip_tac >> drule_all immutable_augassign_forced >>
  disch_then (qspecl_then [`ty`,`e`,`bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem immutable_augassign_rhs_admissible:
  (!gs. eval_target_place cx (TopLevelNameTarget nsid) (es with gas_obs := gs) =
          (INL p,es with gas_obs := gs) /\
        read_place cx p (es with gas_obs := gs) = (INL v0,es with gas_obs := gs) /\
        place_type_value cx p (es with gas_obs := gs) = (INL tv,es with gas_obs := gs)) /\
  gas_admissible (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >> rename1 `INR ex` >>
  `eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)
     (es with gas_obs := gs) = (INR ex,ee)` by
    (irule immutable_augassign_rhs_exception >> metis_tac[]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def,expr_res_ok_def,stmt_res_ok_def]
QED

Theorem immutable_augassign_rhs_exception_exec:
  (!gs. eval_target_place cx (TopLevelNameTarget nsid) (es with gas_obs := gs) =
          (INL p,es with gas_obs := gs) /\
        read_place cx p (es with gas_obs := gs) = (INL v0,es with gas_obs := gs) /\
        place_type_value cx p (es with gas_obs := gs) = (INL tv,es with gas_obs := gs)) /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule immutable_augassign_rhs_exception >> metis_tac[]
QED

Theorem immutable_augassign_rhs_normal_exec:
  (!gs. eval_target_place cx (TopLevelNameTarget nsid) (es with gas_obs := gs) =
          (INL p,es with gas_obs := gs) /\
        read_place cx p (es with gas_obs := gs) = (INL v0,es with gas_obs := gs) /\
        place_type_value cx p (es with gas_obs := gs) = (INL tv,es with gas_obs := gs)) /\
  gas_marked_path F ctx func s0 0 (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop v0 v)) (write_place cx p))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec F (ctx,func)
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      qpat_assum `!gs. eval_target_place _ _ _ = _ /\ _`
        (qspec_then `gas_explicit marks s0.vs_gas_readings ++ tail` strip_assume_tac) >>
      drule_all immutable_augassign_rhs_normal >>
      disch_then (qspecl_then [`ty`,`bop`] mp_tac) >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

(* A guarded boolean read factors a pure prefix globally, including states
   outside the invariant. The fallback retains the original computation. *)
Theorem gas_exempt_cert_pure_prefix:
  (!gs. a (es with gas_obs := gs) = (INL v,es with gas_obs := gs)) /\
  ~s0.vs_halted /\
  gas_exempt_cert memory tops (ctx,func) (k v)
    (es with gas_obs := [],s0) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func) (bind a k)
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  qabbrev_tac `b = (\st. (INL (a st = (INL v,st)),st) : bool evaluation_result)` >>
  qabbrev_tac `h = (\flag. if flag then k v else bind a k)` >>
  `bind a k = bind b h` by
    (simp[FUN_EQ_THM, Abbr `b`, Abbr `h`, bind_def] >>
     qx_gen_tac `st` >> Cases_on `a st = (INL v,st)` >> simp[] >>
     gvs[bind_def]) >>
  pop_assum SUBST1_TAC >>
  `gas_marked_exec memory (ctx,func) b (es,s0) [] (INL T)
     (es with gas_obs := []) (OK s0)` by
    (simp[gas_marked_exec_def,gas_explicit_def,Abbr `b`] >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_bool >> simp[Abbr `h`] >> disch_then irule >> simp[]
QED

Theorem immutable_augassign_rhs_exempt:
  (!gs. eval_target_place cx (TopLevelNameTarget nsid) (es with gas_obs := gs) =
          (INL p,es with gas_obs := gs) /\
        read_place cx p (es with gas_obs := gs) = (INL v0,es with gas_obs := gs) /\
        place_type_value cx p (es with gas_obs := gs) = (INL tv,es with gas_obs := gs)) /\
  gas_marked_path memory ctx func s0 0 (OK t) /\ ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e))
      (return ())) (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)) (return ()) =
   do p <- eval_target_place cx (TopLevelNameTarget nsid);
      cur <- read_place cx p;
      ptv <- place_type_value cx p;
      v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur v);
      ignore_bind (write_place cx p r) (return ()) od` by
    simp[Once evaluate_def,ignore_bind_def,bind_assoc] >>
  pop_assum SUBST1_TAC >>
  `gas_marked_exec memory (ctx,func)
     (eval_target_place cx (TopLevelNameTarget nsid)) (es,s0) [] (INL p)
     (es with gas_obs := []) (OK t)` by
    simp[gas_marked_exec_def,gas_explicit_def] >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >> simp[] >>
  irule gas_exempt_cert_pure_prefix >> simp[] >>
  irule gas_exempt_cert_pure_prefix >> simp[] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem immutable_write_place_gas_obs:
  write_place cx (ImmutablePlace src id path) v es = (res,fin) ==>
  !gs. write_place cx (ImmutablePlace src id path) v (es with gas_obs := gs) =
       (res,fin with gas_obs := gs)
Proof
  simp[write_place_def,get_immutables_def,get_address_immutables_def,
       set_immutable_def,set_address_immutables_def,bind_def,return_def,
       lift_option_type_def,lift_sum_def,raise_def,
       vyperMiscTheory.option_CASE_rator,vyperMiscTheory.sum_CASE_rator] >>
  rpt strip_tac >> gvs[AllCaseEqs(),return_def,raise_def]
QED

Theorem immutable_augassign_continuation_exec:
  bind (lift_sum br) (write_place cx (ImmutablePlace src id path)) ee = (res,fin) /\
  gas_marked_path F ctx func u 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum br) (write_place cx (ImmutablePlace src id path)))
    (ee,u) [] res fin r
Proof
  Cases_on `br` >>
  simp[gas_marked_exec_def,lift_sum_def,bind_def,return_def,raise_def] >>
  strip_tac >> simp[] >> gen_tac >>
  metis_tac[immutable_write_place_gas_obs]
QED
