(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a field of a local struct (S1's
   body_augassign_attr_local): MLOAD at the field's address, the operator,
   MSTORE there. *)
Theory bodyMemAugAssignAttrLocal
Ancestors
  bodySim vyperTypeCallGraph supportedStmts supportedStmtTraverse
  bodyMemoryPreds bodyMemoryDefs stmtSimAugAssignAttr stmtSimAugAssign stmtSimAssignAttr
  exprSimMemDefs bodyExprPreFacts bodyBinopFamiliesMemory bodyBinopFragMemory
  exprLowering exprBopLowering stmtLowering loweringPosts exprSimHyps
  exprSimProps exprOperandVar vyperTypeExprSoundness vyperTypeExprResult
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasPathMem
  exprBopSimDefs exprBopSimProps exprSimSource exprSimDefs stmtSimDefs
  exprSimFieldLayout exprSimAttributeFields exprSimHypsDefs
  vyperTypeInvariants vyperTypeSystem vyperTyping vyperTypeEnv
  finite_map alist compileEnv loweringStateRelDefs
  bodyFieldMemoryProps bodyDeclMemoryCounted bodyDeclMemoryCore
  vyperTypeBuiltins stmtSimDeclStore exprSimWordArgs
  allocaFootprint fragGasSeqMem stmtSimProps localPtrsProps
  exprLoweringProps emitHelper emitHelperProps loweringSlice exprSimOps
  venomExecSemantics venomInst venomState
  fragExec fragExecMem allocLimits valueEncoding valueEncodingDefs freshWrites
  vyperLookup vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperAST
Libs
  monadsyntax emitTacticsLib

(* Pure source boundaries; all observations remain available to the RHS. *)
Theorem augassign_attr_place_reads_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv ==>
  eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
    (INL (MemoryPlace id [AttrSubscript fld]), es) /\
  read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL fv, es) /\
  place_type_value cx (MemoryPlace id [AttrSubscript fld]) es = (INL ftv, es)
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, get_place_def] >>
  simp[extend_place_def, place_type_value_def, read_place_def, bind_def,
       get_scopes_def, lift_option_type_def, return_def,
       read_memory_path_def, evaluate_subscripts_def, subscripts_type_def,
       subscript_type_def, lift_sum_def, extend_memory_place_def,
       get_place_def, ignore_bind_def]
QED

Theorem eval_augassign_attr_forced_mem_src[local]:
  eval_target_place cx (AttributeTarget (NameTarget id) fld) es =
    (INL (MemoryPlace id [AttrSubscript fld]), es) /\
  read_place cx (MemoryPlace id [AttrSubscript fld]) es = (INL fv, es) /\
  place_type_value cx (MemoryPlace id [AttrSubscript fld]) es = (INL ftv, es) ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop fv v);
      write_place cx (MemoryPlace id [AttrSubscript fld]) r od) es
Proof
  strip_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (rr, ee)` >>
  Cases_on `rr` >> simp[] >>
  rename1 `read_result cx raw ee` >>
  Cases_on `read_result cx raw ee` >> rename1 `_ = (rv, ef)` >>
  Cases_on `rv` >> simp[]
QED

Theorem eval_augassign_attr_fields_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop fv v);
      write_place cx (MemoryPlace id [AttrSubscript fld]) r od) es
Proof
  strip_tac >> drule_all augassign_attr_place_reads_mem_src >>
  strip_tac >> irule eval_augassign_attr_forced_mem_src >> simp[]
QED

Theorem eval_augassign_attr_fields_obs_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv ==>
  !gs. eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
    (es with gas_obs := gs) =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ftv bop fv v);
      write_place cx (MemoryPlace id [AttrSubscript fld]) r od)
    (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >> irule eval_augassign_attr_fields_mem_src >>
  simp[] >> metis_tac[]
QED

Theorem augassign_attr_rhs_admissible_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_admissible
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
  qpat_x_assum `lookup_scopes id es.scopes = _` kall_tac >>
  drule_all eval_augassign_attr_fields_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def] >> strip_tac >>
  `no_control_exc y` by
    (qpat_x_assum `bind _ _ _ = (INR y, _)` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  drule_all gas_admissible_result >>
  Cases_on `y` >> gvs[no_control_exc_def, stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_attr_rhs_exception_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
    (INR ex, ee)
Proof
  strip_tac >> drule_all eval_augassign_attr_fields_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def]
QED

Theorem augassign_attr_rhs_normal_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop fv v)) (write_place cx (MemoryPlace id [AttrSubscript fld])) ee
Proof
  strip_tac >> drule_all eval_augassign_attr_fields_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def]
QED

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

Theorem augassign_attr_rhs_exception_exec_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix_mem_src >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_attr_rhs_exception_mem_src >> simp[] >> metis_tac[]
QED

Theorem augassign_attr_rhs_normal_exec_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v)) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >>
  drule_all gas_marked_exec_zero_prefix_mem_src >> strip_tac >>
  `gas_marked_exec memory (ctx,func)
    (do v <- bind (eval_expr cx e) (read_result cx);
        w <- lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          ftv bop fv v);
        write_place cx (MemoryPlace id [AttrSubscript fld]) w od)
    (es,s0) (marks ++ []) res fin r` by
    (irule gas_marked_exec_bind_normal >> simp[] >> metis_tac[]) >>
  drule_all eval_augassign_attr_fields_obs_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] assume_tac) >>
  gvs[gas_marked_exec_def]
QED

Theorem eval_expr_int_literal_agrees_mem_src[local]:
  !cx e es tv es' v es'' n.
    eval_expr cx e es = (INL tv, es') /\
    read_result cx tv es' = (INL v, es'') /\
    expr_int_literal e = SOME n ==> v = IntV n
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[expr_int_literal_def] >>
  rename1 `Literal ty lit` >> Cases_on `lit` >>
  simp[expr_int_literal_def, Once evaluate_def, return_def,
       read_result_def, evaluate_literal_def] >>
  rpt strip_tac >> gvs[read_result_def, return_def]
QED

Theorem well_formed_type_bits_mem_src[local]:
  !tenv ty. well_formed_type tenv ty ==> type_bits ty MOD 8 = 0
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[type_bits_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[type_bits_def, well_formed_type_def, evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem eval_expr_shift_amount_mem_src[local]:
  !cx e es tv es' v es'' tenv vt.
    eval_expr cx e es = (INL tv, es') /\
    read_result cx tv es' = (INL v, es'') /\
    evaluate_type tenv (expr_type e) = SOME vt /\ value_has_type vt v /\
    shift_amount_ok e ==> ?i. v = IntV i /\ 0 <= i
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_uint_type (expr_type e)`
  >- (gvs[is_uint_type_def] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `v` >> gvs[value_has_type_def]) >>
  `nonneg_int_literal e` by gvs[shift_amount_ok_def] >>
  Cases_on `e` >> gvs[nonneg_int_literal_def, int_literal_value_def] >>
  rename1 `Literal ty lit` >> Cases_on `lit` >>
  gvs[int_literal_value_def, AllCaseEqs()] >>
  `expr_int_literal (Literal ty (IntL i)) = SOME i` by simp[expr_int_literal_def] >>
  drule_all eval_expr_int_literal_agrees_mem_src >> strip_tac >> simp[]
QED


Theorem stmt_state_rel_gas_obs_mem_src[local]:
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs) s =
  stmt_state_rel ctx func cenv cx es s
Proof
  SIMP_TAC std_ss [stmt_state_rel_def, state_rel_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
    immutable_alloca_sep_def, evaluation_state_accfupds]
QED
val _ = temp_delsimps ["stmt_state_rel_gas_obs"];
val _ = augment_srw_ss [rewrites [stmt_state_rel_gas_obs_mem_src]];


Theorem augassign_attr_binop_admissible_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] fv v ee)
Proof
  strip_tac >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] fv v ee) <=>
   expr_res_ok (case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err))` by
    (irule bop_result_augassign_res_ok >> simp[]) >>
  drule_all eval_augassign_attr_fields_obs_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`, `gs`] mp_tac) >>
  simp[GSYM bind_assoc, bind_def] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop fv v` >> gvs[expr_res_ok_def] >>
  simp[lift_sum_def, raise_def] >> strip_tac >>
  drule_all gas_admissible_result >> simp[stmt_res_ok_def]
QED

Theorem augassign_attr_write_admissible_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) /\
  bop_result cx ty bop [ty; expr_type e] fv v ee = INL w /\
  write_place cx (MemoryPlace id [AttrSubscript fld]) w ee = (res, fin) ==>
  !m. res <> INR (Error (TypeError m))
Proof
  strip_tac >>
  `?actual. evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     ftv bop fv v = INL actual` by
    metis_tac[bop_result_augassign_success] >>
  Cases_on `write_place cx (MemoryPlace id [AttrSubscript fld]) actual ee` >>
  rename1 `_ = (actual_res, actual_fin)` >>
  `eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
     (es with gas_obs := gs) = (actual_res, actual_fin)` by
    (drule_all eval_augassign_attr_fields_obs_mem_src >>
     disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`, `gs`] mp_tac) >>
     simp[GSYM bind_assoc, bind_def, lift_sum_def, return_def]) >>
  `stmt_res_ok lctx actual_res` by metis_tac[gas_admissible_result] >>
  `res = actual_res` by
    (qspecl_then [`[AttrSubscript fld]`, `cx`, `id`, `w`, `ee`, `actual`]
       mp_tac write_place_short_memory_result >> simp[]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

Theorem augassign_attr_rhs_exempt_mem_src[local]:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  gas_marked_exec memory (ctx,func)
    (eval_target_place cx (AttributeTarget (NameTarget id) fld))
    (es,s0) [] (INL (MemoryPlace id [AttrSubscript fld])) es (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  rewrite_tac[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  simp[bind_assoc] >>
  rewrite_tac[read_place_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[bind_return, lift_option_type_def, read_memory_path_def,
       evaluate_subscripts_def, lift_sum_def] >>
  rewrite_tac[place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[bind_return, lift_option_type_def, subscripts_type_def,
       subscript_type_def, lift_sum_def] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Theorem write_attr_local_gas_obs_mem_src[local]:
  write_place cx (MemoryPlace id [AttrSubscript fld]) v ee = (res,ff) ==>
  write_place cx (MemoryPlace id [AttrSubscript fld]) v
    (ee with gas_obs := obs) = (res,ff with gas_obs := obs)
Proof
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       set_scopes_def, return_def, raise_def] >>
  Cases_on `find_containing_scope id ee.scopes` >> simp[raise_def] >>
  rename1 `find_containing_scope _ _ = SOME q` >> PairCases_on `q` >>
  simp[replace_memory_entry_def, bind_def, ignore_bind_def,
       assert_def, raise_def, return_def, AllCaseEqs()] >>
  Cases_on `evaluate_subscripts q2.type q2.value [AttrSubscript fld]` >>
  simp[return_def, raise_def, bind_def, set_scopes_def] >>
  Cases_on `assign_subscripts q2.type q2.value [AttrSubscript fld] (Replace v)` >>
  simp[return_def, raise_def, bind_def, set_scopes_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem augassign_attr_store_continuation_exec_mem_src[local]:
  br = INL w /\
  gas_marked_exec memory (ctx,func)
    (write_place cx (MemoryPlace id [AttrSubscript fld]) w)
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u) [] res fin r
Proof
  strip_tac >> gvs[gas_marked_exec_def, bind_def, lift_sum_def, return_def]
QED

Theorem augassign_attr_error_continuation_exec_mem_src[local]:
  br = INR err /\ gas_marked_path memory ctx func u 0 r ==>
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum br) (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (ee with gas_obs := [],u) [] (INR (Error err)) (ee with gas_obs := []) r
Proof
  strip_tac >> gvs[gas_marked_exec_def, bind_def, lift_sum_def, raise_def]
QED

(* The source invariant supplies concrete witnesses for the conditional IH. *)
Theorem struct_has_type_field_mem_src[local]:
  !fs vals id ftv.
    struct_has_type fs vals /\ ALOOKUP fs id = SOME ftv ==>
    ?fv. ALOOKUP vals id = SOME fv /\ value_has_type ftv fv
Proof
  Induct >> Cases_on `vals` >>
  FULL_SIMP_TAC std_ss [value_has_type_def, alistTheory.ALOOKUP_def] >>
  rpt gen_tac >>
  rename1 `struct_has_type (ft::fs) (v::vs)` >>
  PairCases_on `ft` >> PairCases_on `v` >>
  FULL_SIMP_TAC std_ss [value_has_type_def, alistTheory.ALOOKUP_def] >>
  rpt strip_tac >> Cases_on `ft0 = id` >>
  FULL_SIMP_TAC std_ss [] >> metis_tac[]
QED

Theorem expr_sim_inv_local_mem_src[local]:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    (?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    (?entry. lookup_scopes id es.scopes = SOME entry) /\
    !entry. lookup_scopes id es.scopes = SOME entry ==>
      evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  rpt gen_tac >>
  pure_rewrite_tac [expr_sim_inv_def, env_consistent_def,
    env_scopes_consistent_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (Cases_on `lookup_scopes id es.scopes` >>
    metis_tac[optionTheory.IS_SOME_DEF]) >> metis_tac[]
QED

Theorem alookup_zip_field_mem_src[local]:
  !fields tvs f fld fty fsz.
    OPT_MMAP f (MAP (FST o SND) fields) = SOME tvs /\
    ALOOKUP fields fld = SOME (fty,fsz) ==>
    ?ftv. ALOOKUP (ZIP (MAP FST fields,tvs)) fld = SOME ftv /\
      f fty = SOME ftv
Proof
  Induct >> FULL_SIMP_TAC list_ss [listTheory.OPT_MMAP_def, alistTheory.ALOOKUP_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  FULL_SIMP_TAC list_ss [listTheory.OPT_MMAP_def, alistTheory.ALOOKUP_def] >>
  strip_tac >> qpat_x_assum `_:: _ = tvs` (SUBST_ALL_TAC o SYM) >>
  Cases_on `h0 = fld` >>
  FULL_SIMP_TAC list_ss [alistTheory.ALOOKUP_def] >> metis_tac[]
QED

Theorem alookup_fields_args_mem_src[local]:
  !fields args fld fty.
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args /\
    ALOOKUP args fld = SOME fty ==>
    ?fsz. ALOOKUP fields fld = SOME (fty, fsz)
Proof
  Induct >> Cases_on `args` >>
  FULL_SIMP_TAC list_ss [alistTheory.ALOOKUP_def] >>
  rpt gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  FULL_SIMP_TAC list_ss [alistTheory.ALOOKUP_def] >>
  strip_tac >> Cases_on `h0 = fld` >>
  FULL_SIMP_TAC list_ss [alistTheory.ALOOKUP_def] >> metis_tac[]
QED

Theorem attribute_type_struct_field_mem_src[local]:
  !cenv cx env es sid fld fty.
    expr_sim_inv cenv cx env es /\
    attribute_type (get_tenv cx) (StructT sid) fld = SOME fty ==>
    ?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                     (nsid_to_string sid)) fld = SOME (fty, fsz)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `attribute_type _ _ _ = _` mp_tac >>
  SIMP_TAC std_ss [attribute_type_def, AllCaseEqs()] >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     pure_rewrite_tac [expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  pure_rewrite_tac [sfields_tenv_consistent_def] >> strip_tac >>
  qpat_x_assum `v1 = StructArgs fields` SUBST_ALL_TAC >>
  first_x_assum drule >> strip_tac >>
  FULL_SIMP_TAC std_ss [get_struct_fields_def] >>
  metis_tac[alookup_fields_args_mem_src]
QED

Theorem struct_field_type_mem_src[local]:
  !cenv cx env es sid fs fld fty fsz.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) ==>
    ?ftv. ALOOKUP fs fld = SOME ftv /\
      evaluate_type (get_tenv cx) fty = SOME ftv
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  SIMP_TAC std_ss [Once vyperValueTheory.evaluate_type_def, LET_THM,
    AllCaseEqs()] >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     pure_rewrite_tac [expr_sim_inv_def] >> metis_tac[]) >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  pure_rewrite_tac [sfields_tenv_consistent_def] >> strip_tac >>
  qpat_x_assum `v1 = StructArgs args` SUBST_ALL_TAC >>
  first_x_assum drule >> strip_tac >>
  FULL_SIMP_TAC std_ss [get_struct_fields_def] >>
  drule (cj 2 evaluate_type_mono) >> strip_tac >>
  FULL_SIMP_TAC std_ss [vyperValueTheory.evaluate_types_OPT_MMAP] >>
  FULL_SIMP_TAC list_ss [vyperValueTheory.type_value_11] >>
  metis_tac[alookup_zip_field_mem_src]
QED

Theorem augassign_attr_source_fields_mem_src[local]:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) ==>
  ?entry fs vals ftv fv.
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\ value_has_type ftv fv
Proof
  strip_tac >>
  drule_all expr_sim_inv_local_mem_src >> strip_tac >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type_mem_src >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  drule_all struct_has_type_field_mem_src >> strip_tac >> metis_tac[]
QED

Theorem write_attr_local_typed_mem_src[local]:
  !cx cenv env id fld sid fty fsz es1 v res es'.
    write_place cx (MemoryPlace id [AttrSubscript fld]) v es1 = (res, es') /\
    (!m. res <> INR (Error (TypeError m))) /\
    expr_sim_inv cenv cx env es1 /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) ==>
    res = INL () /\
    ?pre env1 entry rest fs vals ftv.
      find_containing_scope id es1.scopes = SOME (pre, env1, entry, rest) /\
      entry.type = StructTV fs /\ entry.value = StructV vals /\
      fields_layout (get_struct_fields cenv.ce_struct_fields
                       (nsid_to_string sid)) fs /\
      struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
      evaluate_type (get_tenv cx) fty = SOME ftv /\
      es' = es1 with scopes :=
        pre ++ (env1 |+ (id, entry with
                  <|value := StructV (AFUPDKEY fld (K v) vals);
                    popped := []|>)) :: rest
Proof
  rpt gen_tac >> strip_tac >>
  drule_all augassign_attr_source_fields_mem_src >> strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[expr_sim_inv_local_mem_src] >>
  drule_all struct_fields_layout >> strip_tac >>
  FULL_SIMP_TAC std_ss [type_value_11] >>
  `struct_has_type fs vals` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     SIMP_TAC std_ss [expr_sim_inv_def, state_well_typed_def] >>
     strip_tac >> drule_all scope_well_typed_lookup_scopes >>
     ASM_SIMP_TAC std_ss [value_has_type_def]) >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  ASM_SIMP_TAC std_ss [write_place_def, get_scopes_def, bind_def,
    lift_option_type_def, type_check_def, ignore_bind_def, return_def,
    raise_def, lift_sum_def, replace_memory_entry_def,
    evaluate_subscripts_def, assign_subscripts_def, set_scopes_def,
    assert_def, LET_THM, type_value_case_def, sumTheory.sum_case_def,
    AllCaseEqs()] >>
  Cases_on `entry.assignable` >>
  FULL_SIMP_TAC std_ss [return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> FULL_SIMP_TAC std_ss [] >> metis_tac[]
QED

Theorem augassign_attr_conditional_ih_mem_src[local]:
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==>
     body_expr_mem_ok cx e) /\
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) ==>
  body_expr_mem_ok cx e
Proof
  strip_tac >> drule_all augassign_attr_source_fields_mem_src >> strip_tac >>
  drule_all augassign_attr_place_reads_mem_src >>
  disch_then (qspec_then `cx` strip_assume_tac) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem augassign_attr_typing_mem_src[local]:
  type_stmt env ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)
    = SOME env' ==>
  well_typed_target env (AttributeTarget (NameTarget id) fld) ty /\
  well_typed_expr env e /\ well_typed_binop ty bop ty (expr_type e) /\
  bop <> In /\ bop <> NotIn /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e)
Proof
  simp[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

(* Single fresh-output instruction boundary used by both load phases. *)
Theorem augassign_field_emit_path_mem[local]:
  emit_op opc args sa = (op,sb) /\ opc <> GAS /\ opc <> INVOKE /\
  ~is_terminator opc /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s0 /\
  step_inst_base
    (mk_inst sa.cs_next_id opc args [STRING #"%" (toString sa.cs_next_var)])
    s0 = OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s0) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand op t = SOME w /\ stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. op = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `run_inst_seq (emitted_insts sa sb) s0 = OK (update_var out w s0)` by
    (FULL_SIMP_TAC std_ss [run_inst_seq_def, exec_result_case_def, markerTheory.Abbrev_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    ASM_SIMP_TAC list_ss [mk_inst_def, instruction_accfupds] >>
  `gas_path_mem ctx func s0 0
     (OK (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~(update_var out w s0).vs_halted /\
   (update_var out w s0).vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> ASM_SIMP_TAC std_ss [] >>
     qexists_tac `sa` >> ASM_SIMP_TAC std_ss []) >>
  `alloca_inv s0` by FULL_SIMP_TAC std_ss [stmt_state_rel_def] >>
  `alloca_history func
     (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> ASM_SIMP_TAC std_ss [] >>
     qexistsl_tac [`s0`, `sa`] >> ASM_SIMP_TAC list_ss [mk_inst_def, instruction_accfupds]) >>
  `not_local_ptr cenv es.scopes out` by
    (FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> ASM_SIMP_TAC std_ss []) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> ASM_SIMP_TAC std_ss []) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w s0)` by
    (irule stmt_state_rel_update_var >> ASM_SIMP_TAC std_ss []) >>
  qexists_tac `update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  ASM_SIMP_TAC std_ss [gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def,
    update_var_def, venom_state_accfupds, lookup_var_def, FLOOKUP_UPDATE,
    markerTheory.Abbrev_def, not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def,
    not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  ASM_SIMP_TAC arith_ss [listTheory.CONS_11, ASCIInumbersTheory.toString_inj]
QED

Theorem augassign_field_add_path_mem[local]:
  emit_op ADD [Var p; Lit (n2w off)] sa = (dst,sn) /\
  lookup_var p s0 = SOME w /\
  fn_has_code sa sn func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand dst t = SOME (w + n2w off) /\ stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    local_ptrs_reserved cenv sn /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    sa.cs_next_var <= sn.cs_next_var /\
    (?out. dst = Var out /\ not_fresh_at sn out)
Proof
  strip_tac >> irule augassign_field_emit_path_mem >>
  simp[] >> reverse conj_tac
  >- (irule attr_add_prefix_mem_ok >> metis_tac[]) >>
  qexistsl_tac [`[Var p; Lit (n2w off)]`, `ADD`] >>
  simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, wordsTheory.WORD_ADD_COMM]
QED

Theorem augassign_field_read_path_mem[local]:
  emit_op MLOAD [dst] sa = (cur,sb) /\
  eval_operand dst s0 = SOME addr /\ w2n addr + 32 <= s0.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand cur t = SOME (mload (w2n addr) s0) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. cur = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >> irule augassign_field_emit_path_mem >>
  simp[] >> reverse conj_tac
  >- (irule emit_mload_mem_ok >> metis_tac[]) >>
  qexistsl_tac [`[dst]`, `MLOAD`] >>
  simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]
QED

Theorem augassign_field_address_bound_mem[local]:
  stmt_state_rel ctx func cenv cx es s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME wbase /\ lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ fields_layout fields fs /\
  ALOOKUP fs fld = SOME ftv /\ word_value_type ty /\
  evaluate_type (get_tenv cx) ty = SOME ftv ==>
  w2n (wbase + n2w (struct_field_offset fields fld)) + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n wbase + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n wbase + type_memory_size_fields fs <= s.vs_alloca_next` by
    gvs[type_memory_size_def] >>
  `type_memory_size ftv = 32` by metis_tac[word_value_type_memory_size] >>
  drule_all body_field_address_no_wrap >>
  drule_all body_field_region_frontier >> simp[]
QED

Theorem fields_val_wf_update_mem_src[local]:
  !vals fs fld v ftv.
    struct_has_type fs vals /\ fields_val_wf vals fs /\
    ALOOKUP fs fld = SOME ftv /\ val_wf ftv v ==>
    fields_val_wf (AFUPDKEY fld (K v) vals) fs
Proof
  Induct >> Cases_on `fs` >>
  FULL_SIMP_TAC list_ss [value_has_type_def, val_wf_def,
    alistTheory.ALOOKUP_def, alistTheory.AFUPDKEY_def] >>
  rpt gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  FULL_SIMP_TAC list_ss [value_has_type_def, val_wf_def,
    alistTheory.ALOOKUP_def, alistTheory.AFUPDKEY_def] >>
  strip_tac >> Cases_on `h0 = fld` >>
  FULL_SIMP_TAC list_ss [alistTheory.ALOOKUP_def, alistTheory.AFUPDKEY_def,
    val_wf_def, pairTheory.pair_case_def] >>
  `fld <> h'0` by metis_tac[] >>
  ASM_SIMP_TAC list_ss [val_wf_def, pairTheory.pair_case_def] >> metis_tac[]
QED

Theorem fields_in_memory_mstore_field_mem_src[local]:
  !vals fs flds off s fld v wd ftv.
    fields_layout flds fs /\ struct_has_type fs vals /\
    fields_val_wf vals fs /\ fields_in_memory vals fs off s.vs_memory /\
    ALOOKUP fs fld = SOME ftv /\ type_memory_size ftv = 32 /\
    val_in_memory ftv v (off + struct_field_offset flds fld)
      (mstore (off + struct_field_offset flds fld) wd s).vs_memory ==>
    fields_in_memory (AFUPDKEY fld (K v) vals) fs off
      (mstore (off + struct_field_offset flds fld) wd s).vs_memory
Proof
  Induct >> Cases_on `fs` >> Cases_on `flds` >>
  FULL_SIMP_TAC list_ss [value_has_type_def, fields_layout_def,
    alistTheory.ALOOKUP_def, alistTheory.AFUPDKEY_def, val_in_memory_def] >>
  rpt gen_tac >> PairCases_on `h` >> PairCases_on `h'` >> PairCases_on `h''` >>
  FULL_SIMP_TAC list_ss [value_has_type_def, fields_layout_def,
    alistTheory.ALOOKUP_def, alistTheory.AFUPDKEY_def, val_in_memory_def,
    val_wf_def, pairTheory.pair_case_def] >>
  strip_tac >>
  qpat_x_assum `h'0 = h0` SUBST_ALL_TAC >>
  qpat_x_assum `h0 = h''0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `h'2 = _` SUBST_ALL_TAC >>
  FULL_SIMP_TAC list_ss [LET_THM, pairTheory.pair_case_def] >>
  Cases_on `h0 = fld` >>
  FULL_SIMP_TAC list_ss [struct_field_offset_def, alistTheory.AFUPDKEY_def,
    val_in_memory_def, LET_THM, pairTheory.pair_case_def]
  >- (SIMP_TAC std_ss [mstore_def, venom_state_accfupds, LET_THM] >>
      irule (SIMP_RULE std_ss [mstore_def, venom_state_accfupds, LET_THM]
        (cj 2 valueEncodingPropsTheory.mstore_preserves_val_in_memory)) >>
      ASM_SIMP_TAC list_ss [] ) >>
  conj_tac
  >- (SIMP_TAC std_ss [mstore_def, venom_state_accfupds, LET_THM] >>
      irule (SIMP_RULE std_ss [mstore_def, venom_state_accfupds, LET_THM]
        (cj 1 valueEncodingPropsTheory.mstore_preserves_val_in_memory)) >>
      ASM_SIMP_TAC arith_ss []) >>
  once_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
  first_x_assum irule >> asm_rewrite_tac [] >>
  qexists_tac `ftv` >> asm_rewrite_tac [] >>
  qpat_x_assum `val_in_memory ftv v _ _` mp_tac >>
  pure_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> strip_tac >> asm_rewrite_tac []
QED

Theorem stmt_state_rel_write_field_mem_src[local]:
  !func cenv cx es s id p sz w pre env entry rest fs vals flds fld ftv etv v ctx.
    stmt_state_rel ctx func cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ store_lays_out etv ftv v ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
         pre ++ (env |+ (id, entry with
                   <|value := StructV (AFUPDKEY fld (K v) vals);
                     popped := []|>)) :: rest)
      (mstore (w2n w + struct_field_offset flds fld)
         (typed_val_to_w256 etv v) s)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es.scopes s` by
    FULL_SIMP_TAC std_ss [stmt_state_rel_def, state_rel_def] >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
   val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `struct_field_offset flds fld + 32 <= type_memory_size_fields fs` by
    (drule_all struct_field_offset_le >>
     FULL_SIMP_TAC std_ss [store_lays_out_def]) >>
  `fields_val_wf vals fs /\ fields_in_memory vals fs (w2n w) s.vs_memory` by
    (conj_tac
     >- (qpat_x_assum `val_wf entry.type entry.value` mp_tac >>
         ASM_SIMP_TAC std_ss [val_wf_def, type_value_case_def, value_case_def]) >>
     qpat_x_assum `val_in_memory entry.type entry.value _ _` mp_tac >>
     ASM_SIMP_TAC std_ss [val_in_memory_def, type_value_case_def, value_case_def]) >>
  irule stmtSimAssignStoreTheory.stmt_state_rel_write_local >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac
  >- (ASM_SIMP_TAC std_ss [val_wf_def, type_value_case_def] >>
      irule fields_val_wf_update_mem_src >>
      FULL_SIMP_TAC std_ss [store_lays_out_def, val_wf_def,
        type_value_case_def, value_case_def] >> metis_tac[]) >>
  conj_tac
  >- (irule stmtSimAssignStoreTheory.local_mstore_immutables_at >>
      reverse conj_tac >- metis_tac[] >>
      qexistsl_tac [`id`, `sz`] >> conj_tac
      >- (qpat_x_assum `type_memory_size entry.type <= sz` mp_tac >>
          ASM_SIMP_TAC std_ss [type_memory_size_def] >> decide_tac) >>
      ASM_SIMP_TAC std_ss [local_region_def] >>
      qexistsl_tac [`p`, `w`] >> asm_rewrite_tac []) >>
  qexistsl_tac [`p`, `s`, `sz`, `w`] >>
  ASM_SIMP_TAC std_ss [] >>
  conj_tac
  >- SIMP_TAC std_ss [lookup_var_def, mstore_def, LET_THM, venom_state_accfupds] >>
  conj_tac
  >- (rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
      FULL_SIMP_TAC std_ss [type_memory_size_def] >> decide_tac) >>
  conj_tac
  >- SIMP_TAC std_ss [mstore_def, LET_THM, venom_state_fupdfupds,
                     venom_state_component_equality, venom_state_accfupds] >>
  ASM_SIMP_TAC std_ss [val_in_memory_def, type_value_case_def, value_case_def] >>
  irule fields_in_memory_mstore_field_mem_src >>
  asm_rewrite_tac [] >> qexists_tac `ftv` >>
  FULL_SIMP_TAC std_ss [store_lays_out_def]
QED


Theorem stmt_state_rel_field_word_mem_src[local]:
  !func cenv cx es s id p sz w0 entry fs vals flds fld ftv fv fty ctx.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w0 /\
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout flds fs /\ struct_has_type fs vals /\
    ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
    is_word_type fty /\ evaluate_type (get_tenv cx) fty = SOME ftv /\
    value_has_type ftv fv ==>
    mload (w2n (w0 + n2w (struct_field_offset flds fld))) s =
      typed_val_to_w256 ftv fv
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `w2n w0 + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n w0) s.vs_memory` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     pure_rewrite_tac [local_ptrs_rel_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     FULL_SIMP_TAC std_ss [optionTheory.SOME_11] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `w2n w0 + type_memory_size_fields fs <= s.vs_alloca_next` by
    (qpat_x_assum `type_memory_size entry.type <= sz` mp_tac >>
     ASM_SIMP_TAC std_ss [type_memory_size_def] >> decide_tac) >>
  drule_all body_field_address_no_wrap >>
  SIMP_TAC std_ss [wordsTheory.n2w_w2n] >> strip_tac >>
  `fields_in_memory vals fs (w2n w0) s.vs_memory` by
    (qpat_x_assum `val_in_memory entry.type entry.value _ _` mp_tac >>
     ASM_SIMP_TAC std_ss [val_in_memory_def, type_value_case_def]) >>
  drule_all fields_in_memory_field >> strip_tac >>
  qpat_x_assum `struct_has_type _ _` kall_tac >>
  qpat_x_assum `val_in_memory entry.type entry.value _ _` kall_tac >>
  qpat_x_assum `fields_in_memory _ _ _ _` kall_tac >>
  Cases_on `fty` >> FULL_SIMP_TAC std_ss [is_word_type_def] >-
   (Cases_on `b` >> FULL_SIMP_TAC std_ss [is_word_type_def] >>
    qpat_x_assum `evaluate_type _ _ = SOME ftv` mp_tac >>
    SIMP_TAC std_ss [vyperValueTheory.evaluate_type_def, base_type_case_def,
      bound_case_def, LET_THM, AllCaseEqs()] >> strip_tac >>
    qpat_x_assum `BaseTV _ = ftv` (SUBST_ALL_TAC o SYM) >>
    Cases_on `fv` >>
    FULL_SIMP_TAC std_ss [value_has_type_def, type_value_distinct,
      base_type_distinct, type_value_11, base_type_11] >>
    FULL_SIMP_TAC std_ss [val_in_memory_def,
      typed_val_to_w256_def, valueEncodingPropsTheory.mem_word_at_eq_mload,
      type_value_case_def, base_type_case_def, bound_case_def, AllCaseEqs()] >>
    FULL_SIMP_TAC std_ss [is_word_type_def]) >>
  qpat_x_assum `evaluate_type _ _ = SOME ftv` mp_tac >>
  SIMP_TAC std_ss [vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  strip_tac >> qpat_x_assum `FlagTV _ = ftv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `fv` >>
  FULL_SIMP_TAC std_ss [value_has_type_def, type_value_distinct,
    type_value_11] >>
  FULL_SIMP_TAC std_ss [val_in_memory_def, typed_val_to_w256_def,
    valueEncodingPropsTheory.mem_word_at_eq_mload, type_value_case_def]
QED

Theorem augassign_attr_local_load_mem[local]:
  emit_op ADD [Var p; Lit (n2w (struct_field_offset fields fld))] sa = (dst,sn) /\
  emit_op MLOAD [dst] sn = (cur,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME w0 /\ lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  word_value_type ty /\ evaluate_type (get_tenv cx) ty = SOME ftv /\
  value_has_type ftv fv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand dst t = SOME (w0 + n2w (struct_field_offset fields fld)) /\
    eval_operand cur t = SOME (typed_val_to_w256 ftv fv) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. cur = Var out /\ not_fresh_at sb out) /\
    (?dv. dst = Var dv /\ not_fresh_at sb dv)
Proof
  strip_tac >>
  `cs_extends sa sn /\ cs_extends sn sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `w2n (w0 + n2w (struct_field_offset fields fld)) + 32 <= s0.vs_alloca_next` by
    (irule augassign_field_address_bound_mem >> metis_tac[]) >>
  `mload (w2n (w0 + n2w (struct_field_offset fields fld))) s0 =
    typed_val_to_w256 ftv fv` by
    (irule stmt_state_rel_field_word_mem_src >> metis_tac[word_value_type_word]) >>
  drule_all augassign_field_add_path_mem >> strip_tac >>
  rename1 `gas_marked_path T ctx func s0 0 (OK t1)` >>
  `w2n (w0 + n2w (struct_field_offset fields fld)) + 32 <= t1.vs_alloca_next` by
    simp[] >>
  drule_all augassign_field_read_path_mem >> strip_tac >>
  rename1 `gas_marked_path T ctx func t1 0 (OK t2)` >>
  `gas_marked_path T ctx func s0 0 (OK t2)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!rp. not_fresh_at sa rp ==> not_fresh_at sn rp` by
    metis_tac[not_fresh_at_mono] >>
  qexists_tac `t2` >> gvs[eval_operand_def, mload_def] >>
  metis_tac[not_fresh_at_mono]
QED

(* The store uses the live local region after RHS/operator evaluation. *)
Theorem assign_attr_local_word_store_path_mem:
  emit_void MSTORE [dst; op] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  lookup_var p s = SOME wbase /\
  eval_operand dst s = SOME (wbase + n2w (struct_field_offset fields fld)) /\
  eval_operand op s = SOME (typed_val_to_w256 ftv v) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ word_value_type ty /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?t. stmt_state_rel ctx func cenv cx
        (es with scopes := pre ++
          (env |+ (id, entry with
            <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t /\ gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `w2n (wbase + n2w (struct_field_offset fields fld)) + 32 <= s.vs_alloca_next` by
    (irule augassign_field_address_bound_mem >> metis_tac[]) >>
  `w2n (wbase + n2w (struct_field_offset fields fld)) =
     w2n wbase + struct_field_offset fields fld` by
    ( `w2n wbase + type_memory_size_fields fs <= s.vs_alloca_next` by
        (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
         first_x_assum drule_all >> simp[type_memory_size_def] >> decide_tac) >>
      `s.vs_alloca_next < dimword (:256)` by
        metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
      drule_all body_field_address_no_wrap >> simp[]) >>
  drule_all stmt_state_rel_write_field_mem_src >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = mstore (w2n (wbase + n2w (struct_field_offset fields fld)))
                          (typed_val_to_w256 ftv v) s` >>
  `run_inst_seq (emitted_insts st st') s = OK u` by
    (`step_inst_base (mk_inst st.cs_next_id MSTORE [dst; op] []) s = OK u` by
       (qunabbrev_tac `u` >> irule step_MSTORE >> simp[]) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule emit_mstore_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `st` >> simp[is_terminator_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `st`] >> simp[is_terminator_def]) >>
  `stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) u` by
    simp[Abbr `u`] >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  simp[Abbr `u`, lookup_var_def, mstore_def]
QED

Theorem stmt_state_rel_scopes_gas_obs_mem[local]:
  stmt_state_rel ctx func cenv cx (es with <|scopes := sc; gas_obs := gs|>) s =
  stmt_state_rel ctx func cenv cx (es with scopes := sc) s
Proof
  `es with <|scopes := sc; gas_obs := gs|> =
     ((es with scopes := sc) with gas_obs := gs)` by (Cases_on `es` >> simp[]) >>
  once_asm_rewrite_tac [] >>
  pure_rewrite_tac [stmt_state_rel_gas_obs_mem_src] >> REFL_TAC
QED

Theorem augassign_attr_local_code_parts_mem_src[local]:
  !cenv lctx ty0 ty id fld bop e sa c sf p sz sid.
    stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME (StructT sid) ==>
    c = cenv /\
    ?dst sn cur s1 rhs s2 res_op s3.
      emit_op ADD
        [Var p; Lit (n2w (struct_field_offset
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sa = (dst, sn) /\
      emit_op MLOAD [dst] sn = (cur, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs, s2) /\
      compile_binop bop cur rhs ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void MSTORE [dst; res_op] s3 = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  FULL_SIMP_TAC std_ss [stmt_env_def, declare_stmt_local_def, compile_stmt_def,
    compile_get_target_ptr_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def, LET_THM, var_location_case_def,
    data_location_case_def, place_ty_case_def, vyperASTTheory.type_case_def] >>
  rpt (pairarg_tac >>
    FULL_SIMP_TAC std_ss [comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM, data_location_case_def] >>
    rpt (qpat_x_assum `(_,_) = v` (SUBST_ALL_TAC o SYM)) >>
    FULL_SIMP_TAC std_ss [comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM, data_location_case_def]) >>
  qpat_x_assum `cenv = c` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `cs' = sf` SUBST_ALL_TAC >>
  qpat_x_assum `(s:compile_state) = t` SUBST_ALL_TAC >>
  rename1 `emit_void MSTORE _ _ = (u, sf)` >> Cases_on `u` >>
  metis_tac[]
QED

Theorem well_typed_binop_augassign_word_mem_src[local]:
  !ty bop t2.
    well_typed_binop ty bop ty t2 /\ bop <> In /\ bop <> NotIn ==>
    word_value_type ty /\ word_value_type t2
Proof
  rpt gen_tac >> Cases_on `bop` >>
  SIMP_TAC std_ss [well_typed_binop_def, word_value_type_def,
    is_numeric_type_def] >>
  rpt strip_tac >>
  metis_tac[is_bool_type_def]
QED

Theorem compile_augassign_attr_local_mem:
  (!gs. expr_sim_mem ctx func cenv cx ty e (es with gas_obs := gs)) /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (ty,fsz) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty0 (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all augassign_attr_source_fields_mem_src >> strip_tac >>
  drule_all expr_sim_inv_local_mem_src >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word_mem_src] >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  `cenv.ce_var_type id = SOME (StructT sid)` by
    metis_tac[expr_sim_inv_def] >>
  `struct_has_type fs vals` by
    ( `value_has_type entry.type entry.value` by
        (fs[expr_sim_inv_def, state_well_typed_def] >>
         metis_tac[scope_well_typed_lookup_scopes]) >>
      gvs[value_has_type_def]) >>
  drule_all augassign_attr_local_code_parts_mem_src >> strip_tac >> gvs[] >>
  `cs_extends sa sn /\ cs_extends sn s1 /\ cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s3 /\ cs_extends s1 sb /\
   cs_extends s2 sb /\ cs_extends sa s2 /\ cs_extends sa s3` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `?w0. lookup_var p s0 = SOME w0` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all augassign_attr_local_load_mem >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (simp[] >> irule augassign_attr_rhs_admissible_mem_src >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by simp[] >>
  qpat_x_assum `!gs. expr_sim_mem _ _ _ _ _ _ _`
    (qspec_then `[]` (mp_tac o REWRITE_RULE [expr_sim_mem_def])) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_attr_rhs_exempt_mem_src >>
  conj_tac >- metis_tac[] >>
  qexists_tac `t` >> simp[] >>
  simp[gas_marked_exec_def, gas_explicit_def] >>
  gen_tac >>
  irule (cj 1 augassign_attr_place_reads_mem_src) >> simp[] >> metis_tac[]
QED

Resume compile_augassign_attr_local_mem[rhs_summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule augassign_attr_rhs_exception_exec_mem_src >> metis_tac[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_attr_local_mem[rhs_normal]:
  gvs[] >>
  rename1 `expr_post ctx func cenv cx e _ s1 s2 t (ee with gas_obs := []) v rhs u` >>
  qpat_x_assum `cs_extends sa sn` kall_tac >>
  qpat_x_assum `cs_extends sn s1` kall_tac >>
  qpat_x_assum `s1.cs_next_id <= s2.cs_next_id` kall_tac >>
  qpat_x_assum `s2.cs_next_id <= s3.cs_next_id` kall_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
       (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] fv v
      (ee with gas_obs := []))` by
    (irule augassign_attr_binop_admissible_mem_src >> simp[] >>
     metis_tac[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  rename1 `value_has_type etv v` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees_mem_src] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount_mem_src] >>
  `well_formed_type (get_tenv cx) ty` by simp[well_formed_type_def] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits_mem_src] >>
  `binop_frag_val_mem ctx func cenv cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE)
     [ty; expr_type e] fv v (ee with gas_obs := [])` by
    suspend "typed_dispatch" >>
  suspend "operator"
QED

Resume compile_augassign_attr_local_mem[operator]:
  `word_value fv` by metis_tac[word_value_type_typed] >>
  `eval_operand (Var out) t = SOME (val_to_w256 fv)` by
    simp[exprSimPropsTheory.typed_val_to_w256_word_value] >>
  `eval_operand rhs u = SOME (val_to_w256 v)` by
    (irule expr_val_rel_word >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 fv)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ not_fresh_at s2 dv /\ local_ptrs_reserved cenv s2` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `Var out`, `rhs`, `res_op`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_attr_local_mem[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  `bop_result cx ty bop [ty; expr_type e] fv v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       ftv bop fv v of INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[word_value_not_bytes]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     ftv bop fv v = INL result` by gvs[AllCaseEqs()] >>
  Cases_on `write_place cx (MemoryPlace id [AttrSubscript fld]) result
     (ee with gas_obs := [])` >> rename1 `_ = (wr, fin)` >>
  `bop_result cx ty bop [ty; expr_type e] fv v (ee with gas_obs := []) =
     INL result` by simp[] >>
  `!m. wr <> INR (Error (TypeError m))` by
    (drule_all augassign_attr_write_admissible_mem_src >> simp[]) >>
  `expr_sim_inv cenv cx env (ee with gas_obs := [])` by simp[] >>
  drule_all write_attr_local_typed_mem_src >> strip_tac >> gvs[] >>
  rename1 `find_containing_scope id ee.scopes = SOME (pre, env1, cur, rest)` >>
  `value_has_type ftv result` by
    (mp_tac (Q.INST [`t1` |-> `ty`, `t2` |-> `expr_type e`,
       `tenv` |-> `get_tenv cx`, `result_tv` |-> `ftv`,
       `tv1` |-> `ftv`, `tv2` |-> `etv`, `tv` |-> `ftv`,
       `v1` |-> `fv`, `v2` |-> `v`, `v` |-> `result`,
       `u` |-> `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`]
       well_typed_binop_success_type) >> simp[]) >>
  `store_lays_out ftv ftv result` by
    (irule store_lays_out_typed >> simp[] >>
     qexistsl_tac [`ty`, `get_tenv cx`] >> simp[word_value_type_word]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
     `lookup_var x u = SOME w` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def]) >> metis_tac[]) >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >>
     qpat_x_assum `!n1 p' sz1. _ ==> not_fresh_at sa p'` drule >> simp[]) >>
  `lookup_var p s = SOME w0` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand (Var dv) s = SOME
     (w0 + n2w (struct_field_offset
       (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))` by
    (`eval_operand (Var dv) u = SOME
        (w0 + n2w (struct_field_offset
          (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))` by
       (irule eval_operand_frame >> simp[] >>
        qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
     fs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand res_op s = SOME (typed_val_to_w256 ftv result)` by
    simp[typed_val_to_w256_word_value] >>
  suspend "store"
QED

Resume compile_augassign_attr_local_mem[store]:
  drule_all assign_attr_local_word_store_path_mem >> strip_tac >>
  rename1 `gas_marked_path T ctx func s 0 (OK last)` >>
  `gas_marked_path T ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`INL ()`,
    `ee with <|scopes := pre ++
       (env1 |+ (id, cur with
         <|value := StructV (AFUPDKEY fld (K result) vals'); popped := []|>)) ::
       rest; gas_obs := []|>`, `OK last`] >>
  conj_tac
  >- (irule augassign_attr_rhs_normal_exec_mem_src >>
      qexistsl_tac [`ee`, `entry`] >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      irule augassign_attr_store_continuation_exec_mem_src >> simp[] >>
      simp[gas_marked_exec_def] >>
      drule write_attr_local_gas_obs_mem_src >> simp[]) >>
  disj1_tac >> simp[] >> suspend "post"
QED

Resume compile_augassign_attr_local_mem[post]:
  `s3.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >> simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `s3.cs_current_insts` >>
     gvs[block_is_terminated_def, rich_listTheory.LAST_APPEND, listTheory.LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME b` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def] >> metis_tac[]) >> metis_tac[]) >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- simp[stmt_state_rel_scopes_gas_obs_mem] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]
QED

Resume compile_augassign_attr_local_mem[operator_exit]:
  `bop_result cx ty bop [ty; expr_type e] fv v (ee with gas_obs := []) =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[word_value_not_bytes]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ftv bop fv v`
  >- (gvs[] >> fs[expr_exit_def, exit_result_def]) >>
  gvs[] >>
  qexistsl_tac [`INR (Error y)`, `ee with gas_obs := []`, `r`] >>
  conj_tac
  >- (irule augassign_attr_rhs_normal_exec_mem_src >>
      qexistsl_tac [`ee`, `entry`] >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      irule augassign_attr_error_continuation_exec_mem_src >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED



Theorem int_type_byte_width_mem_src[local]:
  !tenv ty tv. is_int_type ty /\ evaluate_type tenv ty = SOME tv ==>
    type_bits ty MOD 8 = 0
Proof
  rpt gen_tac >> Cases_on `ty` >>
  FULL_SIMP_TAC std_ss [is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  FULL_SIMP_TAC std_ss [is_int_type_def, evaluate_type_def,
    type_bits_def, AllCaseEqs(), vyperASTTheory.base_type_distinct,
    vyperASTTheory.base_type_11, LET_THM]
QED

Theorem int_type_value_mem_src[local]:
  !tenv ty tv v.
    is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    ?i. v = IntV i /\ 0 < type_bits ty /\ type_bits ty <= 256 /\
      type_to_int_bound ty = SOME (if is_signed_type ty then Signed (type_bits ty)
        else Unsigned (type_bits ty)) /\
      within_int_bound (if is_signed_type ty then Signed (type_bits ty)
        else Unsigned (type_bits ty)) i
Proof
  rpt gen_tac >> Cases_on `ty` >>
  FULL_SIMP_TAC std_ss [is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  FULL_SIMP_TAC std_ss [is_int_type_def, evaluate_type_def,
    type_bits_def, AllCaseEqs(), vyperASTTheory.base_type_distinct,
    vyperASTTheory.base_type_11, LET_THM] >>
  rpt strip_tac >> qpat_x_assum `BaseTV _ = tv` (SUBST_ALL_TAC o SYM) >>
  Cases_on `v` >>
  FULL_SIMP_TAC std_ss [value_has_type_def, type_bits_def,
    is_signed_type_def, type_to_int_bound_def, within_int_bound_def,
    vyperValueTheory.value_distinct, vyperValueTheory.value_11] >>
  decide_tac
QED


Theorem word_value_type_value_cases_mem_src[local]:
  !tenv t tv v.
    word_value_type t /\ evaluate_type tenv t = SOME tv /\ value_has_type tv v ==>
    (?n i. t = BaseT (UintT n) /\ tv = BaseTV (UintT n) /\ v = IntV i /\
      0 < n /\ n <= 256 /\ within_int_bound (Unsigned n) i) \/
    (?n i. t = BaseT (IntT n) /\ tv = BaseTV (IntT n) /\ v = IntV i /\
      1 < n /\ n <= 256 /\ within_int_bound (Signed n) i) \/
    (?d. t = BaseT DecimalT /\ tv = BaseTV DecimalT /\ v = DecimalV d /\
      within_int_bound (Signed 168) d) \/
    (?b. t = BaseT BoolT /\ tv = BaseTV BoolT /\ v = BoolV b) \/
    (?nsid m k. t = FlagT nsid /\ tv = FlagTV m /\ v = FlagV k /\ m <= 256)
Proof
  rpt gen_tac >> Cases_on `t` >>
  FULL_SIMP_TAC std_ss [word_value_type_def, is_numeric_type_def,
    is_int_type_def, is_bool_type_def, is_flag_type_def,
    vyperASTTheory.type_distinct] >>
  (TRY (rename1 `evaluate_type tenv (BaseT bt) = SOME tv` >> Cases_on `bt`)) >>
  FULL_SIMP_TAC std_ss [is_int_type_def, is_bool_type_def,
    evaluate_type_def, AllCaseEqs(), LET_THM,
    vyperASTTheory.type_distinct, vyperASTTheory.type_11,
    vyperASTTheory.base_type_distinct, vyperASTTheory.base_type_11] >>
  rpt strip_tac >>
  first_x_assum (SUBST_ALL_TAC o SYM) >>
  Cases_on `v` >>
  FULL_SIMP_TAC std_ss [value_has_type_def, within_int_bound_def,
    vyperValueTheory.value_distinct, vyperValueTheory.value_11] >>
  qexists_tac `m` >> asm_rewrite_tac[]
QED

Theorem decimal_type_value_mem_src[local]:
  !tenv tv v. evaluate_type tenv (BaseT DecimalT) = SOME tv /\
    value_has_type tv v ==> ?d. v = DecimalV d /\ within_int_bound (Signed 168) d
Proof
  rpt strip_tac >>
  `word_value_type (BaseT DecimalT)` by
    (SIMP_TAC std_ss [word_value_type_def, is_numeric_type_def]) >>
  drule_all word_value_type_value_cases_mem_src >>
  SIMP_TAC std_ss [vyperASTTheory.type_distinct, vyperASTTheory.type_11,
    vyperASTTheory.base_type_distinct, vyperASTTheory.base_type_11] >>
  metis_tac[]
QED

Theorem within_int_bound_unsigned_256_mem_src[local]:
  !u n i. (u = Unsigned n \/ u = Signed n) /\ n <= 256 /\
    within_int_bound u i /\ 0 <= i ==> within_int_bound (Unsigned 256) i
Proof
  rpt strip_tac >> qpat_x_assum `u = _` SUBST_ALL_TAC >>
  FULL_SIMP_TAC std_ss [within_int_bound_def, LET_THM]
  >- (`2 ** n <= 2 ** 256` by
        (irule arithmeticTheory.EXP_BASE_LEQ_MONO_IMP >> asm_rewrite_tac[] >> decide_tac) >>
      `Num i < 2 ** 256` suffices_by (SIMP_TAC std_ss []) >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  Cases_on `n = 0`
  >- (FULL_SIMP_TAC std_ss [] >> EVAL_TAC) >>
  FULL_SIMP_TAC std_ss [integerTheory.INT_NOT_LT] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  qpat_x_assum `if i < 0 then _ else _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `2 ** (n - 1) <= 2 ** 256` by
    (irule arithmeticTheory.EXP_BASE_LEQ_MONO_IMP >> decide_tac) >>
  `Num i < 2 ** 256` suffices_by (SIMP_TAC std_ss []) >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED


Theorem binop_frag_int_arith_mem_src[local]:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ is_int_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value_mem_src >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value_mem_src >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  Cases_on `bop` >> fs[]
  >~ [`binop_frag_val_mem _ _ _ _ Div`] >- (irule compile_divmod_sim_mem >> simp[])
  >~ [`binop_frag_val_mem _ _ _ _ Mod`] >- (irule compile_divmod_sim_mem >> simp[]) >>
  irule compile_checked_sim_mem >> simp[]
QED

Theorem binop_frag_decimal_arith_mem_src[local]:
  !ctx func cenv cx bop bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop (BaseT DecimalT) (BaseT DecimalT) bl el
      tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `tv`, `v1`] mp_tac decimal_type_value_mem_src >>
  qspecl_then [`tenv`, `tv`, `v2`] mp_tac decimal_type_value_mem_src >>
  asm_rewrite_tac[] >> rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `MEM bop [Mul; Div]`
  >- (irule compile_decimal_mul_div_sim_mem >> simp[]) >>
  irule compile_decimal_add_sub_mod_sim_mem >> simp[] >>
  Cases_on `bop` >> fs[]
QED

Theorem binop_frag_unsafe_typed_mem_src[local]:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    is_int_type ty /\ type_bits ty MOD 8 = 0 /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value_mem_src >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value_mem_src >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule compile_unsafe_sim_mem >> simp[]
QED

Theorem binop_frag_compare_typed_mem_src[local]:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0 tenv tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt strip_tac >>
  `word_value v1 /\ (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
   !m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256` by
    (qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac
       word_value_type_value_cases_mem_src >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     gvs[word_value_def, is_uint256_def]) >>
  Cases_on `bop = Min \/ bop = Max`
  >- (irule compile_minmax_sim_mem >> metis_tac[]) >>
  irule compile_compare_sim_mem >> gvs[] >> metis_tac[]
QED

Theorem binop_frag_bitwise_typed_mem_src[local]:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    (bop = And \/ bop = Or \/ bop = XOr) /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> irule compile_bitwise_sim_mem >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac word_value_type_value_cases_mem_src >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac word_value_type_value_cases_mem_src >>
  asm_rewrite_tac[] >> rpt strip_tac >> gvs[type_to_int_bound_def]
QED

Theorem binop_frag_shift_typed_mem_src[local]:
  !ctx func cenv cx bop ty t2 bl el tys v1 v2 es0 tenv tv1 tv2 i2.
    (bop = ShL \/ bop = ShR) /\ is_int_type ty /\ type_bits ty = 256 /\
    is_int_type t2 /\ v2 = IntV i2 /\ 0 <= i2 /\
    evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv1`, `v1`] mp_tac int_type_value_mem_src >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value_mem_src >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256_mem_src]) >>
  irule compile_shift_sim_mem >> gvs[]
QED

Theorem binop_frag_shr_narrow_mem_src[local]:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = ShR /\ type_bits t1 < 256 /\ ~(?i. v2 = IntV i /\ i < 0) /\
    ann = t1 /\ is_int_type t1 /\ is_int_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value_mem_src >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value_mem_src >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[] >>
  rename1 `value_has_type tv2 (IntV i2)` >>
  `0 <= i2` by intLib.ARITH_TAC >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256_mem_src]) >>
  `type_bits ann <= 256` by decide_tac >>
  `?v. bop_result cx ann ShR tys (IntV i) (IntV i2) es0 = INL v /\
       word_value v /\ val_to_w256 v =
         (if is_signed_type ann
          then word_asr (val_to_w256 (IntV i)) (w2n (val_to_w256 (IntV i2)))
          else word_lsr (val_to_w256 (IntV i)) (w2n (val_to_w256 (IntV i2))))` by
    (irule exprBopShiftTheory.bop_result_shr >> simp[] >>
     qexists_tac `type_bits ann` >> simp[]) >>
  irule binop_frag_val_mem_straight >>
  (conj_tac >- metis_tac[exprBopShiftTheory.straight_fresh_compile_shift]) >>
  disch_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) exprBopShiftTheory.compile_shift_run >>
  disch_then (qspecl_then [`ss`, `val_to_w256 (IntV i)`, `val_to_w256 (IntV i2)`] mp_tac) >>
  simp[]
QED

Theorem binop_frag_shift_572_mem_src[local]:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ (?i. v2 = IntV i /\ 0 <= i) /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> gvs[well_typed_binop_def]
  >- (irule binop_frag_shift_typed_mem_src >> simp[is_int_type_def, type_bits_def] >>
      metis_tac[])
  >- (irule binop_frag_shift_typed_mem_src >> simp[is_int_type_def, type_bits_def] >>
      metis_tac[]) >>
  `type_bits ann <= 256` by
    (qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value_mem_src >>
     simp[] >> metis_tac[]) >>
  Cases_on `type_bits ann = 256`
  >- (irule binop_frag_shift_typed_mem_src >> simp[] >> metis_tac[]) >>
  irule binop_frag_shr_narrow_mem_src >> simp[] >>
  `type_bits ann < 256` by decide_tac >> metis_tac[integerTheory.INT_NOT_LE]
QED


Theorem bop_result_power_mem_src[local]:
  !cx ann tys a b es u. type_to_int_bound ann = SOME u ==>
    bop_result cx ann Exp tys (IntV a) (IntV b) es =
      if b < 0 then INR (Error (RuntimeError "Exp~"))
      else if within_int_bound u (a ** Num b) then INL (IntV (a ** Num b))
      else INR (Error (RuntimeError "bounded_int_op bound"))
Proof
  rpt strip_tac >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       bounded_int_op_def] >>
  Cases_on `b < 0` >> simp[] >>
  Cases_on `within_int_bound u (a ** Num b)` >> simp[]
QED



Theorem pow_search_midpoint_mem_src[local]:
  !lo hi fuel. lo + 1 < hi /\ hi - lo <= 2 ** SUC fuel ==>
    lo <= (lo + hi) DIV 2 /\ (lo + hi) DIV 2 <= hi /\
    (lo + hi) DIV 2 - lo <= 2 ** fuel /\
    hi - (lo + hi) DIV 2 <= 2 ** fuel
Proof
  rpt gen_tac >> rewrite_tac[arithmeticTheory.EXP] >>
  SPEC_TAC (``2 ** fuel``, ``n:num``) >> gen_tac >> strip_tac >>
  qspec_then `2` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `lo + hi` mp_tac) >>
  simp[Once arithmeticTheory.ADD_COMM] >>
  strip_tac >>
  `((hi + lo) MOD 2) < 2` by simp[] >> decide_tac
QED

Theorem largest_pow_base_search_bounds_mem_src[local]:
  !fuel e L lo hi.
    lo ** e < L /\ L <= hi ** e /\ lo <= hi /\ hi-lo <= 2 ** fuel ==>
    let u = largest_pow_base_search fuel e L lo hi in
      u ** e < L /\ L <= (u+1) ** e
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[largest_pow_base_search_def] >>
      `hi <= lo + 1` by gvs[] >>
      `hi ** e <= (lo + 1) ** e` by
        simp[arithmeticTheory.EXP_EXP_LE_MONO] >> simp[]) >>
  simp[Once largest_pow_base_search_def] >>
  Cases_on `hi <= lo + 1`
  >- (`hi ** e <= (lo + 1) ** e` by
        simp[arithmeticTheory.EXP_EXP_LE_MONO] >> simp[]) >>
  `lo + 1 < hi` by decide_tac >>
  drule_all pow_search_midpoint_mem_src >> strip_tac >>
  `lo + hi = hi + lo` by decide_tac >>
  fs[] >>
  Cases_on `((hi + lo) DIV 2) ** e < L` >> simp[] >>
  first_x_assum irule >> simp[]
QED


Theorem largest_pow_base_bounds_mem_src[local]:
  !e bits signed. 0 < e ==>
    let u = largest_pow_base e bits signed in
      u ** e < 2 ** (bits - if signed then 1 else 0) /\
      2 ** (bits - if signed then 1 else 0) <= (u+1) ** e
Proof
  rpt gen_tac >> strip_tac >>
  simp[largest_pow_base_def] >>
  irule (SIMP_RULE std_ss [LET_THM] largest_pow_base_search_bounds_mem_src) >>
  simp[arithmeticTheory.ZERO_EXP] >>
  mp_tac (Q.SPECL [`e`, `1`, `2 ** (bits - if signed then 1 else 0)`]
    arithmeticTheory.EXP_BASE_LEQ_MONO_IMP) >> simp[]
QED

Theorem largest_pow_base_threshold_mem_src[local]:
  !e bits signed k. 0 < e ==>
    (k <= largest_pow_base e bits signed <=>
     k ** e < 2 ** (bits - if signed then 1 else 0))
Proof
  rpt strip_tac >> drule largest_pow_base_bounds_mem_src >>
  disch_then (qspecl_then [`bits`, `signed`] mp_tac) >> simp[] >> strip_tac >>
  eq_tac >> strip_tac
  >- (`k ** e <= largest_pow_base e bits signed ** e` by
        simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  spose_not_then assume_tac >>
  `largest_pow_base e bits signed + 1 <= k` by decide_tac >>
  `(largest_pow_base e bits signed + 1) ** e <= k ** e` by
    simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac
QED

Theorem largest_pow_base_lt_limit_mem_src[local]:
  !e bits signed. 0 < e ==>
    largest_pow_base e bits signed < 2 ** (bits - if signed then 1 else 0)
Proof
  rpt strip_tac >>
  drule largest_pow_base_threshold_mem_src >>
  disch_then (qspecl_then [`bits`, `signed`,
    `2 ** (bits - if signed then 1 else 0)`] mp_tac) >>
  `2 ** (bits - if signed then 1 else 0) <=
   (2 ** (bits - if signed then 1 else 0)) ** e` by
    (mp_tac (Q.SPECL [`e`, `1`, `2 ** (bits - if signed then 1 else 0)`]
       arithmeticTheory.EXP_BASE_LEQ_MONO_IMP) >> simp[]) >> decide_tac
QED



Theorem square_power_two_even_mem_src[local]:
  !k b:num. b * b = 2 ** k ==> EVEN k
Proof
  completeInduct_on `k` >> rpt strip_tac >>
  Cases_on `k` >- simp[] >>
  `EVEN (b * b)` by
    (asm_rewrite_tac[] >> simp[arithmeticTheory.EVEN_EXP_IFF]) >>
  `EVEN b` by fs[arithmeticTheory.EVEN_MULT] >>
  qpat_x_assum `EVEN b` (mp_tac o REWRITE_RULE [arithmeticTheory.EVEN_EXISTS]) >>
  disch_then (qx_choose_then `c` assume_tac) >>
  Cases_on `n`
  >- (gvs[arithmeticTheory.EXP, GSYM arithmeticTheory.EXP_2,
          arithmeticTheory.EXP_BASE_MULT] >> decide_tac) >>
  rename1 `EVEN (SUC (SUC j))` >>
  `c * c = 2 ** j` by
    (gvs[arithmeticTheory.EXP, GSYM arithmeticTheory.EXP_2,
         arithmeticTheory.EXP_BASE_MULT] >> decide_tac) >>
  `EVEN j` by (first_x_assum irule >> simp[] >> qexists_tac `c` >> pure_asm_rewrite_tac[arithmeticTheory.EXP_2] >> REFL_TAC) >>
  simp[arithmeticTheory.EVEN]
QED

Theorem pow_two_odd_exponent_mem_src[local]:
  !a e k:num. 0 < a /\ a ** e = 2 ** k /\ ODD k ==> ODD e
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `EVEN e` by fs[arithmeticTheory.ODD_EVEN] >>
  qpat_x_assum `EVEN e`
    (mp_tac o REWRITE_RULE [arithmeticTheory.EVEN_EXISTS]) >>
  disch_then (qx_choose_then `n` assume_tac) >>
  `a ** n * a ** n = 2 ** k` by
    (`2 * n = n + n` by decide_tac >>
     qpat_x_assum `a ** e = _` mp_tac >>
     pure_asm_rewrite_tac[arithmeticTheory.EXP_ADD] >>
     disch_then ACCEPT_TAC) >>
  drule square_power_two_even_mem_src >>
  fs[arithmeticTheory.ODD_EVEN]
QED

Theorem byte_width_odd_predecessor_mem_src[local]:
  !bits:num. 0 < bits /\ bits MOD 8 = 0 ==> ODD (bits - 1)
Proof
  rpt strip_tac >>
  qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `bits` assume_tac) >>
  `EVEN bits` by
    (rewrite_tac[arithmeticTheory.EVEN_EXISTS] >>
     qexists_tac `4 * (bits DIV 8)` >> decide_tac) >>
  Cases_on `bits` >> fs[arithmeticTheory.EVEN, arithmeticTheory.ODD_EVEN]
QED


Theorem unsigned_literal_exponent_guard_mem_src[local]:
  !a:int e bits. 1 < e /\ 0 < bits /\ bits <= 256 /\ 0 <= a ==>
    (Num a <= largest_pow_base e bits F <=>
     within_int_bound (Unsigned bits) (a ** e))
Proof
  rpt strip_tac >>
  `0 < e` by decide_tac >>
  drule largest_pow_base_threshold_mem_src >>
  disch_then (qspecl_then [`bits`, `F`, `Num a`] mp_tac) >>
  `a = &(Num a)` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  simp[within_int_bound_def, GSYM integerTheory.INT_POW]
QED

Theorem literal_exponent_typed_shortcut_mem_src[local]:
  !bits s a e. 0 < bits /\ bits MOD 8 = 0 /\
    within_int_bound (if s then Signed bits else Unsigned bits) a /\
    (e = 0 \/ e = 1) ==>
    within_int_bound (if s then Signed bits else Unsigned bits) (a ** e)
Proof
  rpt gen_tac >>
  `a ** 1 = a /\ a ** 0 = 1` by
    (Cases_on `a` >> simp[integerTheory.INT_POW_NEG]) >>
  rpt strip_tac >> gvs[] >> Cases_on `s` >>
  simp[within_int_bound_def] >>
  `8 <= bits` by
    (qspec_then `8` mp_tac arithmeticTheory.DIVISION >> simp[] >>
     disch_then (qspec_then `bits` mp_tac) >>
     Cases_on `bits DIV 8` >> simp[] >> decide_tac) >>
  gvs[within_int_bound_def, arithmeticTheory.ONE_LT_EXP]
QED

Theorem unsigned_power_upper_word_mem_src[local]:
  !e bits. 1 < e /\ 0 < bits /\ bits <= 256 ==>
    w2n (n2w (largest_pow_base e bits F) : bytes32) =
      largest_pow_base e bits F
Proof
  rpt strip_tac >>
  `0 < e` by decide_tac >>
  drule largest_pow_base_lt_limit_mem_src >>
  disch_then (qspecl_then [`bits`, `F`] mp_tac) >> simp[] >> strip_tac >>
  `2 ** bits <= 2 ** 256` by simp[arithmeticTheory.EXP_EXP_LE_MONO] >>
  `largest_pow_base e bits F < 2 ** 256` by decide_tac >>
  fs[wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem signed_literal_exponent_guard_mem_src[local]:
  !a:int e bits. 1 < e /\ 0 < bits /\ bits <= 256 /\ bits MOD 8 = 0 ==>
    (let u = largest_pow_base e bits T in
     let l = if (u+1)**e = 2**(bits-1) then -&(u+1) else -&u in
       (l <= a /\ a <= &u <=> within_int_bound (Signed bits) (a ** e)))
Proof
  rpt strip_tac >> simp_tac bool_ss [LET_THM] >>
  `0 < e` by decide_tac >>
  qabbrev_tac `u = largest_pow_base e bits T` >>
  Cases_on `0 <= a`
  >- (`a = &(Num a)` by simp[] >> pop_assum SUBST_ALL_TAC >>
      qspec_then `e` mp_tac largest_pow_base_threshold_mem_src >>
      simp[] >> disch_then (qspecl_then [`bits`, `T`, `Num a`] mp_tac) >>
      simp[within_int_bound_def, GSYM integerTheory.INT_POW, Abbr `u`] >>
      strip_tac >> IF_CASES_TAC >> simp[] >> intLib.ARITH_TAC) >>
  `a < 0` by intLib.ARITH_TAC >>
  `a = -&(Num (-a))` by (simp[] >> intLib.ARITH_TAC) >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `m = Num (-a)` >>
  `0 < m` by (fs[Abbr `m`] >> intLib.ARITH_TAC) >>
  `(-&m:int) <= &u` by intLib.ARITH_TAC >>
  `0 < m ** e` by simp[] >>
  simp[within_int_bound_def, vyperMiscTheory.int_exp_num] >>
  `ODD (bits - 1)` by metis_tac[byte_width_odd_predecessor_mem_src] >>
  `((u + 1) ** e = 2 ** (bits - 1)) ==> ODD e` by
    (strip_tac >> irule pow_two_odd_exponent_mem_src >>
     qexistsl_tac [`u + 1`, `bits - 1`] >> simp[]) >>
  `m <= u <=> m ** e < 2 ** (bits - 1)` by
    (simp[Abbr `u`, largest_pow_base_threshold_mem_src]) >>
  Cases_on `EVEN e`
  >- (`~((u + 1) ** e = 2 ** (bits - 1))` by
        metis_tac[arithmeticTheory.ODD_EVEN] >> simp[]) >>
  simp[] >> IF_CASES_TAC
  >- (qpat_x_assum `(u + 1) ** e = _`
        (fn th => once_rewrite_tac[GSYM th]) >>
      simp[arithmeticTheory.EXP_EXP_LE_MONO]) >>
  `2 ** (bits - 1) <= (u + 1) ** e` by
    (qspec_then `e` mp_tac largest_pow_base_bounds_mem_src >> simp[] >>
     disch_then (qspecl_then [`bits`, `T`] mp_tac) >> simp[Abbr `u`]) >>
  Cases_on `m <= u` >- (simp[] >> decide_tac) >>
  `u + 1 <= m` by decide_tac >>
  `(u + 1) ** e <= m ** e` by simp[arithmeticTheory.EXP_EXP_LE_MONO] >>
  simp[] >> decide_tac
QED

Theorem signed_power_upper_word_mem_src[local]:
  !e bits. 1 < e /\ 0 < bits /\ bits <= 256 /\ bits MOD 8 = 0 ==>
    w2i (n2w (largest_pow_base e bits T) : bytes32) =
      &(largest_pow_base e bits T)
Proof
  rpt strip_tac >> `0 < e` by decide_tac >>
  drule largest_pow_base_lt_limit_mem_src >>
  disch_then (qspecl_then [`bits`, `T`] mp_tac) >> simp[] >> strip_tac >>
  `2 ** (bits - 1) <= 2 ** 255` by
    (simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  `largest_pow_base e bits T < 2 ** 255` by decide_tac >>
  irule integer_wordTheory.w2i_n2w_pos >> fs[wordsTheory.INT_MIN_def]
QED

Theorem signed_power_lower_word_mem_src[local]:
  !e bits. 1 < e /\ 0 < bits /\ bits <= 256 /\ bits MOD 8 = 0 ==>
    (let u = largest_pow_base e bits T in
     let l = if (u+1)**e = 2**(bits-1) then -&(u+1) else -&u in
       w2i (i2w l : bytes32) = l)
Proof
  rpt strip_tac >> `0 < e` by decide_tac >>
  drule largest_pow_base_lt_limit_mem_src >>
  disch_then (qspecl_then [`bits`, `T`] mp_tac) >> simp[] >> strip_tac >>
  `2 ** (bits - 1) <= 2 ** 255` by
    (simp[arithmeticTheory.EXP_EXP_LE_MONO] >> decide_tac) >>
  `largest_pow_base e bits T < 2 ** 255` by decide_tac >>
  simp_tac bool_ss [LET_THM] >> IF_CASES_TAC >>
  irule integer_wordTheory.w2i_i2w >>
  fs[wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def] >> intLib.ARITH_TAC
QED


Theorem integer_power_word_mem_src[local]:
  !a:int n. (n2w (w2n (i2w a : bytes32) ** n) : bytes32) = i2w (a ** n)
Proof
  gen_tac >> Induct >>
  simp[arithmeticTheory.EXP, integerTheory.INT_POW,
       GSYM wordsTheory.word_mul_n2w, integer_wordTheory.word_i2w_mul] >>
  EVAL_TAC
QED

Theorem literal_exponent_value_word_mem_src[local]:
  !bits signed b. 0 < bits /\ bits <= 256 /\
    within_int_bound (if signed then Signed bits else Unsigned bits) b /\ 0 <= b ==>
    w2n (i2w b : bytes32) = Num b
Proof
  rpt strip_tac >>
  `~(b < 0)` by intLib.ARITH_TAC >>
  `Num b < 2 ** bits` by
    (Cases_on `signed` >> gvs[within_int_bound_def] >>
     `2 ** (bits - 1) <= 2 ** bits` by simp[arithmeticTheory.EXP_EXP_LE_MONO] >>
     decide_tac) >>
  `2 ** bits <= 2 ** 256` by simp[arithmeticTheory.EXP_EXP_LE_MONO] >>
  `Num b < 2 ** 256` by decide_tac >>
  `b = &(Num b)` by simp[] >> pop_assum SUBST_ALL_TAC >>
  fs[integer_wordTheory.i2w_pos, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem literal_exponent_exp_word_mem_src[local]:
  !bits signed a b. 0 < bits /\ bits <= 256 /\
    within_int_bound (if signed then Signed bits else Unsigned bits) b /\ 0 <= b ==>
    word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)
Proof
  rpt strip_tac >>
  drule_all literal_exponent_value_word_mem_src >> strip_tac >>
  simp[wordsTheory.word_exp_def, integer_power_word_mem_src]
QED


Theorem emit_op_exp_mem_src[local]:
  !x y vx vy sa op sb ss.
    emit_op Exp [x;y] sa = (op,sb) /\
    eval_operand x ss = SOME vx /\ eval_operand y ss = SOME vy /\
    fresh_vars_wrt sa ss ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
      eval_operand op ss' = SOME (word_exp vx vy) /\
      same_blocks sa sb /\ fresh_vars_wrt sb ss' /\
      (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
      (!a. a < LENGTH ss.vs_memory ==> EL a ss'.vs_memory = EL a ss.vs_memory) /\
      LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  rw[] >> irule emit_op_pure2_correct >> gvs[] >>
  goal_assum $ drule_at (Pat `emit_op`) >> gvs[] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def, mk_inst_def]
QED

Theorem assert_exp_after_prefix_mem_src[local]:
  !sa sc sd sb ss sg ok x y vx vy op P.
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    run_inst_seq (emitted_insts sa sc) ss = OK sg /\
    fresh_vars_wrt sc sg /\ eval_operand ok sg = SOME (bool_to_word P) /\
    eval_operand x sg = SOME vx /\ eval_operand y sg = SOME vy /\
    emit_void ASSERT [ok] sc = ((),sd) /\
    emit_op Exp [x;y] sd = (op,sb) ==>
    (P ==> ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                  eval_operand op ss' = SOME (word_exp vx vy)) /\
    (~P ==> ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `P` >> fs[]
  >- (`1w <> (0w:bytes32)` by simp[wordsTheory.WORD_EQ, wordsTheory.dimword_def] >>
      drule_all emit_void_ASSERT_ok_full >> strip_tac >> gvs[] >>
      drule_all emit_op_exp_mem_src >> strip_tac >>
      imp_res_tac emit_void_extends >> imp_res_tac emit_op_extends >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      qpat_x_assum `run_inst_seq (emitted_insts sc sd) _ = _` kall_tac >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      metis_tac[]) >>
  drule_all emit_void_ASSERT_revert >> strip_tac >>
  imp_res_tac emit_void_extends >> imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sc) _ = _` kall_tac >>
  `!s. run_inst_seq (emitted_insts sa sd) ss <> OK s` by simp[] >>
  drule_all run_inst_seq_chain_err >> strip_tac >>
  metis_tac[]
QED

Theorem power_bool_word_guard_mem_src[local]:
  (!P. bool_to_word (bool_to_word P = 0w) = bool_to_word (~P)) /\
  (!P Q. bool_to_word P && bool_to_word Q = bool_to_word (P /\ Q))
Proof
  conj_tac
  >- (gen_tac >> Cases_on `P` >>
      simp[bool_to_word_def, wordsTheory.WORD_EQ, wordsTheory.dimword_def]) >>
  rpt gen_tac >> Cases_on `P` >> Cases_on `Q` >>
  simp[bool_to_word_def]
QED

Theorem signed_power_guard_prefix_mem_src[local]:
  !sa s1 s2 s3 s4 sc ss x y lo hi below ge above le ok vx vy.
    emit_op SLT [x;Lit lo] sa = (below,s1) /\
    emit_op ISZERO [below] s1 = (ge,s2) /\
    emit_op SGT [x;Lit hi] s2 = (above,s3) /\
    emit_op ISZERO [above] s3 = (le,s4) /\
    emit_op AND [ge;le] s4 = (ok,sc) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME vx /\
    eval_operand y ss = SOME vy ==>
    ?sg. sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
      run_inst_seq (emitted_insts sa sc) ss = OK sg /\
      fresh_vars_wrt sc sg /\ eval_operand x sg = SOME vx /\
      eval_operand y sg = SOME vy /\
      eval_operand ok sg = SOME
        (bool_to_word (bool_to_word (vx < lo) = 0w) &&
         bool_to_word (bool_to_word (vx > hi) = 0w))
Proof
  rpt gen_tac >> strip_tac >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_ISZERO_correct_mem >>
  chain_step (elim_lit 2 emit_op_SGT_correct) >>
  chain_step emit_op_ISZERO_correct_mem >>
  chain_step emit_op_AND_correct >>
  forward_all_evals >>
  rename1 `eval_operand ok sg = SOME (_ && _)` >>
  qexists_tac `sg` >> simp[]
QED

Theorem unsigned_power_guard_prefix_mem_src[local]:
  !sa s1 sc ss x y hi above ok vx vy.
    emit_op GT [x;Lit hi] sa = (above,s1) /\
    emit_op ISZERO [above] s1 = (ok,sc) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME vx /\
    eval_operand y ss = SOME vy ==>
    ?sg. sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
      run_inst_seq (emitted_insts sa sc) ss = OK sg /\
      fresh_vars_wrt sc sg /\ eval_operand x sg = SOME vx /\
      eval_operand y sg = SOME vy /\
      eval_operand ok sg = SOME (bool_to_word (bool_to_word (w2n vx > w2n hi) = 0w))
Proof
  rpt gen_tac >> strip_tac >>
  chain_step (elim_lit 2 emit_op_GT_correct) >>
  chain_step emit_op_ISZERO_correct_mem >>
  forward_all_evals >>
  rename1 `eval_operand ok sg = SOME (bool_to_word _)` >>
  qexists_tac `sg` >> simp[]
QED

Theorem compile_safe_pow_exponent_run_mem_src:
  !x y ty a b sa op sb ss.
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) a /\
    within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                      else Unsigned (type_bits ty)) b /\ 0 <= b /\
    compile_safe_pow x y ty NONE (SOME b) sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w a) /\
    eval_operand y ss = SOME (i2w b) ==>
    (0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (a ** Num b))) /\
    (~(0 <= b /\ within_int_bound
       (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
       (a ** Num b)) ==>
     ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `Num b = 0 \/ Num b = 1`
  >- suspend "shortcut"
  >> Cases_on `is_signed_type ty`
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume compile_safe_pow_exponent_run_mem_src[shortcut]:
  `within_int_bound
     (if is_signed_type ty then Signed (type_bits ty) else Unsigned (type_bits ty))
     (a ** Num b)` by metis_tac[literal_exponent_typed_shortcut_mem_src] >>
  `word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)` by
    metis_tac[literal_exponent_exp_word_mem_src] >>
  simp[] >>
  fs[compile_safe_pow_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >>
  `eval_operand (Lit 1w) ss = SOME (1w:bytes32)` by simp[eval_operand_def] >>
  `1w <> (0w:bytes32)` by simp[wordsTheory.WORD_EQ, wordsTheory.dimword_def] >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >> gvs[] >>
  chain_step emit_op_exp_mem_src >>
  imp_res_tac emit_void_extends >> imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  metis_tac[]
QED

Resume compile_safe_pow_exponent_run_mem_src[signed]:
  `1 < Num b` by decide_tac >>
  `word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)` by
    metis_tac[literal_exponent_exp_word_mem_src] >>
  `w2i (i2w a : bytes32) = a` by
    (irule vyperArithTheory.w2i_i2w_within_signed >>
     qexists_tac `type_bits ty` >> fs[]) >>
  qspecl_then [`Num b`, `type_bits ty`] mp_tac signed_power_upper_word_mem_src >>
  impl_tac >- simp[] >> disch_tac >>
  qspecl_then [`Num b`, `type_bits ty`] mp_tac signed_power_lower_word_mem_src >>
  impl_tac >- simp[] >> simp_tac bool_ss [LET_THM] >> disch_tac >>
  qspecl_then [`a`, `Num b`, `type_bits ty`] mp_tac signed_literal_exponent_guard_mem_src >>
  impl_tac >- simp[] >> simp_tac bool_ss [LET_THM] >> disch_tac >>
  gvs[compile_safe_pow_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all signed_power_guard_prefix_mem_src >> strip_tac >>
  qpat_x_assum `eval_operand ok sg = SOME _` mp_tac >>
  simp[power_bool_word_guard_mem_src, integer_wordTheory.WORD_LTi,
       integer_wordTheory.WORD_GTi, integerTheory.INT_NOT_LT,
       integerTheory.int_gt] >> disch_tac >>
  drule_all assert_exp_after_prefix_mem_src >>
  simp[]
QED
Resume compile_safe_pow_exponent_run_mem_src[unsigned]:
  `1 < Num b` by decide_tac >>
  `word_exp (i2w a : bytes32) (i2w b) = i2w (a ** Num b)` by
    metis_tac[literal_exponent_exp_word_mem_src] >>
  `0 <= a` by fs[within_int_bound_def] >>
  `w2n (i2w a : bytes32) = Num a` by
    (irule literal_exponent_value_word_mem_src >>
     simp[] >> qexistsl_tac [`type_bits ty`, `F`] >> fs[]) >>
  qspecl_then [`Num b`, `type_bits ty`] mp_tac unsigned_power_upper_word_mem_src >>
  impl_tac >- simp[] >> disch_tac >>
  qspecl_then [`a`, `Num b`, `type_bits ty`] mp_tac unsigned_literal_exponent_guard_mem_src >>
  impl_tac >- simp[] >> disch_tac >>
  gvs[compile_safe_pow_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all unsigned_power_guard_prefix_mem_src >> strip_tac >>
  qpat_x_assum `eval_operand ok sg = SOME _` mp_tac >>
  simp[power_bool_word_guard_mem_src] >> disch_tac >>
  drule_all assert_exp_after_prefix_mem_src >>
  simp[arithmeticTheory.GREATER_DEF, arithmeticTheory.NOT_LESS] >>
  metis_tac[arithmeticTheory.NOT_LESS_EQUAL]
QED
Finalise compile_safe_pow_exponent_run_mem_src[local]


Theorem straight_fresh_pow_exponent_mem_src[local]:
  !x y ty b. straight_fresh (compile_safe_pow x y ty NONE (SOME b))
Proof
  rw[compile_safe_pow_def, LET_THM] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
              irule straight_fresh_ignore_bind >> conj_tac,
              gen_tac >> BETA_TAC,
              irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
              irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC])
QED

Theorem binop_frag_pow_exponent_mem_src[local]:
  !ctx func cenv cx ann t1 t2 b tys v1 es0 tenv tv1 tv2.
    well_typed_binop ann Exp t1 t2 /\ 0 <= b /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 (IntV b) ==>
    binop_frag_val_mem ctx func cenv cx Exp t1 ann NONE (SOME b)
      tys v1 (IntV b) es0
Proof
  rpt gen_tac >> disch_tac >>
  `is_int_type t1 /\ is_int_type t2` by gvs[well_typed_binop_def] >>
  qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac int_type_value_mem_src >>
  qspecl_then [`tenv`, `t2`, `tv2`, `IntV b`] mp_tac int_type_value_mem_src >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[well_typed_binop_def] >>
  rename1 `binop_frag_val_mem _ _ _ _ Exp _ _ _ _ _ (IntV a) _ _` >>
  `type_bits ann MOD 8 = 0` by metis_tac[int_type_byte_width_mem_src] >>
  drule_then assume_tac bop_result_power_mem_src >>
  irule binop_frag_val_mem_straight >> conj_tac
  >- simp[compile_binop_def, straight_fresh_pow_exponent_mem_src] >>
  `~(b < 0)` by intLib.ARITH_TAC >>
  Cases_on `within_int_bound
    (if is_signed_type ann then Signed (type_bits ann) else Unsigned (type_bits ann))
    (a ** Num b)`
  >- (simp[word_value_def] >> strip_tac >> rpt gen_tac >>
      simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`)
        compile_safe_pow_exponent_run_mem_src >> simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >> rpt gen_tac >>
  simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
  drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`)
    compile_safe_pow_exponent_run_mem_src >> simp[] >> metis_tac[]
QED


Theorem binop_frag_augassign_typed_mem_src[local]:
  !ctx func cenv cx bop ty t2 el tys v1 v2 es0 tenv tv1 tv2.
    well_typed_binop ty bop ty t2 /\ type_bits ty MOD 8 = 0 /\
    (bop = Exp ==> (?n. el = SOME n /\ 0 <= n) /\
      (!n. el = SOME n ==> v2 = IntV n)) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    word_value_type ty /\ word_value_type t2 /\
    evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty NONE el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bop = ExpMod` >- gvs[well_typed_binop_def] >>
  Cases_on `bop = Exp`
  >- (gvs[] >> irule binop_frag_pow_exponent_mem_src >> metis_tac[]) >>
  Cases_on `MEM bop [Add; Sub; Mul; Div; Mod]`
  >- (`t2 = ty` by
        (Cases_on `bop` >> gvs[well_typed_binop_def]) >>
      qpat_x_assum `t2 = ty` SUBST_ALL_TAC >>
      `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
      Cases_on `ty = BaseT DecimalT`
      >- (gvs[] >> irule binop_frag_decimal_arith_mem_src >> simp[] >>
          qexistsl_tac [`tenv`, `tv1`] >> simp[]) >>
      `is_int_type ty` by (Cases_on `bop` >> gvs[well_typed_binop_def]) >>
      irule binop_frag_int_arith_mem_src >> simp[] >>
      qexistsl_tac [`tenv`, `tv1`] >> simp[]) >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]`
  >- (`t2 = ty /\ is_int_type ty` by
        (Cases_on `bop` >> gvs[well_typed_binop_def]) >>
      gvs[] >> irule binop_frag_unsafe_typed_mem_src >> simp[] >>
      qexistsl_tac [`tenv`, `tv1`] >> simp[]) >>
  Cases_on `bop = ShL \/ bop = ShR`
  >- (irule binop_frag_shift_572_mem_src >> metis_tac[]) >>
  Cases_on `bop = In \/ bop = NotIn`
  >- gvs[well_typed_binop_def, word_value_type_def] >>
  `t2 = ty` by (Cases_on `bop` >> gvs[well_typed_binop_def]) >> gvs[] >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (irule binop_frag_bitwise_typed_mem_src >> metis_tac[]) >>
  irule binop_frag_compare_typed_mem_src >>
  `MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max]` by
    (Cases_on `bop` >> gvs[]) >> metis_tac[]
QED

Theorem expr_int_literal_value_mem_src[local]:
  !e. expr_int_literal e = int_literal_value e
Proof
  Cases >> simp[expr_int_literal_def, int_literal_value_def] >>
  rename1 `Literal ty lit` >> Cases_on `lit` >>
  simp[expr_int_literal_def, int_literal_value_def]
QED

Resume compile_augassign_attr_local_mem[typed_dispatch]:
  irule binop_frag_augassign_typed_mem_src >> simp[] >> conj_tac
  >- (strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value_mem_src] >>
      Cases_on `expr_int_literal e` >> gvs[]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`expr_type e`, `get_tenv cx`, `ftv`, `etv`] >> simp[]
QED

Finalise compile_augassign_attr_local_mem[local]

Theorem body_augassign_attr_local_mem:
  !cx ty id fld bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supportedExprTraverseTheory.supported_expr_exists_def,
         int_calls_stmt_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  drule augassign_attr_typing_mem_src >> strip_tac >>
  `?sid. FLOOKUP env.var_types id = SOME (StructT sid) /\
         attribute_type env.type_defs (StructT sid) fld = SOME ty` by
    (gvs[well_typed_target_def,
         vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget, AllCaseEqs()] >>
     Cases_on `tgt_ty` >> gvs[attribute_type_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                   (nsid_to_string sid)) fld = SOME (ty,fsz)` by
    metis_tac[attribute_type_struct_field_mem_src, expr_sim_inv_def] >>
  drule_all augassign_attr_conditional_ih_mem_src >> strip_tac >>
  irule compile_augassign_attr_local_mem >> simp[] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `body_expr_mem_ok cx e`
        (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
      disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`,
        `es with gas_obs := gs`] mp_tac) >> simp[body_inv_def]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`env`, `fsz`, `sid`] >> simp[]
QED
