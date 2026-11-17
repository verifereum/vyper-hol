(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a field of a local struct (S1's
   body_augassign_attr_local): MLOAD at the field's address, the operator,
   MSTORE there. *)
Theory bodyMemAugAssignAttrLocal
Ancestors
  targetPlaceSim
  supportedExprTraverse allocLimitsProps
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
  gasStorage vyperStorageTrace vyperStorageFootprint
  allocaFootprint fragGasSeqMem stmtSimProps localPtrsProps
  exprLoweringProps emitHelper emitHelperProps loweringSlice exprSimOps
  venomExecSemantics venomInst venomState
  fragExec fragExecMem allocLimits valueEncoding valueEncodingDefs freshWrites
  vyperLookup vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperAST
Libs
  monadsyntax emitTacticsLib

(* stmt_expr_body_pre's const-name premise, discharged from body_inv. *)
val irule_body_pre = bodyConstNameLib.irule_body_pre;

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

Theorem augassign_attr_rhs_normal_mem_src:
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
  strip_tac >> drule_all stmtSimAugAssignTheory.gas_marked_exec_zero_prefix >>
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
  drule_all stmtSimAugAssignTheory.gas_marked_exec_zero_prefix >> strip_tac >>
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


Theorem stmt_state_rel_gas_obs_mem_src[local]:
  stmt_state_rel H ctx func cenv cx (es with gas_obs := gs) s =
  stmt_state_rel H ctx func cenv cx es s
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
  drule_all expr_sim_inv_local >> strip_tac >>
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
    metis_tac[expr_sim_inv_local] >>
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
  (bop = ShL \/ bop = ShR ==> augassign_shift_amount_ok ty e)
Proof
  simp[type_stmt_def, AllCaseEqs()] >>
  metis_tac[stmtSimAugAssignTheory.augassign_operand_ok_operands]
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
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand op t = SOME w /\ stmt_state_rel H ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. op = Var out /\ not_fresh_at sb out) /\
    t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
    t.vs_requests = s0.vs_requests /\ t.vs_call_ctx = s0.vs_call_ctx
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
  `stmt_state_rel H ctx func cenv cx es (update_var out w s0)` by
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
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand dst t = SOME (w + n2w off) /\ stmt_state_rel H ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    local_ptrs_reserved cenv sn /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    sa.cs_next_var <= sn.cs_next_var /\
    (?out. dst = Var out /\ not_fresh_at sn out) /\
    t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
    t.vs_requests = s0.vs_requests /\ t.vs_call_ctx = s0.vs_call_ctx
Proof
  strip_tac >> irule augassign_field_emit_path_mem >>
  simp[] >> reverse conj_tac
  >- (irule attr_add_prefix_mem_ok >> metis_tac[]) >>
  qexistsl_tac [`[Var p; Lit (n2w off)]`, `ADD`] >>
  simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, wordsTheory.WORD_ADD_COMM]
QED

Theorem augassign_field_read_path_mem:
  emit_op MLOAD [dst] sa = (cur,sb) /\
  eval_operand dst s0 = SOME addr /\ w2n addr + 32 <= s0.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand cur t = SOME (mload (w2n addr) s0) /\
    stmt_state_rel H ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    t.vs_memory = s0.vs_memory /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. cur = Var out /\ not_fresh_at sb out) /\
    t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
    t.vs_requests = s0.vs_requests /\ t.vs_call_ctx = s0.vs_call_ctx
Proof
  strip_tac >> irule augassign_field_emit_path_mem >>
  simp[] >> reverse conj_tac
  >- (irule emit_mload_mem_ok >> metis_tac[]) >>
  qexistsl_tac [`[dst]`, `MLOAD`] >>
  simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def]
QED

Theorem augassign_field_address_bound_mem[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME wbase /\ lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ fields_layout fields fs /\
  ALOOKUP fs fld = SOME ftv /\ is_word_type ty /\
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
  `type_memory_size ftv = 32` by metis_tac[word_tv_memory_size] >>
  drule_all body_field_address_no_wrap >>
  drule_all body_field_region_frontier >> simp[]
QED

Theorem augassign_attr_local_load_mem[local]:
  emit_op ADD [Var p; Lit (n2w (struct_field_offset fields fld))] sa = (dst,sn) /\
  emit_op MLOAD [dst] sn = (cur,sb) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s0 = SOME w0 /\ lookup_scopes id es.scopes = SOME entry /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ftv /\
  value_has_type ftv fv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  alloca_history func s0 ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand dst t = SOME (w0 + n2w (struct_field_offset fields fld)) /\
    eval_operand cur t = SOME (typed_val_to_w256 ftv fv) /\
    stmt_state_rel H ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. cur = Var out /\ not_fresh_at sb out) /\
    (?dv. dst = Var dv /\ not_fresh_at sb dv) /\
    t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
    t.vs_requests = s0.vs_requests /\ t.vs_call_ctx = s0.vs_call_ctx
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
    (irule stmt_state_rel_field_word >> metis_tac[]) >>
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
Theorem assign_attr_local_store_layout_path_mem:
  emit_void MSTORE [dst; op] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  lookup_var p s = SOME wbase /\
  eval_operand dst s = SOME (wbase + n2w (struct_field_offset fields fld)) /\
  eval_operand op s = SOME (typed_val_to_w256 ftv v) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?t. stmt_state_rel H ctx func cenv cx
        (es with scopes := pre ++
          (env |+ (id, entry with
            <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t /\ gas_marked_path T ctx func s 0 (OK t) /\
      t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
      t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `type_memory_size ftv = 32` by fs[stmtSimDeclStoreTheory.store_lays_out_def] >>
  `w2n wbase + type_memory_size_fields fs <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> simp[type_memory_size_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `w2n (wbase + n2w (struct_field_offset fields fld)) =
     w2n wbase + struct_field_offset fields fld` by
    (drule_all body_field_address_no_wrap >> simp[]) >>
  `w2n (wbase + n2w (struct_field_offset fields fld)) + 32 <= s.vs_alloca_next` by
    (drule_all body_field_region_frontier >> simp[]) >>
  drule_all stmt_state_rel_write_field >> strip_tac >>
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
  `stmt_state_rel H ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) u` by
    simp[Abbr `u`] >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  simp[Abbr `u`, lookup_var_def, mstore_def]
QED

Theorem assign_attr_local_word_store_path_mem:
  emit_void MSTORE [dst; op] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  lookup_var p s = SOME wbase /\
  eval_operand dst s = SOME (wbase + n2w (struct_field_offset fields fld)) /\
  eval_operand op s = SOME (typed_val_to_w256 ftv v) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ word_value_type ty /\
  evaluate_type (get_tenv cx) ty = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?t. stmt_state_rel H ctx func cenv cx
        (es with scopes := pre ++
          (env |+ (id, entry with
            <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t /\ gas_marked_path T ctx func s 0 (OK t) /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_requests = s.vs_requests /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> irule assign_attr_local_store_layout_path_mem >>
  simp[] >> metis_tac[word_value_type_word]
QED

Theorem stmt_state_rel_scopes_gas_obs_mem[local]:
  stmt_state_rel H ctx func cenv cx (es with <|scopes := sc; gas_obs := gs|>) s =
  stmt_state_rel H ctx func cenv cx (es with scopes := sc) s
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

Theorem compile_augassign_attr_local_mem_typed:
  (!gs. expr_sim_mem ctx func cenv cx ty e (es with gas_obs := gs)) /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (ty,fsz) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==>
    shift_amount_ok e \/ augassign_shift_amount_ok ty e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty0 (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all augassign_attr_source_fields_mem_src >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_is_word] >>
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
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `?w0. lookup_var p s0 = SOME w0` by metis_tac[local_word_pointer_live] >>
  drule_all augassign_attr_local_load_mem >> strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es t /\
       storage_well_formed_on cx es (FST H)` by
    (gen_tac >> strip_tac >> conj_tac
     >- metis_tac[exprLoweringPropsTheory.stmt_state_rel_fields_transport]
     >- metis_tac[]) >>
  `!H. valid_horizon cx st0 H (es with gas_obs := []).storage_trace ==>
       stmt_state_rel H ctx func cenv cx (es with gas_obs := []) t /\
       storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by fs[] >>
     `stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     `(es with gas_obs := []).accounts = es.accounts /\
      (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
     conj_tac >- simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (simp[] >> irule augassign_attr_rhs_admissible_mem_src >> metis_tac[]) >>
  `!marks.
     gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
       (es with gas_obs := []) t marks ==>
     gas_bad_storage_at cx st0
       (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
       es s0 marks` by
    (rpt strip_tac >>
     `gas_explicit marks s0.vs_gas_readings =
      gas_explicit marks t.vs_gas_readings` by
       (drule gas_marked_path_ok_suffix >> simp[]) >>
     `gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
        es s0 marks` by fs[gasStorageTheory.gas_bad_storage_at_def] >>
     irule stmtSimAugAssignAttrTheory.augassign_attr_rhs_bad_storage >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qpat_x_assum `!gs. expr_sim_mem _ _ _ _ _ _ _`
    (qspec_then `[]` (mp_tac o REWRITE_RULE [expr_sim_mem_def])) >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `rhs`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> first_x_assum irule >> simp[])
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_attr_rhs_exempt_mem_src >>
  conj_tac >- metis_tac[] >>
  qexists_tac `t` >> simp[] >>
  simp[gas_marked_exec_def, gas_explicit_def] >>
  gen_tac >>
  irule (cj 1 augassign_attr_place_reads_mem_src) >> simp[] >> metis_tac[]
QED

Resume compile_augassign_attr_local_mem_typed[rhs_summary]:
  qexists_tac `marks` >>
  Cases_on `gas_bad_storage_at cx st0 (bind (eval_expr cx e) (read_result cx))
              (es with gas_obs := []) t marks`
  >- (disj1_tac >> first_x_assum irule >> simp[]) >>
  disj2_tac >> disj1_tac >>
  qpat_x_assum `gasSummary$gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
  `storage_trace_domain cx st0 es_end.storage_trace` by
    (CCONTR_TAC >>
     metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
  `?H1. valid_horizon cx st0 H1 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  simp[gas_summary_at_def]
  >- suspend "rhs_normal" >>
  `expr_exit res r` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _ /\ _`
       (qspec_then `H1` mp_tac) >> simp[]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> fs[expr_exit_def]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule augassign_attr_rhs_exception_exec_mem_src >> metis_tac[]) >>
  disj2_tac >> simp[] >> rpt strip_tac
  >- (simp[stmt_exit_def] >> disj1_tac >> metis_tac[expr_exit_INR_type]) >>
  fs[exprSimDefsTheory.halt_exit_def]
QED

Resume compile_augassign_attr_local_mem_typed[rhs_normal]:
  gvs[] >> rename1 `gas_marked_exec _ _ _ _ _ _ ee (OK u)` >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H1` mp_tac) >> impl_tac >- simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `cs_extends sa sn` kall_tac >>
  qpat_x_assum `cs_extends sn s1` kall_tac >>
  qpat_x_assum `s1.cs_next_id <= s2.cs_next_id` kall_tac >>
  qpat_x_assum `s2.cs_next_id <= s3.cs_next_id` kall_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
       (INL v, ee with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_x_assum `bind (eval_expr cx e) _ _ = _` assume_tac >>
     drule_at (Pos (el 2)) vyperStorageFootprintTheory.valid_horizon_frame >>
     simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e (es with gas_obs := []) s1 s2 t
         (ee with gas_obs := []) v rhs u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H1 es.storage_trace` by metis_tac[] >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] fv v
      (ee with gas_obs := []))` by
    (irule augassign_attr_binop_admissible_mem_src >> simp[] >>
     metis_tac[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >>
  strip_tac >> gvs[] >>
  rename1 `value_has_type etv v` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==>
     (?i. v = IntV i /\ 0 <= i) \/
     (ty = BaseT (BytesT (Fixed 32)) /\
      ?bs. v = BytesV bs /\ LENGTH bs = 32))` by
    metis_tac[augassign_shift_operand] >>
  `well_formed_type (get_tenv cx) ty` by simp[well_formed_type_def] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `binop_frag_mem_post (expr_val_rel cx ty) ctx func cenv cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE)
     [ty; expr_type e] fv v
     (typed_val_to_w256 ftv fv) (typed_val_to_w256 etv v)
     (ee with gas_obs := [])` by
    suspend "typed_dispatch" >>
  suspend "operator"
QED

Resume compile_augassign_attr_local_mem_typed[operator]:
  `post_value_type cenv e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_word >> simp[]) >>
  `expr_post H1 ctx func cenv cx e (es with gas_obs := []) s1 s2 t
     (ee with gas_obs := []) v rhs u` by metis_tac[] >>
  `eval_operand rhs u = SOME (typed_val_to_w256 etv v)` by
    (irule expr_val_rel_typed >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand (Var out) u = SOME (typed_val_to_w256 ftv fv)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ not_fresh_at s2 dv /\ local_ptrs_reserved cenv s2` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_mem_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_mem_post_def]) >>
  disch_then (qspecl_then [`st0`, `s2`, `s3`, `Var out`, `rhs`, `res_op`, `u`]
    mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- metis_tac[compile_lower_value_var] >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
                      expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
        (drule_then mp_tac) >>
      simp[expr_post_def]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_attr_local_mem_typed[operator_normal]:
  gvs[] >> rename1 `expr_val_rel cx ty result res_op s` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\
       storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> strip_tac >>
     `(ee with gas_obs := []).accounts = ee.accounts /\
      (ee with gas_obs := []).tStorage = ee.tStorage` by simp[] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     conj_tac >- (qpat_x_assum `stmt_state_rel H _ _ _ _ _ s` mp_tac >> simp[]) >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `stmt_state_rel H1 ctx func cenv cx ee s` by metis_tac[] >>
  `bop_result cx ty bop [ty; expr_type e] fv v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       ftv bop fv v of INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[augassign_compare_not_bytes]) >>
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
     qexistsl_tac [`ty`, `get_tenv cx`] >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
     `lookup_var x u = SOME w` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
          (qspec_then `H1` mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
        metis_tac[]) >> metis_tac[]) >>
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
        qexistsl_tac [`s1`, `t`] >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
          (qspec_then `H1` mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
        simp[]) >>
     fs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand res_op s = SOME (typed_val_to_w256 ftv result)` by
    (irule expr_val_rel_typed >> simp[]) >>
  suspend "store"
QED

Resume compile_augassign_attr_local_mem_typed[store]:
  `!(H:(bool # bytes32 # type_value) list # num list).
       stmt_state_rel H ctx func cenv cx ee s ==>
       ?t2. stmt_state_rel H ctx func cenv cx
              (ee with scopes := pre ++
                (env1 |+ (id, cur with
                  <|value := StructV (AFUPDKEY fld (K result) vals');
                    popped := []|>)) :: rest) t2 /\
            t2.vs_accounts = s.vs_accounts /\
            t2.vs_transient = s.vs_transient /\
            t2.vs_requests = s.vs_requests /\ t2.vs_call_ctx = s.vs_call_ctx` by
    (gen_tac >> strip_tac >> drule_all assign_attr_local_store_layout_path_mem >>
     strip_tac >> metis_tac[]) >>
  `stmt_state_rel H1 ctx func cenv cx ee s` by metis_tac[] >>
  drule_all assign_attr_local_store_layout_path_mem >> strip_tac >>
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
  disj1_tac >> qexists_tac `last` >> conj_tac >- REFL_TAC >>
  qx_gen_tac `H` >> strip_tac >> suspend "post"
QED

Resume compile_augassign_attr_local_mem_typed[post]:
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
  `stmt_state_rel H ctx func cenv cx ee s /\
   storage_well_formed_on cx ee (FST H)` by metis_tac[] >>
  `?t2. stmt_state_rel H ctx func cenv cx
          (ee with scopes := pre ++
            (env1 |+ (id, cur with
              <|value := StructV (AFUPDKEY fld (K result) vals');
                popped := []|>)) :: rest) t2 /\
        t2.vs_accounts = s.vs_accounts /\
        t2.vs_transient = s.vs_transient /\
        t2.vs_requests = s.vs_requests /\ t2.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> ?t2. _`
       (qspec_then `H` mp_tac) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx
     (ee with scopes := pre ++
       (env1 |+ (id, cur with
         <|value := StructV (AFUPDKEY fld (K result) vals');
           popped := []|>)) :: rest) last` by
    (match_mp_tac (Q.INST [`H0` |-> `H1`, `s` |-> `t2`]
       (INST_TYPE [alpha |-> ``:256``]
         exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
     rpt conj_tac >> metis_tac[]) >>
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
           FLOOKUP last.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME b` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ e _ _ _ _ _ _ _ _`
          (qspec_then `H1` mp_tac) >>
        impl_tac >- simp[] >>
        disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
        metis_tac[]) >> metis_tac[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x last = SOME w` by
    (rpt strip_tac >> metis_tac[]) >>
  `s0.vs_alloca_next <= last.vs_alloca_next` by decide_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `storage_well_formed_on cx
     ((ee with <|scopes := pre ++
        (env1 |+ (id, cur with
          <|value := StructV (AFUPDKEY fld (K result) vals'); popped := []|>)) ::
        rest; gas_obs := []|>) with gas_obs := []) (FST H)` by
    (`((ee with <|scopes := pre ++
        (env1 |+ (id, cur with
          <|value := StructV (AFUPDKEY fld (K result) vals'); popped := []|>)) ::
        rest; gas_obs := []|>) with gas_obs := []).accounts = ee.accounts /\
      ((ee with <|scopes := pre ++
        (env1 |+ (id, cur with
          <|value := StructV (AFUPDKEY fld (K result) vals'); popped := []|>)) ::
        rest; gas_obs := []|>) with gas_obs := []).tStorage = ee.tStorage` by
       simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  qexists_tac `cenv` >> rpt conj_tac
  >- simp[stmt_lands_def]
  >- first_assum ACCEPT_TAC
  >- simp[]
  >- simp[cenv_top_ext_refl]
  >- (qpat_x_assum `stmt_state_rel H _ _ _ _ _ last` mp_tac >>
      simp[stmt_state_rel_scopes_gas_obs_mem])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED

Resume compile_augassign_attr_local_mem_typed[operator_exit]:
  `bop_result cx ty bop [ty; expr_type e] fv v (ee with gas_obs := []) =
    case evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >>
     metis_tac[augassign_compare_not_bytes]) >>
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
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[stmt_exit_def, exprSimDefsTheory.halt_exit_def] >> rpt strip_tac >>
  metis_tac[expr_exit_INR_type]
QED


Resume compile_augassign_attr_local_mem_typed[typed_dispatch]:
  irule (Q.INST [`t2` |-> `expr_type e`, `tv1` |-> `ftv`, `tv2` |-> `etv`]
    augassign_binop_frag_typed_mem) >> simp[] >>
  strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
  Cases_on `expr_int_literal e` >> gvs[]
QED

Finalise compile_augassign_attr_local_mem_typed[local]

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
  strip_tac >> irule compile_augassign_attr_local_mem_typed >> simp[]
QED

Theorem body_augassign_attr_local_mem:
  !cx ty id fld bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_stmt_safe tops (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
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
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >> fs[body_inv_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule_body_pre stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
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
  irule compile_augassign_attr_local_mem_typed >> simp[] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `body_expr_mem_ok cx e`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
      disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`,
        `es with gas_obs := gs`] mp_tac) >> simp[body_inv_def]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`env`, `fsz`, `sid`] >> simp[]
QED
