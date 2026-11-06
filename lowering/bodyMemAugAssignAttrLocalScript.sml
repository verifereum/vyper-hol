(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a field of a local struct (S1's
   body_augassign_attr_local): MLOAD at the field's address, the operator,
   MSTORE there. *)
Theory bodyMemAugAssignAttrLocal
Ancestors
  bodyMemoryPreds stmtSimAugAssignAttr stmtSimAugAssign stmtSimAssignAttr
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasPathMem
  exprBopSimDefs exprBopSimProps exprSimSource exprSimDefs stmtSimDefs
  exprSimFieldLayout exprSimAttributeFields exprSimHypsDefs
  vyperTypeInvariants vyperTypeSystem vyperTyping vyperTypeEnv
  finite_map alist compileEnv
  bodyFieldMemoryProps bodyDeclMemoryCounted bodyDeclMemoryCore
  allocaFootprint fragGasSeqMem stmtSimProps localPtrsProps
  exprLoweringProps emitHelper emitHelperProps loweringSlice exprSimOps
  venomExecSemantics venomInst venomState
  fragExec fragExecMem allocLimits valueEncoding freshWrites
  vyperLookup vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperAST
Libs
  monadsyntax

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
    (irule bop_result_augassign_success >> goal_assum (drule_at Any) >> simp[]) >>
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
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `evaluate_type (get_tenv cx) (StructT sid) = SOME entry.type` by
    metis_tac[] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  `value_has_type entry.type entry.value` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `entry.value` >> gvs[value_has_type_def] >>
  drule_all struct_has_type_field >> strip_tac >> metis_tac[]
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
    gvs[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by simp[mk_inst_def] >>
  `gas_path_mem ctx func s0 0
     (OK (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~(update_var out w s0).vs_halted /\
   (update_var out w s0).vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `alloca_history func
     (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s0`, `sa`] >> simp[mk_inst_def]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def] >>
  gvs[update_var_def] >>
  simp[Abbr `out`, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
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
  simp[is_terminator_def, step_inst_base_def, mk_inst_def,
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
  simp[is_terminator_def, step_inst_base_def, mk_inst_def, exec_read1_def]
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
    (irule stmt_state_rel_field_word >> metis_tac[word_value_type_word]) >>
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
  `stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) u` by
    simp[Abbr `u`] >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  simp[Abbr `u`, lookup_var_def, mstore_def]
QED

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
  cheat
QED
