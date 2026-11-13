(* Join the physical RHS post to the staged local store. *)
Theory widenedAssignPtrRead
Ancestors widenedAssignPtrContinuation widenedAssignPtrRhsInput assignRelayoutCaller
  bodySim bodyPtrDefs exprSimHyps exprSimHypsDefs exprSimDefs exprSimSource
  exprLowering exprLoweringProps loweringPosts compileEnv context
  stmtSimAssignSource memoryLocalRhsProps stmtSimAugAssign
  vyperTypeExprSoundness vyperTypeSystem vyperTypeInvariants vyperTypeValues
  valueTypingMemoryProps vyperTyping vyperAST valueEncodingDefs
  loweringStateRelDefs localPtrsProps venomState venomExecSemantics ptrDiscipline
  gasSummaryComposePtr gasSummary gasOutcome fragGasPathPtr stmtFragPtr
  finite_map words
Libs monadsyntax

Theorem widened_assign_retained_read_continuation_ptr:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  e = Call ann (IntCall fid) args drv /\
  type_stmt env rty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
  stmt_exprs_ok ce (Assign (BaseTarget (NameTarget id)) e) /\
  FLOOKUP env.var_types id = SOME ty /\
  type_widens_to env.type_defs (expr_type e) ty /\
  ~is_word_type ty /\ 0 < type_memory_bytes ce ty /\
  type_memory_bytes ce ty < 2 ** 64 /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ce.ce_var_type id = SOME ty /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
    ty (lowered_value_type ce e) bytes sb = ((),sf) /\
  fn_has_code sb sf fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sb /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sb x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sb x) /\
  ~ctx_has_dalloca ctx /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INL v) ee G tn (OK s) /\
  expr_post ctx fn ce cx e es sa sb s0 ee v op s /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s.vs_halted /\
  ghost_inv d ce cx ee G tn s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\ ptr_buf_ok ce e op G s ==>
  ?ee' G' tn' t.
    (!tail. write_place cx (MemoryPlace id []) v (ee with gas_obs := tail) =
      (INL (), ee' with gas_obs := tail)) /\
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (es,s0,G0,tn0) marks (INL ()) ee' G' tn' (OK t) /\
    t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx fn ce cx ee' t /\ ghost_inv d ce cx ee' G' tn' t /\
    (!x. not_fresh_at sb x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v, ee with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  rename1 `find_containing_scope id ee.scopes = SOME (pre,sc,entry,rest)` >>
  `lookup_scopes id ee.scopes = SOME entry` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `get_tenv cx = env.type_defs` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?dtv. evaluate_type (get_tenv cx) ty = SOME dtv` by
    (drule_all expr_sim_inv_local >> strip_tac >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  `entry.type = dtv` by
    (irule memory_rhs_read_local_type >>
     goal_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     qexistsl_tac [`ee with gas_obs := []`,`id`,`ty`,`v`] >>
     simp[] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> metis_tac[]) >>
  `value_runtime_typed env ty v` by metis_tac[memory_rhs_read_destination_typed] >>
  `value_has_type entry.type v` by
    (qpat_x_assum `value_runtime_typed env ty v` mp_tac >>
     simp[value_runtime_typed_def] >> metis_tac[optionTheory.SOME_11]) >>
  `~is_word_type (post_value_type ce e) /\
   post_value_type ce e = lowered_value_type ce e /\
   ?stv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
     type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
     type_memory_size stv < 2 ** 64` by
    (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
     drule retained_intcall_physical_layout >>
     (impl_tac >- metis_tac[expr_type_def]) >> metis_tac[]) >>
  `0 < type_memory_bytes ce (lowered_value_type ce e) /\
   ?rp. vv = LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) rp /\
     rp.ptr_location = LocMemory` by
    (qpat_assum `e = Call _ _ _ _` SUBST_ALL_TAC >>
     irule widened_assign_retained_call_memory >> metis_tac[expr_type_def]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sb)` by
    (pure_rewrite_tac[lower_value_def, comp_bind_def] >>
     asm_rewrite_tac[] >> simp[] >> metis_tac[]) >>
  drule_all retained_rhs_physical_input_ptr >> strip_tac
  >- fs[] >>
  `tv = stv` by metis_tac[optionTheory.SOME_11] >>
  `value_runtime_typed env (post_value_type ce e) v` by
    metis_tac[memory_rhs_read_post_typed] >>
  `value_has_type stv v` by
    (qpat_x_assum `value_runtime_typed env (post_value_type ce e) v` mp_tac >>
     simp[value_runtime_typed_def] >> metis_tac[optionTheory.SOME_11]) >>
  `val_wf entry.type v` by metis_tac[value_has_type_memory_wf] >>
  `type_memory_bytes ce ty = type_memory_size entry.type` by
    metis_tac[expr_sim_inv_memory_size] >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[expr_post_def] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv ce cx env es` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_def] >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `type_memory_size entry.type + 64 < dimword (:256) /\
   type_memory_size stv < dimword (:256)` by
    (simp[dimword_def] >> gvs[]) >>
  `compile_assign_value ce (Var p) LocMemory op F (SOME LocMemory)
    ty (lowered_value_type ce e) bytes sb = ((),sf)` by
    metis_tac[vv_location_def] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `type_widens_to env.type_defs (post_value_type ce e) (expr_type e)` by
    metis_tac[post_value_type_widens] >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) ty` by
    metis_tac[assignRelayoutCallerTheory.type_widens_to_trans] >>
  qabbrev_tac `ee' = ee with scopes :=
    pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` >>
  `write_place cx (MemoryPlace id []) v ee = (INL (),ee')` by
    (qpat_x_assum `!tail. write_place _ _ _ _ = _` (qspec_then `ee.gas_obs` mp_tac) >>
     simp[Abbr `ee'`]) >>
  mp_tac (Q.INST
    [`cenv` |-> `ce`, `sty` |-> `lowered_value_type ce e`, `dty` |-> `ty`,
     `sa` |-> `sb`, `sb` |-> `sf`, `va` |-> `sa`, `vb` |-> `sb`,
     `es` |-> `ee`, `es'` |-> `ee'`, `sw` |-> `w`,
     `D` |-> `cx_dead cx`, `PG` |-> `PG`]
    (SPEC_ALL widened_assign_staged_local_ptr)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 Gf tf (OK u)` >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (bind (bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [])))
    (es,s0,G0,tn0) marks (INL ()) ee' Gf tf (OK u)` by
    (irule (SRULE []
      (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
     goal_assum (drule_at Any) >>
     simp[gas_marked_exec_ptr_def,gas_explicit_def,Abbr `ee'`]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (es,s0,G0,tn0) marks (INL ()) ee' Gf tf (OK u)` by
    (drule assign_local_admissible_run >> strip_tac >>
     qpat_x_assum `gas_marked_exec_ptr _ _ _ (bind _ _) _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def]) >>
  qexistsl_tac [`ee'`,`Gf`,`tf`,`u`] >> simp[Abbr `ee'`]
QED
