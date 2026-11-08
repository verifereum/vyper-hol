(* Local struct fields: keep robust representation separate from execution. *)
Theory assignBasePtrAttrLocal
Ancestors wordLoadStorePtr assignBasePtrFieldAddress assignBasePtrFieldRobust
  assignBasePtrScopePost assignBasePtrScalarPost assignBasePtrWordStore
  typedCopyPtr assignTuplePtrStoreHead bodyPtrDefs stmtSimAssignAttr
  venomState venomExecSemantics venomMemProofs ptrDiscipline venomInst
  valueEncoding valueEncodingProps compileEnv localPtrsProps words finite_map pred_set
  assignTuplePtrStoreWord assignTuplePtrCopyEndpoint stmtSimDeclStore exprSimProps exprLoweringProps
  emitHelper emitHelperProps context vyperLookup exprSimFieldLayout gasContext
  loweringPosts stmtSimDefs stmtSimProps gasSummaryComposePtr
  exprSimHypsDefs stmtSimAugAssign list gasSummary fragGasMode fragGasPath
  exprSimSource vyperEvalExprPreservesScopesDom fragExec stmtSimDeclMem
  fragGasPathPtr exprSimDefs bodyPtrPreds bodySim bodyExprPreFacts
  supportedExprTraverse supportedStmtTraverse supportedExprs supportedStmts
  vyperTypeEnv vyperTyping exprSimHyps vyperTypeCallGraph
  vyperTypeSystem vyperTypeInvariants

Theorem assign_base_attr_local_store_ghost:
  !d cenv cx es G tn s id pre sc entry rest p sz rootw dst addr value v sa fn PG iid
    flds fs vals fld ftv.
  ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME rootw /\ lookup_var dst s = SOME addr /\
  w2n addr = w2n rootw + struct_field_offset flds fld /\
  eval_operand value s = SOME (typed_val_to_w256 ftv v) /\ op_taint tn value = {} /\
  local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s id (w2n rootw) sz /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ fields_val_wf vals fs /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
  type_memory_size ftv = 32 /\ type_memory_size (StructTV fs) <= sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (StructTV fs) (StructV vals) (w2n rootw) mem) ==>
  ghost_inv d cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with
      <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
    (step_prov PG G (mk_inst iid MSTORE [Var dst; value] [])
      (mstore (w2n addr) (typed_val_to_w256 ftv v) s))
    (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
      (mstore (w2n addr) (typed_val_to_w256 ftv v) s) tn)
    (mstore (w2n addr) (typed_val_to_w256 ftv v) s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `iid`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tf.t_var = tn.t_var` >>
  `!x. not_fresh_at sa x ==>
    lookup_var x (mstore (w2n addr) (typed_val_to_w256 ftv v) s) = lookup_var x s /\
    FLOOKUP G x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    simp[mstore_def, lookup_var_def, op_taint_def] >>
  `!mem. mem_agree_outside tf.t_mem
    (mstore (w2n addr) (typed_val_to_w256 ftv v) s).vs_memory mem ==>
    val_in_memory entry.type (StructV (AFUPDKEY fld (K v) vals)) (w2n rootw) mem` by
    (simp[] >> rpt strip_tac >>
     irule assign_base_field_update_robust >> simp[] >>
     goal_assum (drule_at (Pat `fields_layout _ _`)) >>
     qexistsl_tac [`tn.t_mem`, `ftv`, `s`] >>
     simp[arithmeticTheory.ADD_ASSOC]) >>
  `!i. ~(w2n rootw <= i /\ i < w2n rootw+sz) ==>
    mem_bytes_at i 1 (mstore (w2n addr) (typed_val_to_w256 ftv v) s).vs_memory =
      mem_bytes_at i 1 s.vs_memory /\ (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >>
     qpat_assum `tf.t_mem = _` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `w2n addr = _` (fn th => pure_rewrite_tac [th]) >>
     irule assign_base_field_store_exterior >> simp[] >>
     goal_assum (drule_at (Pat `fields_layout _ _`)) >> simp[] >>
     qexists_tac `sz` >> fs[]) >>
  `stor_taint_ok cx tf (mstore (w2n addr) (typed_val_to_w256 ftv v) s)` by
    (qunabbrev_tac `tf` >> irule mstore_storage_taint_frame_ptr >>
     simp[] >> metis_tac[ghost_inv_def]) >>
  gvs[] >> irule (cj 1 assign_base_local_scope_ghost_post) >> simp[] >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  qexistsl_tac [`fn`, `sz`, `sa`] >> simp[] >> metis_tac[]
QED

Theorem assign_base_attr_local_store_runtime_ptr:
  !d cenv cx es G tn s id pre sc entry rest p sz rootw dst addr value v sa fn PG
    flds fs vals fld ftv sb.
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME rootw /\ lookup_var dst s = SOME addr /\
  w2n addr = w2n rootw + struct_field_offset flds fld /\
  ptr_covers G tn dst s 32 /\
  eval_operand value s = SOME (typed_val_to_w256 ftv v) /\ op_taint tn value = {} /\
  local_ptrs_rel fn cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  local_region cenv es.scopes s id (w2n rootw) sz /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\ fields_val_wf vals fs /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
  type_memory_size ftv = 32 /\ type_memory_size (StructTV fs) <= sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (StructTV fs) (StructV vals) (w2n rootw) mem) ==>
  ?tf u.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tf (OK u) /\
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) G tf u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x u = lookup_var x s /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_attr_local_store_ghost >>
  disch_then (qspecl_then [`PG`, `sa.cs_next_id`] assume_tac) >>
  `stmt_state_rel ctx fn cenv cx
    (es with scopes := pre ++ (sc |+ (id,entry with
      <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
    (mstore (w2n addr) (typed_val_to_w256 ftv v) s)` by
    (pure_asm_rewrite_tac [] >> irule stmt_state_rel_write_field >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `emit_inst MSTORE [Var dst; value] [] sa = ((),sb)` by
    gvs[emit_void_def, emit_inst_def] >>
  drule_all emit_mstore_zero_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] assume_tac) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `sa.cs_next_id`] strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qexistsl_tac
    [`step_taint (mk_inst sa.cs_next_id MSTORE [Var dst; value] []) s
        (mstore (w2n addr) (typed_val_to_w256 ftv v) s) tn`,
     `mstore (w2n addr) (typed_val_to_w256 ftv v) s
        with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[] >> simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx] >>
  simp[mstore_def, lookup_var_def, op_taint_def]
QED

(* Recover the runtime store's local premises at its actual endpoint. *)
Theorem assign_base_attr_local_endpoint:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME bw /\
  entry.type = StructTV fs /\ entry.value = StructV vals ==>
  local_ptrs_rel fn cenv es.scopes s /\
  local_region cenv es.scopes s id (w2n bw) sz /\
  ptr_covers G tn p s sz /\
  w2n bw + sz <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  type_memory_size (StructTV fs) <= sz /\ fields_val_wf vals fs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (StructTV fs) (StructV vals) (w2n bw) mem)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `local_ptrs_rel fn cenv es.scopes s /\ alloca_room ctx fn s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n bw + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (qpat_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `ptr_covers G tn p s sz /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n bw) mem)` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (simp[local_region_def] >> metis_tac[]) >>
  gvs[val_wf_def] >> metis_tac[alloca_room_next_lt]
QED

Theorem assign_base_attr_local_store_ptr:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME bw /\
  eval_operand (Var dst) s = SOME (bw + n2w (struct_field_offset flds fld)) /\
  op_prov G (Var dst) = op_prov G (Var p) /\ op_taint tn (Var dst) = {} /\
  eval_operand value s = SOME (typed_val_to_w256 ftv v) /\ op_taint tn value = {} /\
  local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?tf u.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G tf (OK u) /\
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with
        <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) G tf u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x u = lookup_var x s /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all assign_base_attr_local_endpoint >> strip_tac >>
  `type_memory_size ftv = 32` by fs[store_lays_out_def] >>
  `struct_field_offset flds fld + 32 <= type_memory_size_fields fs` by
    metis_tac[struct_field_offset_le] >>
  `w2n (bw + n2w (struct_field_offset flds fld)) =
    w2n bw + struct_field_offset flds fld` by
    (irule buffer_offset_no_wrap >> qexists_tac `type_memory_size_fields fs` >>
     gvs[type_memory_size_def]) >>
  `ptr_covers G tn dst s 32` by
    (irule assign_base_field_destination_coverage >> simp[] >>
     goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
     qexistsl_tac [`bw`, `struct_field_offset flds fld`] >>
     gvs[eval_operand_def, type_memory_size_def]) >>
  irule assign_base_attr_local_store_runtime_ptr >> simp[] >>
  goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `fields_layout _ _`)) >>
  gvs[eval_operand_def] >> metis_tac[]
QED

(* The S1 normal-source corollary is private; expose its source-only interface
   here so the pointer continuation need not unfold statement evaluation. *)
Theorem assign_base_attr_local_normal_source:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre sc entry rest fs vals ftv.
    find_containing_scope id ee.scopes = SOME (pre,sc,entry,rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\ store_lays_out ftv ftv v /\
    !tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := tail) =
      (INL (), ee with <|scopes := pre ++
        (sc |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
          popped := []|>)) :: rest; gas_obs := tail|>)
Proof
  strip_tac >> drule_all assign_attr_local_continuation_all_tails >> strip_tac >>
  Cases_on `eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs ++ [])` >> rename1 `_ = (res,ff)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs ++ [])` by simp[] >>
  drule_all assign_attr_local_source >> strip_tac >>
  qpat_x_assum `!tail. vyperState$bind _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `r = INL v /\ es1 = (ee with gas_obs := [])` by
    (qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
     qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, pairTheory.UNCURRY]) >>
  gvs[] >> metis_tac[]
QED

Theorem assign_base_attr_local_store_post_ptr:
  emit_void MSTORE [Var dst; op] su = ((),sb) /\
  fn_has_code su sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
  expr_post ctx fn cenv cx e es sa su s0 ee v op s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  find_containing_scope id ee.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME bw /\
  eval_operand (Var dst) s = SOME (bw + n2w (struct_field_offset flds fld)) /\
  op_prov G (Var dst) = op_prov G (Var p) /\ op_taint tn (Var dst) = {} /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
  local_ptrs_reserved cenv su /\ ~block_is_terminated sb /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout flds fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v /\
  (!tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
    (ee with gas_obs := tail) =
    (INL (),ee with <|scopes := pre ++ (sc |+ (id,entry with
      <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest;
      gas_obs := tail|>)) ==>
  ?ff tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (write_place cx (MemoryPlace id [AttrSubscript fld]) v)
      (ee,s,G,tn) [] (INL ()) ff G tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff G tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x))
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s /\
   eval_operand op s = SOME (typed_val_to_w256 ftv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  drule_all assign_base_attr_local_store_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`ee with scopes := pre ++ (sc |+ (id,entry with
    <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest`,
    `tf`, `u`] >>
  conj_tac >- simp[gas_marked_exec_ptr_def] >>
  simp[] >> conj_tac
  >- (simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
      fs[expr_post_def] >> metis_tac[]) >>
  fs[ghost_kept_def] >> metis_tac[]
QED

Theorem assign_base_attr_local_initial_pointer:
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ ghost_inv d cenv cx es G tn s0 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa ==>
  not_fresh_at sa p /\ ptr_covers G tn p s0 sz /\ ?bw. lookup_var p s0 = SOME bw
Proof
  strip_tac >> conj_tac
  >- metis_tac[local_ptrs_reserved_def] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  conj_tac >- (fs[ghost_inv_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  qpat_x_assum `!name entry p sz. _` drule_all >> metis_tac[]
QED

Theorem assign_base_attr_local_marked_exec_ptr:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec_ptr D (ctx,fn) PG
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (es,s0,G0,tn0) marks res ee G tn r ==>
  gas_marked_exec_ptr D (ctx,fn) PG
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (es,s0,G0,tn0) marks res ee G tn r
Proof
  strip_tac >> drule assign_attr_local_admissible_run >> strip_tac >>
  gvs[gas_marked_exec_ptr_def]
QED

Theorem assign_base_attr_local_after_read_ptr:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\ expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0,Gi,ti) marks (INL v) ee G tn (OK s) /\
  expr_post ctx fn cenv cx e es sa su s0 (ee with gas_obs := []) v op s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  emit_void MSTORE [Var dst; op] su = ((),sb) /\ fn_has_code su sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ ~block_is_terminated sb /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME bw /\
  eval_operand (Var dst) s = SOME (bw + n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) /\
  op_prov G (Var dst) = op_prov G (Var p) /\ op_taint tn (Var dst) = {} /\
  ptr_val_ok cx (expr_type e) v op G tn s /\ local_ptrs_reserved cenv su /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) ==>
  ?ff tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (es,s0,Gi,ti) marks (INL ()) ff G tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff G tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x))
Proof
  strip_tac >>
  `!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
  drule_all assign_base_attr_local_normal_source >> strip_tac >>
  `find_containing_scope id (ee with gas_obs := []).scopes =
    SOME (pre,sc,entry,rest)` by simp[] >>
  `?ff tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (write_place cx (MemoryPlace id [AttrSubscript fld]) v)
      (ee with gas_obs := [],s,G,tn) [] (INL ()) ff G tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff G tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x))` by
    (irule assign_base_attr_local_store_post_ptr >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fields_layout _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ff`, `tf`, `u`] >> simp[] >>
  irule assign_base_attr_local_marked_exec_ptr >>
  (conj_tac >- (qexists_tac `lctx` >> simp[])) >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
  qexistsl_tac [`G`, `ee`, `s`, `tn`, `v`] >> simp[]
QED

Theorem assign_base_attr_local_normal_continuation_ptr:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\ expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
    sm = (dst,sn) /\ unwrap_value cenv vv sn = (op,su) /\
  emit_void MSTORE [dst;op] su = ((),sb) /\
  fn_has_code sm sn fn /\ fn_has_code sn su fn /\ fn_has_code su sb fn /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ~block_is_terminated sb /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv su /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_fresh_at sa p /\ lookup_var p s0 = SOME bw /\ op_taint tn (Var p) = {} /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (eval_expr cx e)
    (es,s0,Gi,ti) marks (INL tv) ee G tn (OK s) /\
  vv_post ctx fn cenv cx e es sa sm s0 (ee with gas_obs := []) tv vv s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  ptr_vv_ok cx (expr_type e) tv vv (ee with gas_obs := []) G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!v. read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) ==>
    value_has_type rty v) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x) ==>
  ?ff H tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (es,s0,Gi,ti) marks (INL ()) ff H tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff H tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x))
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME bw` by
    (fs[vv_post_def, eval_operand_def] >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes /\
   is_word_type (expr_type e)` by simp[] >>
  drule_all assign_base_field_add_word_read_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `lookup_var p z = SOME bw` by (fs[expr_post_def] >> metis_tac[]) >>
  `FLOOKUP H p = FLOOKUP G p` by (fs[ghost_kept_def] >> metis_tac[]) >>
  `op_prov H dst = op_prov H (Var p)` by gvs[op_prov_def] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (vyperState$bind (eval_expr cx e) (read_result cx))
    (es,s0,Gi,ti) marks (INL v) ee H tf (OK z)` by
    (irule (SIMP_RULE std_ss [APPEND_NIL]
      (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
     qexistsl_tac [`G`, `ee`, `s`, `tn`, `tv`] >> simp[] >>
     fs[gas_marked_exec_ptr_def]) >>
  `~z.vs_halted` by
    (drule_all gas_marked_exec_ptr_exec >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  qrefinel [`_`, `H`, `_`, `_`] >>
  irule assign_base_attr_local_after_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem assign_base_attr_local_rhs_source:
  expr_body_pre cenv cx env e es /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e)
    (es,s0,Gi,ti) marks (INL tv) ee G tn (OK s) ==>
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ?rty. evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
    (!v. read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) ==>
      value_has_type rty v)
Proof
  strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL tv,ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[APPEND_NIL]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  conj_tac
  >- (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_all expr_body_pre_runtime_typed >> metis_tac[]
QED

Theorem compile_assign_attr_local_case_ptr:
  expr_vv_sim_ptr d ctx PG fn cenv cx (expr_type e) e es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_local_code_parts >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn su /\ cs_extends su sb` by
    metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
      ci_mono_unwrap_value, ci_mono_emit_void, pairTheory.SND, ci_mono_def] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn /\
   fn_has_code sn su fn /\ fn_has_code su sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `~block_is_terminated sb` by
    (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule assign_attr_local_admissible_raw >> simp[]) >>
  suspend "rhs"
QED

Resume compile_assign_attr_local_case_ptr[rhs]:
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_ptr_at_marked] >> strip_tac
      >- suspend "normal" >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
      qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
      >- (irule assign_base_attr_local_marked_exec_ptr >>
          (conj_tac >- (qexists_tac `lctx` >> simp[])) >>
          ntac 2 (irule gas_marked_exec_ptr_bind_exception) >> simp[]) >>
      disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_attr_local_exempt >> simp[]
QED

Resume compile_assign_attr_local_case_ptr[normal]:
  gvs[] >>
  drule_all assign_base_attr_local_rhs_source >> strip_tac >>
  drule_all assign_base_attr_local_initial_pointer >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_var <= su.cs_next_var` by
    metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
      ci_mono_unwrap_value, ci_mono_def, pairTheory.SND,
      arithmeticTheory.LESS_EQ_TRANS] >>
  `local_ptrs_reserved cenv su` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x`
    by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at su x`
    by metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  `op_taint tn (Var p) = {}` by
    (fs[ptr_covers_def, ghost_kept_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (drule_all gas_marked_exec_ptr_exec >> simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `?ff H tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (es,s0,G0,tn0) marks (INL ()) ff H tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff H tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x))` by
    (irule assign_base_attr_local_normal_continuation_ptr >> simp[] >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`INL ()`, `ff`, `H`, `tf`, `OK u`] >> simp[] >>
  disj1_tac >> fs[stmt_post_def] >>
  simp[stmtFragPtrTheory.ghost_inv_gas_obs] >> metis_tac[]
QED
Finalise compile_assign_attr_local_case_ptr

Theorem body_assign_attr_local_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
    occurs_abi_decode_target target tops) /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) =
    SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  attribute_type env.type_defs (StructT sid) fld = SOME fty /\ is_word_type fty ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  strip_tac >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (Cases_on `type_place_target env (AttributeTarget (NameTarget id) fld)` >>
     gvs[type_stmt_def, atarget_accepts_def] >>
     rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
     gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[type_widens_to_word]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> fs[body_inv_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
     (conj_tac >- fs[body_inv_def]) >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_ptr d ctx PG fn cenv cx fty e es` by
    metis_tac[body_expr_ptr_ok_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
    (nsid_to_string sid)) fld = SOME (fty,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  irule compile_assign_attr_local_case_ptr >> simp[] >> metis_tac[]
QED
