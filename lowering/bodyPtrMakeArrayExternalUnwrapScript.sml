Theory bodyPtrMakeArrayExternalUnwrap
Ancestors
  bodyPtrMakeArrayExternalCaller bodyPtrMakeArrayExternalInstall
  bodyPtrMakeArrayAllocatedOne bodyPtrMakeArrayAllocatedStorage
  bodyPtrMakeArrayAllocatedImmutable bodyPtrMakeArrayImmutableSource
  exprLowering exprLoweringProps emitHelper context compileEnv
  vyperStatePreservation vyperEvalExprPreservesScopesDom
  bodyPtrMakeArrayConsumerPost bodyPtrMakeArrayExternalCompiler

Theorem external_storage_one_unwrap:
  compile_expr cenv (expr_type e) e si = (LocatedValue t p,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value cenv (LocatedValue t p) sn = (op,sb) /\
  fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\
  expr_body_pre cenv cx env e esi /\ local_ptrs_reserved cenv si /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func cenv cx e esi si sn s0 es' raw (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue t p) es' G tn s /\
  ghost_inv d cenv cx es' G tn s /\ stmt_state_rel ctx func cenv cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  ~is_word_type (expr_type e) /\
  (type_memory_bytes cenv t + 31) DIV 32 = 1 ==>
  ?v z H tm.
    read_result cx raw es' = (INL v,es') /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func cenv cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (expr_type e) v op H tm z /\ ptr_buf_ok cenv e op H z /\
    ghost_inv d cenv cx es' H tm z /\ ghost_kept cenv es' sn G tn s H tm /\
    stmt_state_rel ctx func cenv cx es' z
Proof
  strip_tac >>
  drule_all external_consumer_compile_frame >> strip_tac >>
  drule_all make_array_storage_consumer_read >> strip_tac >>
  drule_all make_array_storage_consumer_taint >> strip_tac >>
  `p.ptr_location <> LocMemory` by (Cases_on `tr` >> simp[]) >>
  drule_all external_located_unwrap_sizes >> strip_tac >>
  drule_all external_storage_value_bounds >> strip_tac >>
  `type_memory_bytes cenv t = 32` by decide_tac >>
  `~is_word_type t` by metis_tac[] >>
  drule_all unwrap_storage_aggregate_split >> strip_tac >>
  gvs[] >> suspend "install"
QED

Resume external_storage_one_unwrap[install]:
  `?dst. buf'.buf_operand = Var dst` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def, emit_def,
       comp_ignore_bind_def] >> strip_tac >> gvs[]) >>
  `?tmp. loaded = Var tmp` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >> strip_tac >> gvs[]) >>
  drule (Q.INST [`n` |-> `1`] storage_allocated_install) >>
  disch_then (qspecl_then [`tr`, `p.ptr_operand`, `sb`, `func`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  gvs[] >>
  `type_slot_size tvt <= 1` by simp[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x`
    by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x`
    by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sn sm') (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `!k j. w2n a <= w2n k /\ w2n k < w2n a + type_slot_size tvt /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) tvt (w2n k) j` by simp[] >>
  drule_all allocated_one_slot_endpoint_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "post"
QED

Resume external_storage_one_unwrap[post]:
  `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  qpat_x_assum `!esi si e raw vv base. _` (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`z`, `H`, `tm`] >> simp[]
QED

Finalise external_storage_one_unwrap

Theorem external_storage_loop_unwrap:
  compile_expr cenv (expr_type e) e si = (LocatedValue t p,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value cenv (LocatedValue t p) sn = (op,sb) /\
  fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\
  expr_body_pre cenv cx env e esi /\ local_ptrs_reserved cenv si /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func cenv cx e esi si sn s0 es' raw (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue t p) es' G tn s /\
  ghost_inv d cenv cx es' G tn s /\ stmt_state_rel ctx func cenv cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  ~is_word_type (expr_type e) /\
  (type_memory_bytes cenv t + 31) DIV 32 <> 1 ==>
  ?v z H tm.
    read_result cx raw es' = (INL v,es') /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func cenv cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (expr_type e) v op H tm z /\ ptr_buf_ok cenv e op H z /\
    ghost_inv d cenv cx es' H tm z /\ ghost_kept cenv es' sn G tn s H tm /\
    stmt_state_rel ctx func cenv cx es' z
Proof
  strip_tac >>
  drule_all external_consumer_compile_frame >> strip_tac >>
  drule_all make_array_storage_consumer_read >> strip_tac >>
  drule_all make_array_storage_consumer_taint >> strip_tac >>
  `p.ptr_location <> LocMemory` by (Cases_on `tr` >> simp[]) >>
  drule_all external_located_unwrap_sizes >> strip_tac >>
  drule_all external_storage_value_bounds >> strip_tac >>
  `~is_word_type t` by metis_tac[] >>
  drule_all unwrap_storage_aggregate_split >> strip_tac >>
  gvs[] >> suspend "install"
QED

Resume external_storage_loop_unwrap[install]:
  `?dst. buf'.buf_operand = Var dst` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def, emit_def,
       comp_ignore_bind_def] >> strip_tac >> gvs[]) >>
  drule (Q.INST [`n` |-> `type_slot_size tvt`] storage_allocated_install) >>
  disch_then (qspec_then `tvt` mp_tac) >>
  disch_then (qspecl_then [`tr`, `p.ptr_operand`, `sb`, `func`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x`
    by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x`
    by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sn sm') (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `compile_alloc_buffer (32 * type_slot_size tvt) sn = (buf',sm') /\
   32 * type_slot_size tvt < dimword(:256) /\
   type_slot_size tvt <= type_slot_size tvt` by simp[] >>
  `MEM (mk_inst sn.cs_next_id ALLOCA [Lit (n2w (32 * type_slot_size tvt))]
    [STRING #"%" (toString sn.cs_next_var)]) (fn_insts func)` by simp[] >>
  `!k j. w2n a <= w2n k /\ w2n k < w2n a + type_slot_size tvt /\
    j < 32 /\ j IN key_taint (if tr then tn.t_trans else tn.t_stor) k ==>
    dead_bytes (if tr then contract_transient s else contract_storage s)
      (w2n a) tvt (w2n k) j` by simp[] >>
  drule_all allocated_storage_loop_endpoint_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> suspend "post"
QED

Resume external_storage_loop_unwrap[post]:
  `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  `val_footprint tvt v <= 32 * type_slot_size tvt` by simp[] >>
  qpat_x_assum `!esi si e raw vv base. _` (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`z`, `H`, `tm`] >> simp[]
QED

Finalise external_storage_loop_unwrap

Theorem external_code_unwrap:
  compile_expr cenv (expr_type e) e si = (LocatedValue t p,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value cenv (LocatedValue t p) sn = (op,sb) /\
  fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\
  expr_body_pre cenv cx env e esi /\ local_ptrs_reserved cenv si /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func cenv cx e esi si sn s0 es' raw (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue t p) es' G tn s /\
  ghost_inv d cenv cx es' G tn s /\ stmt_state_rel ctx func cenv cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\
  ~is_word_type (expr_type e) ==>
  ?v z H tm.
    read_result cx raw es' = (INL v,es') /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func cenv cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (expr_type e) v op H tm z /\ ptr_buf_ok cenv e op H z /\
    ghost_inv d cenv cx es' H tm z /\ ghost_kept cenv es' sn G tn s H tm /\
    stmt_state_rel ctx func cenv cx es' z
Proof
  strip_tac >>
  drule_all external_consumer_compile_frame >> strip_tac >>
  drule_all make_array_immutable_consumer_read >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by metis_tac[] >>
  `p.ptr_location <> LocMemory` by simp[] >>
  drule_all external_located_unwrap_sizes >> strip_tac >>
  `~is_word_type t` by metis_tac[] >>
  drule_all unwrap_code_aggregate_split >> strip_tac >>
  gvs[] >> suspend "install"
QED

Resume external_code_unwrap[install]:
  `?dst. buf'.buf_operand = Var dst` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, emit_inst_def, fresh_id_def, emit_def,
       comp_ignore_bind_def] >> strip_tac >> gvs[]) >>
  drule_all immutable_allocated_install >> strip_tac >> gvs[] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x`
    by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x`
    by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sn sm') (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sm' sb) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by simp[] >>
  `op_taint tn p.ptr_operand = {}` by
    fs[bodyPtrDefsTheory.ptr_vv_ok_def] >>
  `w2n a + type_memory_size tv < dimword(:256) /\
   type_memory_size tv < dimword(:256)` by decide_tac >>
  drule_all allocated_immutable_runtime_endpoint_frame >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> suspend "post"
QED

Resume external_code_unwrap[post]:
  `MAP FDOM esi.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  qpat_x_assum `!esi si e raw vv base. _` (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`z`, `H`, `tm`] >> simp[]
QED

Finalise external_code_unwrap

Theorem external_nonword_unwrap:
  compile_expr cenv (expr_type e) e si = (LocatedValue t p,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value cenv (LocatedValue t p) sn = (op,sb) /\
  fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\
  expr_body_pre cenv cx env e esi /\ local_ptrs_reserved cenv si /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func cenv cx e esi si sn s0 es' raw (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue t p) es' G tn s /\
  ghost_inv d cenv cx es' G tn s /\ stmt_state_rel ctx func cenv cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  p.ptr_location <> LocMemory /\ ~cenv.ce_is_ctor /\
  ~is_word_type (expr_type e) ==>
  ?v z H tm.
    read_result cx raw es' = (INL v,es') /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func cenv cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (expr_type e) v op H tm z /\ ptr_buf_ok cenv e op H z /\
    ghost_inv d cenv cx es' H tm z /\ ghost_kept cenv es' sn G tn s H tm /\
    stmt_state_rel ctx func cenv cx es' z
Proof
  strip_tac >>
  drule unwrap_external_calldata_excluded >> strip_tac >>
  Cases_on `p.ptr_location = LocCode`
  >- (drule_all external_code_unwrap >> simp[]) >>
  `?tr. p.ptr_location = (if tr then LocTransient else LocStorage)` by
    (Cases_on `p.ptr_location` >> gvs[] >>
     metis_tac[]) >>
  Cases_on `(type_memory_bytes cenv t + 31) DIV 32 = 1`
  >- (drule_all external_storage_one_unwrap >> simp[]) >>
  drule_all external_storage_loop_unwrap >> simp[]
QED
