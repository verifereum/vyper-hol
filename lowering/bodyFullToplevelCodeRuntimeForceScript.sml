(* One runtime immutable-copy endpoint for every finite horizon. *)
Theory bodyFullToplevelCodeRuntimeForce
Ancestors
  bodyFullToplevelCodePosts bodyFullToplevelCodeAllocation
  bodyImmutableUnwrapMemory exprPtrUnwrapCodeCopyShape
  valueEncodingProps vyperStorageFootprint loweringPosts exprLowering
  bodyPtrDefs exprSimProps

Theorem toplevel_code_runtime_force_full:
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\
  ~is_word_type t /\ ~cenv.ce_is_ctor /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  (is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    is_word_type (expr_type (TopLevelName ann nsid))) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo ret cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
      ghost_inv_at (DF H) lo ret cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
        (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op G' tn' z /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      ptr_buf_ok cenv (TopLevelName ann nsid) op G' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand op z = SOME w ==> type_memory_size rt = 0 \/
        w2n w+type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
    (TopLevelName ann nsid) es sa sm s0 ee tv (LocatedValue t p) s /\
   ghost_inv_at (DF (storage_trace_horizon ee.storage_trace)) lo ret cenv cx ee G tn s` by metis_tac[] >>
  drule_all exprPtrUnwrapCodeTheory.vv_post_code_source >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by fs[vv_post_def] >>
  `type_memory_bytes cenv t = type_memory_size rty /\ type_memory_size rty < 2**64` by metis_tac[] >>
  `compile_ensure_in_memory p.ptr_operand LocCode (type_memory_bytes cenv t)
    ((type_memory_bytes cenv t+31) DIV 32) F cenv.ce_imm_alloca sb = (op,sc)` by
    gvs[unwrap_value_def] >>
  drule_all ensure_runtime_code_layout >> strip_tac >>
  `32*((type_memory_bytes cenv t+31) DIV 32) = type_memory_size rty` by
    simp[type_memory_size_slots, arithmeticTheory.ADD_DIV_ADD_DIV] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (fs[contextTheory.vv_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  `evaluate_type (get_tenv cx) t = SOME rty` by metis_tac[] >>
  `w2n a + type_memory_size rty <= LENGTH s.vs_data_section` by
    (drule_all runtime_immutable_data_section >> simp[]) >>
  `w2n a + type_memory_size rty < dimword(:256)` by
    metis_tac[exprSimCopyTheory.immutable_holds_bounds] >>
  `type_memory_bytes cenv t < dimword(:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
  `32*((type_memory_bytes cenv t+31) DIV 32) <= type_memory_bytes cenv t /\
   w2n a+32*((type_memory_bytes cenv t+31) DIV 32) <= LENGTH s.vs_data_section /\
   w2n a+32*((type_memory_bytes cenv t+31) DIV 32) < dimword(:256)` by simp[] >>
  drule_all toplevel_code_runtime_execution_full_at >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  suspend "posts"
QED

Resume toplevel_code_runtime_force_full[posts]:
  markerLib.RESUME_TAC >>
  qpat_assum `vv_post (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac toplevel_code_runtime_posts_full) >>
  disch_then (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (mp_tac o REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `v' = v` by gvs[] >> qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  qexistsl [`v`, `z with vs_inst_idx := LENGTH sc.cs_current_insts`, `Gf`, `tnf`] >>
  simp[] >> (reverse conj_tac >- gvs[]) >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac toplevel_code_runtime_posts_full) >>
  disch_then (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  qpat_x_assum `ghost_inv_at (DF (storage_trace_horizon _)) _ _ _ _ _ _ _ _` kall_tac >>
  disch_then (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (mp_tac o REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> gvs[]
QED

Finalise toplevel_code_runtime_force_full
