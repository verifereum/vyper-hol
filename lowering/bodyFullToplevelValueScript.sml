(* Word forcing uses the checked direct joint loaders, never the aggregate
   unwrap dispatcher.  Constructor robustness is retained as a producer input. *)
Theory bodyFullToplevelValue
Ancestors
  bodyFullUnwrapWord exprLoweringProps exprLowering compileEnv loweringPosts
  bodyPtrDefs exprSimMemDefs vyperStorageFootprint vyperAST context

Theorem toplevel_word_force_full:
  compile_expr cenv ty (TopLevelName ann nsid) sa =
    (LocatedValue ann p,sa) /\ is_word_type ann /\
  lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand (LocatedValue ann p) = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sa s0 ee tv
       (LocatedValue ann p) s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee tv (LocatedValue ann p) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv
    (LocatedValue ann p) ee G tn s /\
  (cenv.ce_is_ctor /\ vv_location (LocatedValue ann p) = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
                eval_operand (vv_operand (LocatedValue ann p)) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
     vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
       (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op G' tn' z /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
     ptr_buf_ok cenv (TopLevelName ann nsid) op G' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sa x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sa s z /\
    ghost_kept_at lo cenv ee sa G tn s G' tn'
Proof
  strip_tac >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   p.ptr_location = LocCode` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_expr_def, expr_type_def] >>
     Cases_on `emit_inst INVALID [] [] sa` >> simp[] >>
     Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[] >>
     rename1 `SOME loc` >> Cases_on `loc` >> simp[mk_ptr_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `unwrap_value cenv (LocatedValue ann p) sa = (op,sc)` by
    gvs[lower_value_def, comp_bind_def] >>
  (Cases_on `p.ptr_location = LocCode`
   >- (irule unwrap_code_word_origin_ptr >> simp[expr_type_def] >>
       qexistsl [`p`, `sa`, `ann`, `ty`] >>
       gvs[expr_type_def, post_value_type_def]) >>
   irule unwrap_slot_word_origin_ptr >> simp[expr_type_def] >>
   qexistsl [`p`, `sa`, `ann`, `ty`] >>
   gvs[expr_type_def, post_value_type_def])
QED
