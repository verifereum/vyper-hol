(* Counted stages for reaching a write destination. An intermediate base
   can be a mapping reference; only the place stage has consumed get_place. *)
Theory bodyWriteTargetStageMods
Ancestors
  bodyFullPostsMods bodyFullTargetDefs bodyMemoryDefs targetPlaceSimCases
  targetPlaceSim loweringPosts gasOutcomeFullMods vyperFixedShapePath
  vyperStorageFootprint alist finite_map

Definition write_target_location_mods_def[nocompute]:
  write_target_location_mods cenv cx bt ee pv vt
    (r : operand # data_location option # place_ty option) G t <=>
    case pv of
      PlaceR (ImmutablePlace owner id path) =>
        target_root bt = TopLevelNameTarget (owner,id) /\
        cenv.ce_is_ctor /\ FST (SND r) = SOME LocCode /\
        op_prov G (FST r) = NONE /\
        (?ty off imms itv iv k ptv v.
           vt = Type ty /\
           FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
           ALOOKUP ee.immutables cx.txn.target = SOME imms /\
           FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
           mem_path_offset itv path = SOME (k,ptv) /\
           evaluate_type (get_tenv cx) ty = SOME ptv /\
           evaluate_subscripts itv iv path = INL v /\
           eval_operand (FST r) t = SOME (n2w (off+k)) /\
           (~target_through_dynarray cenv bt ==> fixed_shape_path itv path))
    | _ =>
        place_readable cx ee pv /\
        (?w. eval_operand (FST r) t = SOME w /\
             place_ptr_rel cenv cx t pv w (FST (SND r)) vt)
End

Definition write_target_post_mods_def[nocompute]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee pv vt
    (r : operand # data_location option # place_ty option) G0 tn0 G tn t <=>
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods D lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    SND (SND r) = SOME (value_type_place vt) /\
    (!x. FST r = Var x ==> not_fresh_at sb x) /\
    target_ptr_ok cenv pv r G tn t /\
    write_target_location_mods cenv cx bt ee pv vt r G t
End

(* The two stages share code and machine-entry premises, but not their
   source admissibility tests or the types of the source results. *)
Definition write_target_entry_mods_def[nocompute]:
  write_target_entry_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx bt es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 <=>
    compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target bt) shadow_sa = (r,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
                 dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s0 /\
         storage_well_formed_on cx es (FST H) /\
         immutable_frame_mods func cenv cx es s0 /\
         ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition write_base_sim_mods_def[nocompute]:
  write_base_sim_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      write_target_entry_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx bt es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 /\
      gas_admissible (eval_base_place cx bt) target_res_ok es ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (eval_base_place cx bt) (es,s0,G0,tn0)
        (\H res ee G tn t. ?pv. res = INL pv /\
          write_target_post_mods H (DF H) lo d ctx func cenv cx bt
            es sa sb s0 ee pv vt r G0 tn0 G tn t)
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Definition write_place_sim_mods_def[nocompute]:
  write_place_sim_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es <=>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      write_target_entry_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx bt es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (eval_target_place cx bt) (es,s0,G0,tn0)
        (\H res ee G tn t. ?p. res = INL p /\
          write_target_post_mods H (DF H) lo d ctx func cenv cx bt
            es sa sb s0 ee (PlaceR p) (Type ty) r G0 tn0 G tn t /\
          (!id path. p = MemoryPlace id path ==>
             ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                       evaluate_subscripts entry.type entry.value path = INL v))
        (\H res ee gt q.
          expr_exit res q /\ halt_exit H cx ee res q /\
          (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
End

Theorem write_target_post_view_mods:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee pv vt
    r G0 tn0 G tn t ==>
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sa s0 t /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods D lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  SND (SND r) = SOME (value_type_place vt) /\
  (!x. FST r = Var x ==> not_fresh_at sb x) /\
  target_ptr_ok cenv pv r G tn t /\
  write_target_location_mods cenv cx bt ee pv vt r G t
Proof
  simp[write_target_post_mods_def]
QED

(* Projection at a nested constructor write, using the actual owner. *)
Theorem write_target_immutable_view_mods:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee
    (PlaceR (ImmutablePlace owner id path)) (Type ty) r G0 tn0 G tn t ==>
  target_root bt = TopLevelNameTarget (owner,id) /\
  cenv.ce_is_ctor /\ FST (SND r) = SOME LocCode /\
  op_prov G (FST r) = NONE /\
  ?off imms itv iv k ptv v.
    FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
    ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
    mem_path_offset itv path = SOME (k,ptv) /\
    evaluate_type (get_tenv cx) ty = SOME ptv /\
    evaluate_subscripts itv iv path = INL v /\
    eval_operand (FST r) t = SOME (n2w (off+k)) /\
    (~target_through_dynarray cenv bt ==> fixed_shape_path itv path)
Proof
  simp[write_target_post_mods_def, write_target_location_mods_def]
QED

(* Projection at an intermediate mapping root, before consuming a key. *)
Theorem write_target_mapping_view_mods:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee
    (HashMapRef tr slot kt vt) place_ty r G0 tn0 G tn t ==>
  eval_operand (FST r) t = SOME slot /\ FST (SND r) = SOME (slot_loc tr) /\
  place_ty = HashMapT kt vt /\ op_prov G (FST r) = NONE /\
  op_taint tn (FST r) = {}
Proof
  simp[write_target_post_mods_def, write_target_location_mods_def,
       place_ptr_rel_def, target_ptr_ok_def, place_readable_def]
QED

Theorem write_target_storage_view_mods:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r G0 tn0 G tn t ==>
  eval_operand (FST r) t = SOME slot /\ FST (SND r) = SOME (slot_loc tr) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ op_prov G (FST r) = NONE /\
  op_taint tn (FST r) = {}
Proof
  simp[write_target_post_mods_def, write_target_location_mods_def,
       place_ptr_rel_def, target_ptr_ok_def, place_readable_def]
QED
