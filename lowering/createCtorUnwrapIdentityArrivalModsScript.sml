(* A stack operand or a non-word memory pointer unwraps at the same state. *)
Theory createCtorUnwrapIdentityArrivalMods
Ancestors
  createCtorUnwrapIdentityArrival createExprSizeExitDefsMods
  createCtorSegmentArrival exprSimVVFrame exprSimUnwrapProps exprSimUnwrap
  exprSimWordArgs exprSimMemDefs fragGasOriginPtr bodyPtrDefs loweringPosts
  exprLowering compileEnv context vyperStorageFootprint relation bodyFullPostsMods

Theorem ctor_unwrap_identity_arrival_mods:
  ~is_word_type (post_value_type cenv e) /\
  ((?ann op0. vv = StackValue ann op0) \/
   (?ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory /\
                                      ~is_word_type ann)) /\
  sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G s) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn ==>
  sc = sb /\ op = vv_operand vv /\
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                  sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
                  i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s s /\
  ?v. read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK s, G, tn) /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op s /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) s /\
    vv_at cenv cx (post_value_type cenv e) sa sm ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) s /\
    expr_store_bound cx (post_value_type cenv e) v op s /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
    ptr_buf_ok cenv e op G s /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op s = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
    wb_frame cenv ee ee sb s s /\
    ghost_kept_at lo cenv ee sb G tn s G tn
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sc = sb /\ op = vv_operand vv` by
    (qpat_assum `(?ann op0. _) \/ (?ann p. _)` strip_assume_tac >>
     gvs[unwrap_value_def, comp_return_def, vv_operand_def]) >>
  `?v. read_result cx tv ee = (INL v, ee) /\
       ptr_val_ok cx (post_value_type cenv e) v op G tn s` by
    (qpat_assum `(?ann op0. _) \/ (?ann p. _)` strip_assume_tac >>
     gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def] >> metis_tac[]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sm ee tv
      (LocatedValue (post_value_type cenv e) (mk_ptr (vv_operand vv) LocMemory)) s` by
    (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_assum `(?ann op0. _) \/ (?ann p. _)` strip_assume_tac >>
     gvs[vv_operand_def, vv_at_def, mk_ptr_def, expr_val_at_def, local_place_at_def] >>
     metis_tac[]) >>
  rpt BasicProvers.VAR_EQ_TAC >> rpt (conj_tac >- simp[]) >> qexists_tac `v` >>
  simp[wb_frame_refl, ghost_kept_at_def, cj 1 gas_origin_ptr_path_rules] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      `vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s` by
        (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` kall_tac >>
         qpat_assum `(?ann op0. _) \/ (?ann p. _)` strip_assume_tac >>
         qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         Cases_on `tv` >> simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def,
                                vv_place_ptr_mods_def, vv_place_ptr_def] >>
         TRY (rename1 `read_result cx (PlaceR pl) ee = _` >> Cases_on `pl` >> simp[]) >>
         rpt strip_tac >> first_x_assum irule >> simp[]) >>
      `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v) vv s` by
        (irule vv_post_vars_frame >> simp[] >> conj_tac
         >- fs[vv_post_def] >>
         qexistsl_tac [`s`, `sm`] >> simp[] >> metis_tac[vv_post_read_result]) >>
      simp[expr_post_mods_def] >> conj_tac
      >- (qpat_assum `(?ann op0. _) \/ (?ann p. _)` strip_assume_tac >>
          gvs[vv_operand_def] >>
          metis_tac[expr_post_of_vv_post_stack, expr_post_of_vv_post_memory]) >>
      fs[vv_post_mods_def])
  >- (irule vv_at_vars_frame >> simp[] >> metis_tac[]) >>
  qpat_assum `(?ann op0. _) \/ (?ann p. _)` strip_assume_tac >>
  gvs[vv_operand_def, vv_store_bound_def, expr_store_bound_def] >> metis_tac[]
QED
