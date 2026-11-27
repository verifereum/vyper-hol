(* A copied nonword keeps its registered memory allocation across the suffix. *)
Theory bodyExtOwnedRowEndpointMods
Ancestors
  bodyFullExtCallPosTransport bodyFullPostsMods allocaSiteResource
  exprSimProps exprSimHypsDefs loweringPosts loweringStateRelDefs bodyPtrDefs
  exprLowering compileEnv context venomState

Theorem ext_owned_row_endpoint_mods:
  compile_snapshot_vv cenv T (ext_call_arg_value (lowered_value_type cenv e) vv)
    sm = (LocatedValue (lowered_value_type cenv e) p,ss) /\
  ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory /\
  p.ptr_operand = Var x /\ eval_operand p.ptr_operand u = SOME w /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  val_wf tv v /\ FLOOKUP u.vs_allocas sm.cs_next_id =
    SOME (w2n w,type_memory_size tv) /\
  si.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < ss.cs_next_id /\
  (!n b len. local_region cenv pos.scopes u n b len ==>
    regions_disjoint (w2n w) (type_memory_size tv) b len) /\
  (?raw. read_result cx raw pos = (INL v,pos) /\
    vv_holds_mods cenv cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) pos u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) pos Gp tp u) /\
  ptr_buf_ok cenv e p.ptr_operand Gp u /\ not_fresh_at ss x /\
  wb_frame cenv pos ee ss u t /\ ghost_kept_at lo cenv pos ss Gp tp u G tn /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ alloca_inv u /\
  (!n b len. local_region cenv pos.scopes u n b len <=>
    local_region cenv ee.scopes t n b len) ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) ee t /\
    vv_at cenv cx (lowered_value_type cenv e) si ss ee raw
      (LocatedValue (lowered_value_type cenv e) p) t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw
      (LocatedValue (lowered_value_type cenv e) p) ee G tn t /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw
      (LocatedValue (lowered_value_type cenv e) p) t) /\
  ptr_buf_ok cenv e p.ptr_operand G t /\
  (?q w tv. vv_location (LocatedValue (lowered_value_type cenv e) p) = SOME LocMemory /\
    vv_operand (LocatedValue (lowered_value_type cenv e) p) = Var q /\
    eval_operand (vv_operand (LocatedValue (lowered_value_type cenv e) p)) t = SOME w /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    val_wf tv v /\ FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    sm.cs_next_id < ss.cs_next_id /\
    (!n b len. local_region cenv ee.scopes t n b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len))
Proof
  strip_tac >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
   lowered_value_type cenv e` by
    (Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` >>
     qpat_x_assum `compile_snapshot_vv cenv T _ sm = _` mp_tac >>
     simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  `ptr_val_ok cx (lowered_value_type cenv e) v (Var x) Gp tp u /\
   val_in_memory tv v (w2n w) u.vs_memory` by
    gvs[vv_holds_mods_def, vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  `lookup_var x u = SOME w` by
    (qpat_x_assum `eval_operand p.ptr_operand u = SOME w` mp_tac >>
     simp[eval_operand_def]) >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next` by
    (drule_all_then ACCEPT_TAC alloca_site_registered_below) >>
  `!n b len. local_region cenv ee.scopes t n b len ==>
    local_region cenv pos.scopes u n b len` by metis_tac[] >>
  CONV_TAC (REWR_CONV CONJ_ASSOC) >> reverse conj_tac
  >- (qexistsl_tac [`x`,`w`,`tv`] >>
      simp[vv_operand_def, vv_location_def, eval_operand_def] >> metis_tac[]) >>
  simp[vv_holds_mods_def, GSYM LEFT_EXISTS_AND_THM] >>
  qexists_tac `Value v` >> pure_rewrite_tac[GSYM CONJ_ASSOC] >>
  irule (Q.INST [`cut` |-> `ss`, `a` |-> `sm`, `aid` |-> `sm.cs_next_id`,
                 `sz` |-> `type_memory_size tv`] extcall_request_materialized_endpoint) >>
  gvs[vv_operand_def, regions_disjoint_def] >>
  qexistsl_tac [`Gp`, `ext_call_arg_value (lowered_value_type cenv e) vv`,
                `lo`, `pos`, `sm`, `u`, `tp`, `w`] >>
  simp[val_footprint_le] >> first_assum ACCEPT_TAC
QED
