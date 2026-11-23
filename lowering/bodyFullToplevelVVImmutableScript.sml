(* Raw TopLevelName immutable judgment, conditional on the ctor source interface. *)
Theory bodyFullToplevelVVImmutable
Ancestors
  bodySimFull bodySim exprSimSource gasOutcomeFullCompose
  exprSimTopLevelImmutable exprSimHypsDefs exprLoweringProps exprLowering
  loweringPosts bodyPtrDefs accountsRelProps fragGasPathPtr context words
  finite_map pred_set list vyperInterpreter vyperState vyperAST exprSimHyps
  exprSimDefs loweringStateRelDefs fragGasOriginPtr exprSimMemDefs
  bodyFullToplevelVVNil

Theorem toplevel_immutable_vv_nil_from_contract:
  (!tops ctx cenv cx env ann id es H D lo func s d G tn src off imms rt v.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
    cenv.ce_is_ctor /\ dead_lo_ok
      (H : (bool # 256 word # type_value) list # num list) D lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at D lo d cenv cx es G tn s /\ src = cenv.ce_module /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ann = SOME rt ==>
    off + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory rt v off mem)) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
  toplevel_vv_nil (DF,lo,d,ctx,func)
    cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  rw[toplevel_vv_nil_def] >>
  drule_all toplevel_immutable_lookup >> strip_tac >> gvs[] >>
  drule compile_toplevel_immutable_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  qexistsl_tac [`PlaceR (ImmutablePlace cenv.ce_module id [])`, `es`] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
       get_immutables_def, get_address_immutables_def, lift_option_type_def,
       return_def, raise_def] >> rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> strip_tac >>
  suspend "posts"
QED

Resume toplevel_immutable_vv_nil_from_contract[posts]:
  markerLib.RESUME_TAC >>
  simp[mk_ptr_def, vv_location_def, vv_operand_def, expr_type_def,
       ghost_kept_at_def, gas_origin_ptr_path_rules, vv_store_bound_nonmem,
       ptr_vv_ok_def, ptrDisciplineTheory.op_taint_def] >>
  all_tac >~ [`read_result _ _ _`]
  >- (qpat_x_assum `!tops ctx cenv cx env ann id es H D lo func s d G tn off imms rt v. _` drule >>
      disch_then drule >>
      simp[] >>
      strip_tac >>
      qpat_x_assum `!H. dead_lo_ok H (DF H) _ _ _` (qspec_then `H` assume_tac) >>
      `off + type_memory_size tv <= lo /\
       !mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
         val_in_memory tv v off mem` by
        (first_x_assum irule >> goal_assum (drule_at Any) >>
         qexistsl [`G0`, `d`, `func`] >> simp[]) >>
      `off < dimword (:256)` by decide_tac >>
      qexists `v` >>
      simp[read_result_def, read_place_def, get_immutables_def,
           get_address_immutables_def, lift_option_type_def, bind_def,
           return_def, evaluate_subscripts_def, lift_sum_def,
           venomStateTheory.eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  suspend "ordinary"
QED

Resume toplevel_immutable_vv_nil_from_contract[ordinary]:
  markerLib.RESUME_TAC >> gvs[mk_ptr_def] >>
  all_tac >~ [`ghost_inv_at _ _ _ _ _ (es with gas_obs := []) _ _ _`]
  >- (simp[ghost_inv_at_def] >> metis_tac[ghost_inv_at_def]) >>
  irule (SRULE [mk_ptr_def] toplevel_immutable_post) >> simp[]
QED

Finalise toplevel_immutable_vv_nil_from_contract

Theorem toplevel_immutable_vv_full_from_contract:
  (!tops ctx cenv cx env ann id es H D lo func s d G tn src off imms rt v.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
    cenv.ce_is_ctor /\ dead_lo_ok
      (H : (bool # 256 word # type_value) list # num list) D lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at D lo d cenv cx es G tn s /\ src = cenv.ce_module /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ann = SOME rt ==>
    off + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory rt v off mem)) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >> irule toplevel_vv_nil_full >> irule toplevel_immutable_vv_nil_from_contract >>
  simp[] >> metis_tac[]
QED
