(* Seam 2 joint induction, a family leaf of the agg step: attributes. *)
Theory bodyIntCallFamAggAttribute
Ancestors
  bodyIntCallFamAggAttributeTypedSupport
  bodyIntCallJointContract bodyIntCallJointAggCore bodyAttributeMemory
  exprSimFieldLayout exprSimAttributeProps bodyFieldMemoryProps
  loweringPosts exprSimVVFrame exprLoweringProps emitHelperProps
  compileEnv loweringStateRelDefs moduleLoweringProps venomState fragGasMode typedMemoryCopy instIdxIndep
  emitHelper exprSimAttribute exprSimDefs exprSimHypsDefs context
  exprSimUnwrap fragExec supportedExprs vyperTypeCallGraph stmtSimForced
  exprSimHyps vyperInterpreter vyperAST

Theorem attribute_add_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 ee sm s /\
  sa.cs_next_var <= sm.cs_next_var /\
  compile_expr ce ty e si = (vv,sm) /\
  local_ptrs_reserved ce si /\ si.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand vv; Lit (n2w off)] sm = (dst,sn) /\
  fn_has_code sm sn fp.jc_func /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sm t0 ee tv vv s /\
  eval_operand (vv_operand vv) s = SOME w ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es0 sa s0 ee sn u /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es si sn t0 ee tv vv u /\
    eval_operand (vv_operand vv) u = SOME w /\
    eval_operand dst u = SOME (w + n2w off) /\
    (!x. dst = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >> drule_all buffer_emit_add_run >> strip_tac >>
  drule_all attr_add_run_post >> strip_tac >>
  `~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
   s.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  drule_all attr_add_gas_path >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sm.cs_next_var <= sn.cs_next_var` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def, comp_ignore_bind_def] >>
     strip_tac >> gvs[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[gas_marked_path_from_mem, vv_post_inst_idx,
       eval_op_inst_idx] >>
  reverse conj_tac
  >- metis_tac[typed_copy_emit_op_fresh] >>
  gvs[] >>
  irule intcall_expr_cont_readonly >>
  simp[stmt_state_rel_inst_idx, update_var_def, same_blocks_def] >>
  conj_tac >- fs[vv_post_def, update_var_def] >>
  qexistsl_tac [`s`, `sm`] >>
  simp[lookup_var_update_not_fresh, update_var_def, lookup_var_def,
       venom_state_component_equality] >>
  rpt strip_tac >>
  fs[finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def]
QED

Theorem attribute_field_window:
  fields_layout fields fs /\ ALOOKUP fs fld = SOME ftv /\
  a <= w2n (w:bytes32) /\
  w2n w + type_memory_size_fields fs <= a + k /\
  a + k < dimword (:256) ==>
  a <= w2n (w + n2w (struct_field_offset fields fld)) /\
  w2n (w + n2w (struct_field_offset fields fld)) + type_memory_size ftv
    <= a + k
Proof
  strip_tac >> drule_all struct_field_offset_le >> strip_tac >>
  `w2n (w + n2w (struct_field_offset fields fld)) =
   w2n w + struct_field_offset fields fld` by
    (irule field_ptr_w2n >>
     qexistsl_tac [`type_memory_size ftv`, `type_memory_size_fields fs`] >>
     simp[]) >>
  simp[]
QED

Theorem attribute_selection_landing:
  intcall_frame_ok fp /\
  expr_body_pre ce fp.jc_cx env (Attribute ann obj fld) es /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv;
    Lit (n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld))]
    sm = (dst,sn) /\ fn_has_code sm sn fp.jc_func /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sm s0 ee tv bvv t /\
  intcall_expr_cont fp ce env es sa s0 ee sm t /\
  (!tvb. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce obj) = SOME tvb /\
     vv_loc bvv = LocMemory ==>
     ?w a k. eval_operand (vv_operand bvv) t = SOME w /\
       a <= w2n w /\ w2n w + type_memory_size tvb <= a + k /\
       a + k < dimword (:256) /\
       (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
  eval_expr fp.jc_cx obj (es with gas_obs := gs) = (INL tv,ee) ==>
  ?tv' u w.
    (!tail. select_result fp.jc_cx (expr_type obj) tv (AttrSubscript fld)
      (ee with gas_obs := tail) = (INL tv',ee with gas_obs := tail)) /\
    gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s0 ee sn u /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Attribute ann obj fld)
      es sa sn s0 ee tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u /\
    eval_operand (vv_operand bvv) t = SOME w /\
    eval_operand dst u = SOME
      (w + n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld)) /\
    (!x. dst = Var x ==> not_fresh_at sn x) /\
    (!ftv. evaluate_type (get_tenv fp.jc_cx) ann = SOME ftv /\
       vv_loc bvv = LocMemory ==>
       ?fw a k. eval_operand dst u = SOME fw /\
         a <= w2n fw /\ w2n fw + type_memory_size ftv <= a + k /\
         a + k < dimword (:256) /\
         (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z))
Proof
  strip_tac >> drule attr_pre_base >> strip_tac >>
  drule_all attr_select_field >> strip_tac >>
  `?w. eval_operand (vv_operand bvv) t = SOME w` by
    (fs[vv_post_def] >> Cases_on `bvv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  drule_all attribute_add_landing >> strip_tac >>
  `post_value_type ce obj = expr_type obj` by
    (irule attr_post_value_type >> metis_tac[]) >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx (Attribute ann obj fld)
      es sa sn s0 ee tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) u` by
    (irule attr_vv_post >> simp[] >> qexists_tac `tv` >> gvs[]) >>
  qexistsl_tac [`tv'`, `u`, `w`] >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  fs[valueEncodingTheory.type_memory_size_def] >>
  drule attribute_field_window >>
  disch_then (qspecl_then [`w`, `k`, `ftv`, `fld`, `a`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  simp[attr_offset_def] >>
  qexistsl_tac [`a`, `k`] >> simp[] >> metis_tac[]
QED

Theorem intcall_attribute_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base fld. e = Attribute a base fld) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >> rename1 `Attribute ann obj fld` >>
  reverse conj_tac
  >- (irule intcall_map_producer_other >> simp[]) >>
  rewrite_tac[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  drule attr_pre_base >> strip_tac >>
  drule compile_expr_attribute >> strip_tac >> gvs[] >>
  rename1 `compile_expr ce ty obj sa = (bvv,sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule attr_extends >> strip_tac >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `gas_admissible (eval_expr fp.jc_cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `intcall_expr_producer fp obj` by
    (first_x_assum (qspec_then `obj` mp_tac) >> simp[]) >>
  qpat_x_assum `intcall_expr_producer fp obj` mp_tac >>
  pure_rewrite_tac[intcall_expr_producer_def] >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`env`, `es`, `s`] mp_tac) >>
  (impl_tac >- (fs[int_calls_expr_def] >>
    metis_tac[supported_attribute_child])) >>
  strip_tac >>
  once_rewrite_tac[evaluate_def] >>
  irule forced_vv_then_outcome >>
  conj_tac >- simp[] >>
  gvs[] >> qmatch_assum_abbrev_tac `gas_outcome _ _ _ _ _ Q _` >>
  qexists_tac `\tv ee t. Q (INL tv) ee t` >>
  reverse conj_tac >- fs[Abbr `Q`] >>
  rpt gen_tac >> simp[Abbr `Q`] >> strip_tac >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sm s ee tv bvv t` by
    (gvs[vv_post_def, intcall_expr_cont_def, intcall_joint_res_def, intcall_expr_res_def] >>
     first_assum ACCEPT_TAC) >>
  `post_value_type ce obj = expr_type obj` by
    (irule attr_post_value_type >> metis_tac[]) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) attribute_selection_landing >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ (Attribute _ _ _) _`)) >>
  disch_then (qspecl_then [`sb`, `gs`, `p`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    Cases_on `bvv` >>
    gvs[vv_loc_def, vv_location_def, is_word_type_def, is_bytestring_type_def] >>
    qexistsl_tac [`a`, `k`] >> simp[] >>
    disj2_tac >> qexistsl_tac [`b`, `z`] >> simp[])) >>
  strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexistsl_tac [`INL tv'`, `ee`, `OK u`] >>
  gvs[vv_post_def, vv_operand_def, mk_ptr_def, expr_type_def]
QED
