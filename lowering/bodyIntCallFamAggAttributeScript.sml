(* Seam 2 joint induction, a family leaf of the agg step: attributes. *)
Theory bodyIntCallFamAggAttribute
Ancestors
  bodyIntCallJointContract bodyIntCallJointAggCore bodyAttributeMemory
  exprSimFieldLayout exprSimAttributeProps bodyFieldMemoryProps
  loweringPosts exprSimVVFrame exprLoweringProps emitHelperProps
  compileEnv moduleLoweringProps venomState fragGasMode typedMemoryCopy instIdxIndep
  emitHelper

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

Theorem intcall_attribute_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  (?a base fld. e = Attribute a base fld) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  cheat
QED
