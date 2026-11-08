Theory bodyPtrTypeBuiltinsExtract32HeaderFrame
Ancestors
  bodyPtrSignedConvertSourceFrame exprSimExtract32Post exprSimCopy
  exprSimWordArgs loweringPosts exprLoweringProps compileEnv venomState
  exprSimExtract32Read fragExec rich_list

Theorem extract32_prepare_post_readonly:
  expr_post ctx func cenv cx src es sa sm s0 ee (BytesV bs) op s /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_id <= sb.cs_next_id /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  eval_operand op t = eval_operand op s ==>
  expr_post ctx func cenv cx src es sa sb s0 ee (BytesV bs) op t
Proof
  strip_tac >>
  `post_value_type cenv src = expr_type src` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!scopes n b sz. local_region cenv scopes t n b sz <=>
      local_region cenv scopes s n b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sm` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`s`,`sm`] >> gvs[expr_post_def]) >>
  `wb_frame cenv es sa s0 t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sm`,`s`] >>
     simp[] >> metis_tac[expr_post_frame]) >>
  `expr_val_at cenv cx (expr_type src) sa sb ee (BytesV bs) op t` by
    (gvs[expr_post_def, expr_val_at_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >> qexists_tac `w` >> simp[] >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  gvs[expr_post_def, wb_frame_def, expr_val_rel_def] >> gvs[]
QED

Theorem extract32_prepare_site:
  compile_bytestring_src op sm = ((len,dp),sb) /\ fn_has_code sm sb func ==>
  sm.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  ?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
    !j. j < LENGTH (emitted_insts sm sb) ==>
      get_instruction bb (LENGTH sm.cs_current_insts+j) =
        SOME (EL j (emitted_insts sm sb))
Proof
  strip_tac >>
  `ci_mono sm sb` by
    (qspec_then `op` (qspec_then `sm` mp_tac) ci_mono_compile_bytestring_src >>
     simp[]) >>
  drule_at (Pos (el 2)) extract32_read_code_shape >>
  simp[extract32_read_prepare] >> strip_tac >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  simp[] >> conj_tac >- gvs[ci_mono_def] >>
  drule_all fn_has_code_same_block >>
  simp[arithmeticTheory.ADD_COMM]
QED
