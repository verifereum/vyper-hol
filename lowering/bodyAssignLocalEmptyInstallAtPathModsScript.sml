(* The empty saved operand updates only the selected subplace's header. *)
Theory bodyAssignLocalEmptyInstallAtPathMods
Ancestors
  bodyAssignLocalPreStoreMods bodyAssignLocalStoreCutsMods bodyAssignLocalInstallMods
  bodyQualifiedPlaceRhsPostMods bodyLocalEmptyWriteMods bodyLocalCopyWritesMods
  memoryLocalRhsProps bodyFullUnwrapRun emitHelperProps placeMemoryStateRebuild
  stateRelProj vyperStorageFootprint words loweringShapeRules venomState venomInst
  venomExecSemantics exprLoweringProps bodyAssignQualifiedStageJoinMods
  bodyAssignLocalPlaceRoutesMods loweringPosts exprSimProps bodyPtrDefs
  ptrDiscipline stmtSimDeclMem vyperTyping vyperState finite_map
  valueEncodingProps reasonCopySourcePtr

Theorem empty_subplace_history[local]:
  emit_void MSTORE [Var q;Lit 0w] st = ((),sb) /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  alloca_history func z /\ alloca_inv z /\
  z.vs_current_bb = st.cs_current_bb /\
  z.vs_inst_idx = LENGTH st.cs_current_insts /\ lookup_var q z = SOME a ==>
  alloca_history func
    (mstore (w2n a) 0w z with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `sb.cs_current_bb = st.cs_current_bb /\ sb.cs_current_insts =
    st.cs_current_insts ++ [mk_inst st.cs_next_id MSTORE [Var q;Lit 0w] []]` by
    gvs[emit_void_eq] >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [Var q;Lit 0w] []) z =
    OK (mstore (w2n a) 0w z)` by (irule step_MSTORE >> simp[eval_operand_def]) >>
  `run_inst_seq [mk_inst st.cs_next_id MSTORE [Var q;Lit 0w] []] z =
    OK (mstore (w2n a) 0w z)` by simp[run_inst_seq_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    [mk_inst st.cs_next_id MSTORE [Var q;Lit 0w] []]` by
    simp[mk_inst_def,is_terminator_def] >>
  drule_all emitted_alloca_history >> simp[]
QED

val rhs_post =
  ``qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0``;

Theorem assign_local_empty_install_at_path_mods:
  qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\ saved = NONE /\
  type_widens_to env.type_defs (expr_type e) dty /\
  local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
    (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw)
    ee st z Gz tz /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?t Gf tf. !H. valid_horizon cx st0 H ff.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (z,Gz,tz) [] (OK t,Gf,tf) /\
    local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx
      (ff with gas_obs := []) t Gf tf s0 sa es G0 tn0 (INL ())
Proof
  strip_tac >> gvs[] >>
  qhdtm_x_assum `local_assign_here_mods`
    (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
  qhdtm_x_assum `qualified_assign_rhs_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qhdtm_x_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP qualified_place_rhs_saved_view_mods)) >>
  gvs[] >>
  `has_length_word dty` by drule_all_then ACCEPT_TAC type_widens_to_has_length_word >>
  `32 <= type_memory_size ptv` by
    (mp_tac (Q.SPECL [`get_tenv cx`,`dty`,`ptv`,`w2n dw`,
      `(mstore (w2n dw) 0w z).vs_memory`] memory_length_word_layout) >>
     simp[mstore_mem_word_at_same]) >>
  `0 < type_memory_size ptv` by decide_tac >>
  qpat_x_assum `0 < _ ==> _` (drule_then strip_assume_tac) >>
  rename1 `FST dst = Var q` >>
  `dst = (Var q,SOME LocMemory,SOME (ValPT dty))` by metis_tac[] >>
  gvs[eval_operand_def] >>
  `emit_void MSTORE [Var q;Lit 0w] st = ((),sb)` by
    fs[qualified_assign_code_mods_def,assign_place_memory_store_code_mods] >>
  `w2n dw + 32 <= z.vs_alloca_next` by decide_tac >>
  `ptr_covers Gz tz q z 32` by metis_tac[ptr_covers_mono] >>
  suspend "store"
QED

Resume assign_local_empty_install_at_path_mods[store]:
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`PG` |-> `PG`, `ctx` |-> `ctx`, `typ` |-> `dty`,
             `lo` |-> `lo`, `v` |-> `default_value tyv`,
             `tenv` |-> `get_tenv cx`] local_empty_write_path_mods)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qabbrev_tac `t = mstore (w2n dw) 0w z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `tf = tz with t_mem := tz.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` >>
  qexistsl_tac [`t`,`Gz`,`tf`] >> gen_tac >> disch_tac >> conj_tac
  >- simp[] >>
  `ff.storage_trace = ee.storage_trace /\ ff.gas_obs = []` by
    (drule_then strip_assume_tac write_memory_place_entry_update >>
     qpat_assum `ff = _` (once_rewrite_tac o single) >> simp[]) >>
  `ff with gas_obs := [] = ff` by simp[evaluation_state_component_equality] >>
  asm_rewrite_tac [] >>
  `valid_horizon cx st0 H ee.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  suspend "install"
QED
Resume assign_local_empty_install_at_path_mods[install]:
  `alloca_inv z` by (drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `alloca_history func t` by
    (qpat_x_assum `w2n dw = _` kall_tac >> simp[Abbr `t`] >>
     irule empty_subplace_history >> simp[] >> qexistsl_tac [`q`,`st`] >> simp[]) >>
  `~block_is_terminated sb` by
    (drule_then irule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  `st.cs_next_var <= sb.cs_next_var` by
    drule_then (simp o single) emitted_insts_emit_void >>
  `w2n b + off = w2n dw` by decide_tac >>
  `typed_copy_state_frame st (w2n b + off) 32 z t` by
    (qpat_assum `w2n b + off = w2n dw` (pure_once_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  qpat_assum `write_place _ _ _ _ = _`
    (mp_then (Pat `write_place _ _ _ _ = _`) mp_tac
      (Q.INST [`bytes` |-> `32`] (INST_TYPE [alpha |-> ``:256``] assign_local_install_post_mods))) >>
  disch_then (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (fn th => qpat_assum `lookup_var p z = SOME b`
    (mp_then (Pat `lookup_var _ _ = SOME _`) mp_tac th)) >>
  disch_then (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`tf` |-> `tf`, `sb` |-> `sb`,
                              `lctx` |-> `lctx`, `Gf` |-> `Gz`] o SPEC_ALL) >>
  impl_tac >- suspend "install_premises" >>
  strip_tac >> gvs[local_assign_normal_at_cut_mods] >> first_assum ACCEPT_TAC
QED

Resume assign_local_empty_install_at_path_mods[install_premises]:
  conj_tac >- (strip_tac >> irule local_copy_immutable_frame_mods >>
    goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
    goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >> simp[]) >>
  simp[default_value_well_typed, ret_pc_ok_def, Abbr `tf`, op_taint_def] >>
  conj_tac
  >- (`off + (w2n b + 32) = w2n dw + 32` by decide_tac >>
      qpat_assum `off + (w2n b + 32) = _` (pure_once_rewrite_tac o single) >>
      qpat_assum `w2n dw = off + w2n b` (pure_once_rewrite_tac o single o SYM) >>
      qpat_assum `!m. mem_agree_outside _ t.vs_memory m ==> _` mp_tac >>
      simp_tac (srw_ss()) []) >>
  rpt gen_tac >> disch_tac >>
  qhdtm_assum `ret_pc_ok` (drule_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [ret_pc_ok_def])
QED
Finalise assign_local_empty_install_at_path_mods
