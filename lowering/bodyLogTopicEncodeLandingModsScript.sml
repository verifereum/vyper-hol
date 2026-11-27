(* A restored indexed argument is encoded at its actual compiler cursor. *)
Theory bodyLogTopicEncodeLandingMods
Ancestors
  bodyFullLogSuffix bodyExtractSavedDescriptorMods bodyForRangeScalarFrameMods
  bodyFullPathHistory bodyFullPostsMods bodyFullShadowBodyInv
  stmtSimLogTopics stmtSimLogSource stmtSimLogArgs exprSimHashBoundary
  exprSafeOperand exprLoweringProps exprSimHypsDefs exprSimWordArgs
  valueCopyBytes valueEncodingProps wordArgsPtr
  loweringPosts loweringStateRelDefs bodyPtrDefs compileEnv stmtLowering context
  vyperEvent vyperStorageTrace vyperStorageFootprint fragGasOriginPtr venomState

(* Only the hash branch needs a local-window argument. Its physical type is
   a base bytestring or string even when the containing local is qualified. *)
Theorem log_hash_arg_clear_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\ is_bytestring_type ty ==>
  log_arg_clear cenv cx ty v
Proof
  strip_tac >> simp[log_arg_clear_def] >> rpt gen_tac >> strip_tac >>
  drule_all bytestring_type_value >> strip_tac >>
  gvs[] >> drule_all_then ACCEPT_TAC extract_local_window_apart
QED

Theorem log_topic_readonly_state_mods[local]:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx es (t with vs_inst_idx := s.vs_inst_idx)` suffices_by
    simp[stmt_state_rel_inst_idx] >>
  irule hash_readonly_state_rel >> qexistsl [`s`,`sm`] >>
  fs[lookup_var_def, venom_state_component_equality]
QED

Theorem log_topic_encode_landing_mods:
  local_ptrs_reserved cenv sm /\ expr_sim_inv_mods mods cenv cx env es /\
  expr_val_rel cx ty v src s /\ expr_val_at cenv cx ty sa sm es v src s /\
  supported_event_leaf_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ encode_event_topic ty v = SOME topic /\
  safe_operand sm src /\
  compile_encode_log_topic src (is_bytestring_type ty) sm = (op,sb) /\
  ptr_val_ok cx ty v src G tn s /\ expr_store_bound cx ty v src s /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t /\ immutable_frame_mods func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es Gf tf t) /\
    wb_frame cenv es es sm s t /\ ghost_kept_at lo cenv es sm G tn s Gf tf /\
    alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    safe_operand sb op /\ eval_operand op t = SOME topic /\ op_taint tf op = {} /\
    (!x. not_fresh_at sm x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `is_bytestring_type ty`)
  >- (drule_all_then assume_tac log_event_word_topic >>
      `is_word_type ty` by (drule log_event_topic_shape >> simp[]) >>
      `eval_operand src s = SOME topic` by fs[expr_val_rel_def] >>
      gvs[compile_encode_log_topic_def, comp_return_def, ptr_val_ok_def] >>
      qexistsl [`s`,`G`,`tn`] >>
      simp[gas_origin_ptr_path_rules, wb_frame_refl, ghost_kept_at_refl,
           venom_state_component_equality] >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC) >>
  qpat_assum `?H. valid_horizon cx st0 H es.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `hz` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `log_arg_rel cenv cx sa sm es s (src,ty) v` by
    (simp[log_arg_rel_def] >> drule_all log_hash_arg_clear_mods >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  qpat_x_assum `safe_operand sm src`
    (strip_assume_tac o REWRITE_RULE [safe_operand_def]) >>
  drule_all compile_log_hash_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "frame"
QED

Resume log_topic_encode_landing_mods[frame]:
  drule_all log_topic_frontier >> strip_tac >>
  qpat_x_assum `(!x sz. cenv.ce_return_buf = _ ==> _) /\ _ ==> _` kall_tac >>
  qpat_assum `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `alloca_history func t` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK t,Gf,tf)`
       (qspec_then `DF hz` (mp_then Any irule body_full_path_alloca_history)) >>
     asm_rewrite_tac[]) >>
  `sm.cs_current_bb = sb.cs_current_bb` by
    (qpat_assum `t.vs_current_bb = sb.cs_current_bb` mp_tac >> simp[]) >>
  `safe_operand sb op` by simp[safe_operand_def] >>
  qexistsl [`t`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule log_topic_readonly_state_mods >> qexistsl [`s`,`sm`] >>
      asm_rewrite_tac[] >> rpt strip_tac >>
      qpat_assum `!p. not_fresh_at sm p ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >> qexistsl [`es`,`s`,`sm`] >>
      asm_rewrite_tac[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  irule ghost_inv_at_mods_exterior_frame >> qexistsl [`G`,`es`,`s`,`sm`,`tn`] >>
  asm_rewrite_tac[]
QED

Finalise log_topic_encode_landing_mods
