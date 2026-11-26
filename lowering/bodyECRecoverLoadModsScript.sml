(* The successful ECRecover continuation reads the output word without
   changing the allocation or any linked module's immutable memory. *)
Theory bodyECRecoverLoadMods
Ancestors
  bodyForRangeScalarFrameMods exprSimPrecompiles decoderNavigationPtr
  decoderSetupStepPtr exprSimWordArgs exprPtrCtorImmStore
  instMemFrontier unitTransformDefs allocaHistory fragExec emitHelperProps
  exprLoweringProps bodyFullShadowBodyInv bodyFullPostsMods bodyPtrDefs
  loweringPosts loweringStateRelDefs valueEncodingProps memSafeRun
  venomState venomInst vyperValue compileEnv finite_map words

Theorem ecrecover_loaded_word[local]:
  mem_word_at (w2n wo) before.vs_memory = 0w /\
  s.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) before).vs_memory /\
  data = (case a of NONE => [] | SOME x => PAD_LEFT 0w 32 (word_to_bytes x T)) ==>
  mload (w2n wo) s = typed_val_to_w256 (BaseTV AddressT)
    (AddressV (case a of NONE => 0w | SOME x => x))
Proof
  strip_tac >> simp[GSYM mem_word_at_eq_mload] >>
  irule ecrecover_output_write >> Cases_on `a` >> simp[]
QED

Theorem ecrecover_load_mods:
  emit_op MLOAD [Var qo] cq = (op,sb) /\ fn_has_code cq sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = cq.cs_current_bb /\
  s.vs_inst_idx = LENGTH cq.cs_current_insts /\
  lookup_var qo s = SOME wo /\ ptr_covers G tn qo s 32 /\
  w2n wo + 32 <= s.vs_alloca_next /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) /\
  mem_word_at (w2n wo) before.vs_memory = 0w /\
  s.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) before).vs_memory /\
  data = (case a of NONE => [] | SOME x => PAD_LEFT 0w 32 (word_to_bytes x T)) /\
  local_ptrs_reserved ce cq /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at cq x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at cq x) /\
  immutable_frame_mods func ce cx es s /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es s /\
       ghost_inv_at_mods (DF H) lo d ce cx es G tn s) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    expr_val_rel cx (BaseT AddressT) (AddressV (case a of NONE => 0w | SOME x => x)) op t /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_data_section = s.vs_data_section /\
    tn'.t_mem = tn.t_mem /\
    (!x. not_fresh_at cq x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    immutable_frame_mods func ce cx es t /\ wb_frame ce es es cq s t /\
    ghost_kept_at lo ce es cq G tn s G' tn' /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func ce cx es t /\
         ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t)
Proof
  strip_tac >>
  drule emit_op_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString cq.cs_next_var)` >> gvs[] >>
  qabbrev_tac `i = mk_inst cq.cs_next_id MLOAD [Var qo] [out]` >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i` by
    (drule_all fn_has_code_same_block >>
     disch_then (qx_choose_then `bb` strip_assume_tac) >> qexists_tac `bb` >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `u = update_var out (mload (w2n wo) s) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G' = step_prov PG G i u` >>
  qabbrev_tac `tn' = step_taint i s u tn` >>
  `eval_operand (Var qo) s = SOME wo` by simp[eval_operand_def] >>
  `step_inst_base i s = OK u` by (drule step_MLOAD >> simp[Abbr `i`, Abbr `u`]) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >>
  conj_tac >- suspend "path" >>
  conj_tac >- simp[Abbr `t`, Abbr `u`, update_var_def] >>
  conj_tac >- simp[Abbr `t`] >>
  conj_tac >- simp[Abbr `t`, Abbr `u`, update_var_def] >>
  conj_tac >- (simp[Abbr `t`] >> drule_all alloca_history_base_step >>
               simp[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  conj_tac >- suspend "word" >>
  suspend "frame"
QED

Resume ecrecover_load_mods[path]:
  `inst_mem_below_frontier i s` by simp[Abbr `i`, below_frontier_MLOAD] >>
  gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn i s` by
     (simp[Abbr `i`] >> irule ptr_inst_ok_mload_lo >> simp[]) >>
  simp[NoAsms, Abbr `t`, Abbr `G'`, Abbr `tn'`] >>
  irule straight_line_step_origin >>
  `i.inst_opcode = MLOAD` by simp[Abbr `i`, mk_inst_def] >>
  gvs[is_terminator_def, inst_dload_in_section_def, dalloca_no_wrap_def]
QED

Resume ecrecover_load_mods[word]:
  `mload (w2n wo) s = typed_val_to_w256 (BaseTV AddressT)
      (AddressV (case a of NONE => 0w | SOME x => x))` by
    (irule ecrecover_loaded_word >> qexistsl_tac [`before`,`case a of
       NONE => [] | SOME x => PAD_LEFT 0w 32 (word_to_bytes x T)`] >> simp[]) >>
  simp[expr_val_rel_def, Abbr `t`, Abbr `u`, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, evaluate_type_def,
       is_word_type_def]
QED

Resume ecrecover_load_mods[frame]:
  `op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
   u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_allocas = s.vs_allocas /\
   tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!x. x <> out ==> lookup_var x u = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))` by
    (irule setup_mload_ghost >> qexistsl_tac [`PG`,`wo`,`cq.cs_next_id`,`qo`] >>
     simp[Abbr `G'`, Abbr `tn'`, Abbr `i`, Abbr `u`]) >>
  `!x. not_fresh_at cq x ==> x <> out` by simp[Abbr `out`, not_fresh_at_def] >>
  `!x. not_fresh_at cq x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[Abbr `t`, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  `not_local_ptr ce es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `cq` >> simp[]) >>
  `immutable_frame_mods func ce cx es t` by
    (irule immutable_frame_mods_exterior_frame >>
     qexistsl_tac [`es`,`s`,`cq`] >>
     simp[Abbr `t`, Abbr `u`, update_var_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[Abbr `t`]) >>
  `wb_frame ce es es cq s t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`cq`,`s`] >>
     simp[wb_frame_refl, Abbr `t`, Abbr `u`, update_var_def] >>
     metis_tac[lookup_var_def]) >>
  `ghost_kept_at lo ce es cq G tn s G' tn'` by simp[ghost_kept_at_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es t /\
       ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     conj_tac
     >- (simp[Abbr `t`, Abbr `u`, stmt_state_rel_inst_idx] >>
         irule stmt_state_rel_update_var >> simp[]) >>
     irule ghost_inv_at_mods_exterior_frame >>
     qexistsl_tac [`G`,`es`,`s`,`cq`,`tn`] >>
     simp[Abbr `t`, Abbr `u`, update_var_def] >> metis_tac[lookup_var_def]) >>
  simp[Abbr `t`, Abbr `u`, update_var_def]
QED

Finalise ecrecover_load_mods
