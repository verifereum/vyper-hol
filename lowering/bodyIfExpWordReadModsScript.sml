(* Forcing the selected word arm, without changing the selected module frame. *)
Theory bodyIfExpWordReadMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyFullUnwrapRun bodyFullPathHistory bodyPtrSignedConvertSourceFrame
  exprSimBopRestWordLoadPath exprSimBopRestWordLoadSafety
  exprPtrUnwrapLoad exprPtrUnwrapStorage exprPtrUnwrapLoadSegment
  exprPtrCtorCodeLoad exprPtrCodeCopyLoad exprPtrCtorImmStore
  fragGasOriginPtrDead representationCleanPtr exprSimIfExp
  reasonSourceProps loweringPosts loweringStateRelDefs exprSimUnwrapProps
  exprOperandVar bodyInvSplit bodyPtrDefs ptrDiscipline exprSimProps freshWrites
  emitHelperProps exprLoweringProps exprLowering compileEnv context
  vyperStorageFootprint vyperState vyperAST venomInst venomState
  finite_map arithmetic words list memSafeRun exprSimCopy venomExecSemantics
  fragGasSeqPtr ptrSafeRun slotCopyExecution exprSimMemDefs exprPtrUnwrapFacts
  assignTuplePtrLoadStep immutableCopyExecution exprSimAttribute stateRelProj
  valueEncodingDefs valueEncodingProps fragGasOriginPtr pred_set

Theorem word_arm_immutables[local]:
  immutable_frame_mods func ce cx ee s /\ local_ptrs_reserved ce sm /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) ==>
  immutable_frame_mods func ce cx ee u
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  simp[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutable_frame_mods_def,immutables_rel_mods_def,immutables_rel_def] >>
      first_assum ACCEPT_TAC) >>
  fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >> qexistsl [`s`,`ee`] >>
  simp[] >> rpt strip_tac >> qexists `id` >>
  qmatch_asmsub_rename_tac `local_region (ce with ce_module := src) _ _ _ _ _` >>
  `local_region (ce with ce_module := src) ee.scopes u id b sz <=>
   local_region (ce with ce_module := src) ee.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >> metis_tac[local_ptrs_reserved_def]) >>
  gs[]
QED

Theorem word_arm_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\ local_ptrs_reserved ce sm /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm ==>
  ghost_inv_at_mods D lo d ce cx ee Gf tf u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sm p /\ ptr_covers G tn p s sz ==>
          ptr_covers Gf tf p u sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem word_arm_value_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) ==>
  expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op u
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule word_arm_immutables >> qexistsl [`s`,`sm`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  rewrite_tac[expr_post_mods_def, expr_post_def, post_value_type_def, expr_type_def] >>
  simp[expr_val_rel_def,expr_val_at_def,expr_val_own_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
               conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> fs[]
QED

(* The physical slice determines the endpoint before any horizon is chosen. *)
Theorem word_arm_loaded_path[local]:
  compile_ptr_load ctor imm loc addr sm = (op,sb) /\ loc <> LocCalldata /\
  eval_operand addr s = SOME w /\
  ((loc = LocMemory \/ (loc = LocCode /\ ctor)) ==>
    w2n w + 32 <= s.vs_alloca_next) /\
  (loc = LocCode /\ ~ctor ==> w2n w <= LENGTH s.vs_data_section) /\
  (loc = LocCode /\ ctor /\ imm <> NONE ==> eval_operand (THE imm) s = SOME 0w) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\ alloca_inv s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
  run_inst_seq (emitted_insts sm sb) s = OK q /\
  eval_operand op q = SOME value /\
  (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s) ==>
  ?u. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
      u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
      eval_operand op u = SOME value /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u
Proof
  strip_tac >> drule_all_then strip_assume_tac rest_word_ptr_load_code >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode /\ i.inst_opcode <> DALLOCA)
    (emitted_insts sm sb)` by
    (simp[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `EVERY (\i. MEM _ _) _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (irule rest_word_ptr_load_mem_ok >>
     qexistsl [`w`,`addr`,`ctor`,`imm`,`loc`,`op`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `q = s with vs_vars := q.vs_vars` by
    (drule_all_then strip_assume_tac rest_word_ptr_load_run_frame >> simp[]) >>
  qexists `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (irule emitted_origin_ptr_path >> conj_tac >- simp[] >>
      qexistsl [`emitted_insts sm sb`,`sm`] >>
      simp[] >> reverse conj_tac >- fs[EVERY_MEM] >>
      rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >> fs[EVERY_APPEND, EVERY_MEM]) >>
  conj_tac >- (qpat_assum `q = s with vs_vars := _` (fn th => simp[Once th])) >>
  conj_tac >- (Cases_on `op` >> fs[eval_operand_def,lookup_var_def]) >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- (qpat_assum `q = s with vs_vars := _` (fn th => simp[Once th])) >>
  conj_tac >- simp[] >>
  irule emitted_alloca_history >> conj_tac >- simp[] >>
  qexistsl [`emitted_insts sm sb`,`s`,`sm`] >> fs[EVERY_MEM]
QED

(* Code-backed arm operands can be computed offsets. The same machine load
   covers both literal and computed operands. *)
Theorem word_arm_code_packet[local]:
  compile_imm_load_word ctor imm addr sm = (op,sb) /\
  copy_old_operand sm addr /\ eval_operand addr s = SOME w /\
  op_taint tn addr = {} /\ op_prov G addr = NONE /\
  (ctor ==> w2n w + 32 <= lo /\ mem_word_taint tn.t_mem (w2n w) = {} /\
    !base. imm = SOME base ==> eval_operand base s = SOME 0w /\
      copy_old_operand sm base /\ op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK q /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    eval_operand op q = SOME (immutable_copy_read ctor w s) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  Cases_on `ctor` >> simp[] >> strip_tac
  >- (drule_all_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) code_copy_ctor_load >>
      qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `s.vs_inst_idx` mp_tac) >>
      simp[venom_state_component_equality] >> strip_tac >>
      fs[copy_runtime_frame_def] >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all_then (qspecl_then [`func`,`PG`,`G`,`D`] strip_assume_tac) code_copy_runtime_load >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` mp_tac) >>
  simp[venom_state_component_equality] >> strip_tac >>
  fs[copy_runtime_frame_def] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem word_arm_memory_packet[local]:
  emit_op MLOAD [Var src] sm = (op,sb) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK q /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    eval_operand op q = SOME (mload (w2n w) s) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_op >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `q = update_var out (mload (w2n w) s) s` >>
  `run_inst_seq [mk_inst sm.cs_next_id MLOAD [Var src] [out]] s = OK q` by
    simp[Abbr `q`, run_inst_seq_def, mk_inst_def, step_inst_base_opcode_eqs,
         exec_read1_def, eval_operand_def] >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (simp[Abbr `out`, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `?Gf tf.
    (!k. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst sm.cs_next_id MLOAD [Var src] [out]] (s with vs_inst_idx := k) Gf tf) /\
    op_taint tf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))` by
    (qpat_assum `run_inst_seq [_] s = OK q` (mp_then Any mp_tac ctor_mload_segment) >>
     disch_then (qspecl_then [`w`,`tn`,`lo`,`func`,`ctx`,`PG`,`not_fresh_at sm`,`G`,`D`] mp_tac) >>
     simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >> qexistsl [`Gf`,`tnf`] >> simp[]) >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` mp_tac) >>
  simp[venom_state_component_equality] >> strip_tac >>
  qexistsl [`q`,`Gf`,`tf`] >> simp[Abbr `q`, GSYM markerTheory.Abbrev_def,
     eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >> simp[]
QED

Theorem word_arm_slot_packet[local]:
  emit_op (if tr then TLOAD else SLOAD) [addr] sm = (op,sb) /\
  eval_operand addr s = SOME w /\ op_taint tn addr = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?q Gf tf.
    run_inst_seq (emitted_insts sm sb) s = OK q /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    eval_operand op q = SOME (if tr then tload w s else sload w s) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_then strip_assume_tac emitted_insts_emit_op >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `ld = if tr then TLOAD else SLOAD` >>
  mp_tac (Q.INST [`load` |-> `ld`, `id` |-> `sm.cs_next_id`, `out` |-> `out`,
    `fn` |-> `func`, `PG` |-> `PG`, `G` |-> `G`, `D` |-> `D`, `key` |-> `w`,
    `arg` |-> `addr`] copy_slot_load_segment) >>
  (impl_tac >- (Cases_on `tr` >> fs[Abbr `ld`])) >> strip_tac >>
  qexistsl [`t`,`Gf`,`tnf`] >>
  `!x. not_fresh_at sm x ==> x <> out` by
    (simp[Abbr `out`, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `op_prov Gf (Var out) = NONE` by
    (`step_inst_base (mk_inst sm.cs_next_id ld [addr] [out]) s = OK t` by
       (qpat_x_assum `run_inst_seq [_] s = OK t` mp_tac >>
        simp[run_inst_seq_def, AllCaseEqs()]) >>
     qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[inst_seq_ptr_def] >> strip_tac >> irule step_prov_out_none >>
     simp[mk_inst_def] >> irule out_prov_other_none >> Cases_on `tr` >> simp[Abbr `ld`,mk_inst_def]) >>
  Cases_on `tr` >> fs[Abbr `ld`, slot_copy_word_def, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem word_arm_noncode_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location <> LocCode ==>
  vv_post H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `vv_place_ptr ce cx ee s tv (LocatedValue t p)` by
    (Cases_on `tv` >> fs[vv_place_ptr_mods_def, vv_place_ptr_def] >>
     rename1 `PlaceR pl` >> Cases_on `pl` >> fs[vv_place_ptr_mods_def, vv_place_ptr_def]) >>
  fs[vv_post_def, vv_holds_mods_def] >>
  conj_tac >- (qpat_x_assum `if p.ptr_location = LocCode then _ else _` mp_tac >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem word_arm_endpoint_frame[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm ==>
  expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op u /\
  ghost_inv_at_mods D lo d ce cx ee Gf tf u /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  strip_tac >> conj_tac
  >- (irule word_arm_value_post >> simp[] >>
      qexistsl [`e`,`s`,`sm`,`tv`,`vv`] >> simp[] >> fs[] >> metis_tac[]) >>
  conj_tac
  >- (irule word_arm_ghost >> qexistsl [`G`,`s`,`sm`,`tn`] >> simp[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]
QED

(* The word read and its physical instruction packet are independent of H. *)
val arm_word_packet = ``
    read_result cx tv ee = (INL v,ee) /\
    eval_operand p.ptr_operand s = SOME w /\
    ((p.ptr_location = LocMemory \/ (p.ptr_location = LocCode /\ ce.ce_is_ctor)) ==>
      w2n w + 32 <= s.vs_alloca_next) /\
    (p.ptr_location = LocCode /\ ~ce.ce_is_ctor ==> w2n w <= LENGTH s.vs_data_section) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor /\ ce.ce_imm_alloca <> NONE ==>
      eval_operand (THE ce.ce_imm_alloca) s = SOME 0w) /\
    run_inst_seq (emitted_insts sm sb) s = OK q /\
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
    eval_operand op q = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))``;

Theorem word_arm_loc_memory[local]:
  vv_post H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ is_word_type t /\ post_value_type ce e = t /\
  ptr_vv_ok cx t tv (LocatedValue t p) ee G tn s /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_store_bound cx t (lowered_value_type ce e) ee tv (LocatedValue t p) s /\
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v w q Gf tf. ^arm_word_packet
Proof
  strip_tac >> drule unwrap_memory_word_input >> simp[] >>
  disch_then drule >> strip_tac >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (drule_all_then (qspec_then `v` strip_assume_tac) word_value_memory_extent >>
     qpat_assum `vv_store_bound _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_store_bound_def]) >>
     qpat_x_assum `!vt op v tvt w. _` (qspecl_then [`t`,`Var src`,`v`,`rt`,`w`] mp_tac) >>
     simp[]) >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> gen_tac >>
     Cases_on `x < 32` >> simp[] >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` (qspec_then `x + w2n w` mp_tac) >>
     `w2n w <= x + w2n w /\ x + w2n w < w2n w + 32` by decide_tac >> simp[]) >>
  `emit_op MLOAD [Var src] sm = (op,sb)` by
    (qpat_x_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >> simp[compile_ptr_load_def]) >>
  drule_all word_arm_memory_packet >> simp[]
QED

Theorem word_arm_loc_slot[local]:
  vv_post H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = slot_loc tr /\ is_word_type t /\ post_value_type ce e = t /\
  ptr_vv_ok cx t tv (LocatedValue t p) ee G tn s /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v w q Gf tf. ^arm_word_packet
Proof
  strip_tac >> drule unwrap_storage_word_input >> simp[] >>
  disch_then (qspec_then `tr` mp_tac) >> simp[] >>
  disch_then drule >> strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (op,sb)` by
    (qpat_x_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >> fs[slot_loc_def, compile_ptr_load_def]) >>
  drule_all word_arm_slot_packet >> Cases_on `tr` >> fs[slot_loc_def]
QED

Theorem word_arm_loc_code[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = LocCode /\ is_word_type (post_value_type ce e) /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue t p) ee G tn s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  (ce.ce_is_ctor ==> ?val. read_result cx tv ee = (INL val,ee) /\
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
           eval_operand p.ptr_operand s = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt val (w2n w) mem)) /\
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  copy_old_operand sm p.ptr_operand /\ local_ptrs_reserved ce sm /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v w q Gf tf. ^arm_word_packet
Proof
  strip_tac >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_mods_def,vv_holds_mods_def,immutable_holds_mods_def] >>
     strip_tac >> drule immutable_holds_read >> simp[]) >>
  drule_all_then strip_assume_tac local_copy_raw_code_source_mods >>
  drule_all_then assume_tac word_tv_memory_size >>
  `stmt_state_rel H ctx func ce cx ee s` by fs[vv_post_mods_def] >>
  drule stmt_state_rel_immutable_base_zero >> simp[immutable_base_zero_def] >> strip_tac >>
  `compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand sm = (op,sb)` by
    (qpat_x_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >> simp[compile_ptr_load_def]) >>
  `ce.ce_is_ctor ==> w2n w + 32 <= lo /\ mem_word_taint tn.t_mem (w2n w) = {} /\
    !base. ce.ce_imm_alloca = SOME base ==> eval_operand base s = SOME 0w /\
      copy_old_operand sm base /\ op_taint tn base = {} /\ op_prov G base = NONE` by
    (strip_tac >> fs[] >> conj_tac
     >- (drule_all_then strip_assume_tac robust_typed_word_clean >>
         simp[mem_word_taint_def, EXTENSION] >> gen_tac >> Cases_on `x < 32` >> simp[] >>
         qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` (qspec_then `x + w2n w` mp_tac) >>
         `w2n w <= x + w2n w /\ x + w2n w < w2n w + 32` by decide_tac >> simp[]) >>
     `lo <> 0` by decide_tac >>
     gen_tac >> strip_tac >> simp[copy_old_operand_def] >>
     rename1 `ce.ce_imm_alloca = SOME base0` >>
     Cases_on `base0` >> fs[op_taint_def,op_prov_def,copy_old_operand_def] >>
     fs[ghost_inv_at_mods_def,op_taint_def] >> metis_tac[local_ptrs_reserved_imm_base]) >>
  `immutable_copy_read ce.ce_is_ctor w s = typed_val_to_w256 rt v` by
    (Cases_on `ce.ce_is_ctor` >> fs[immutable_copy_read_def]
     >- (`val_in_memory rt v (w2n w) s.vs_memory` by
           (qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> _`
              (qspec_then `s.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
         drule_all val_in_memory_word_type >> simp[mem_word_at_eq_mload]) >>
     drule_all val_in_memory_word_type >> simp[mem_word_at_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all_then (qspecl_then [`func`,`PG`,`D`] strip_assume_tac) word_arm_code_packet >>
  qexistsl [`q`,`Gf`,`tf`] >> simp[] >>
  Cases_on `ce.ce_is_ctor` >> fs[] >- (Cases_on `ce.ce_imm_alloca` >> fs[] >> decide_tac) >>
  decide_tac
QED

Theorem word_arm_location[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue j p) s /\
  post_value_type ce e = t /\ is_word_type t ==>
  j = t /\ p.ptr_location <> LocCalldata
Proof
  simp[vv_post_mods_def,vv_holds_mods_def] >>
  Cases_on `p.ptr_location` >> rw[vv_holds_def] >>
  metis_tac[valueCopyBytesTheory.is_bytestring_word_type]
QED

Theorem word_arm_located_packet[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  post_value_type ce e = t /\ is_word_type t /\ p.ptr_location <> LocCalldata /\
  ptr_vv_ok cx t tv (LocatedValue t p) ee G tn s /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  vv_store_bound cx t (lowered_value_type ce e) ee tv (LocatedValue t p) s /\
  (ce.ce_is_ctor /\ p.ptr_location = LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location p.ptr_operand sm = (op,sb) /\
  copy_old_operand sm p.ptr_operand /\ local_ptrs_reserved ce sm /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?v w q Gf tf. ^arm_word_packet
Proof
  strip_tac >> Cases_on `p.ptr_location = LocCode`
  >- (irule word_arm_loc_code >> simp[] >>
      conj_tac >- (qexistsl [`Dh`,`d`] >> simp[]) >>
      qexistsl [`H`,`e`,`es`,`s0`,`sa`,`t`] >> simp[] >>
      metis_tac[ADD_COMM]) >>
  `vv_post H ctx func ce cx e es sa sm s0 ee tv (LocatedValue t p) s` by
    metis_tac[word_arm_noncode_post] >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (irule word_arm_loc_memory >> simp[] >> qexistsl [`H`,`e`,`es`,`s0`,`sa`] >> simp[]) >>
  `?tr. p.ptr_location = slot_loc tr` by
    (Cases_on `p.ptr_location` >> fs[slot_loc_def] >> metis_tac[]) >>
  irule word_arm_loc_slot >> simp[] >>
  conj_tac >- (qexists `tr` >> simp[]) >>
  qexistsl [`H`,`e`,`es`,`s0`,`sa`] >> simp[]
QED
(* Join the physical endpoint to all horizon-indexed posts. *)
val arm_word_result = ``
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) /\
      expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op u /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u) /\
    expr_store_bound cx t v op u /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~u.vs_halted /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\ ptr_val_ok cx t v op Gf tf u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf``;

val empty_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                      d_imm := K {}; d_ret := K {}|>``;

Theorem word_arm_finish[local]:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME rt /\
  read_result cx tv ee = (INL v,ee) /\ eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ ~s.vs_halted /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  op_taint tf op = {} /\ op_prov Gf op = NONE /\
  gas_origin_ptr_path (^empty_dead,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf) ==>
  ^arm_word_result
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v op u /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf u /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     irule word_arm_endpoint_frame >> simp[] >>
     qexistsl [`G`,`e`,`s`,`sm`,`tn`,`tv`,`vv`] >> simp[] >>
     qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  simp[expr_store_bound_def,ptr_val_ok_def] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >> fs[allocas_below_fmp_def] >> strip_tac >> fs[]
QED

Theorem ifexp_arm_word_read_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (op,sb) /\
  is_word_type t /\ (e = a \/ e = b) /\ expr_type e = t /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rt v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt val (w2n w) mem)) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?v u Gf tf. ^arm_word_result
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce e = t` by fs[] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e` by (fs[] >> metis_tac[]) >>
  `copy_old_operand sm (vv_operand vv)` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[copy_old_operand_def]) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  Cases_on `vv`
  >- (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
      simp[compile_ifexp_arm_def,unwrap_value_def,comp_return_def] >>
      disch_then (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS) >>
      rename1 `compile_expr ce ty e sa = (StackValue tag x,sm)` >>
      `?v. read_result cx tv ee = (INL v,ee) /\
           eval_operand x s = SOME (typed_val_to_w256 rt v)` by
        (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
         qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
         simp[vv_holds_mods_def,vv_holds_def,expr_val_rel_def] >>
         strip_tac >> qexists `v` >> simp[]) >>
      `op_taint tn x = {} /\ op_prov G x = NONE` by
        (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
         simp[ptr_vv_ok_def,ptr_val_ok_def]) >>
      qexistsl [`v`,`s`,`G`,`tn`] >> irule word_arm_finish >>
      simp[cj 1 gas_origin_ptr_path_rules] >>
      qexistsl [`e`,`sm`,`StackValue tag x`] >> simp[]) >>
  rename1 `LocatedValue tag p` >>
  drule word_arm_location >> simp[] >> strip_tac >>
  qpat_x_assum `tag = t` SUBST_ALL_TAC >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def,unwrap_value_def] >> disch_tac >>
  qpat_x_assum `copy_old_operand _ _`
    (assume_tac o REWRITE_RULE [vv_operand_def]) >>
  qpat_assum `ghost_inv_at_mods (DF H0) _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^empty_dead`] word_arm_located_packet)) >>
  simp[] >>
  (impl_tac >- (conj_tac >- (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >> simp[]) >>
                conj_tac >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >> simp[]) >>
                qpat_x_assum `ce.ce_is_ctor /\ vv_location _ = _ ==> _` mp_tac >>
                simp[vv_location_def,vv_operand_def] >> metis_tac[ADD_COMM])) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `alloca_inv s` by
    (fs[vv_post_mods_def] >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  qexistsl [`v`,`u`,`Gf`,`tf`] >> irule word_arm_finish >> simp[] >>
  qexistsl [`e`,`sm`,`LocatedValue t p`] >> simp[] >>
  rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _` drule >> simp[]
QED
