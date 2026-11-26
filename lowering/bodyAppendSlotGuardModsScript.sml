(* The storage/transient Append guard, at the cursor after RHS staging. *)
Theory bodyAppendSlotGuardMods
Ancestors
  bodyFullAppendNestedFrames bodyFullShadowBodyInv appendStorageGhostPtr
  placeStoreStorage targetSubscriptStorage accountsRelProps bodyPtrDefs
  stateRelProj loweringStateRelDefs sourceUnitExecution vyperStorageBackend
  vyperStoragePlaceObserved vyperStoragePlaceRegion vyperStorageFootprint
  vyperStorage vyperTypeValues vyperValue vyperState venomState vfmState stateFrame
  exprLowering exprLoweringProps exprOperandVar typedMemoryCopy freshWrites
  compileEnv fragExec fragGasOriginPtrLoop ptrDiscipline exprSimDefs
  finite_map pred_set words

Theorem append_slot_guard_bounds[local]:
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) ==>
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)
Proof
  simp[storage_place_observed_def] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  drule_then assume_tac storage_subregion_bounds >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by simp[type_slot_size_def] >>
  `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n (root + n2w delta) = w2n root + delta` by
    simp[word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  simp[] >> decide_tac
QED

Theorem append_slot_guard_read[local]:
  stmt_state_rel H ctx func cenv cx mid s /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) /\ eval_operand bop s = SOME slot /\
  dead_lo_ok_mods H DH lo cenv cx /\ ghost_inv_at_mods DH lo d cenv cx mid G tn s ==>
  (if tr then tload slot s else sload slot s) = lookup_storage slot (get_storage cx mid tr) /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  allocas_from lo s /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)
Proof
  strip_tac >> drule_all_then assume_tac append_slot_guard_bounds >>
  `!raw. storage_read_live H tr raw slot (ArrayTV tv (Dynamic cap))` by
    (gen_tac >> irule storage_place_observed_read_live >> simp[type_slot_size_def]) >>
  conj_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] (cj 2 target_storage_array_len_ok)) >>
      conj_tac >- (qexists_tac `bop` >> simp[]) >>
      qexistsl_tac [`H`, `cenv`, `ctx`, `func`, `cap`, `tv`] >> simp[]) >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >> simp[call_ctx_rel_def]) >>
  simp[] >> conj_tac
  >- (irule (INST_TYPE [alpha |-> ``:256``] storage_dead_key_taint_empty) >>
      qexistsl_tac [`H`, `if tr then contract_transient s else contract_storage s`,
                    `tr`, `ArrayTV tv (Dynamic cap)`] >>
      simp[type_slot_size_def] >> Cases_on `tr` >>
      gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def,
          cx_dead_def, contract_storage_def, contract_transient_def, lookup_account_def]) >>
  fs[ghost_inv_at_mods_def]
QED

Theorem append_slot_guard_compile[local]:
  emit_op (if tr then TLOAD else SLOAD) [bop] sd = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) ==>
  s3.cs_current_bb = sd.cs_current_bb /\
  (!x. not_fresh_at sd x ==> not_fresh_at s3 x) /\
  (!x. lop = Var x ==> not_fresh_at s3 x)
Proof
  strip_tac >>
  drule_then assume_tac (SIMP_RULE (srw_ss()) [same_blocks_def] emit_void_same_blocks) >>
  qpat_assum `emit_op LT _ s1 = _`
    (assume_tac o SIMP_RULE (srw_ss()) [same_blocks_def] o MATCH_MP emit_op_same_blocks) >>
  qpat_assum `emit_op _ [bop] sd = _`
    (assume_tac o SIMP_RULE (srw_ss()) [same_blocks_def] o MATCH_MP emit_op_same_blocks) >>
  simp[] >>
  `ci_mono sd s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3` by
    (rpt conj_tac >> metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND]) >>
  `ci_mono s1 s3` by metis_tac[ci_mono_trans] >>
  qpat_assum `emit_op _ [bop] sd = _`
    (strip_assume_tac o MATCH_MP typed_copy_emit_op_fresh) >>
  metis_tac[compiler_ci_mono_not_fresh]
QED

Theorem append_slot_guard_operand[local]:
  u.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sd x ==> lookup_var x u = lookup_var x s /\
     FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) ==>
  !op. (!x. op = Var x ==> not_fresh_at sd x) ==>
    eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
    op_taint tu op = op_taint tn op
Proof
  strip_tac >> Cases >> simp[eval_operand_def, op_prov_def] >>
  rw[] >> fs[op_taint_def]
QED

Theorem append_slot_guard_run_mods:
  emit_op (if tr then TLOAD else SLOAD) [bop] sd = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\ fn_has_code sd s3 func /\
  stmt_state_rel H ctx func cenv cx mid s /\
  ghost_inv_at_mods DH lo d cenv cx mid G tn s /\ dead_lo_ok_mods H DH lo cenv cx /\
  valid_horizon cx st0 H mid.storage_trace /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  cap < dimword (:256) /\ eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  (!x. bop = Var x ==> not_fresh_at sd x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sd.cs_current_bb /\ s.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  let len = w2n (lookup_storage slot (get_storage cx mid tr)) in
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  if cap <= len then
    ?r Gr trn.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort r,Gr,trn)) /\
      (!R es. stmt_exit_ptr R es (INR (Error (RuntimeError "append full storage array")))
        trn (Abort Revert_abort r))
  else
    ?u Gu tu.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
      u.vs_current_bb = s3.cs_current_bb /\ u.vs_inst_idx = LENGTH s3.cs_current_insts /\
      ~u.vs_halted /\ allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      state_frame (u with vs_inst_idx := s.vs_inst_idx) = state_frame s /\
      eval_operand lop u = SOME (n2w len) /\ op_taint tu lop = {} /\
      (!x. lop = Var x ==> not_fresh_at s3 x) /\
      eval_operand bop u = SOME slot /\ op_taint tu bop = {} /\
      (!x. not_fresh_at sd x ==> not_fresh_at s3 x /\ lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
      (!op. (!x. op = Var x ==> not_fresh_at sd x) ==>
        eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
        op_taint tu op = op_taint tn op) /\
      tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  `regions_consistent (FST H)` by fs[valid_horizon_def] >>
  drule_all_then strip_assume_tac append_slot_guard_read >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx mid tr))` >>
  Cases_on `cap <= len` >> asm_rewrite_tac[]
  >- suspend "full" >> suspend "room"
QED

Resume append_slot_guard_run_mods[full]:
  `~(w2n (if tr then tload slot s else sload slot s) < cap)` by
    fs[Abbr `len`, arithmeticTheory.NOT_LESS] >>
  drule_all append_storage_guard_abort_conditional_uniform >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choosel_then [`r`,`j`,`Gr`,`trn`] strip_assume_tac)) >>
  qexistsl_tac [`r with vs_inst_idx := j`,`Gr`,`trn`] >>
  simp[stmt_exit_ptr_def, expr_exit_def]
QED

Resume append_slot_guard_run_mods[room]:
  `w2n (if tr then tload slot s else sload slot s) < cap` by
    (fs[Abbr `len`] >> decide_tac) >>
  drule_all append_storage_guard_conditional_uniform >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choosel_then [`r`,`Gu`,`tu`] strip_assume_tac)) >>
  drule_all_then strip_assume_tac append_slot_guard_compile >>
  qabbrev_tac `u = r with vs_inst_idx := LENGTH s3.cs_current_insts` >>
  `!x. not_fresh_at sd x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x r = _ /\ _`
       (drule_then strip_assume_tac) >>
     asm_rewrite_tac[] >> fs[Abbr `u`, lookup_var_def]) >>
  `u.vs_labels = s.vs_labels` by
    (fs[Abbr `u`, state_frame_def, venom_state_component_equality]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sd x) ==>
    eval_operand op u = eval_operand op s /\ op_prov Gu op = op_prov G op /\
    op_taint tu op = op_taint tn op` by (match_mp_tac append_slot_guard_operand >> simp[]) >>
  qexistsl_tac [`u`,`Gu`,`tu`] >>
  `eval_operand lop u = SOME (n2w len)` by
    (Cases_on `lop` >> fs[Abbr `u`, Abbr `len`, eval_operand_def, lookup_var_def]) >>
  suspend "normal_frame"
QED

Resume append_slot_guard_run_mods[normal_frame]:
  `eval_operand bop u = SOME slot /\ op_taint tu bop = {}` by
    (qpat_assum `!op. _ ==> eval_operand op u = _ /\ _`
       (qspec_then `bop` mp_tac) >> simp[]) >>
  `state_frame (u with vs_inst_idx := LENGTH sd.cs_current_insts) = state_frame s` by
    fs[Abbr `u`, state_frame_def, venom_state_component_equality] >>
  `u.vs_current_bb = s3.cs_current_bb /\ u.vs_inst_idx = LENGTH s3.cs_current_insts /\
   ~u.vs_halted /\ allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[Abbr `u`, state_frame_def, venom_state_component_equality,
        allocas_from_def, allocas_below_fmp_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> qpat_assum `ctx_has_dalloca ctx ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >> simp[]
QED

Finalise append_slot_guard_run_mods
