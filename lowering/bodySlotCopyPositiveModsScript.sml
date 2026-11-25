(* One counted sparse copy and its source and ghost posts at every horizon. *)
Theory bodySlotCopyPositiveMods
Ancestors
  bodySlotCopyFieldsMods bodySlotCopyStateMods bodySlotCopyTaintMods
  bodyFullStoreSlotsPath bodyFullStoreSlotsFrame bodyFullPathHistory
  stmtSimAssignStorageSparse bodyFullShared bodySimFull bodyMemoryDefs
  vyperStorageFootprint vyperStoragePlaceObserved vyperStoragePlaceRegion
  vyperPlaceFrames vyperStorageBackend tuplePlaceStep placeStoreStorage
  stateRelProj bodyPtrDefs loweringPosts finite_map list words
  bodyFullShadowBodyInv loweringStateRelDefs ptrDiscipline

Theorem slot_copy_observed_bounds[local]:
  storage_place_observed H (StoragePlace tr dw tv) /\
  regions_consistent (FST H) /\ 0 < type_slot_size tv ==>
  w2n dw + type_slot_size tv <= dimword (:256) /\
  ?rootk root path delta. MEM (tr,rootk,root) (FST H) /\
    storage_subregion root path delta tv /\ w2n dw = w2n rootk + delta
Proof
  pure_rewrite_tac[storage_place_observed_def] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`rootk`,`root`,`path`,`delta`] strip_assume_tac)
    strip_assume_tac) >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  drule_then assume_tac storage_subregion_bounds >>
  `w2n dw = w2n rootk + delta` by
    (`w2n rootk + delta < dimword (:256)` by decide_tac >>
     `rootk + n2w delta = n2w (w2n rootk + delta)` by simp[GSYM word_add_n2w] >>
     pure_asm_rewrite_tac[] >> simp[w2n_n2w]) >>
  conj_tac >- decide_tac >> qexistsl_tac [`rootk`,`root`,`path`,`delta`] >> asm_rewrite_tac[]
QED

Theorem slot_copy_positive_post[local]:
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_place_observed H (StoragePlace tr dw dtv) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx ee (FST H) /\
  ~cx.txn.is_static /\ 0 < type_slot_size dtv /\
  well_formed_type_value dtv /\ value_has_type dtv v /\
  encode_value dtv v = SOME writes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory dtv v off mem) /\
  ef = set_storage cx ee tr (apply_writes dw writes (get_storage cx ee tr)) /\
  ef.scopes = ee.scopes /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  store_copy_normalize s t = FOLDL (\q j. (if tr then tstore else sstore)
    (dw+n2w j) (mload (off+32*j) s) q) s ks /\
  (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tnf (Var x) = op_taint tn (Var x)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
  (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
  (if tr then tnf.t_trans else tnf.t_stor) SUBSET
    FOLDL (\X j. key_update X (dw+n2w j) (mem_word_taint tn.t_mem (off+32*j)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_immutables = s.vs_immutables /\ return_buf_sep d cenv ee s ==>
  stmt_state_rel H ctx func cenv cx ef t /\
  storage_well_formed_on cx ef (FST H) /\
  ghost_inv_at_mods D lo d cenv cx ef Gf tnf t /\ return_buf_sep d cenv ef t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then strip_assume_tac slot_copy_observed_bounds >>
  `val_in_memory dtv v off s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  conj_asm1_tac
  >- (qpat_assum `ef = _` (fn th => pure_once_rewrite_tac[th]) >>
      irule slot_copy_sparse_state_mods >> asm_rewrite_tac[] >>
      qexistsl_tac [`delta`,`ks`,`off`,`path`,`root`,`rootk`,`s`,`sa`,`dtv`,`v`] >>
      simp[]) >>
  conj_tac
  >- (irule slot_copy_write_wf_mods >> asm_rewrite_tac[] >>
      qexistsl_tac [`ee`,`dw`,`tr`,`dtv`,`v`] >> simp[write_storage_place_eq]) >>
  conj_tac
  >- (`stor_taint_ok_at D tn s` by fs[ghost_inv_at_mods_def] >>
      `s.vs_call_ctx.cc_address = cx.txn.target` by
        (qpat_assum `stmt_state_rel _ _ _ _ _ ee s` (mp_tac o MATCH_MP stmt_state_rel_state_rel) >>
         disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >> simp[call_ctx_rel_def]) >>
      `stor_taint_ok_at D tnf t` by
        (drule_all_then ACCEPT_TAC slot_copy_post_stor_taint_mods) >>
      irule slot_copy_ghost_frame_mods >> asm_rewrite_tac[] >>
      qexistsl_tac [`G`,`ee`,`s`,`sa`,`tn`] >> asm_rewrite_tac[]) >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> asm_rewrite_tac[] >>
  conj_tac >-
    (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_assum `t.vs_allocas = _` (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `return_buf_sep _ _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def] o cj 1 o REWRITE_RULE [return_buf_sep_def])) >>
  qexistsl_tac [`H`,`ctx`,`cx`,`ee`,`func`,`s`,`sa`] >> simp[]
QED

(* The run and the successful source value are chosen before H is quantified.
   Only physical layout coverage is required of the input pointer. *)
Theorem slot_copy_positive_path_mods:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                            sz = type_memory_size rt) fields) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  0 < type_slot_size dtv /\ well_formed_type_value dtv /\ value_has_type dtv v /\
  encode_value dtv v = SOME writes /\ type_slot_size tv <= type_slot_size dtv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory dtv v (w2n sw) mem) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~cx.txn.is_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sb.cs_next_var /\ return_buf_frame d cenv sa s /\
  alloca_history func s /\ alloca_inv s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     storage_place_observed H (StoragePlace tr dw dtv) /\
     storage_well_formed_on cx ee (FST H) /\ stmt_state_rel H ctx func cenv cx ee s /\
     dead_lo_ok_mods H (DF H) lo cenv cx /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
     return_buf_sep d cenv ee s) ==>
  ?ef t Gf tnf.
    write_place cx (StoragePlace tr dw dtv) v ee = (INL (),ef) /\
    ef.scopes = ee.scopes /\ ef.immutables = ee.immutables /\ ef.storage_trace = ee.storage_trace /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_immutables = s.vs_immutables /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ tnf.t_mem = tn.t_mem /\
    ~t.vs_halted /\ stmt_lands lctx sb (INL ()) t /\ ~block_is_terminated sb /\
    return_buf_frame d cenv sb t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ef t /\ storage_well_formed_on cx ef (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tnf t /\ return_buf_sep d cenv ef t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `w2n dw + type_slot_size tv <= dimword (:256) /\
   allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_call_ctx.cc_static` by
    (qpat_assum `?H. valid_horizon _ _ H _` strip_assume_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     `regions_consistent (FST H)` by fs[valid_horizon_def] >>
     drule_all_then strip_assume_tac slot_copy_observed_bounds >>
     `~s.vs_call_ctx.cc_static` by
       (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
        simp[call_ctx_rel_def]) >>
     fs[ghost_inv_at_mods_def] >> decide_tac) >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`] (SPEC_ALL compile_store_slots_origin_ptr_path)) >>
  (impl_tac >- (pure_asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choosel_then [`t`,`ks`,`Gf`,`tnf`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qabbrev_tac `ef = set_storage cx ee tr (apply_writes dw writes (get_storage cx ee tr))` >>
  `write_place cx (StoragePlace tr dw dtv) v ee = (INL (),ef)` by
    simp[write_storage_place_eq, Abbr `ef`] >>
  drule_then assume_tac write_storage_place_scopes >>
  drule_then assume_tac write_storage_place_immutables >>
  drule_then assume_tac write_place_storage_trace >>
  drule_then strip_assume_tac (BETA_RULE (Q.INST
    [`key` |-> `\j. dw+n2w j`, `rd` |-> `\j. mload (w2n sw+32*j) s`]
    slot_copy_normalized_fields)) >>
  `~block_is_terminated sb` by
    (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`) (cj 1 store_slots_open) >> simp[]) >>
  qexistsl_tac [`ef`,`t`,`Gf`,`tnf`] >> asm_rewrite_tac[stmt_lands_def] >>
  conj_tac >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sa`] >> simp[]) >>
  conj_tac >-
    (`gas_origin_ptr_path (ARB,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)` by simp[] >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  conj_tac >- (drule store_slots_normalize_allocas_below_fmp >> simp[store_slots_fold_allocas_below_fmp]) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)` by fs[valid_horizon_def] >>
  `ef = set_storage cx ee tr (apply_writes dw writes (get_storage cx ee tr))` by simp[Abbr `ef`] >>
  drule_all_then ACCEPT_TAC slot_copy_positive_post
QED
