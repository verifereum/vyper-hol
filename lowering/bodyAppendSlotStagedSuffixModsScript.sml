(* Join the reached storage Append cut on a single counted execution. *)
Theory bodyAppendSlotStagedSuffixMods
Ancestors
  bodyAppendSlotGuardMods bodyAppendSlotAddressMods bodyAppendSlotStaticMods
  bodyAppendSlotStoreTailMods bodyAppendSlotStateMods bodyAppendSlotTaintMods
  bodyAppendSlotEndpointFramesMods stmtSimAppendStorageCompose
  gasOutcomeFullPostMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  assignTuplePtrCopyLen typedMemoryCopy valueEncodingProps bodyPtrDefs
  exprSimWordArgs stateFrame stateRelProj bodyFullShared haltExitProj
  exprOpenPrimitives exprLoweringProps loweringStateRelDefs stmtLoweringMono exprOperandVar
  fragGasOriginPtrLoop fragExec loweringPosts exprSimDefs stmtSimDefs
  vyperStorageBackend vyperStorageFootprint vyperValue vyperState
  stmtSimStoreCopy sourceUnitExecution compileEnv ptrDiscipline
  vfmState venomState venomInst freshWrites list arithmetic words finite_map pred_set

Theorem append_slot_suffix_cuts[local]:
  emit_op (if tr then TLOAD else SLOAD) [bop] sd = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w stride)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (pop,s6) /\
  compile_store_slots cenv src pop elem tr s6 = ((),s7) /\
  emit_op ADD [lop; Lit 1w] s7 = (nop,s8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] s8 = ((),sf) /\
  fn_has_code sd sf func ==>
  fn_has_code sd s3 func /\ fn_has_code s3 s6 func /\ fn_has_code s6 s7 func /\
  fn_has_code s7 s8 func /\ fn_has_code s8 sf func /\ sd.cs_next_var <= sf.cs_next_var
Proof
  strip_tac >>
  `ci_mono sd s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3` by
    metis_tac[typed_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6` by
    metis_tac[typed_copy_emit_op_mono] >>
  `ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 sf` by
    metis_tac[cj 1 ci_mono_compile_store_slots, typed_copy_emit_op_mono,
      ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sd s3 /\ ci_mono s3 s6` by metis_tac[ci_mono_trans] >>
  `ci_mono s7 sf /\ ci_mono s6 sf /\ ci_mono s3 sf /\ ci_mono sd sf` by
    (rpt conj_tac >> metis_tac[ci_mono_trans]) >>
  qpat_assum `ci_mono sd sf` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
  fs[ci_mono_def] >>
  `fn_has_code sd s3 func /\ fn_has_code s3 sf func` by metis_tac[fn_has_code_split] >>
  `fn_has_code s3 s6 func /\ fn_has_code s6 sf func` by metis_tac[fn_has_code_split] >>
  `fn_has_code s6 s7 func /\ fn_has_code s7 sf func` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem append_slot_guard_fields[local]:
  state_frame (g with vs_inst_idx := s.vs_inst_idx) = state_frame s ==>
  store_copy_normalize s g = s /\ g.vs_call_ctx = s.vs_call_ctx /\
  g.vs_memory = s.vs_memory /\ g.vs_allocas = s.vs_allocas /\
  g.vs_alloca_next = s.vs_alloca_next /\ g.vs_labels = s.vs_labels /\
  g.vs_data_section = s.vs_data_section /\ g.vs_immutables = s.vs_immutables
Proof
  simp[state_frame_def, store_copy_normalize_def, venom_state_component_equality]
QED

Theorem append_slot_normalize_fold[local]:
  !ks base.
    store_copy_normalize s
      (FOLDL (\q i. (if tr then tstore else sstore) (key i) (rd i) q) base ks) =
    FOLDL (\q i. (if tr then tstore else sstore) (key i) (rd i) q)
      (store_copy_normalize s base) ks
Proof
  Induct >> simp[] >> Cases_on `tr` >>
  simp[store_copy_normalize_def, tstore_def, sstore_def]
QED

Theorem append_slot_normalize_store[local]:
  store_copy_normalize s ((if tr then tstore else sstore) k w z) =
    (if tr then tstore else sstore) k w (store_copy_normalize s z)
Proof
  Cases_on `tr` >> simp[store_copy_normalize_def, tstore_def, sstore_def]
QED

Theorem append_slot_rebase_writes[local]:
  store_copy_normalize s t = s /\
  store_copy_normalize t u =
    (if tr then tstore else sstore) slot h
      (FOLDL (\q i. (if tr then tstore else sstore) (key i) (rd i) q) t (ks:num list)) ==>
  store_copy_normalize s u =
    (if tr then tstore else sstore) slot h
      (FOLDL (\q i. (if tr then tstore else sstore) (key i) (rd i) q) s ks)
Proof
  strip_tac >>
  `store_copy_normalize s u = store_copy_normalize s (store_copy_normalize t u)` by
    simp[NoAsms, store_copy_normalize_def] >>
  pop_assum SUBST1_TAC >>
  qpat_assum `store_copy_normalize t u = _` SUBST1_TAC >>
  pure_rewrite_tac[append_slot_normalize_store, append_slot_normalize_fold] >>
  simp[]
QED

Theorem append_slot_staged_error[local]:
  ~s.vs_halted /\
  (!tail. source (mid with gas_obs := tail) =
          (INR (Error (RuntimeError msg)),mid with gas_obs := tail)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (Abort reason u,Gf,tf)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (mid,s,G,tn) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  strip_tac >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`Gf`,`mid`,`Abort reason u`,`INR (Error (RuntimeError msg))`,`tf`] >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def, halt_exit_def]
QED

Theorem append_slot_gas_obs_frames[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- (simp[immutable_frame_mods_def,immutables_rel_mods_def,
       immutable_alloca_sep_mods_def,immutable_alloca_sep_def,immutables_rel_def] >> metis_tac[])
  >- simp[ghost_inv_at_mods_def] >>
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem append_slot_staged_suffix_mods:
  compile_dynarray_append cenv bop src 1 ((type_memory_bytes cenv elem + 31) DIV 32)
    elem elem cap F (if tr then LocTransient else LocStorage) sd = ((),sf) /\
  fn_has_code sd sf func /\ fn_inst_ids_distinct func /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  evaluate_type (get_tenv cx) elem = SOME tv /\ value_has_type tv v /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  (!x. bop = Var x \/ src = Var x ==> not_fresh_at sd x) /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  eval_operand src s = SOME sw /\ op_taint tn src = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==> ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\ lo <= s.vs_alloca_next /\
  cap < dimword (:256) /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H) /\
    immutable_frame_mods func cenv cx mid s /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sd.cs_current_bb /\
  s.vs_inst_idx = LENGTH sd.cs_current_insts /\
  sa.cs_next_var <= sd.cs_next_var /\ local_ptrs_reserved cenv sd /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x) /\
  return_buf_frame d cenv sd s /\ return_buf_sep d cenv mid s /\
  alloca_history func s /\ alloca_inv s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv mid s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  cenv_top_ext cenv0 cenv mid.scopes /\
  len = w2n (lookup_storage slot (get_storage cx mid tr)) /\ encode_value tv v = SOME writes /\
  (!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
           (mid with gas_obs := tail) =
    if cap <= len then (INR (Error (RuntimeError "append full storage array")),mid with gas_obs := tail)
    else if cx.txn.is_static then (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)
    else (INL (), (set_storage cx mid tr
          (update_storage slot (n2w (len+1))
            (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes
              (get_storage cx mid tr)))) with gas_obs := tail)) /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
    (if cap <= len then (INR (Error (RuntimeError "append full storage array")),mid)
     else if cx.txn.is_static then (INR (Error (RuntimeError "write in static context")),mid)
     else (INL (), set_storage cx mid tr (update_storage slot (n2w (len+1))
           (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes (get_storage cx mid tr))))) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v) (mid,s,G,tn)
    (\H res ee Gf tf u. ?cenv'.
      stmt_lands lctx sf res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sf /\ cenv' = cenv) /\
      cenv_top_ext cenv0 cenv' ee.scopes /\
      stmt_state_rel H ctx func cenv' cx ee u /\ immutable_frame_mods func cenv' cx ee u /\
      storage_well_formed_on cx ee (FST H) /\ return_buf_frame d cenv' sf u /\
      alloca_history func u /\ return_buf_sep d cenv' ee u /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv' cx ee Gf tf u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 cenv' ee u /\
      (!aid off sz i.
        FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==> off + sz <= b \/ b + sz' <= off) /\
        off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem))
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `((type_memory_bytes cenv elem + 31) DIV 32) = type_slot_size tv` by
    simp[type_memory_size_slots, Once MULT_COMM, ADD_DIV_ADD_DIV] >>
  qpat_assum `(type_memory_bytes cenv elem + 31) DIV 32 = _` (fn stride =>
    qpat_x_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
      (strip_assume_tac o SIMP_RULE bool_ss [stride, append_storage_copy_suffix_parts])) >>
  drule_all_then strip_assume_tac append_slot_suffix_cuts >>
  `?H. valid_horizon cx st0 H mid.storage_trace` by metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _` drule >> strip_tac >>
  `dead_lo_ok_mods H (DF H) lo cenv cx` by simp[] >>
  `!x. bop = Var x ==> not_fresh_at sd x` by metis_tac[] >>
  drule_all append_slot_guard_run_mods >>
  disch_then (qspecl_then [`PG`] mp_tac) >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  qpat_assum `len = w2n _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  Cases_on `cap <= len` >> asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`g`,`Gg`,`tg`] strip_assume_tac))
  >- suspend "capacity" >> suspend "address"
QED

Resume append_slot_staged_suffix_mods[capacity]:
  irule append_slot_staged_error >>
  simp[] >> qexistsl_tac [`Gg`,`Revert_abort`,`tg`,`g`] >>
  simp[]
QED

Resume append_slot_staged_suffix_mods[address]:
  `eval_operand lop g = SOME (n2w len)` by simp[] >>
  `len < cap /\ w2n slot + (1 + cap * type_slot_size tv) <= dimword (:256)` by
    (conj_tac >- fs[arithmeticTheory.NOT_LESS] >>
     qpat_assum `w2n slot + type_slot_size _ <= _`
       (mp_tac o REWRITE_RULE [type_slot_size_def]) >> decide_tac) >>
  `!x. bop = Var x \/ lop = Var x ==> not_fresh_at s3 x` by metis_tac[] >>
  drule_all append_slot_address_run_mods >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gg`]
    (qx_choosel_then [`addr_tmp`,`placed`,`Gp`,`ptn`] strip_assume_tac)) >>
  `!x. not_fresh_at sd x ==> not_fresh_at s6 x /\ lookup_var x placed = lookup_var x s /\
    FLOOKUP Gp x = FLOOKUP G x /\ op_taint ptn (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s3 x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!x. src = Var x ==> not_fresh_at sd x` by
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. bop = Var x \/ src = Var x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `!x. src = Var x ==> not_fresh_at s3 x` by
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at s3 x /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!x. src = Var x \/ pop = Var x \/ lop = Var x \/ bop = Var x ==> not_fresh_at s6 x` by
    (qx_gen_tac `x` >> strip_tac >> fs[] >>
     qpat_assum `!x. not_fresh_at s3 x ==> not_fresh_at s6 x /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. bop = Var x \/ lop = Var x ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `eval_operand src placed = SOME sw /\ op_taint ptn src = {}` by
    (qpat_assum `!op. _ ==> eval_operand op g = _ /\ _` (qspec_then `src` mp_tac) >>
     qpat_assum `!op. _ ==> eval_operand op placed = _ /\ _` (qspec_then `src` mp_tac) >> simp[]) >>
  `state_frame (g with vs_inst_idx := s.vs_inst_idx) = state_frame s` by
    (pure_asm_rewrite_tac[] >> REFL_TAC) >>
  drule_then strip_assume_tac append_slot_guard_fields >>
  `store_copy_normalize s placed = s` by
    (qpat_assum `store_copy_normalize s g = s` mp_tac >>
     qpat_assum `store_copy_normalize g placed = g` mp_tac >>
     simp[NoAsms,store_copy_normalize_def,venom_state_component_equality]) >>
  `placed.vs_data_section = s.vs_data_section /\ placed.vs_immutables = s.vs_immutables /\
   placed.vs_call_ctx = s.vs_call_ctx /\ placed.vs_memory = s.vs_memory /\
   placed.vs_allocas = s.vs_allocas /\ placed.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `store_copy_normalize s placed = s` mp_tac >>
     simp[NoAsms,store_copy_normalize_def,venom_state_component_equality]) >>
  `placed.vs_call_ctx.cc_static = cx.txn.is_static` by
    (drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[call_ctx_rel_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK placed,Gp,ptn)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gg`,`g`,`tg`] >> simp[]) >>
  `type_memory_size tv <> 0 ==> ?x. src = Var x /\ ptr_covers Gp ptn x placed (type_memory_size tv)` by
    (strip_tac >> qpat_assum `_ ==> ?x. src = Var x /\ ptr_covers G tn x s _`
       (drule_then (qx_choose_then `p` strip_assume_tac)) >> qexists_tac `p` >> fs[ptr_covers_def] >>
     qpat_assum `!x. not_fresh_at sd x ==> lookup_var x placed = _ /\ _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `ptn.t_mem = tn.t_mem /\ ptn.t_stor = tn.t_stor /\ ptn.t_trans = tn.t_trans /\
   ptn.t_imm = tn.t_imm` by fs[] >>
  `!mem. mem_agree_outside ptn.t_mem placed.vs_memory mem ==>
     val_in_memory tv v (w2n sw) mem` by simp[] >>
  Q.SUBGOAL_THEN `type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= placed.vs_alloca_next`
    assume_tac >- simp[] >>
  `lo <= placed.vs_alloca_next` by simp[] >>
  Cases_on `cx.txn.is_static`
  >- suspend "static" >> suspend "success"
QED

Resume append_slot_staged_suffix_mods[static]:
  `placed.vs_call_ctx.cc_static` by simp[] >>
  `!x. src = Var x \/ pop = Var x ==> not_fresh_at s6 x` by
    (qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. src = Var x \/ pop = Var x \/ _ ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `type_slot_size tv = 0 ==>
     (!x. bop = Var x \/ lop = Var x ==> not_fresh_at s6 x) /\
     eval_operand lop placed = SOME (n2w len) /\ op_taint ptn lop = {} /\
     eval_operand bop placed = SOME slot /\ op_taint ptn bop = {}` by
    (simp[] >> strip_tac >> qx_gen_tac `x` >> strip_tac >>
     qpat_assum `!x. src = Var x \/ pop = Var x \/ _ ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  drule_all (Q.INST [`s` |-> `placed`, `sa` |-> `s6`] append_slot_static_tail_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`blocked`,`Gb`,`tbn`] strip_assume_tac)) >>
  irule append_slot_staged_error >> simp[] >>
  qexistsl_tac [`Gb`,`ExHalt_abort`,`tbn`,`halt_state (set_returndata [] blocked)`] >>
  gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gp`,`placed`,`ptn`] >> simp[]
QED

Resume append_slot_staged_suffix_mods[success]:
  `~placed.vs_call_ctx.cc_static` by simp[] >>
  drule_all (Q.INST [`s` |-> `placed`, `sa` |-> `s6`] append_slot_store_tail_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`ks`,`u`,`Gf`,`tf`] strip_assume_tac)) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gp`,`placed`,`ptn`] >> simp[]) >>
  qabbrev_tac `k = slot+n2w (1+len*type_slot_size tv)` >>
  qabbrev_tac `ef = set_storage cx mid tr (update_storage slot (n2w (len+1))
                       (apply_writes k writes (get_storage cx mid tr)))` >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
           (mid with gas_obs := tail) = (INL (),ef with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. append_place _ _ _ _ = _` (qspec_then `tail` mp_tac) >>
     simp[Abbr `ef`,Abbr `k`]) >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid = (INL (),ef)` by
    (qpat_assum `append_place _ _ _ mid = _` mp_tac >> simp[Abbr `ef`,Abbr `k`]) >>
  `ef.storage_trace = mid.storage_trace /\ ef.scopes = mid.scopes /\ ef.immutables = mid.immutables` by
    (Cases_on `tr` >> simp[NoAsms,Abbr `ef`,set_storage_def]) >>
  suspend "normal_frame"
QED

Resume append_slot_staged_suffix_mods[normal_frame]:
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_immutables = s.vs_immutables /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
   (allocas_below_fmp u <=> allocas_below_fmp s)` by
    (fs[] >> qpat_assum `store_copy_normalize s placed = s` mp_tac >>
      simp[NoAsms,store_copy_normalize_def,venom_state_component_equality,allocas_below_fmp_def]) >>
  `!x. not_fresh_at sd x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> not_fresh_at s6 x /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at s6 x ==> not_fresh_at sf x /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `store_copy_normalize s u =
      (if tr then tstore else sstore) slot (n2w (len+1))
       (FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
                    (mload (w2n sw+32*i) s) q) s ks)` by
    (irule (SIMP_RULE bool_ss [] (Q.INST [`key` |-> `\i. k+n2w i`,
       `rd` |-> `\i. mload (w2n sw+32*i) s`] append_slot_rebase_writes)) >>
     qexists_tac `placed` >>
     qpat_assum `store_copy_normalize placed u = _` mp_tac >>
     simp[GSYM mem_word_at_eq_mload]) >>
  `(if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans)` by
    (Cases_on `tr` >> fs[]) >>
  `(if tr then tf.t_trans else tf.t_stor) SUBSET
    key_update
      (FOLDL (\Y j. key_update Y (k+n2w j) (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks) slot {}` by
    (qunabbrev_tac `k` >> qpat_x_assum `_ SUBSET key_update _ _ _` mp_tac >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `well_formed_type_value tv` by drule_then ACCEPT_TAC vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
  irule gas_outcome_full_mods_pure >> asm_rewrite_tac[] >>
  qexistsl_tac [`Gf`,`ef`,`INL ()`,`u`,`tf`] >>
  asm_rewrite_tac[] >> qx_gen_tac `hz` >> strip_tac >> BETA_TAC >>
  suspend "horizon"
QED

Resume append_slot_staged_suffix_mods[horizon]:
  `valid_horizon cx st0 hz mid.storage_trace` by fs[] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  `regions_consistent (FST hz) /\ storage_locks_separated (FST hz) (SND hz)` by
    fs[valid_horizon_def] >>
  `dead_lo_ok_mods hz (DF hz) lo cenv cx` by simp[] >>
  `k = slot+n2w (1+len*type_slot_size tv)` by simp[Abbr `k`] >>
  `ef = set_storage cx mid tr (update_storage slot (n2w (len+1))
                       (apply_writes k writes (get_storage cx mid tr)))` by simp[Abbr `ef`] >>
  `!x. not_fresh_at sd x ==> lookup_var x u = lookup_var x s` by
    (gen_tac >> strip_tac >> qpat_assum `!x. not_fresh_at sd x ==> lookup_var x u = _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac (Q.INST [`H` |-> `hz`, `sa` |-> `sd`] append_slot_state_wf_mods) >>
  drule_all_then assume_tac (Q.INST [`H` |-> `hz`] append_slot_taint_mods) >>
  `gas_origin_ptr_path (DF hz,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)` by simp[] >>
  drule_all_then strip_assume_tac (Q.INST [`D` |-> `DF hz`] append_slot_endpoint_frames_mods) >>
  qexists_tac `cenv` >>
  qpat_x_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  simp_tac (srw_ss()) [stmt_lands_def,return_buf_sep_gas_obs,append_slot_gas_obs_frames,
    stmt_state_rel_start_gas_obs,alloca_frame_gas_obs] >>
  asm_rewrite_tac[]
QED

Finalise append_slot_staged_suffix_mods
