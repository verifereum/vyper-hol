(* The source and counted suffix for aggregate storage/transient Append. *)
Theory bodyAppendSlotCopyMods
Ancestors
  stmtSimAppendStorage vyperStorageBackend vyperStorage vyperState
  vyperValue vfmState words integer_word
  bodyAppendSlotRhsMods bodyAppendSlotScratchMods bodyAppendSlotStagedSuffixMods
  bodyAppendStageJoinMods gasOutcomeFullZeroPrefixMods stmtSimAugAssignPlaceStorage
  bodyInvSplit bodyInvCodeProps exprBodyPreProps exprSimHypsDefs
  bodyFullShared bodyFullPostsMods stmtSimDefs wordArgsPtr exprSimCopy stateRelProj
  vyperTypeEvalCaseProofs vyperStorageTrace vyperStorageFootprint
  exprLoweringProps loweringPosts freshWrites exprSimProps bodySim
  stmtLoweringMono compileEnv finite_map arithmetic pair

(* Read the header at the reached state, not at target entry. *)
Theorem append_slot_copy_source_mods:
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  encode_value tv v = SOME writes ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    if cap <= len then (INR (Error (RuntimeError "append full storage array")), es)
    else if cx.txn.is_static then (INR (Error (RuntimeError "write in static context")), es)
    else (INL (), set_storage cx es tr
           (update_storage slot (n2w (len+1))
             (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes
               (get_storage cx es tr))))
Proof
  strip_tac >> gvs[] >>
  IF_CASES_TAC >- simp[stmtSimAppendStorageTheory.append_storage_full] >>
  `w2n (lookup_storage slot (get_storage cx es tr)) < cap` by decide_tac >>
  IF_CASES_TAC >- simp[stmtSimAppendStorageTheory.append_storage_static] >>
  simp[append_storage_writes, ignore_bind_def, bind_def,
       write_storage_slot_eq, get_storage_after_set, encode_value_def,
       encode_base_to_slot_def, apply_writes_def, i2w_def] >>
  Cases_on `tr` >> simp[set_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem append_slot_copy_landing_mods:
  contract_inv mods exps ctx cenv cx /\
  compile_get_target_ptr compile_expr cenv bt sa = (dst,sp) /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  append_store_code_mods cenv e dst (slot_loc tr) elem cap op sm sf func /\
  ~is_word_type elem /\ stmt_exprs_ok cenv (Append bt e) /\
  target_place_type cenv bt = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  expr_body_pre_mods mods cenv cx env e reached /\
  type_widens_to env.type_defs (expr_type e) elem /\
  eval_target_place cx bt (es with gas_obs := ts) =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),reached) /\
  bind (eval_expr cx e) (read_result cx) (reached with gas_obs := gs) = (INL v,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H reached.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0 reached
      (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic cap))))
      (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gp tp p) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    append_rhs_post_mods DF lo d ctx func cenv cx e reached sp sm p op Gp tp H v mid G tn s) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sp /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\ return_buf_sep d cenv mid s /\ ~s.vs_halted /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv mid s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!n b sz. local_region cenv mid.scopes s n b sz <=> local_region cenv es.scopes s0 n b sz) /\
  cenv_top_ext cenv0 cenv mid.scopes ==>
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
    (append_exit_mods ctx cx RetQ)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H reached.storage_trace` by
    (rpt strip_tac >>
     `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
     drule_all valid_horizon_frame >> simp[]) >>
  `?H. valid_horizon cx st0 H mid.storage_trace` by metis_tac[storage_trace_domain_def] >>
  `valid_horizon cx st0 H reached.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon cx st0 H reached.storage_trace ==> _`
    (drule_then assume_tac) >>
  qpat_assum `!H. _ ==> append_rhs_post_mods DF lo d ctx func cenv cx e reached sp sm p op Gp tp H v mid G tn s`
    (drule_then (strip_assume_tac o REWRITE_RULE [append_rhs_post_mods_def])) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) append_slot_rhs_input_mods >>
  qpat_x_assum `append_store_code_mods _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [append_store_code_mods_def]) >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`tmp`,`sc`,`sd`] strip_assume_tac) >>
  qpat_x_assum `?stv xs sw writes. _`
    (qx_choosel_then [`stv`,`xs`,`sw`,`writes`] strip_assume_tac) >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,n). !tyv. evaluate_type (get_tenv cx) fty = SOME tyv ==>
        n = type_memory_size tyv) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "scratch"
QED

Resume append_slot_copy_landing_mods[scratch]:
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
    (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) mp_tac append_slot_scratch_ready_mods) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`explicit` |-> `explicit`,`PG` |-> `PG`,
    `lo` |-> `lo`,`dtv` |-> `tv`] o SPEC_ALL) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choosel_then [`z`,`q`,`b`,`Gz`,`tz`] strip_assume_tac) >>
  suspend "frames"
QED

Resume append_slot_copy_landing_mods[frames]:
  `ci_mono sm sc /\ ci_mono sc sd` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_store_memory,SND] >>
  `ci_mono sm sd` by metis_tac[ci_mono_trans] >>
  `sm.cs_next_var <= sd.cs_next_var` by fs[ci_mono_def] >>
  `sa.cs_next_var <= sd.cs_next_var` by
    (irule LESS_EQ_TRANS >> qexists_tac `sm.cs_next_var` >> simp[]) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by
    (irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >> simp[]) >>
  `local_ptrs_reserved cenv sd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!n b sz. local_region cenv mid.scopes z n b sz <=> local_region cenv mid.scopes s n b sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sm` >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv mid z` by
    (irule alloca_frame_trans >>
     qpat_assum `alloca_frame cenv mid sm s cenv mid z` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` by
    (irule ghost_kept_at_trans >>
     qpat_assum `ghost_kept_at lo cenv mid sm G tn s Gz tz` (irule_at Any) >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x z = _` (drule_then SUBST1_TAC) >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP z.vs_allocas aid = SOME ent` by
    (rpt strip_tac >> qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> _`
       (drule_then assume_tac) >>
     qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> _` (drule_then ACCEPT_TAC)) >>
  `return_buf_frame d cenv sd z` by simp[] >>
  `return_buf_sep d cenv mid z` by suspend "separation" >>
  suspend "horizons"
QED

Resume append_slot_copy_landing_mods[separation]:
  irule return_buf_sep_transport >>
  qpat_assum `return_buf_sep d cenv mid s` (irule_at Any) >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ _ [] _` (qspec_then `DF H` assume_tac) >>
      rpt gen_tac >> disch_tac >> drule_all return_buf_allocas_path >> simp[]) >>
  simp[]
QED

Resume append_slot_copy_landing_mods[horizons]:
  `!hz. valid_horizon cx st0 hz mid.storage_trace ==>
        stmt_state_rel hz ctx func cenv cx mid z /\ storage_well_formed_on cx mid (FST hz) /\
        immutable_frame_mods func cenv cx mid z /\ ghost_inv_at_mods (DF hz) lo d cenv cx mid Gz tz z /\
        storage_place_observed hz (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))` by
    (qx_gen_tac `hz` >> strip_tac >>
     `valid_horizon cx st0 hz reached.storage_trace` by simp[] >>
     qpat_assum `!H. _ ==> append_rhs_post_mods DF lo d ctx func cenv cx e reached sp sm p _ Gp tp H v mid G tn s`
       (qspec_then `hz` (drule_then (strip_assume_tac o REWRITE_RULE
           [append_rhs_post_mods_def,expr_post_mods_def,expr_post_def]))) >>
     simp[] >> drule_all_then ACCEPT_TAC aug_place_target_observed) >>
  `stmt_state_rel H ctx func cenv cx mid z` by simp[] >>
  `alloca_inv z` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid z`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  suspend "suffix"
QED

Resume append_slot_copy_landing_mods[suffix]:
  `compile_dynarray_append cenv (FST dst) tmp.buf_operand 1
    ((type_memory_bytes cenv elem + 31) DIV 32) elem elem cap F
    (if tr then LocTransient else LocStorage) sd = ((),sf)` by
    (Cases_on `tr` >>
     qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o SIMP_RULE bool_ss
         [slot_loc_def,word_scale_def,elem_size_in_location_def,is_slot_addressed_def,LET_THM]) >>
     simp[]) >>
  `eval_operand (FST dst) z = SOME slot /\ op_taint tz (FST dst) = {}` by
    (qpat_assum `!op. _ ==> eval_operand op z = _ /\ _` (qspec_then `FST dst` mp_tac) >> simp[]) >>
  `!x. FST dst = Var x \/ tmp.buf_operand = Var x ==> not_fresh_at sd x` by
    (rpt strip_tac >> gvs[] >>
     qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `w2n (n2w b:bytes32) = b` by
    (simp[w2n_n2w] >> irule LESS_MOD >> irule LESS_EQ_LESS_TRANS >>
     qexists_tac `b + type_memory_size tv` >> simp[]) >>
  `type_memory_size tv <> 0 ==> ?x. tmp.buf_operand = Var x /\ ptr_covers Gz tz x z (type_memory_size tv)` by
    (strip_tac >> qexists_tac `q` >> simp[]) >>
  suspend "source_replay"
QED

Resume append_slot_copy_landing_mods[source_replay]:
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx mid tr))` >>
  `len = w2n (lookup_storage slot (get_storage cx mid tr))` by simp[Abbr `len`] >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v mid =
    (if cap <= len then (INR (Error (RuntimeError "append full storage array")),mid)
     else if cx.txn.is_static then (INR (Error (RuntimeError "write in static context")),mid)
     else (INL (), set_storage cx mid tr (update_storage slot (n2w (len+1))
           (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes (get_storage cx mid tr)))))` by
    (irule append_slot_copy_source_mods >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!tail. append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v
           (mid with gas_obs := tail) =
    if cap <= len then (INR (Error (RuntimeError "append full storage array")),mid with gas_obs := tail)
    else if cx.txn.is_static then (INR (Error (RuntimeError "write in static context")),mid with gas_obs := tail)
    else (INL (), (set_storage cx mid tr
          (update_storage slot (n2w (len+1))
            (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes
              (get_storage cx mid tr)))) with gas_obs := tail)` by
    (qx_gen_tac `tail` >> Cases_on `cap <= len` >> Cases_on `cx.txn.is_static` >>
     qpat_x_assum `append_place _ _ _ mid = _` mp_tac >>
     asm_rewrite_tac[] >>
     disch_then (MATCH_ACCEPT_TAC o MATCH_MP
       stmtSimAppendStorageComposeTheory.append_storage_place_gas_obs)) >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Gz`,`z`,`tz`] >>
  conj_tac >- simp[] >>
  `append_exit_mods ctx cx RetQ =
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
       !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))` by
    simp[NoAsms,FUN_EQ_THM,append_exit_mods_def] >>
  pop_assum SUBST1_TAC >>
  irule append_slot_staged_suffix_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qexistsl_tac [`len`,`writes`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qexistsl_tac [`FST dst`,`elem`,`sd`,`tmp.buf_operand`,`n2w b`] >>
      qpat_assum `w2n (n2w b:bytes32) = b` (fn th => PURE_REWRITE_TAC [th]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise append_slot_copy_landing_mods
