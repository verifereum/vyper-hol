(* The reached memory Append continuation.  The array lives at an offset
   within its owning local; a scratch copy is only an operand of the write. *)
Theory bodyAppendMemoryLandingMods
Ancestors
  bodyAppendMemorySuffixMods bodyAppendMemorySourceMods
  bodyAppendMemoryRhsViewMods bodyAppendMemoryWordInputMods bodyAppendMemoryScratchMods
  bodyAssignLocalInstallMods bodyLocalCopyWritesMods bodyFullPathHistory
  gasOutcomeFullPostMods bodyFullShared bodyFullPostsMods exprSimWordArgs
  contextCodegenRel emitHelperProps emitHelper exprLoweringProps typedMemoryCopy
  stmtSimDefs fragGasOriginPtrLoop vyperStorageFootprint valueEncodingTyping
  loweringPosts loweringStateRelDefs venomState venomInst list finite_map words
  exprLowering context compileEnv stmtSimDeclMem bodyInvSplit bodyFullShadowBodyInv
  bodyFullHashKeccakFixed stateRelProj vyperTyping vyperAST valueEncoding
  fragExec bodyPtrDefs exprSimDefs stmtLoweringMono freshWrites vyperTypeSystem
  bodyFullMemoryFrames bodyFullTargetDefs exprSimHypsDefs exprBodyPreProps
  bodyAssignNameLinkedSetup bodyInvCodeProps bodyAnnNonwordReadTypesMods
  exprSimMemDefs allocLimits valueEncodingProps exprSimSource ptrDiscipline
  exprSimProps valueTypingMemoryProps vyperTypeEvalCaseProofs bodyWriteSubscriptSourceMods
  vyperState vyperValue vyperValueOperation exprLoweringProps arithmetic

Theorem memory_append_final_store[local]:
  compile_dynarray_append cenv bop src 32 stride elem elem cap F LocMemory a = ((),b) ==>
  ?a8 next. emit_void MSTORE [bop;next] a8 = ((),b)
Proof
  simp[compile_dynarray_append_def, compile_ptr_load_def, compile_ptr_store_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem memory_append_code_open[local]:
  compile_dynarray_append cenv bop src 32 stride elem elem cap F LocMemory a = ((),b) ==>
  ~block_is_terminated b
Proof
  strip_tac >> drule_then strip_assume_tac memory_append_final_store >>
  irule emit_void_nonterminator_open >> goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
  simp[is_terminator_def]
QED

Theorem memory_append_gas_obs_frames[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       loweringStateRelDefsTheory.immutables_rel_def]
  >- simp[ghost_inv_at_mods_def]
  >> irule storage_well_formed_on_backends >> simp[]
QED

val append_memory_post =
  ``\(H : (bool # 256 word # type_value) list # num list) res ee Gf tf t. ?ce.
    stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
    cenv_top_ext cenv ce ee.scopes /\ stmt_state_rel H ctx func ce cx ee t /\
    immutable_frame_mods func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ee t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 ce ee t /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region cenv es.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

val append_memory_exit =
  ``\(H : (bool # 256 word # type_value) list # num list) res ee (gt : (string |-> num # num) # taint) r.
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==>
      !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z)``;

Theorem memory_append_suffix_landing[local]:
  compile_dynarray_append cenv (Var p) src 32 (type_memory_size tv)
    elem elem cap F LocMemory a = ((),sb) /\ fn_has_code a sb func /\
  evaluate_type (get_tenv cx) elem = SOME tv /\ type_memory_bytes cenv elem = type_memory_size tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  cap < dimword (:256) /\ value_has_type tv v /\ val_wf tv v /\
  lookup_var p s = SOME bp /\ not_fresh_at a p /\ (!x. src = Var x ==> not_fresh_at a x) /\
  ptr_covers G tn p s (type_memory_size (ArrayTV tv (Dynamic cap))) /\
  w2n bp + type_memory_size (ArrayTV tv (Dynamic cap)) <= s.vs_alloca_next /\
  (if is_word_type elem then
     eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}
   else ?xs sw. src = Var xs /\ lookup_var xs s = SOME sw /\
     ptr_covers G tn xs s (type_memory_size tv) /\
     w2n sw + val_store_size tv v <= s.vs_alloca_next /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v (w2n sw) mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n bp) mem) /\
  lookup_scopes id fin.scopes = SOME entry /\ value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  mem_path_offset entry.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\ lookup_var root s = SOME basew /\
  w2n bp = w2n basew+k /\ k+type_memory_size (ArrayTV tv (Dynamic cap)) <= sz /\ lo <= w2n bp /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin s /\ immutable_frame_mods func cenv cx fin s /\
    storage_well_formed_on cx fin (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx fin G tn s) /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) fin /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK s,G,tn)) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv a /\
  sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at a x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at a x) /\
  return_buf_frame d cenv a s /\ return_buf_sep d cenv fin s /\ alloca_history func s /\
  ~u.vs_halted /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv fin s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (append_place cx (MemoryPlace id path) v) (fin,u,Gu,tu)
    ^append_memory_post ^append_memory_exit
Proof
  strip_tac >>
  `?H. valid_horizon cx st0 H fin.storage_trace` by metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _` drule >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_then (assume_tac o MATCH_MP alloca_room_next_lt) stmt_state_rel_alloca_room >>
  `LENGTH vs <= cap /\ (!j. j < LENGTH vs ==> val_wf tv (EL j vs))` by
    (fs[value_has_type_def,all_have_type_EVERY,EVERY_EL] >> metis_tac[value_has_type_val_wf]) >>
  `type_memory_size (ArrayTV tv (Dynamic cap)) = 32+cap*type_memory_size tv` by
    simp[type_memory_size_def, bound_length_def] >>
  `ptr_covers G tn p s (32+cap*type_memory_size tv) /\
   w2n bp+32+cap*type_memory_size tv <= s.vs_alloca_next` by fs[] >>
  qpat_assum `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac append_memory_counted_suffix_mods) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME bp`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ (32+_)`)) >>
  disch_then (mp_tac o Q.INST [`vs` |-> `vs`,`lo` |-> `lo`,`bp` |-> `bp`,
    `ctx` |-> `ctx`,`func` |-> `func`,`explicit` |-> `explicit`,`PG` |-> `PG`] o SPEC_ALL) >>
  suspend "counted"
QED

Resume memory_append_suffix_landing[counted]:
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  drule_all append_memory_source_cases_mods >>
  Cases_on `LENGTH vs < cap` >> simp[]
  >- (strip_tac >> strip_tac >> suspend "install") >>
  strip_tac >> strip_tac >> suspend "overflow"
QED

Resume memory_append_suffix_landing[overflow]:
  irule gas_outcome_full_mods_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`fin`,`Abort Revert_abort r`,
    `INR (Error (RuntimeError "append overflow"))`,`tf`] >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def, halt_exit_def] >>
  metis_tac[gas_origin_ptr_path_trans]
QED

Resume memory_append_suffix_landing[install]:
  rename1 `write_place _ _ _ fin = (INL (),ff)` >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `alloca_history func t` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gf,tf)`
       (qspec_then `DF H` (mp_then Any mp_tac body_full_path_alloca_history)) >> simp[]) >>
  `~block_is_terminated sb` by drule_then ACCEPT_TAC memory_append_code_open >>
  `a.cs_next_var <= sb.cs_next_var` by
    metis_tac[ci_mono_compile_dynarray_append, ci_mono_def, pairTheory.SND] >>
  irule gas_outcome_full_mods_pure >> asm_rewrite_tac[] >>
  qexistsl_tac [`Gf`,`ff`,`INL ()`,`t`,`tf`] >> asm_rewrite_tac[] >>
  qx_gen_tac `hz` >> strip_tac >> BETA_TAC >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  pure_rewrite_tac[memory_append_gas_obs_frames, return_buf_sep_gas_obs,
    stmt_state_rel_gas_obs, alloca_frame_gas_obs] >> simp[] >> suspend "post"
QED

Resume memory_append_suffix_landing[post]:
  `typed_copy_state_frame a (w2n basew+k)
    (type_memory_size (ArrayTV tv (Dynamic cap))) s t` by fs[] >>
  qpat_assum `write_place _ _ _ _ = _`
    (mp_then (Pat `write_place _ _ _ _ = _`) mp_tac
      (INST_TYPE [alpha |-> ``:256``] assign_local_install_post_mods)) >>
  disch_then (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (fn th => qpat_assum `ghost_inv_at_mods (DF hz) _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel hz _ _ _ _ _ _`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (mp_tac o Q.INST [`tf` |-> `tf`,`sb` |-> `sb`,`lctx` |-> `lctx`,
                               `Gf` |-> `Gf`] o SPEC_ALL) >>
  (impl_tac >- suspend "install_premises") >>
  strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED

Resume memory_append_suffix_landing[install_premises]:
  conj_tac
  >- (strip_tac >> irule local_copy_immutable_frame_mods >>
      goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >> simp[]) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise memory_append_suffix_landing[local]

(* This is the saved target, not a second evaluation of the path.  Its
   provenance names the root allocation even when its offset is nonzero. *)
Theorem memory_append_saved_covers[local]:
  ptr_covers G tn root u sz /\ lookup_var root u = SOME basew /\
  lookup_var p u = SOME bp /\ FLOOKUP G p = FLOOKUP G root /\ op_taint tn (Var p) = {} /\
  w2n bp = w2n basew+k /\ k+bytes <= sz ==>
  ptr_covers G tn p u bytes
Proof
  rw[ptr_covers_def] >> goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  `w = basew` by metis_tac[optionTheory.SOME_11] >> gvs[] >> decide_tac
QED

Theorem memory_append_scratch_kept[local]:
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
  (!n b sz. local_region cenv fin.scopes u n b sz <=>
             local_region cenv es.scopes s0 n b sz) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
  ghost_kept_at lo cenv fin sm Gu tu u Gz tz ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz
Proof
  strip_tac >> irule wordArgsPtrTheory.ghost_kept_at_trans >>
  goal_assum (drule_at (Pat `ghost_kept_at _ _ fin _ _ _ _ _ _`)) >> simp[]
QED

(* A bytestring can have different declared and physical bounds, but the
   same value footprint and local placement. *)
Theorem memory_append_physical_at[local]:
  evaluate_type (get_tenv cx) pt = SOME ptv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type ptv v /\ value_has_type stv v /\
  (pt = sty \/ is_bytestring_type pt /\ is_bytestring_type sty) /\
  expr_val_at cenv cx pt sp sm fin v op u ==>
  expr_val_at cenv cx sty sp sm fin v op u
Proof
  strip_tac >> Cases_on `pt = sty` >- fs[] >> fs[] >>
  `val_footprint ptv v = val_footprint stv v` by metis_tac[valueCopyBytesTheory.bytestring_val_footprint_eq] >>
  `!n k. local_val_at cenv cx n k ptv v ==> local_val_at cenv cx n k stv v` by
    (`?b1. ptv = BaseTV b1` by metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
     `?b2. stv = BaseTV b2` by metis_tac[valueCopyBytesTheory.bytestring_type_value] >>
     gvs[local_val_at_def] >> rpt strip_tac >> disj2_tac
     >- (qexists_tac `b1` >> simp[] >> metis_tac[val_footprint_le,value_has_type_memory_wf]) >>
     qexists_tac `bt0` >> simp[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def,value_has_type_memory_wf,valueCopyBytesTheory.is_bytestring_word_type] >>
  disch_then (qx_choose_then `w` strip_assume_tac) >> qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]
QED

Theorem memory_append_operand[local]:
  evaluate_type (get_tenv cx) pt = SOME ptv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type ptv v /\ value_has_type stv v /\
  ~is_word_type pt /\
  (pt = sty \/ is_bytestring_type pt /\ is_bytestring_type sty) /\
  expr_val_rel cx pt v op u /\ ptr_val_ok cx pt v op G tn u /\
  expr_store_bound cx pt v op u /\ u.vs_alloca_next < dimword (:256) /\
  0 < type_memory_size stv ==>
  ?w. eval_operand op u = SOME w /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
       val_in_memory stv v (w2n w) mem) /\
    w2n w + val_store_size stv v <= u.vs_alloca_next /\
    w2n w + val_store_size stv v < dimword (:256)
Proof
  strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_val_rel_def] >>
  `!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
      val_in_memory ptv v (w2n w) mem` by fs[ptr_val_ok_def,ptr_mem_ok_def] >>
  `val_store_size ptv v = val_store_size stv v` by
    (Cases_on `pt = sty` >- gvs[] >> fs[] >> metis_tac[valueCopyBytesTheory.bytestring_val_store_size_eq]) >>
  `0 < val_store_size stv v` by simp[bodyDeclCopyMemoryTheory.val_store_size_pos] >>
  `w2n w + val_store_size stv v <= u.vs_alloca_next` by
    (qpat_assum `expr_store_bound _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_store_bound_def]) >>
     disch_then (qspecl_then [`ptv`,`w`] mp_tac) >> simp[]) >>
  `w2n w + val_store_size stv v < dimword (:256)` by decide_tac >>
  qexists_tac `w` >> simp[] >>
  Cases_on `pt = sty` >- gvs[] >> fs[] >> metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer]
QED

Theorem append_memory_landing_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env e (mid with gas_obs := gs) /\
  type_widens_to env.type_defs (expr_type e) elem /\ assignable_type (get_tenv cx) elem /\
  stmt_exprs_ok cenv (Append bt e) /\ target_place_type cenv bt = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) = (INL v,fin) /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) fin /\
  compile_get_target_ptr compile_expr cenv bt sa = ((Var p,SOME LocMemory,SOME (ValPT (ArrayT elem (Dynamic cap)))),sp) /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  (if is_word_type elem then
     compile_dynarray_append cenv (Var p) op (word_scale LocMemory)
       (elem_size_in_location cenv LocMemory elem) elem (lowered_value_type cenv e)
       cap T LocMemory sm = ((),sb) /\ fn_has_code sm sb func
   else ?tmp sc sd.
     compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
     compile_store_memory cenv op tmp.buf_operand elem (lowered_value_type cenv e) sc = ((),sd) /\
     compile_dynarray_append cenv (Var p) tmp.buf_operand (word_scale LocMemory)
       (elem_size_in_location cenv LocMemory elem) elem elem cap F LocMemory sd = ((),sb) /\
     fn_has_code sm sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func) /\
  lookup_var p s = SOME bp /\ not_fresh_at sp p /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (Var p,SOME LocMemory,SOME (ValPT (ArrayT elem (Dynamic cap)))) G tn s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) bp (SOME LocMemory)
    (Type (ArrayT elem (Dynamic cap))) /\
  lookup_scopes id mid.scopes = SOME initial /\
  (!ty. cenv.ce_var_type id = SOME ty ==> evaluate_type (get_tenv cx) ty = SOME initial.type) /\
  evaluate_subscripts initial.type initial.value path = INL v0 /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\ immutable_frame_mods func cenv cx mid s /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
    expr_post_mods H ctx func cenv cx e mid sp sm s fin v op u /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tu u) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  ghost_kept_at lo cenv mid sp G tn s Gu tu /\
  ptr_val_ok cx (post_value_type cenv e) v op Gu tu u /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gu u) /\
  expr_store_bound cx (post_value_type cenv e) v op u /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sp /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  (!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm u /\ return_buf_sep d cenv fin u /\ alloca_history func u /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv fin u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
  (!n b sz. local_region cenv fin.scopes u n b sz <=>
             local_region cenv es.scopes s0 n b sz) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (append_place cx (MemoryPlace id path) v) (fin,u,Gu,tu)
    ^append_memory_post ^append_memory_exit
Proof
  strip_tac >>
  `?H. valid_horizon cx st0 H fin.storage_trace` by metis_tac[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _` drule >> strip_tac >>
  qpat_assum `place_ptr_rel _ _ _ (PlaceR (MemoryPlace _ _)) _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  gvs[] >>
  Cases_on `evaluate_type (get_tenv cx) elem` >>
  gvs[Once evaluate_type_def, LET_THM, bound_length_def, AllCaseEqs()] >>
  rename1 `evaluate_type (get_tenv cx) elem = SOME tv` >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `type_memory_bytes cenv elem = type_memory_size tv` by
    (irule assign_name_memory_bytes_mods >> goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >> simp[]) >>
  `0 < type_memory_size tv` by simp[type_memory_size_slots] >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz)` >>
  rename1 `lookup_var root s = SOME basew` >>
  `0 < sz ==> lo <= w2n basew` by suspend "floor" >>
  qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qabbrev_tac `bp = basew + n2w k` >>
  `bp = basew + n2w k` by simp[Abbr `bp`] >>
  drule_all_then strip_assume_tac
    (PURE_REWRITE_RULE [write_subscript_source_gas_obs_mods] append_memory_rhs_view_mods) >>
  suspend "saved"
QED

Resume append_memory_landing_mods[floor]:
  strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] body_full_local_region_lower_bound_mods) >>
  goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  qpat_assum `immutable_frame_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def]) >>
  qexistsl_tac [`DF H`,`H`,`mid`,`id`,`sz`,`s`] >>
  simp[local_region_def, immutable_decl_sep_mods_def] >> metis_tac[]
QED

Resume append_memory_landing_mods[saved]:
  qpat_x_assum `bp = basew + n2w k` kall_tac >>
  qpat_x_assum `Abbrev (bp = _)` kall_tac >>
  `ci_mono sp sm` by metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
  `sp.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `not_fresh_at sm p` by metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sp` >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     stmt_state_rel H ctx func cenv cx fin u /\ immutable_frame_mods func cenv cx fin u /\
     storage_well_formed_on cx fin (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tu u` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> _`
       (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post_mods H ctx func cenv cx e mid sp sm s fin v op u`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `lookup_var p u = SOME bp` by
    (qpat_assum `!x w. not_fresh_at sp x /\ lookup_var x s = SOME w ==> _` (drule_all_then ACCEPT_TAC)) >>
  `op_taint tu (Var p) = {} /\ FLOOKUP Gu p = FLOOKUP Gu root` by suspend "saved_ghost" >>
  `ptr_covers Gu tu root u sz` by
    (qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tu u`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     qpat_assum `!name entry p sz. lookup_scopes name fin.scopes = SOME entry /\ _ ==> _`
       (qspecl_then [`id`,`entry`,`root`,`sz`] mp_tac) >> simp[]) >>
  `ptr_covers Gu tu p u (type_memory_size (ArrayTV tv (Dynamic cap)))` by
    (irule memory_append_saved_covers >> simp[] >> qexistsl_tac [`basew`,`k`,`root`,`sz`] >> simp[]) >>
  `type_memory_size tv + 64 < dimword (:256) /\ cap < dimword (:256)` by suspend "sizes" >>
  Cases_on `is_word_type elem` >>
  qpat_x_assum `if is_word_type elem then _ else _` mp_tac >> simp[] >> strip_tac
  >- suspend "word" >>
  suspend "aggregate"
QED

Resume append_memory_landing_mods[saved_ghost]:
  `not_fresh_at sp root` by
    (qpat_assum `local_ptrs_reserved cenv sp`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = SOME _ ==> _`
       (qspecl_then [`id`,`id`,`root`,`sz`,`sz`] mp_tac) >> simp[]) >>
  qpat_assum `ghost_kept_at lo cenv mid sp G tn s Gu tu`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `!x. not_fresh_at sp x ==> _` (qspec_then `root` mp_tac) >>
  qpat_assum `!x. not_fresh_at sp x ==> _` (qspec_then `p` mp_tac) >>
  qpat_assum `target_ptr_ok _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_ptr_ok_def,op_prov_def]) >> simp[]
QED

Resume append_memory_landing_mods[sizes]:
  conj_tac
  >- (`type_memory_bytes cenv elem < 2**64` by
        (qpat_assum `target_place_type cenv bt = _` (fn ty =>
           qpat_assum `stmt_exprs_ok cenv (Append bt e)`
             (mp_tac o SRULE [bodySimTheory.stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,ty])) >>
         Cases_on `is_word_type elem` >> simp[] >>
         drule_all_then (fn size => simp[size]) entryDecodeStaticPropsTheory.word_type_memory_size) >>
      qpat_assum `type_memory_bytes cenv elem = type_memory_size tv` (fn size =>
        qpat_assum `type_memory_bytes cenv elem < 2**64` (mp_tac o PURE_REWRITE_RULE [size])) >>
      simp[dimword_def] >> decide_tac) >>
  `cap <= cap * type_slot_size tv` by
    (qpat_assum `0 < type_slot_size tv` mp_tac >>
     Cases_on `type_slot_size tv` >> simp[MULT_CLAUSES]) >>
  qpat_assum `type_slot_size (ArrayTV tv (Dynamic cap)) < _` mp_tac >>
  pure_rewrite_tac[type_slot_size_def,bound_length_def] >> decide_tac
QED

Resume append_memory_landing_mods[word]:
  qpat_assum `expr_post_mods H ctx func cenv cx e mid sp sm s fin v op u`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_all_then strip_assume_tac (SRULE [] (Q.INST [`es` |-> `mid with gas_obs := gs`] append_memory_word_input_mods)) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK u,Gu,tu)` by
    simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  irule memory_append_suffix_landing >> suspend "word_inputs"
QED

Resume append_memory_landing_mods[word_inputs]:
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gu`,`sm`,`basew`,`bp`,`cap`,`elem`,`entry`,`k`,
    `p`,`root`,`u`,`op`,`sz`,`tu`,`tv`,`vs`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Resume append_memory_landing_mods[aggregate]:
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `type_widens_to (get_tenv cx) (expr_type e) elem` by fs[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  drule_all_then strip_assume_tac ann_copy_nonword_read_types_mods >>
  rename1 `evaluate_type _ (lowered_value_type cenv e) = SOME rt` >>
  rename1 `evaluate_type _ (post_value_type cenv e) = SOME pt` >>
  `u.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx fin u`
       (assume_tac o MATCH_MP stmt_state_rel_alloca_room) >>
     drule_then ACCEPT_TAC alloca_room_next_lt) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sp sm fin v op u` by
    (irule memory_append_physical_at >>
     qpat_assum `expr_val_at cenv cx (post_value_type cenv e) _ _ _ _ _ _` (irule_at Any) >>
     qexistsl_tac [`rt`,`pt`] >> simp[]) >>
  drule_all_then (qx_choose_then `sw` strip_assume_tac) memory_append_operand >>
  `?xs. op = Var xs /\ ptr_covers Gu tu xs u (type_memory_size rt)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     conj_tac >- fs[ptr_val_ok_def] >>
     conj_tac >- (qexists_tac `sw` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `not_fresh_at sm xs` by
    (drule exprOperandVarTheory.compile_lower_value_var >> disch_then (qspec_then `xs` mp_tac) >> simp[]) >>
  `lookup_var xs u = SOME sw` by fs[eval_operand_def] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `local_region cenv fin.scopes u id (w2n basew) sz` by
    (pure_rewrite_tac[local_region_def] >> simp[]) >>
  `val_wf (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))` by simp[value_has_type_memory_wf] >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  suspend "scratch"
QED

Resume append_memory_landing_mods[scratch]:
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        len = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
      (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_inv_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc)` by simp[] >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  qpat_assum `compile_store_memory _ _ _ _ _ _ = _`
    (mp_then (Pat `compile_store_memory _ _ _ _ _ _ = _`) mp_tac append_memory_scratch_ready_mods) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  disch_then (mp_tac o Q.INST [`explicit` |-> `explicit`,`PG` |-> `PG`,
    `H0` |-> `H`,`G` |-> `Gu`,`tn` |-> `tu`,`lo` |-> `lo`,
    `vs` |-> `vs`,`bp` |-> `bp`,`k` |-> `k`,`cap` |-> `cap`,
    `dtv` |-> `tv`,`stv` |-> `rt`] o SPEC_ALL) >>
  (impl_tac >- suspend "scratch_inputs") >>
  disch_then (qx_choosel_then [`z`,`q`,`b`,`Gz`,`tz`] strip_assume_tac) >>
  suspend "scratch_finish"
QED

Resume append_memory_landing_mods[scratch_inputs]:
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume append_memory_landing_mods[scratch_finish]:
  `lookup_var p z = SOME bp /\ not_fresh_at sd p` by
    (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `not_fresh_at sm root` by
    (qpat_assum `local_ptrs_reserved cenv sm`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP _ n1 = SOME _ ==> _`
       (qspecl_then [`id`,`id`,`root`,`sz`,`sz`] mp_tac) >> simp[]) >>
  `lookup_var root z = SOME basew` by
    (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (qspec_then `root` mp_tac) >> simp[]) >>
  `ptr_covers Gz tz p z (type_memory_size (ArrayTV tv (Dynamic cap)))` by
    (qpat_assum `!x len. not_fresh_at sm x /\ ptr_covers Gu tu x u len ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `!hz. valid_horizon cx st0 hz fin.storage_trace ==>
     stmt_state_rel hz ctx func cenv cx fin z /\ immutable_frame_mods func cenv cx fin z /\
     storage_well_formed_on cx fin (FST hz) /\ ghost_inv_at_mods (DF hz) lo d cenv cx fin Gz tz z` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==> stmt_state_rel _ _ _ _ _ fin u /\ _`
       (drule_then strip_assume_tac) >> first_assum (drule_then ACCEPT_TAC)) >>
  `alloca_frame cenv es sa s0 cenv fin z` by
    (irule alloca_frame_trans >>
     qpat_assum `alloca_frame cenv fin sm u cenv fin z` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` by
    (irule memory_append_scratch_kept >>
     qpat_assum `ghost_kept_at lo cenv fin sm Gu tu u Gz tz` (irule_at Any) >> simp[]) >>
  `return_buf_sep d cenv fin z` by suspend "scratch_sep" >>
  suspend "aggregate_inputs"
QED

Resume append_memory_landing_mods[scratch_sep]:
  irule return_buf_sep_transport >>
  qpat_assum `return_buf_sep d cenv fin u` (irule_at Any) >>
  conj_tac
  >- (rpt strip_tac >> gvs[bodySimFullTheory.return_buf_sep_def, return_buf_frame_def, allocas_from_def] >>
      rpt strip_tac >>
      qpat_assum `!aid off len. FLOOKUP z.vs_allocas aid = SOME (off,len) ==> _`
         (drule_then strip_assume_tac) >> res_tac >> decide_tac) >>
  rpt strip_tac >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  irule (iffLR exprSimCopyTheory.copy_buffer_local_region_frame) >>
  qexistsl_tac [`sm`,`z`] >> simp[]
QED

Resume append_memory_landing_mods[aggregate_inputs]:
  `compile_dynarray_append cenv (Var p) tmp.buf_operand 32 (type_memory_size tv)
    elem elem cap F LocMemory sd = ((),sb)` by
    (qpat_assum `compile_dynarray_append cenv (Var p) tmp.buf_operand _ _ _ _ _ _ _ _ = _`
       (mp_tac o PURE_REWRITE_RULE [word_scale_def, elem_size_in_location_def, is_slot_addressed_def]) >>
     simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
    s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w` by
    (rpt strip_tac >> `not_fresh_at sm x` by simp[] >>
     qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at sd x /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> _`
       (drule_all_then assume_tac) >> simp[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP z.vs_allocas aid = SOME ent` by
    (rpt strip_tac >>
     qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> _` (drule_then assume_tac) >>
     qpat_assum `!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==> _` (drule_then ACCEPT_TAC)) >>
  `!x len. cenv.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x len. cenv.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x. tmp.buf_operand = Var x ==> not_fresh_at sd x` by simp[] >>
  `?xs sw. tmp.buf_operand = Var xs /\ lookup_var xs z = SOME sw /\
    ptr_covers Gz tz xs z (type_memory_size tv) /\
    w2n sw + val_store_size tv v <= z.vs_alloca_next /\
    !mem. mem_agree_outside tz.t_mem z.vs_memory mem ==> val_in_memory tv v (w2n sw) mem` by
    suspend "scratch_value" >>
  irule memory_append_suffix_landing >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gz`,`sd`,`basew`,`bp`,`cap`,`elem`,`entry`,`k`,
    `p`,`root`,`z`,`tmp.buf_operand`,`sz`,`tz`,`tv`,`vs`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

Resume append_memory_landing_mods[scratch_value]:
  qexistsl_tac [`q`,`n2w b`] >>
  `w2n (n2w b:bytes32) = b` by (simp[w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
  `val_store_size tv v <= type_memory_size tv` by (irule val_store_size_le >> first_assum ACCEPT_TAC) >>
  simp[] >> decide_tac
QED

Finalise append_memory_landing_mods
