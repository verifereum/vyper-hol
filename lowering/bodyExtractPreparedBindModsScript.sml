(* Bind the reached, forced Extract32 offset to the word-producing suffix. *)
Theory bodyExtractPreparedBindMods
Ancestors
  bodyExtractPrepareMods bodyExtractSavedDescriptorMods bodyExtractJoinFrameMods
  bodyExtractOffsetWordMods bodyExtractSuffixMods bodyForcedStorageFrameMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  bodyFullPostsMods exprBodyPreProps vyperStorageFootprint vyperStorageTrace
  exprLoweringProps loweringStateRelDefs bodyFullShadowBodyInv freshWrites
  exprSimWordArgs typeBuiltinPrereqs exprSimExtract32Source context exprSimDefs loweringPosts
Libs monadsyntax

val prepare_stmt = concl (Q.INST [`ee` |-> `mid`] (SPEC_ALL extract32_prepare_mods));
val prepared =
  let val (args, body) = boolSyntax.strip_exists (snd (boolSyntax.dest_imp prepare_stmt))
  in list_mk_abs (args, body) end;

val extract_expr = ``TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]``;
val extract_vv = ``StackValue (BaseT bt) op``;
val forced_off = ``bind (eval_expr cx off) (read_result cx)``;
val next = ``\w. bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
    [expr_type src;expr_type off] [BytesV bs;w])) (\v. return (Value v))``;

val off_post = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:value + exception) ee G3 tn3 t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx off mid sn sq u ee v offop t /\
  expr_store_bound cx (post_value_type cenv off) v offop t /\
  t.vs_current_bb = sq.cs_current_bb /\ t.vs_inst_idx = LENGTH sq.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  u.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G3 tn3 t /\
  ptr_val_ok cx (post_value_type cenv off) v offop G3 tn3 t /\
  (~is_word_type (post_value_type cenv off) ==> ptr_buf_ok cenv off offop G3 t) /\
  ghost_kept_at lo cenv mid sn G2 tn2 u G3 tn3``;

val outcome = ``gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0``;
val outcome_vv = Term.inst [Type.alpha |-> ``:eval_result``] outcome;
val outcome_value = Term.inst [Type.alpha |-> ``:value``] outcome;
val exit_post = ``\(H:(bool # bytes32 # type_value) list # num list) res ee
    (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;

val off_exit = Term.inst [Type.alpha |-> ``:value``] exit_post;
val vv_exit = Term.inst [Type.alpha |-> ``:eval_result``] exit_post;

val vv_post = ``\(H:(bool # bytes32 # type_value) list # num list) (res:eval_result + exception) ee G tn t. ?tv. res = INL tv /\
  vv_post_mods H ctx func cenv cx ^extract_expr es sa sb s0 ee tv ^extract_vv t /\
  vv_store_bound cx (post_value_type cenv ^extract_expr)
    (lowered_value_type cenv ^extract_expr) ee tv ^extract_vv t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv ^extract_expr) tv ^extract_vv ee G tn t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv ^extract_expr) /\
       ~is_bytestring_type (post_value_type cenv ^extract_expr) ==>
       vv_own cenv cx (post_value_type cenv ^extract_expr) sa sb ee tv ^extract_vv t /\
       (!t' p. ^extract_vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location ^extract_vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv ^extract_expr) = SOME rt /\
                 eval_operand (vv_operand ^extract_vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
  (!t' op'. ^extract_vv = StackValue t' op' /\
      ~is_word_type (post_value_type cenv ^extract_expr) ==> ptr_buf_ok cenv ^extract_expr op' G t) /\
  (!t' p. ^extract_vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv ^extract_expr p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem extract32_prepared_bind_mods:
  (^prepared) p u G2 tn2 len data /\
  (^outcome_value) (^forced_off) (mid,u,G2,tn2) (^off_post) (^off_exit) /\
  expr_body_pre_mods mods cenv cx env off mid /\
  body_const_cells_agree_mods mods cx env mid /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := xs) = (INL (BytesV bs),mid) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  extract32_result_base_ok bt /\ is_word_type (BaseT bt) /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  expr_type off = BaseT (UintT k) /\
  lower_value compile_expr cenv ty off sn = (offop,sq) /\
  compile_extract32_load lenop dataop offop sq = (raw,sr) /\
  compile_clamp_basetype raw (BaseT bt) sr = (op,sb) /\
  ci_mono sa sn /\ ci_mono sn sq /\ fn_has_code sq sb func /\ fn_inst_ids_distinct func ==>
  (^outcome_vv) (bind (^forced_off) (^next)) (mid,u,G2,tn2) (^vv_post) (^vv_exit)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL v) em (OK t)` >>
      qexistsl_tac [`em`,`t`,`v`] >> BETA_TAC >> conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- irule bodyForcedStorageFrameModsTheory.bop_forced_storage_frame
  >- simp[storage_trace_frame_bind_all,storage_trace_frame_lifts,storage_trace_frame_return] >>
  qexists_tac `\H res ee G3 tn3 t. (^off_post) H res ee G3 tn3 t /\
    ~t.vs_halted /\ ee.gas_obs = []` >> BETA_TAC >> conj_tac
  >- suspend "reached" >>
  irule gas_outcome_full_mods_post_source >> BETA_TAC >>
  goal_assum (drule_at Any) >> BETA_TAC >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC
    [INST_TYPE [beta |-> ``:value``] stmtSimPropsTheory.expr_exit_INR_type,
     INST_TYPE [beta |-> ``:value``] haltExitProjTheory.halt_exit_INR_type] >> simp[]
QED

Resume extract32_prepared_bind_mods[reached]:
  qx_genl_tac [`marks`,`res`,`ee`,`G3`,`tn3`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >> disj1_tac >> qexists_tac `v` >>
  pure_rewrite_tac[REFL_CLAUSE, AND_CLAUSES] >>
  qabbrev_tac `obs = gas_explicit marks u.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `(^forced_off) (mid with gas_obs := obs) = (INL v,ee)` by
    (qpat_assum `!tail. bind (eval_expr cx off) _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >> simp[Abbr `obs`]) >>
  `expr_body_pre_mods mods cenv cx env off (mid with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (mid with gas_obs := obs)` by
    simp[bodyWriteSubscriptSourceModsTheory.write_subscript_source_gas_obs_mods] >>
  drule_all_then (qx_choose_then `i` strip_assume_tac) extract32_offset_word_mods >>
  qpat_x_assum `v = IntV i` SUBST_ALL_TAC >>
  suspend "suffix"
QED

Resume extract32_prepared_bind_mods[suffix]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H (mid with gas_obs := obs).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl_tac [`^forced_off`,`INL (IntV i)`,`ee`] >>
     asm_rewrite_tac[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H (es with gas_obs := xs).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl_tac [`bind (eval_expr cx src) (read_result cx)`,`INL (BytesV bs)`,`mid`] >>
     asm_rewrite_tac[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
    (qspecl_then [`storage_trace_horizon ee.storage_trace`] mp_tac) >>
  (impl_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_assum `expr_body_pre_mods _ _ _ _ off mid`
    (assume_tac o MATCH_MP expr_body_pre_mods_inv) >>
  qpat_x_assum `lenop = Var len` SUBST_ALL_TAC >>
  qpat_x_assum `dataop = Var data` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac extract32_saved_descriptor_mods >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
   sn.cs_next_var <= sq.cs_next_var` by fs[ci_mono_def] >>
  `sa.cs_next_var <= sq.cs_next_var /\ s0.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `local_ptrs_reserved cenv sq` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sq x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sq x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `not_fresh_at sq len /\ not_fresh_at sq data` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sn` >> simp[]) >>
  `allocas_from lo t` by fs[ghost_inv_at_mods_def] >>
  qpat_assum `expr_post_mods _ _ _ _ _ off _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `alloca_inv t` by fs[stmt_state_rel_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
     wb_frame cenv es ee sa s0 t /\
     (~expr_has_effect ^extract_expr ==> pure_frame cenv func es sa s0 t) /\
     immutable_frame_mods func cenv cx ee t /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G3 tn3 t /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 G3 tn3` by suspend "join_frames" >>
  suspend "apply_suffix"
QED

Resume extract32_prepared_bind_mods[join_frames]:
  qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H es.storage_trace` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?v. _) /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `INL (IntV i) = INL _` (SUBST_ALL_TAC o SIMP_RULE bool_ss [sumTheory.INL_11]) >>
  irule extract32_join_frame_mods >>
  qpat_assum `expr_post_mods H _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post_mods H _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` (irule_at Any) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume extract32_prepared_bind_mods[apply_suffix]:
  irule gas_outcome_full_mods_post_source >> irule_at Any extract32_suffix_mods >>
  qpat_assum `compile_extract32_load _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_clamp_basetype _ _ _ = _` (irule_at Any) >>
  qpat_assum `ptr_mem_ok _ _ _ _ G3 tn3 t` (irule_at Any) >>
  qpat_assum `val_in_memory _ (BytesV bs) p _` (irule_at Any) >>
  qexistsl_tac [`tn0`,`sa`,`s0`,`es`,`d`,`G0`] >>
  BETA_TAC >> simp[DISJ_IMP_THM,FORALL_AND_THM,post_value_type_def,vyperASTTheory.expr_type_def,
    vv_location_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==>
    stmt_state_rel _ _ _ _ _ _ _ /\ storage_well_formed_on _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Finalise extract32_prepared_bind_mods
