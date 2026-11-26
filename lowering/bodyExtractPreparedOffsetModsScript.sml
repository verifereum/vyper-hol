(* Launch the forced offset at the machine-only Extract32 preparation cut. *)
Theory bodyExtractPreparedOffsetMods
Ancestors
  bodyExtractPrepareMods bodyAugGuardedPrefixMods bodyFullIfExpReach
  exprSimFullBundleProps exprOperandVar bodyMemoryDefs stateRelProj
  vyperStorageFootprint rawCallBufferPtr typeBuiltinPrereqs
  exprLoweringProps vyperValue compileEnv bodyFullPostsMods loweringPosts
  exprSimHypsDefs bodyPtrDefs freshWrites
Libs monadsyntax

(* Take the preparation certificate verbatim at the source landing. *)
val prepare_stmt = concl (SPEC_ALL extract32_prepare_mods);
val prepare_contract = boolSyntax.list_mk_forall (free_vars prepare_stmt, prepare_stmt);
val prepare_at = concl (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
  (SPEC_ALL extract32_prepare_mods));
val prepared =
  let val (args, body) = boolSyntax.strip_exists (snd (boolSyntax.dest_imp prepare_at))
  in list_mk_abs (args, body) end;

val src_post = ``expr_post_mods (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx src es sa sm s0 ee (BytesV bs) srcop s /\
  expr_store_bound cx (expr_type src) (BytesV bs) srcop s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  ptr_val_ok cx (expr_type src) (BytesV bs) srcop G tn s /\
  ptr_buf_ok cenv src srcop G s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

val off_post = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:value + exception) tail G3 tn3 t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx off ee sn sq u tail v offop t /\
  expr_store_bound cx (post_value_type cenv off) v offop t /\
  t.vs_current_bb = sq.cs_current_bb /\ t.vs_inst_idx = LENGTH sq.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx tail G3 tn3 t /\
  ptr_val_ok cx (post_value_type cenv off) v offop G3 tn3 t /\
  (~is_word_type (post_value_type cenv off) ==> ptr_buf_ok cenv off offop G3 t) /\
  ghost_kept_at lo cenv ee sn G2 tn2 u G3 tn3``;

val off_exit = ``\(H:(bool # bytes32 # type_value) list # num list)
    (res:value + exception) tail (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx tail res r /\
  (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z)``;

val outcome = ``gas_outcome_full_mods
  (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0``;
val value_outcome = Term.inst [Type.alpha |-> ``:value``] outcome;
val forced_off = ``bind (eval_expr cx off) (read_result cx)``;

Theorem extract32_prepared_offset_mods:
  ^prepare_contract ==>
  lower_value compile_expr cenv (expr_type src) src sa = (srcop,sm) /\
  compile_bytestring_src srcop sm = ((lenop,dataop),sn) /\
  ci_mono sa sm /\ ci_mono sm sn /\ fn_has_code sm sn func /\
  lower_value compile_expr cenv ty off sn = (offop,sq) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr off) shn =
    (offop,shq) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sn,sq,shn,shq) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\ return_buf_frame d cenv sa s0 /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ~s.vs_halted /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ^src_post) /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty off ee /\
  gas_admissible (^forced_off) expr_res_ok ee /\ storage_trace_frame (bind (^forced_off) k) /\
  (!sv p u G2 tn2 len data.
    srcop = Var sv /\ (^prepared) p u G2 tn2 len data /\
    (^value_outcome) (^forced_off) (ee,u,G2,tn2) (^off_post) (^off_exit) ==>
    (^outcome) (bind (^forced_off) k) (ee,u,G2,tn2) Q R) ==>
  (^outcome) (bind (^forced_off) k) (ee,s,G,tn) Q R
Proof
  disch_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qhdtm_x_assum `expr_sim_full_code`
    (strip_assume_tac o PURE_REWRITE_RULE [expr_sim_full_code_def]) >>
  qpat_x_assum `!sv p u G2 tn2 len data. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (assume_tac o BETA_RULE) >>
  `~is_word_type (expr_type src)` by simp[is_word_type_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ^src_post`
    (drule_then strip_assume_tac) >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `alloca_inv s` by fs[expr_post_def, stmt_state_rel_def] >>
  `?sv. srcop = Var sv` by
    (drule_all_then strip_assume_tac extract32_source_post_alloca_bound >>
     `ptr_mem_ok cx (expr_type src) (BytesV bs) srcop G tn s` by fs[ptr_val_ok_def] >>
     drule_all_then strip_assume_tac ptr_mem_ok_dynamic_bytes_site >> simp[]) >>
  `not_fresh_at sm sv` by (drule_all compile_lower_value_var >> simp[]) >>
  `^prepare_at` by first_assum MATCH_ACCEPT_TAC >>
  pop_assum mp_tac >> impl_tac >- suspend "prepare_inputs" >>
  disch_then (qx_choosel_then [`p`,`u`,`G2`,`tn2`,`len`,`data`] (fn th =>
    assume_tac th >> strip_assume_tac th)) >>
  suspend "launch_and_attach"
QED

Resume extract32_prepared_offset_mods[prepare_inputs]:
  qpat_assum `srcop = Var sv` (fn th => pure_rewrite_tac [GSYM th]) >>
  asm_simp_tac bool_ss [] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> first_x_assum irule >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> first_x_assum irule >> simp[])
  >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ^src_post`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[Once CONJ_ASSOC] >>
  strip_tac >> simp[]
QED

Resume extract32_prepared_offset_mods[launch_and_attach]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
    (drule_then strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o PURE_REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sn u` by
    (qpat_assum `expr_post_mods _ _ _ _ _ src _ _ sn _ ee _ _ u`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK u,G2,tn2)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
         gas_origin_ptr_path_dalloca_fmp_headroom) >>
     disch_then (fn th => map_every qx_gen_tac [`ff`,`ii`,`zz`] >> strip_tac >>
       qspecl_then [`ff`,`ii`,`zz`] mp_tac th) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x)` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `(^value_outcome) (^forced_off) (ee,u,G2,tn2) (^off_post) (^off_exit)` by
    (qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
     disch_then (qspecl_then [`st0`,`sn`,`sq`,`shn`,`shq`,`offop`,`u`,`G2`,`tn2`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  irule augassign_zero_prefix_guarded_mods >>
  asm_simp_tac bool_ss [] >> qexistsl_tac [`G2`,`u`,`tn2`] >>
  conj_tac
  >- (qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ [] _ /\ _`
        (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_x_assum `!sv p u G2 tn2 len data. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qspecl_then [`sv`,`p`,`u`,`G2`,`tn2`,`len`,`data`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise extract32_prepared_offset_mods
