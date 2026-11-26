(* The outer Concat run, conditional on the normal checked fold interface. *)
Theory bodyConcatCompactRouteMods
Ancestors
  bodyConcatStaticMods bodyConcatOuterCodeMods bodyConcatPrefixAllocMods
  bodyConcatZeroEntryMods bodyConcatHeaderMods bodyConcatOuterFrameMods
  bodyConcatResultValueMods bodyConcatReadMods bodyConcatCutsMods
  bodyAugGuardedPrefixMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  bodyFullPostsMods bodyFullPredsMods bodyFullShadowBodyInv exprSimFullBundleProps
  exprLoweringProps exprLowering compileEnv context contextProps gasShadowCompileContext
  exprSimAccounts freshWrites fragExec exprSimDefs stmtSimProps haltExitProj
  loweringPosts loweringStateRelDefs
  gasExemptCertMods gasSummary gasStorage vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState vyperAST venomState venomInst words list arithmetic

val loop_post = ``\scratch anchor s5
    (H : (bool # bytes32 # type_value) list # num list)
    (res : value list + vyperState$exception) ee g ts t.
    ?vs. res = INL vs /\ ee.gas_obs = [] /\
      LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                             value_has_type tv v) args vs /\
      concat_live_mods (func,cenv,lo) scratch (ee,s5,t,g,ts)
        ([] ++ FLAT (MAP concat_payload_mods vs)) /\
      concat_old_frame_mods (func,cenv,lo,~EXISTS expr_has_effect args)
        scratch anchor (ee,s5,t,g,ts) /\
      concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,s5,t,g,ts) /\
      expr_sim_inv_mods mods cenv cx env ee /\ return_buf_frame d cenv s5 t``;

val loop_exit = ``\(H : (bool # bytes32 # type_value) list # num list)
   (res : value list + vyperState$exception) ee
   (gt : (string |-> num # num) # taint) r.
   expr_exit res r /\ halt_exit H cx ee res r /\
   (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

val compact_loop = ``!st0 s4 s5 h4 h5 t4 G4 tn4 scratch.
    concat_loop_entry_mods
      (mods,exps,cx,env,src,tops,st0,cenv,~EXISTS expr_has_effect args)
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) scratch (es,s4,t4,G4,tn4)
      args (s5,h4,h5) (es,s4,t4,G4,tn4) [] 0 ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (eval_exprs cx args) (es,t4,G4,tn4)
      (^loop_post scratch (es,s4,t4,G4,tn4) s5) ^loop_exit``;

Theorem concat_compact_vv_mods[local]:
  ^compact_loop /\
  (builtin_args_length_ok (Concat n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Concat n) args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) concat_static_mods >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >>
      (reverse conj_tac >- first_assum ACCEPT_TAC) >> qx_gen_tac `tail` >>
      qpat_x_assum `eval_expr cx (Builtin a (Concat n) args) = _` kall_tac >>
      Cases_on `eval_expr cx (Builtin a (Concat n) args) (es with gas_obs := tail)` >>
      qpat_assum `eval_expr cx _ _ = (_,_)` (pure_rewrite_tac o single) >>
      pure_rewrite_tac[pairTheory.SND] >>
      drule_at (Pat `f st = _`) storage_trace_frame_preserves_bad_domain >>
      simp[evaluate_storage_trace_frame]) >>
  suspend "code"
QED

Resume concat_compact_vv_mods[code]:
  markerLib.RESUME_TAC >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func)
       (sa,sb,shadow_sa,shadow_sb)` by
    (pure_rewrite_tac[expr_sim_full_code_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then (qx_choosel_then
    [`buf`,`ob`,`bv`,`dv`,`ov`,`s1`,`s2`,`s3`,`s4`,`s5`,`s6`,
     `h1`,`h2`,`h3`,`h4`,`h5`,`h6`,`fo`,`binst`,`oinst`]
     (map_every assume_tac o CONJUNCTS) o BETA_RULE o REWRITE_RULE [LET_THM])
    concat_outer_code_mods >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  qabbrev_tac `bsz = concat_alloc_size (MAP expr_type args)` >>
  `32 <= bsz` by (qpat_assum `32 + SUM _ <= bsz` mp_tac >> decide_tac) >>
  `bsz < dimword (:256)` by
    (irule LESS_TRANS >> qexists_tac `2 ** 64` >> simp[dimword_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _`
       (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_inv_at_mods_def]) >> simp[]) >>
  suspend "alloc"
QED

Resume concat_compact_vv_mods[alloc]:
  markerLib.RESUME_TAC >>
  `gas_shadow_state s1 h1` by
    (mp_tac (Q.INST [`nbytes` |-> `bsz`]
      gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     pure_rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  `gas_shadow_state s2 h2` by
    (mp_tac (Q.SPECL [`s1`,`h1`]
      (REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]
        (Q.INST [`opc` |-> `ADD`,`ops` |-> `[Var bv; Lit 32w]`]
          gas_shadow_compiles_emit_op_same))) >> simp[]) >>
  `cs_extends sa s3` by
    (irule cs_extends_trans >> qexists_tac `s2` >>
     (reverse conj_tac >- (irule loweringHaltTheory.compile_alloc_buffer_extends >>
                          goal_assum (drule_at Any))) >>
     irule cs_extends_trans >> qexists_tac `s1` >>
     metis_tac[loweringHaltTheory.compile_alloc_buffer_extends,emit_op_extends_next_var]) >>
  `cs_extends s3 s4` by
    (qspecl_then [`MSTORE`,`[Var ov;Lit 0w]`,`s3`] mp_tac ci_mono_emit_void >>
     simp[ci_mono_def]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) fn_has_code_split >>
  `emit_op ADD [buf.buf_operand; Lit 32w] s1 = (Var dv,s2)` by
    (qpat_assum `buf.buf_operand = Var bv` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`sha` |-> `shadow_sa`, `shbuf` |-> `buf`, `sh1` |-> `h1`,
                  `sh2` |-> `h2`, `shob` |-> `ob`, `sh3` |-> `h3`, `ce` |-> `cenv`,
                  `data_operand` |-> `Var dv`, `s` |-> `s0`,
                  `H0` |-> `storage_trace_horizon es.storage_trace`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL concat_prefix_alloc_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t3`,`G4`,`tn3`,`bv'`,`dv'`,`ov'`,`B`,`ow`]
      (map_every assume_tac o CONJUNCTS)) >>
  suspend "zero"
QED

Resume concat_compact_vv_mods[zero]:
  markerLib.RESUME_TAC >>
  `bv' = bv /\ dv' = dv /\ ov' = ov` by
    (rpt conj_tac >> metis_tac[operand_11]) >>
  qpat_x_assum `bv' = bv` SUBST_ALL_TAC >>
  qpat_x_assum `dv' = dv` SUBST_ALL_TAC >>
  qpat_x_assum `ov' = ov` SUBST_ALL_TAC >>
  qpat_assum `!ow B. concat_loop_code_mods _ _ _ _ _`
    (qspecl_then [`ow`,`B`] assume_tac) >>
  `binst.inst_opcode = ALLOCA /\ oinst.inst_opcode = ALLOCA /\
   binst.inst_id < s4.cs_next_id /\ oinst.inst_id < s4.cs_next_id /\
   FLOOKUP t3.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP t3.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by
    (simp[mk_inst_def] >> decide_tac) >>
  `sa.cs_next_var <= s3.cs_next_var` by fs[ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s3 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qabbrev_tac `pure = ~EXISTS expr_has_effect args` >>
  `pure ==> ~EXISTS expr_has_effect args` by simp[Abbr `pure`] >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `hctx` |-> `shadow_ctx`,
                  `hfunc` |-> `shadow_func`, `G` |-> `G4`, `tn` |-> `tn3`]
    (SPEC_ALL concat_zero_entry_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t4`,`tn4`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!st0 s4 s5 h4 h5 t4 G4 tn4 scratch. concat_loop_entry_mods _ _ _ _ _ _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  irule augassign_zero_prefix_guarded_mods >>
  (conj_tac >- simp[evaluate_storage_trace_frame]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G4`,`t4`,`tn4`] >>
  (conj_tac >- (rpt strip_tac >>
      qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK t4,_,_)` (MATCH_ACCEPT_TAC o SPEC_ALL))) >>
  suspend "bind"
QED

Resume concat_compact_vv_mods[bind]:
  markerLib.RESUME_TAC >>
  qpat_assum `eval_expr cx (Builtin a (Concat n) args) = _`
    (pure_once_rewrite_tac o single) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ finalP _` >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) (es,t4,G4,tn4) listP _` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame (_ : evaluation_state -> (eval_result + vyperState$exception) # evaluation_state)`]
  >- (qx_gen_tac `vs` >> Cases_on `evaluate_concat n vs` >>
      simp[storage_trace_frame_def])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[]) >>
  qexists_tac `listP` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs _ _) _ listP _`
        (irule_at Any) >> BETA_TAC >> simp_tac bool_ss [] >>
      qx_genl_tac [`H`,`res`] >> Cases_on `res` >> simp[] >>
      once_rewrite_tac[INST_TYPE [beta |-> ``:value list``] expr_exit_INR_type,
                       INST_TYPE [beta |-> ``:value list``] halt_exit_INR_type] >> simp[]) >>
  suspend "header_entry"
QED

Resume concat_compact_vv_mods[header_entry]:
  markerLib.RESUME_TAC >>
  qx_genl_tac [`marks`,`res`,`ee`,`G5`,`tn5`,`t5`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.UNABBREV_TAC `listP` >> rule_assum_tac BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
      (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> ?vs. _`
    (drule_then (qx_choose_then `vs` (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp_tac bool_ss [] >>
  qabbrev_tac `p = FLAT (MAP concat_payload_mods vs)` >>
  `concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz) (ee,s5,t5,G5,tn5) p` by
    (qpat_assum `concat_live_mods _ _ _ _` (ACCEPT_TAC o REWRITE_RULE [APPEND])) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    concat_horizon_mods (ctx,func,cenv,cx,lo,d) (H,DF H) (ee,s5,t5,G5,tn5)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ?vs. _`
       (drule_then (qx_choose_then `ws` (map_every assume_tac o CONJUNCTS))) >>
     first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= s5.cs_next_var` by
    (qpat_assum `ci_mono s4 s5` (mp_tac o REWRITE_RULE [ci_mono_def]) >>
     qpat_assum `s4.cs_next_var = _` mp_tac >> decide_tac) >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x` by
    (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x` by
    (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at sa x`
       (drule_then ACCEPT_TAC)) >>
  mp_tac (Q.INST [`sm` |-> `s6`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL concat_header_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t6`,`G6`,`tn6`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "parent_frame"
QED

Resume concat_compact_vv_mods[parent_frame]:
  markerLib.RESUME_TAC >>
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_id <= s4.cs_next_id` by
    (qpat_assum `ci_mono sa s4` (mp_tac o REWRITE_RULE [ci_mono_def]) >> simp_tac bool_ss []) >>
  `!z. not_fresh_at sa z ==> lookup_var z t4 = lookup_var z s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!z. not_fresh_at sa z ==> lookup_var z t4 = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `sa.cs_next_id <= binst.inst_id /\ sa.cs_next_id <= oinst.inst_id` by
    (qpat_assum `binst = mk_inst _ _ _ _` (pure_rewrite_tac o single) >>
     qpat_assum `oinst = mk_inst _ _ _ _` (pure_rewrite_tac o single) >>
     simp[mk_inst_def]) >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:num # num``] concat_outer_frame_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "result"
QED

Resume concat_compact_vv_mods[result]:
  markerLib.RESUME_TAC >>
  qpat_assum `concat_live_mods _ _ (ee,s5,t5,G5,tn5) p`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [concat_live_mods_def]) >>
  `FLOOKUP t6.vs_allocas binst.inst_id = SOME (B,bsz)` by
    (qpat_assum `t6.vs_allocas = t5.vs_allocas` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `binst.inst_id < sb.cs_next_id` by
    (qpat_assum `sb.cs_next_id = _` (pure_rewrite_tac o single) >>
     irule LESS_TRANS >> qexists_tac `s5.cs_next_id` >> simp[]) >>
  `!name b sz. local_region cenv ee.scopes t6 name b sz ==> B+bsz <= b \/ b+sz <= B` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b sz. local_region cenv ee.scopes t6 name b sz ==> regions_disjoint _ _ _ _ /\ _`
       (drule_then (mp_tac o REWRITE_RULE [regions_disjoint_def] o CONJUNCT1)) >>
     simp_tac bool_ss [DISJ_COMM]) >>
  `~expr_has_effect (Builtin a (Concat n) args) ==> pure_frame cenv func es sa s0 t6` by
    (rewrite_tac[expr_has_effect_thm] >> disch_tac >>
     qpat_assum `pure ==> pure_frame _ _ _ _ _ _` irule >>
     simp_tac bool_ss [Abbr `pure`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                    concat_horizon_mods _ _ (ee,sb,t6,G6,tn6)`
    (assume_tac o REWRITE_RULE [concat_horizon_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t6 /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee t6 /\ storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t6 /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `?tvr. evaluate_type (get_tenv cx) a = SOME tvr` (qx_choose_then `tv` assume_tac) >>
  qpat_assum `Abbrev (p = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (bsz = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  mp_tac (Q.INST [`G` |-> `G6`, `tn` |-> `tn6`, `t` |-> `t6`, `aid` |-> `binst.inst_id`]
    (SPEC_ALL (BETA_RULE (REWRITE_RULE [LET_THM] concat_result_value_mods)))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  suspend "outcome"
QED

Resume concat_compact_vv_mods[outcome]:
  markerLib.RESUME_TAC >>
  drule_then (map_every assume_tac o CONJUNCTS) expr_sim_full_endpoint_fields >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t6` by
    (drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  `ee with gas_obs := [] = ee` by
    (simp[evaluation_state_component_equality]) >>
  irule gas_outcome_full_mods_pure >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G6`,`ee`,`INL (Value v)`,`t6`,`tn6`] >>
  (conj_tac >- (qx_gen_tac `tail` >> BETA_TAC >>
    qpat_assum `evaluate_concat n vs = INL v` (fn th => simp_tac (srw_ss()) [th]))) >>
  qx_gen_tac `H` >> disch_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path (D,_,_,_,_,_) (t5,_,_) [] _` irule) >>
  qpat_assum `ee with gas_obs := [] = ee` SUBST1_TAC >>
  simp_tac bool_ss [Abbr `finalP`] >>
  qexists_tac `Value v` >> simp_tac bool_ss [REFL_CLAUSE, AND_CLAUSES] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _ /\ ghost_inv_at_mods _ _ _ _ _ ee G6 tn6 t6`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ t6`
    (drule_then assume_tac) >>
  `is_bytestring_type a` by
    (qpat_assum `(a = _ /\ _) \/ (a = _ /\ _)` strip_assume_tac >> simp[is_bytestring_type_def]) >>
  qpat_assum `is_bytestring_type a`
    (fn th => simp_tac bool_ss [post_value_type_def,expr_type_def,th]) >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   qpat_assum `buf.buf_operand = Var bv`
     (fn th => simp_tac (srw_ss()) [base_ptr_def,vv_location_def,th]) >>
   first_assum ACCEPT_TAC)
QED

Finalise concat_compact_vv_mods

Theorem concat_from_loop_entry_mods:
  ^compact_loop /\
  (builtin_args_length_ok (Concat n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Concat n) args) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_asm1_tac
  >- (mp_tac (SPEC_ALL (BETA_RULE concat_compact_vv_mods)) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) concat_static_mods >>
  mp_tac (SPEC_ALL concat_buffer_read_mods) >>
  (impl_tac >-
   ((conj_tac >- first_assum ACCEPT_TAC) >> (reverse conj_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `(a = _ /\ _) \/ (a = _ /\ _)` strip_assume_tac >> simp[])) >>
  disch_then ACCEPT_TAC
QED
