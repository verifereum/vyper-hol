(* Linked nonword declarations: allocate, read the reached RHS, and install. *)
Theory bodyAnnNonwordRoutesMods
Ancestors arithmetic[qualified,ignore_grammar]
  bodyAnnCopyDeclaredRhsMods bodyAnnCopyIntervalsMods bodyAnnAllocEntryMods
  bodyAnnCopySequenceMods bodyAnnEmptyContinuationMods bodyAnnNonwordReadTypesMods
  bodyAnnCopySourceReadyMods bodyAnnCopyReadFrameMods bodyAnnBytesInstalledMods
  bodyAnnTypedInstalledMods bodyAssignNameCopyReadFrontierMods
  bodyFullPredsMods bodyFullPostsMods bodyFullHashKeccakFixed bodyFullAbiEncodeOriginFloor
  gasOutcomeFullZeroPrefixMods gasOutcomeFullPostMods bodyFullIfExpReach bodyFullShadowBodyInv
  augAssignFullRhsSaved stmtSimDeclTypedCode
  stmtSimDeclSource vyperStorageTrace vyperStorageFootprint haltExitProj
  bodyFullShared bodyInvCodeProps exprBodyPreProps stateRelProj
  exprSimDefs stmtSimDefs loweringPosts bodyPtrDefs freshWrites fragExec words
  exprLoweringProps venomInst assignPlaceEndpoint exprOpenTerminals
  fragGasMode gasOutcomeFullMods

(* The read's actual successful path, not just its final coordinates,
   shows that the compiler's write cursor is open. *)
Theorem ann_copy_read_open_mods[local]:
  cs_extends a b /\ fn_has_code a b func /\ ~block_is_terminated a /\
  entry.vs_current_bb = a.cs_current_bb /\ entry.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!H res ee G tn t. P H res ee G tn t ==>
    t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,entry,Ga,tna) P R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,entry,Ga,tna)
    (\H res ee G tn t. P H res ee G tn t /\ ~block_is_terminated b) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >>
      qpat_assum `!H res ee G tn t. P _ _ _ _ _ _ ==> _`
        (drule_then strip_assume_tac) >>
      drule_then assume_tac gas_origin_ptr_path_erase >>
      irule endpoint_path_open >>
      qexistsl_tac [`ctx`,`func`,`LENGTH marks`,`entry`,`a`,`t`] >>
      asm_rewrite_tac[gas_marked_path_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem annassign_nonword_store_mods:
  (!ctx cenv src tops env es bindings s ret_ty env'.
     contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
     expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==> body_expr_full_ok_mods mods exps cx e) ==>
  ~is_word_type typ ==> body_stmt_full_ok_mods mods exps cx (AnnAssign id typ e)
Proof
  disch_then (mk_asm "resolve") >> rpt disch_tac >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (AnnAssign id typ e))` by
    (asm "resolve" irule >> metis_tac[]) >>
  asm_x "resolve" kall_tac >>
  drule_all ann_copy_declared_rhs_mods >> strip_tac >>
  rw[stmt_frag_full_mods_def] >>
  rename1 `stmt_env _ _ _ (AnnAssign _ _ _) sa = (ce,sf)` >>
  drule_all_then (qx_choosel_then
    [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
    strip_assume_tac) ann_copy_intervals_mods >>
  qpat_assum `!sa ce r. declare_local _ _ _ sa = _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!DF lo d PG func shadow_func. _`
    (qspecl_then [`DF`,`lo`,`d`,`PG`,`func`,`shadow_func`] strip_assume_tac) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "allocate" >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >> rpt strip_tac >>
  Cases_on `eval_stmt cx (AnnAssign id typ e) (es with gas_obs := tail)` >> fs[] >>
  drule_at (Pat `f st = _`) gasStorageTheory.storage_trace_frame_preserves_bad_domain >>
  simp[evaluate_storage_trace_frame] >> qexistsl_tac [`st0`,`cx`] >> simp[]
QED

Resume annassign_nonword_store_mods[allocate]:
  `sz < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists_tac `2 ** 64` >>
     simp[wordsTheory.dimword_def] >> gvs[]) >>
  drule_all annassign_alloc_entry_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac)) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0 /\
   stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es entry` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ cenv _ _ s0 /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ ce _ _ entry /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (qpat_assum `stmt_state_rel _ _ _ ce _ _ entry`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  `!fn inst s. frag_reachable ctx func entry fn inst s ==> dalloca_fmp_headroom inst s` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (rpt strip_tac >> irule body_inv_no_phi_mods >> metis_tac[]) >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK entry,_,_)`
       (qspec_then `ARB` (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom)) >>
     asm_rewrite_tac[]) >>
  `!H. dead_lo_ok_mods H (DF H) lo ce cx` by
    (gen_tac >> qpat_x_assum `!H. dead_lo_ok_mods H _ _ cenv _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [dead_lo_ok_mods_def])) >>
     simp[dead_lo_ok_mods_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `inst.inst_id = sa.cs_next_id /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p]` by
    simp[Abbr `inst`,mk_inst_def] >>
  `sa.cs_next_id <= inst.inst_id /\ inst.inst_id < a.cs_next_id` by simp[] >>
  `type_memory_size dtv <= sz` by simp[] >>
  Cases_on `has_length_word typ /\ is_empty_value_expr e`
  >- suspend "empty" >>
  suspend "ordinary"
QED

Resume annassign_nonword_store_mods[empty]:
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  `MEM inst (fn_insts func)` by simp[Abbr `inst`] >>
  `FLOOKUP entry.vs_allocas inst.inst_id = SOME (w2n w,sz)` by simp[] >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x entry = SOME z` by simp[] >>
  `a.cs_next_var <= b.cs_next_var` by
    (qpat_assum `compile_expr ce _ e a = _`
       (mp_then Any mp_tac (cj 1 compile_expr_grows)) >> simp[]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  mp_tac (Q.INST [`old` |-> `cenv`, `tyv` |-> `dtv`, `H0` |-> `storage_trace_horizon es.storage_trace`]
    ann_copy_empty_continuation_mods) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `P` strip_assume_tac) >>
  irule ann_copy_sequence_installed_mods >>
  conj_tac >- (BETA_TAC >> rpt gen_tac >> strip_tac >>
    match_mp_tac augassign_expr_exit_to_stmt_exit >>
    conj_tac >- (qpat_assum `expr_exit (INR _) _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
    conj_tac >- (qpat_assum `halt_exit _ _ _ (INR _) _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[halt_exit_INR_type]) >>
    first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Ga`,`P`,`cenv`,`d`,`dtv`,`entry`,`sa`,`tna`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (simp[] >>
    qpat_assum `ce.ce_modules = cenv.ce_modules` (fn eq =>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ P _`
        (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!marks res mid G tn s. _`
    (drule_all_then (qx_choosel_then [`v`,`out`,`t`,`Gf`,`tf`] strip_assume_tac)) >>
  qexistsl_tac [`v`,`out`,`t`,`Gf`,`tf`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> strip_tac >> qexists_tac `ce` >>
  qpat_assum `!H. valid_horizon _ _ H out.storage_trace ==> _`
    (drule_all_then (strip_assume_tac o BETA_RULE)) >> simp[] >> first_assum ACCEPT_TAC
QED

Resume annassign_nonword_store_mods[ordinary]:
  qpat_assum `~(has_length_word typ /\ is_empty_value_expr e)` (fn th =>
    qpat_x_assum `if _ then _ else _` (strip_assume_tac o PURE_REWRITE_RULE [th,COND_CLAUSES])) >>
  `type_widens_to (get_tenv cx) (expr_type e) typ` by
    (qpat_assum `env.type_defs = get_tenv cx` (fn th =>
       qpat_assum `type_widens_to env.type_defs _ _` (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  `return_buf_sep d ce es entry` by
    (irule return_buf_sep_transport >> conj_tac
     >- (rpt gen_tac >> strip_tac >> gvs[] >>
       qpat_assum `return_buf_frame (SOME _) cenv sa s0` (mp_tac o REWRITE_RULE [return_buf_frame_def]) >>
       qpat_assum `return_buf_sep (SOME _) _ _ _` (mp_tac o REWRITE_RULE [bodySimFullTheory.return_buf_sep_def]) >>
       rpt strip_tac >>
       qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK entry,_,_)` (qspec_then `ARB` assume_tac) >>
       drule_all abi_encode_origin_path_allocas_from >> simp[]) >>
     qexistsl_tac [`cenv`,`es`,`s0`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp[loweringStateRelDefsTheory.local_region_def] >> rpt gen_tac >> strip_tac >>
     rename1 `FLOOKUP ce.ce_vars n = SOME (PtrVar (Var q) len)` >>
     rename1 `lookup_var q entry = SOME qw` >>
     `n <> id` by (strip_tac >> gvs[]) >>
     `FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var q) len)` by
       (qpat_assum `!name. name <> id ==> FLOOKUP ce.ce_vars name = _`
          (drule_then (fn th => fs[GSYM th]))) >>
     `not_fresh_at sa q` by
       (qpat_assum `local_ptrs_reserved cenv sa`
          (strip_assume_tac o PURE_REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
        qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP cenv.ce_vars n1 = SOME _ ==> _`
          (qspecl_then [`n`,`n`,`q`,`len`,`len`] mp_tac) >> simp[]) >>
     rename1 `lookup_scopes n es.scopes = SOME ent` >>
     qexistsl_tac [`ent`,`q`,`qw`] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x entry = _ /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  drule_then assume_tac annassign_admissible_rhs >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `sa` |-> `a`, `sm` |-> `sv`, `sb` |-> `b`,
      `opr` |-> `op`, `s0` |-> `entry`, `G0` |-> `Ga`, `tn0` |-> `tna`,
      `shadow_sa` |-> `shadow_a`, `shadow_sb` |-> `shadow_b`,
      `ty` |-> `typ`] assign_name_copy_read_frontier_mods) >>
  (impl_tac >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
    rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind _ _) _ Q0 _` >>
  `~block_is_terminated a` by
    (irule emit_inst_nonterminator_open >>
     qpat_assum `emit_inst ALLOCA _ _ r = _` (irule_at Any) >> simp[is_terminator_def]) >>
  `!H res ee G tn t. Q0 H res ee G tn t ==>
    t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (simp[Abbr `Q0`] >> rpt strip_tac >> simp[]) >>
  drule_all_then assume_tac ann_copy_read_open_mods >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ Q0 _` kall_tac >>
  qpat_x_assum `!H res ee G tn t. Q0 H res ee G tn t ==> _` kall_tac >>
  qunabbrev_tac `Q0` >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind _ _) _ ReadPost _` >>
  irule ann_copy_sequence_installed_mods >>
  conj_tac >- (BETA_TAC >> rpt gen_tac >> strip_tac >>
    match_mp_tac augassign_expr_exit_to_stmt_exit >>
    conj_tac >- (qpat_assum `expr_exit (INR _) _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
    conj_tac >- (qpat_assum `halt_exit _ _ _ (INR _) _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[halt_exit_INR_type]) >>
    first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Ga`,`ReadPost`,`cenv`,`d`,`dtv`,`entry`,`sa`,`tna`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (simp[] >>
    qpat_assum `ce.ce_modules = cenv.ce_modules` (fn eq =>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ ReadPost _`
        (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  suspend "ordinary_suffix"
QED

Resume annassign_nonword_store_mods[ordinary_suffix]:
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ReadPost _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "read_at_horizon")
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `Abbrev (ReadPost = _)` (fn def =>
    asm_x "read_at_horizon"
      (map_every assume_tac o CONJUNCTS o BETA_RULE o
       PURE_ONCE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] def])) >>
  qpat_x_assum `?v. res = INL v /\ _`
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  `mid with gas_obs := [] = mid`
    by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `res = INL v` (fn th =>
    qpat_x_assum `!tail. bind _ _ _ = _` (assume_tac o PURE_REWRITE_RULE [th])) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings) = (INL v,mid)`
    by (qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [eq])))) >>
  `0 < type_memory_size dtv` by simp[] >>
  drule_all_then (qx_choosel_then [`pt`,`rt`] (map_every assume_tac o CONJUNCTS))
    ann_copy_nonword_read_types_mods >>
  `a.cs_next_var <= b.cs_next_var /\ a.cs_next_id <= b.cs_next_id` by
    (qpat_assum `lower_value compile_expr ce _ e a = _`
       (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0` by
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x entry = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (Q.INST [`old` |-> `cenv`, `H` |-> `storage_trace_horizon mid.storage_trace`]
    ann_copy_read_install_frame_mods) >>
  (impl_tac >- (simp[] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    rpt strip_tac >> qpat_assum
      `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel H _ _ ce _ _ entry /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz)` by simp[] >>
  drule_all_then (qx_choosel_then [`xs`,`sw`] (map_every assume_tac o CONJUNCTS))
    ann_copy_source_ready_mods >>
  drule_all_then (qx_choosel_then [`sc`,`rest`] (map_every assume_tac o CONJUNCTS))
    annassign_continuation_success >>
  qmatch_asmsub_abbrev_tac `new_variable id dtv v mid = (INL (),out)` >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func ce cx mid s /\ storage_well_formed_on cx mid (FST H) /\
      immutable_frame_mods func ce cx mid s /\ ghost_inv_at_mods (DF H) lo d ce cx mid G tn s` by
    (gen_tac >> strip_tac >>
     qpat_assum `Abbrev (ReadPost = _)` (fn def =>
       qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ReadPost _ _ _ _ _ _ /\ _`
         (drule_then (map_every assume_tac o CONJUNCTS o BETA_RULE o
           PURE_ONCE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] def] o CONJUNCT1))) >>
     qpat_x_assum `?z. res = INL z /\ _` (qx_choose_then `z` strip_assume_tac) >>
     `z = v` by fs[] >>
     qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ z _ _`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     simp[]) >>
  qpat_assum `op = Var xs` (fn eq =>
    qpat_assum `compile_assign_value ce _ _ op _ _ _ _ _ b = _`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  Cases_on `is_bytestring_type typ /\ vv_location vv <> SOME LocMemory`
  >- suspend "bytes_install" >>
  suspend "typed_install"
QED

Resume annassign_nonword_store_mods[bytes_install]:
  qpat_assum `is_bytestring_type typ /\ vv_location vv <> SOME LocMemory`
    (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `is_bytestring_type typ /\ vv_location vv <> SOME LocMemory ==> _`
    (drule_all_then (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)))) >>
  `?J:(bool # 256 word # type_value) list # num list. stmt_state_rel J ctx func cenv cx es s0` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >> first_assum ACCEPT_TAC) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    simp[Abbr `inst`] >>
  mp_tac (Q.INST [`old` |-> `cenv`, `dw` |-> `w`, `sty` |-> `lowered_value_type ce e`,
    `loc` |-> `vv_location vv`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `sz'` |-> `type_memory_bytes ce typ`] ann_copy_bytes_installed_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >> qexists_tac `storage_trace_horizon es.storage_trace` >>
    first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`out`,`t`,`Gf`,`tf`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> strip_tac >> qexists_tac `ce` >>
  qpat_assum `!H. valid_horizon _ _ H out.storage_trace ==> _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Resume annassign_nonword_store_mods[typed_install]:
  qpat_assum `~(is_bytestring_type typ /\ vv_location vv <> SOME LocMemory)`
    (assume_tac o SIMP_RULE bool_ss [DE_MORGAN_THM]) >>
  qpat_assum `(~is_bytestring_type typ \/ vv_location vv = SOME LocMemory) ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `vv_location vv = SOME LocMemory ==>
    expr_val_at ce cx (lowered_value_type ce e) a b mid v (Var xs) s` by
    (strip_tac >> qpat_assum `vv_location vv = SOME LocMemory ==> expr_val_at _ _ _ _ _ _ _ _ _ /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `contract_inv mods exps ctx ce cx`
    (mp_then Any assume_tac contract_inv_acyclic_struct_metadata) >>
  qpat_assum `expr_body_pre_mods mods ce cx env e es`
    (mp_then Any assume_tac expr_body_pre_mods_inv) >>
  qpat_assum `expr_sim_inv_mods mods ce cx env es`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [exprSimHypsDefsTheory.expr_sim_inv_mods_def]) >>
  `~block_is_terminated sf` by
    (qpat_assum `compile_assign_value ce _ _ (Var xs) _ _ _ _ _ b = ((),sf)`
       (mp_then Any mp_tac compile_assign_value_typed_open) >> asm_rewrite_tac[]) >>
  qpat_assum `ghost_inv_at_mods _ lo d ce cx mid G tn s`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `type_memory_size rt < dimword (:256) /\
   w2n w + type_memory_size dtv < dimword (:256) /\
   w2n w + type_memory_size dtv <= s.vs_alloca_next /\
   inst.inst_id < b.cs_next_id /\ sa.cs_next_var <= b.cs_next_var` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`w2n sw + type_memory_size rt < dimword (:256)`, `w2n w + sz < dimword (:256)`,
        `type_memory_size dtv <= sz`, `w2n w + sz <= s.vs_alloca_next`,
        `inst.inst_id < a.cs_next_id`, `a.cs_next_id <= b.cs_next_id`,
        `sa.cs_next_var <= a.cs_next_var`, `a.cs_next_var <= b.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  mp_tac (Q.INST [`old` |-> `cenv`, `dty` |-> `typ`, `sty` |-> `lowered_value_type ce e`,
    `loc` |-> `vv_location vv`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `start` |-> `a`, `stv` |-> `rt`, `H0` |-> `storage_trace_horizon es.storage_trace`,
    `J` |-> `storage_trace_horizon mid.storage_trace`]
    (INST_TYPE [alpha |-> ``:256``] ann_copy_typed_installed_mods)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`out`,`t`,`Gf`,`tf`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> strip_tac >> qexists_tac `ce` >>
  qpat_assum `!H. valid_horizon _ _ H out.storage_trace ==> _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise annassign_nonword_store_mods
