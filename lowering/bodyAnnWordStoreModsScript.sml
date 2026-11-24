(* Counted execution of a word-local declaration in a linked body. *)
Theory bodyAnnWordStoreMods
Ancestors
  bodyAnnWordRhsMods bodyAnnWordIntervalsMods bodyAnnAllocEntryMods
  bodyAnnWordWritePathMods bodyAnnWordInstallMods bodyFullIfExpReach
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullZeroPrefixMods
  stmtSimDeclSource stmtSimProps emitHelperProps bodyFullPredsMods bodyFullPostsMods
  vyperStorageTrace vyperStorageFootprint gasExemptCertMods exprSimDefs
  augAssignFullRhsSaved bodyFullShadowBodyInv stateRelProj stmtSimDefs loweringPosts bodyPtrDefs
  freshWrites words fragExec unitTransformDefs

Theorem annassign_linked_bind[local]:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna)
    P (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!H exc ee gt r. expr_exit (INR exc : value + exception) r /\
    halt_exit H cx ee (INR exc) r /\
    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
    R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 u.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H res mid G1 tn1 u /\ ~u.vs_halted /\ mid.gas_obs = []) ==>
    (?v. res = INL v /\
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
        (new_variable id tyv v) (mid,u,G1,tn1) Q R)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmt cx (AnnAssign id typ e)) (es,entry,Ga,tna) Q R
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn u. P H res ee G tn u /\
                    ~u.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >- (BETA_TAC >> rpt strip_tac >> disj1_tac >>
      qpat_x_assum `!marks res mid G1 tn1 u. _` (qspecl_then [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> Cases_on `res`
  >- fs[expr_exit_def] >>
  simp[] >> first_x_assum irule >> fs[halt_exit_def]
QED

Theorem annassign_word_store_mods:
  (!ctx cenv src tops env es bindings s ret_ty env'.
     contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
     expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==> body_expr_full_ok_mods mods exps cx e) ==>
  is_word_type typ ==> body_stmt_full_ok_mods mods exps cx (AnnAssign id typ e)
Proof
  disch_then (mk_asm "resolve") >> rpt disch_tac >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (AnnAssign id typ e))` by
    (asm "resolve" irule >> metis_tac[]) >>
  asm_x "resolve" kall_tac >>
  drule_all annassign_word_declared_rhs_mods >>
  rw[stmt_frag_full_mods_def] >>
  qpat_x_assum `!shadow_func lo func d PG DF. _`
    (qspecl_then [`shadow_func`,`lo`,`func`,`d`,`PG`,`DF`] strip_assume_tac) >>
  rename1 `stmt_env _ _ _ (AnnAssign _ _ _) sa = (ce,sf)` >>
  drule_all_then (qx_choosel_then [`r`,`shadow_r`,`p`,`a`,`b`,`op`,`shadow_a`,`shadow_b`]
    strip_assume_tac) annassign_word_intervals_mods >>
  qpat_assum `!sa ce r. declare_local _ _ _ sa = _ ==> _`
    (drule_then strip_assume_tac) >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "allocate" >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >>
  rpt strip_tac >>
  Cases_on `eval_stmt cx (AnnAssign id typ e) (es with gas_obs := tail)` >> fs[] >>
  drule_at (Pat `f st = _`) gasStorageTheory.storage_trace_frame_preserves_bad_domain >>
  simp[evaluate_storage_trace_frame] >> qexistsl_tac [`st0`,`cx`] >> simp[]
QED

Resume annassign_word_store_mods[allocate]:
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  `32 = type_memory_bytes cenv typ` by simp[] >>
  drule_all (Q.SPEC `32` (Q.GEN `sz` annassign_alloc_entry_mods)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac)) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0 /\
   stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es entry` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ cenv _ _ s0 /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ ce _ _ entry /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (qpat_assum `stmt_state_rel _ _ _ ce _ _ entry` (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
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
  drule_then assume_tac annassign_admissible_rhs >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,`op`,`entry`,`Ga`,`tna`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  suspend "sequence"
QED

Resume annassign_word_store_mods[sequence]:
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ Final Exit` >>
  qabbrev_tac `Provisional = \H res ee G tn t.
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) ==>
      Final H res ee G tn t` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. Provisional H res ee G tn t /\
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t)`, `Exit`] >>
  conj_tac >- simp[Abbr `Provisional`] >>
  conj_tac >- simp[] >>
  ho_match_mp_tac gas_outcome_full_mods_return_buf_allocas >>
  reverse conj_tac >- simp[] >>
  irule gas_outcome_full_mods_zero_prefix >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >>
  conj_tac >- simp[] >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (bind _ _) _ _ _` mp_tac >>
  simp[] >>
  disch_then (mp_then Any mp_tac annassign_linked_bind) >>
  simp[] >>
  disch_then irule >>
  conj_tac >- (rpt strip_tac >> simp[Abbr `Exit`] >>
    match_mp_tac augassign_expr_exit_to_stmt_exit >>
    conj_tac >- (qpat_assum `expr_exit (INR _) _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[expr_exit_INR_type]) >>
    conj_tac >- (qpat_assum `halt_exit _ _ _ (INR _) _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[haltExitProjTheory.halt_exit_INR_type]) >>
    first_assum ACCEPT_TAC) >>
  qexists_tac `tyv` >>
  simp[] >> rpt strip_tac >>
  suspend "store"
QED

Resume annassign_word_store_mods[store]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    (?v. res = INL v /\ expr_post_mods H ctx func ce cx e es a b entry mid v op u /\
      u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func u /\ entry.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G1 tn1 u /\
      ptr_val_ok cx (post_value_type ce e) v op G1 tn1 u /\
      ghost_kept_at lo ce es a Ga tna entry G1 tn1) /\ ~u.vs_halted /\ mid.gas_obs = []` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[post_value_type_def]) >>
  qpat_assum `expr_type e = typ` (fn th =>
    drule_all (REWRITE_RULE [th] annassign_word_write_path_mods)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`]
    (qx_choosel_then [`v`,`sc`,`rest`,`out`,`t`,`Gf`,`tnf`] strip_assume_tac)) >>
  `~u.vs_halted /\ mid.gas_obs = []` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qpat_assum `res = INL _` (irule_at Any) >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`out`,`INL ()`,`t`,`tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `out.gas_obs = [] /\ out.storage_trace = mid.storage_trace` by
    (qpat_assum `out = mid with scopes := _` SUBST1_TAC >> simp[]) >>
  `out with gas_obs := [] = out /\ mid with gas_obs := [] = mid` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `out with gas_obs := [] = out` (fn th => simp[NoAsms,th]) >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[] >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  qpat_assum `!tail. new_variable _ _ _ _ = _` (qspec_then `[]` assume_tac) >>
  suspend "install"
QED

Resume annassign_word_store_mods[install]:
  `v' = v` by
    (qpat_assum `res = INL v'` mp_tac >> qpat_assum `res = INL v` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[sumTheory.INL_11]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `bind _ _ _ = (res,_)` mp_tac >>
     qpat_assum `res = INL v` (fn th => simp[NoAsms,th]) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms,th])) >>
  `new_variable id tyv v mid = (INL (),out)` by
    (qpat_assum `new_variable _ _ _ (mid with gas_obs := []) = _` mp_tac >>
     qpat_assum `out with gas_obs := [] = out` (fn th => simp[NoAsms,th]) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms,th])) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `bind _ _ _ = (INL v,mid)`
       (mp_tac o MATCH_MP eval_read_preserves_scopes_dom) >> simp[]) >>
  `alloca_frame ce es a entry ce mid u` by
    (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
     irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`func`] >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `alloc_inst = mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]` >>
  `MEM alloc_inst (fn_insts func) /\ alloc_inst.inst_opcode = ALLOCA /\
   alloc_inst.inst_outputs = [p] /\ alloc_inst.inst_id = sa.cs_next_id` by
    (conj_tac >- first_assum ACCEPT_TAC >>
     qunabbrev_tac `alloc_inst` >> simp[NoAsms, venomInstTheory.mk_inst_def]) >>
  `FLOOKUP u.vs_allocas alloc_inst.inst_id = SOME (w2n w,32) /\
   sa.cs_next_id <= alloc_inst.inst_id` by
    (qpat_assum `alloc_inst.inst_id = sa.cs_next_id` SUBST1_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms]) >>
  `!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  `!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `a` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x entry = lookup_var x s0` by simp[] >>
  `?J:(bool # 256 word # type_value) list # num list.
     stmt_state_rel J ctx func cenv cx es s0` suffices_by
    (disch_tac >> suspend "finish_install") >>
  qexists_tac `storage_trace_horizon es.storage_trace` >> first_assum ACCEPT_TAC
QED

Resume annassign_word_store_mods[finish_install]:
  `!x. not_fresh_at sa x ==> FLOOKUP Ga x = FLOOKUP G0 x /\
       op_taint tna (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x entry = _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
         (?v. _ /\ expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ exprSimMemDefs$expr_store_bound _ _ _ _ _ /\ _) /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`inst` |-> `alloc_inst`, `t` |-> `t`, `old` |-> `cenv`,
                  `D` |-> `DF H`, `gs` |-> `gas_explicit marks s0.vs_gas_readings`]
    annassign_word_install_post_mods) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qunabbrev_tac `Provisional` >> qunabbrev_tac `Final` >> BETA_TAC >>
  disch_tac >> qexists_tac `ce` >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[NoAsms] >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `_ ==> return_buf_sep d ce out t` irule >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise annassign_word_store_mods
