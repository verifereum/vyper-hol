(* The actual fallthrough landing executes the emitted void suffix. *)
Theory bodySelectedFallthroughSuffixMods
Ancestors
  bodyFullPostsMods bodyExprPreFacts bodySelectedUnlockTaintMods
  stmtSimProps stmtSimReturn stateRelProj nonreentrantEquiv
  vyperStorageTrace vyperStorageFootprint guardSourceEntryStorage
  vyperFiniteStoragePreservation stmtLowering externalCallSelected[qualified]
  bodySim compileEnv loweringStateRelDefs loweringPosts bodyFullShadowBodyInv
  bodyInvSplit venomState vyperInterpreter fragExec
(* Native statement OK post, specialized here to the actual NoLoop landing. *)
val qstmt = ``\(H : (bool # bytes32 # type_value) list # num list) res ee G tn t. ?cenv''.
  stmt_lands NoLoop z res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated z /\ cenv'' = out) /\
  cenv_top_ext body_ce cenv'' ee.scopes /\
  stmt_state_rel H ctx callee cenv'' p ee t /\
  immutable_frame_mods callee cenv'' p ee t /\
  storage_well_formed_on p ee (FST H) /\
  return_buf_frame d cenv'' z t /\ alloca_history callee t /\
  return_buf_sep d cenv'' ee t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  at_body.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv'' p ee G tn t /\
  (!x w. not_fresh_at a x /\ lookup_var x at_body = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP at_body.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at a x ==>
       FLOOKUP G x = FLOOKUP Gl x /\
       op_taint tn (Var x) = op_taint tnl (Var x)) /\
  alloca_frame body_ce locked a at_body cenv'' ee t /\
  (!aid off sz i.
     FLOOKUP at_body.vs_allocas aid = SOME (off,sz) /\ aid < a.cs_next_id /\
     (!n b sz'. local_region body_ce locked.scopes at_body n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tnl.t_mem)``;

Theorem fallthrough_return_code[local]:
  ce.ce_return_pc = SOME (PtrVar (Var rpc) sz) /\
  ce.ce_nonreentrant = (nr,key,T,view) /\ ~block_is_terminated z /\
  (if block_is_terminated z then ((),z)
   else comp_ignore_bind
     (if nr then compile_nonreentrant_unlock key T view else comp_return ())
     (emit_inst RET [Var rpc] []) z) = ((),final) ==>
  compile_stmt ce NoLoop (BaseT BoolT) (Return NONE) z = ((),final)
Proof
  strip_tac >>
  qpat_x_assum `(if block_is_terminated z then _ else _) = _` mp_tac >>
  simp[Once compile_stmt_def, compile_return_unlock_def]
QED

Theorem fallthrough_return_release[local]:
  ce.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> p.nonreentrant_slot = SOME key) /\
  unlock_if_nr p nr view ee = (INL (),released) /\
  ce.ce_returns_count = 0 /\ state_rel H callee ce p ee t ==>
  state_rel H callee ce p (released with scopes := []) (return_unlock_state ce t)
Proof
  strip_tac >>
  qabbrev_tac `ir = <|iret_values := []; iret_adopt_fmp := NONE|>` >>
  `intret_q H callee ce p rtv NoneV (ee with scopes := [])
     (IntRet ir (return_unlock_state ce t))` by
    (irule intret_q_intro >>
     simp[Abbr `ir`, result_rel_def, intret_vals_match_def] >>
     qexists_tac `t` >> simp[state_rel_scopes_nil]) >>
  drule_all intret_q_source_epilogue >>
  `unlock_if_nr p nr view (ee with scopes := []) =
     (INL (),released with scopes := [])` by
    (drule externalCallSelectedTheory.unlock_if_nr_with_scopes >> simp[]) >>
  Cases_on `nr` >> Cases_on `view` >>
  gvs[unlock_if_nr_def, vyperStateTheory.return_def, result_rel_def, Abbr `ir`]
QED

Theorem fallthrough_release_immutables[local]:
  ce.ce_nonreentrant = (nr,key,T,view) /\
  unlock_if_nr p nr view ee = (INL (),released) /\
  immutable_frame_mods callee ce p ee t ==>
  immutables_rel_mods ce p.txn.target ce.ce_is_ctor released (return_unlock_state ce t)
Proof
  strip_tac >> Cases_on `nr /\ ~view` >> Cases_on `p.nonreentrant_slot` >>
  gvs[unlock_if_nr_def, vyperStateTheory.return_def,
      release_nonreentrant_lock_execution, immutable_frame_mods_def,
      immutables_rel_mods_def, immutables_rel_def, return_unlock_state_def, tstore_def] >>
  first_assum ACCEPT_TAC
QED

Theorem fallthrough_release_storage[local]:
  unlock_if_nr p nr view ee = (INL (),released) /\
  valid_horizon p st0 H released.storage_trace /\
  storage_well_formed_on p ee (FST H) ==>
  storage_well_formed_on p released (FST H)
Proof
  rpt strip_tac >> Cases_on `nr /\ ~view`
  >- (irule unlock_if_nr_storage >> simp[valid_horizon_def] >>
      fs[valid_horizon_def] >>
      qexistsl_tac [`view`,`nr`,`released.storage_trace`,`INL ()`,`ee`] >>
      asm_rewrite_tac[] >> rpt strip_tac >>
      gvs[unlock_if_nr_def, release_nonreentrant_lock_execution]) >>
  gvs[unlock_if_nr_def, vyperStateTheory.return_def]
QED

Theorem selected_fallthrough_suffix_run_mods:
  stmts_env body_ce NoLoop (BaseT BoolT) body_stmts a = (out,z) /\
  body_ce.ce_return_pc = SOME (PtrVar (Var rpc) sz) /\
  body_ce.ce_nonreentrant = (nr,key,T,view) /\
  body_ce.ce_returns_count = 0 /\
  (nr ==> p.nonreentrant_slot = SOME key) /\
  (nr /\ ~view ==> ~p.txn.is_static) /\
  ret_pc_ok body_ce a at_body /\
  (if block_is_terminated z then ((),z)
   else comp_ignore_bind
     (if nr then compile_nonreentrant_unlock key T view else comp_return ())
     (emit_inst RET [Var rpc] []) z) = ((),final) /\
  fn_has_code z final callee /\
  unlock_if_nr p nr view ee = (INL (),released) /\
  storage_trace_domain p st0 ee.storage_trace /\
  (!H. dead_lo_ok_mods H (DF H) lo body_ce p) /\
  (!H. valid_horizon p st0 H ee.storage_trace ==>
       (^qstmt) H (INL ()) ee G tn t) ==>
  ?ir cs J N.
    ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
    cs = return_unlock_state out t /\ N.t_mem = tn.t_mem /\
    same_frame body_ce out /\ intret_vals_match rtv NoneV ir.iret_values /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG)
      (t,G,tn) [] (IntRet ir cs,J,N)) /\
    (!H. valid_horizon p st0 H ee.storage_trace ==>
      state_rel H callee out p (released with scopes := []) cs /\
      immutables_rel_mods out p.txn.target out.ce_is_ctor released cs /\
      stor_taint_ok_at (DF H) N cs /\
      (!i. i < lo /\ i IN N.t_mem ==>
        imm_section_dead_mods out (mem_bytes_at 0 lo cs.vs_memory) i)) /\
    (!H. valid_horizon p st0 H released.storage_trace ==>
      storage_well_formed_on p released (FST H))
Proof
  BETA_TAC >> strip_tac >>
  `valid_horizon p st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon p st0 H ee.storage_trace ==> ?ce. _`
    (assume_tac o SIMP_RULE bool_ss [stmt_lands_def, sumTheory.sum_distinct]) >>
  qpat_assum `!H. valid_horizon p st0 H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac cenv_top_ext_same_frame >>
  `out.ce_return_pc = body_ce.ce_return_pc /\
   out.ce_nonreentrant = body_ce.ce_nonreentrant /\
   out.ce_returns_count = body_ce.ce_returns_count` by
    fs[same_frame_def, compile_env_component_equality] >>
  `a.cs_next_var <= z.cs_next_var` by
    drule_then (ACCEPT_TAC o cj 2) (REWRITE_RULE [cs_mono_def] stmts_env_cs_mono) >>
  `ret_pc_ok out z t` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`body_ce`,`at_body`,`a`] >> simp[]) >>
  `compile_stmt out NoLoop (BaseT BoolT) (Return NONE) z = ((),final)` by
    (qpat_assum `(if block_is_terminated z then _ else _) = _`
       (mp_then Any mp_tac fallthrough_return_code) >>
     disch_then irule >> simp[]) >>
  `allocas_from lo t /\ op_taint tn (Var rpc) = {}` by fs[ghost_inv_at_mods_def] >>
  drule_then (assume_tac o MATCH_MP state_rel_call_ctx_rel) stmt_state_rel_state_rel >>
  `t.vs_call_ctx.cc_static = p.txn.is_static` by fs[call_ctx_rel_def] >>
  `out.ce_return_pc = SOME (PtrVar (Var rpc) sz) /\
   ((FST out.ce_nonreentrant /\ ~SND (SND (SND out.ce_nonreentrant))) ==>
    ~t.vs_call_ctx.cc_static)` by simp[] >>
  `out.ce_nonreentrant = (nr,key,T,view) /\ out.ce_returns_count = 0` by simp[] >>
  drule_all_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `J` (qx_choose_then `N` strip_assume_tac)))
    compile_return_none_int_origin_ptr_taint >>
  `N.t_stor = tn.t_stor /\ N.t_trans SUBSET tn.t_trans /\ N.t_imm = tn.t_imm` by
    (qpat_assum `_ ==> N.t_stor = _ /\ _` mp_tac >>
     qpat_assum `out.ce_nonreentrant = (nr,key,T,view)`
       (pure_rewrite_tac o single) >> simp[NoAsms]) >>
  qexistsl_tac [`<|iret_values := []; iret_adopt_fmp := NONE|>`,
                `return_unlock_state out t`,`J`,`N`] >>
  simp[intret_vals_match_def] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon p st0 H ee.storage_trace ==> _`
        (drule_then strip_assume_tac) >>
      conj_tac
      >- (drule_then assume_tac stmt_state_rel_state_rel >>
          drule_all_then ACCEPT_TAC fallthrough_return_release) >>
      conj_tac >- drule_all_then ACCEPT_TAC fallthrough_release_immutables >>
      `dead_lo_ok_mods H (DF H) lo out p` by
        fs[same_frame_def, compile_env_component_equality, dead_lo_ok_mods_def] >>
      `((FST out.ce_nonreentrant /\ ~SND (SND (SND out.ce_nonreentrant))) ==>
         FST (SND (SND out.ce_nonreentrant)))` by simp[] >>
      drule_all selected_unlock_exit_taint_mods >> simp[]) >>
  gen_tac >> strip_tac >>
  `valid_horizon p st0 H ee.storage_trace` by
    (qpat_assum `unlock_if_nr p nr view ee = _`
       (mp_then Any mp_tac valid_horizon_frame) >>
     disch_then irule >> simp[storage_trace_frame_optional_locks]) >>
  qpat_assum `!H. valid_horizon p st0 H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then ACCEPT_TAC fallthrough_release_storage
QED
