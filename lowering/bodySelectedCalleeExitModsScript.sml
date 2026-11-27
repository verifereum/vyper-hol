(* Assemble endpoints of the selected qualified callee, before caller restoration. *)
Theory bodySelectedCalleeExitMods
Ancestors
  bodySelectedReturningExitPostMods bodySelectedCalleeProtectedExitMods
  gasOutcomeFullMods createSizeExit fragExec guardSourceEntryStorage
  vyperStorageTrace externalCallSelected vyperFiniteStoragePreservation
  vyperStorageFootprint bodySelectedTerminalBodyExitMods fragGasOriginPtr
  loweringStateRelDefs bodyFullPostsMods bodyInvSplit
  bodySelectedFallthroughSuffixMods stmtSimReturn compileEnv nonreentrantEquiv bodySim
  bodySelectedQualifiedBodySourceMods bodySelectedQualifiedBodyFocusMods fragGasPathMem
  vyperInterpreter vyperState bodySelectedLockLandingMods
  bodySelectedQualifiedLockShortCircuitMods bodySelectedLockedBodyRunMods
Libs monadsyntax

val _ = Parse.hide "rc";

val selected_src = ``do lock_if_nr cx nr (is_view_mut mut);
  try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
          return NoneV od) handle_function od``;

(* Exact callee post consumed by the caller restoration, with the caller
   environment named cenv to distinguish it from the materialized frame. *)
val selected_exit = ``\(H : (bool # bytes32 # type_value) list # num list)
    (res : value + exception) ee (gt : (string |-> num # num) # taint) r.
  (expr_exit res r /\ halt_exit H cx ee res r) \/
  ?v ir cs. res = INL v /\ r = IntRet ir cs /\
    (?out. unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\
      state_rel H func cenv cx (out with scopes := []) cs /\
      immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor out cs /\
      storage_well_formed_on cx out (FST H) /\ immutable_metadata_frame es1 out) /\
    LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
    intret_vals_match rtv v ir.iret_values /\
    stor_taint_ok_at (DF H) (SND gt) cs /\
    (!i. i < lo /\ i IN (SND gt).t_mem ==>
      imm_section_dead_mods cenv (mem_bytes_at 0 lo cs.vs_memory) i) /\
    (!b sz. lo <= b /\ b + sz <= t.vs_alloca_next /\
      (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==>
        regions_disjoint b sz a cap) ==>
      mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN (SND gt).t_mem /\
      (!aid a cap. FLOOKUP t.vs_allocas aid = SOME (a,cap) /\
        sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==> i < a \/ a + cap <= i) ==>
      i IN tn.t_mem) /\
    (rc = 0 /\ 0 < rbs ==> !mem. mem_agree_outside (SND gt).t_mem cs.vs_memory mem ==>
      val_in_memory rtv v (w2n (HD (argv : bytes32 list))) mem)``;

val pushed = ``cx with stk updated_by CONS (src,name)``;
val explicit_sites = ``gas_explicit_sites ctx shadow_ctx``;
val callee_pins = ``MAP (op_prov G) arg_ops``;
val entry_start = ``(entered:venom_state,FEMPTY:(string |-> num # num),tn with t_var := FEMPTY)``;
val callee_outcome = ``gas_outcome_full_mods (DF,lo,^explicit_sites,ctx,callee,^callee_pins) mods cx st0
    ^selected_src (es1,^entry_start) (\H res ee J N u. F) ^selected_exit``;
val return_input = ``
  contract_inv mods exps ctx cenv cx /\ contract_inv mods exps ctx body_ce ^pushed /\
  IS_SOME (ALOOKUP mods cenv.ce_module) /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  (!(H : (bool # bytes32 # type_value) list # num list). dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  (!setup. setup_callee callee argv t = SOME setup ==> fmp_room ctx callee setup) /\
  (!b sz. MEM (SOME (b,sz)) ^callee_pins ==>
    ?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
          sa.cs_next_id <= aid /\ aid < sm.cs_next_id)``;

Theorem selected_complete_intret[local]:
  ^return_input /\
  (!tail. (^selected_src) (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
          (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) /\
  LENGTH ir.iret_values = rc /\ (0 < rc \/ 0 < rbs ==> ret_tv = rtv) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,^explicit_sites,ctx,callee,^callee_pins)
      ^entry_start marks (IntRet ir cs,J,tc) /\
    result_rel H callee ret_tv body_ce ^pushed
      (INR (ReturnException v),out with scopes := []) (IntRet ir cs) /\
    immutable_frame_mods callee body_ce ^pushed (ee with scopes := []) cs /\
    storage_well_formed_on cx out (FST H) /\ stor_taint_ok_at (DF H) tc cs /\
    (!i. i < lo /\ i IN tc.t_mem ==>
      imm_section_dead_mods body_ce (mem_bytes_at 0 lo cs.vs_memory) i) /\
    (rc = 0 /\ 0 < rbs ==> !mem. mem_agree_outside tc.t_mem cs.vs_memory mem ==>
       val_in_memory ret_tv v (w2n (HD argv)) mem)) ==>
  ^callee_outcome
Proof
  BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.SPECL [`rc`,`rbs`] selected_returning_exit_post_mods) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
    >- (gen_tac >> strip_tac >>
        qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
        Cases_on `rc = 0 /\ 0 < rbs` >> simp[]) >>
    gen_tac >> strip_tac >>
    qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _`
      (qspec_then `H` mp_tac) >> simp_tac bool_ss [] >> strip_tac >>
    mp_tac (Q.INST [`D` |-> `DF H`, `p` |-> `cx with stk updated_by CONS (src,name)`,
       `u` |-> `cs`, `N` |-> `tc`, `n` |-> `sa.cs_next_id`, `m` |-> `sm.cs_next_id`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
       (Q.INST_TYPE [`:'a` |-> `:256`] selected_callee_protected_exit_mods)) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC)) >>
  strip_tac >> pure_rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL v`, `ee`, `IntRet ir cs`, `J`, `tc`] >>
  asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> state_rel _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[exit_result_def, create_size_exit_ok_def] >>
  conj_tac >- (qexists_tac `out'` >> fs[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* For a returning body, the release touches the lock already observed by
   the acquisition.  The horizon here is the one before release. *)
Theorem selected_release_at_body_horizon[local]:
  (!tail. lock_if_nr cx nr view (es1 with gas_obs := tail) =
     (INL (),locked with gas_obs := tail)) /\
  eval_stmts (cx with stk updated_by CONS (src,name)) ss
      (locked with gas_obs := obs) = (res,ee with gas_obs := tail) /\
  valid_horizon cx st0 H ee.storage_trace /\
  storage_well_formed_on cx ee (FST H) /\
  unlock_if_nr cx nr view (ee with gas_obs := []) = (INL (),out) ==>
  storage_well_formed_on cx out (FST H)
Proof
  strip_tac >>
  `storage_trace_frame (eval_stmts (cx with stk updated_by CONS (src,name)) ss)` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  drule_all_then strip_assume_tac vyperStorageTraceTheory.storage_trace_frame_prefix >>
  `storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx (ee with gas_obs := []) (FST H) <=>
      storage_well_formed_on cx ee (FST H)` by
        (irule storage_well_formed_on_backends >> simp[]) >>
     simp[]) >>
  irule guardSourceEntryStorageTheory.unlock_if_nr_storage >>
  fs[valid_horizon_def, Excl "unlock_if_nr_def", Excl "lock_if_nr_def"] >>
  qexistsl_tac [`view`,`nr`,`ee.storage_trace`,`INL ()`,`ee with gas_obs := []`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!tail. lock_if_nr cx _ _ _ = _` (qspec_then `[]` assume_tac) >>
      drule_all_then assume_tac lock_if_nr_success_trace >> fs[]) >>
  fs[]
QED

Theorem selected_reached_body_storage[local]:
  type_stmts env ret ss = SOME env_after /\
  runtime_consistent env p locked /\ functions_well_typed p /\
  call_evaluation_safe p (int_calls_stmts ss) /\
  eval_stmts p ss (locked with gas_obs := obs) = (res,ee with gas_obs := tail) /\
  valid_horizon p st0 H locked.storage_trace /\
  valid_horizon p st0 H ee.storage_trace /\
  storage_well_formed_on p locked (FST H) ==>
  storage_well_formed_on p ee (FST H)
Proof
  strip_tac >>
  `storage_well_formed_on p (ee with gas_obs := tail) (FST H) <=>
   storage_well_formed_on p ee (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `storage_well_formed_on p (locked with gas_obs := obs) (FST H) <=>
   storage_well_formed_on p locked (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `runtime_consistent env p (locked with gas_obs := obs)` by
    fs[vyperTypeExprSoundnessTheory.runtime_consistent_def,
       vyperTypeInvariantsTheory.gas_obs_type_invariants] >>
  qpat_assum `valid_horizon p st0 H ee.storage_trace`
    (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
  `storage_observations_ok p H (ee with gas_obs := tail).storage_trace` by simp[] >>
  `storage_well_formed_on p (locked with gas_obs := obs) (FST H)` by simp[] >>
  drule_all_then mp_tac (cj 2 (Q.SPEC `H` eval_storage_well_formed_on_mutual)) >> simp[]
QED

val native_start = ``(at_body:venom_state,Gl:string |-> num # num,tnl:taint)``;
val native_result = ``(r:exec_result,J:string |-> num # num,tc:taint)``;
val native_code = ``((DF : ((bool # bytes32 # type_value) list # num list) -> dead) H,
                     lo:num,^explicit_sites,ctx,callee:ir_function,^callee_pins)``;
val whole_source_run = ``!tail. (^selected_src)
    (es1 with gas_obs := gas_explicit marks entered.vs_gas_readings ++ tail) =
    (answer,ee with gas_obs := tail)``;
val callee_retq = ``\(H : (bool # bytes32 # type_value) list # num list)
    v ee (gt : (string |-> num # num) # taint) r.
  intret_q H callee body_ce ^pushed ret_tv v ee r /\
  !ir cs. r = IntRet ir cs ==>
    immutable_frame_mods callee body_ce ^pushed (ee with scopes := []) cs /\
    stor_taint_ok_at (DF H) (SND gt) cs /\
    (!i. i < lo /\ i IN (SND gt).t_mem ==>
      imm_section_dead_mods body_ce (mem_bytes_at 0 lo cs.vs_memory) i) /\
    (rc = 0 /\ 0 < rbs ==> !mem. mem_agree_outside (SND gt).t_mem cs.vs_memory mem ==>
       val_in_memory ret_tv v (w2n (HD (argv:bytes32 list))) mem)``;
val terminal_answer = ``case (res : unit + exception) of
  INL _ => INL NoneV | INR ex => FST (handle_function ex ee)``;

Theorem selected_immutable_frame_gas_obs[local]:
  immutable_frame_mods fn ce p (e with <|scopes := s1; scopes := s2; gas_obs := obs|>) u <=>
  immutable_frame_mods fn ce p (e with scopes := s1) u
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
    immutable_alloca_sep_mods_def, exprLoweringPropsTheory.immutable_alloca_sep_def]
QED

Theorem selected_compose_native_terminal[local]:
  ^return_input /\ ^whole_source_run /\ answer = ^terminal_answer /\
  body_ce.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  body_ce.ce_returns_count = rc /\ (0 < rc \/ 0 < rbs ==> ret_tv = rtv) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  storage_trace_domain ^pushed st0 ee.storage_trace /\
  (!(H : (bool # bytes32 # type_value) list # num list).
    valid_horizon cx st0 H ee.storage_trace ==> valid_horizon ^pushed st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path ^native_code ^entry_start [] (OK at_body,Gl,tnl)) /\
  (!H out. valid_horizon cx st0 H ee.storage_trace /\
    unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) ==>
    storage_well_formed_on cx out (FST H)) /\
  (!H. valid_horizon ^pushed st0 H ee.storage_trace ==>
    gas_origin_ptr_path ^native_code ^native_start marks ^native_result /\
    exit_result r /\ create_size_exit_ok ctx res r /\
    (!tail. stmt_exit_ptr ((^callee_retq) H) ((ee with gas_obs := []) with gas_obs := tail)
      res (J,tc) r) /\ halt_exit H ^pushed (ee with gas_obs := []) res r /\
    (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
       allocas_below_fmp s)) ==>
  ^callee_outcome
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`frame` |-> `body_ce`, `rtv` |-> `ret_tv`,
    `RetQ` |-> `^callee_retq`, `explicit` |-> `^explicit_sites`,
    `PG` |-> `^callee_pins`, `start` |-> `^native_start`,
    `Gc` |-> `J`] selected_terminal_body_exit_mods) >> BETA_TAC >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[])) >>
  strip_tac
  >- suspend "return" >> suspend "exception"
QED

Resume selected_compose_native_terminal[return]:
  qpat_x_assum `answer = INL v` SUBST_ALL_TAC >>
  qpat_x_assum `r = IntRet ir cs` SUBST_ALL_TAC >>
  irule selected_complete_intret >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac >- (qexistsl_tac [`bb`,`inst`,`lbl`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`J`,`body_ce`,`cs`,`ee`,`exps`,`ir`,`marks`,`out`,`ret_tv`,`tc`,`v`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon cx _ H _ ==> valid_horizon _ _ _ _`
        (drule_then assume_tac) >>
      qpat_assum `!H. valid_horizon (cx with stk updated_by _) _ H _ ==> _ /\ _ /\ create_size_exit_ok ctx (INL v) _ /\ _`
        (drule_then strip_assume_tac) >>
      conj_tac
      >- (qpat_assum `!H. valid_horizon cx _ H _ ==> gas_origin_ptr_path _ _ [] _`
            (drule_then assume_tac) >>
          drule gas_origin_ptr_path_append >>
          disch_then (qspecl_then [`at_body`,`Gl`,`tnl`] mp_tac) >> simp[]) >>
      `storage_well_formed_on cx out (FST H)` by
        (qpat_assum `!h u. valid_horizon cx _ h _ /\ _ ==> _`
           (qspecl_then [`H`,`out`] mp_tac) >> simp[Excl "unlock_if_nr_def"]) >>
      qpat_x_assum `!i c. IntRet ir cs = IntRet i c ==> _`
        (qspecl_then [`ir`,`cs`] mp_tac) >>
      simp_tac bool_ss [pairTheory.SND, vyperStateTheory.evaluation_state_fupdcanon,
                        selected_immutable_frame_gas_obs] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      asm_rewrite_tac[result_rel_def] >>
      qpat_x_assum `immutable_frame_mods _ _ _ _ _`
        (ACCEPT_TAC o REWRITE_RULE [selected_immutable_frame_gas_obs])) >>
  simp[]
QED

Resume selected_compose_native_terminal[exception]:
  qpat_x_assum `answer = INR ex` SUBST_ALL_TAC >>
  pure_rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INR ex`,`ee`,`r`,`J`,`tc`] >>
  asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx _ H _ ==> valid_horizon _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon (cx with stk updated_by _) _ H _ ==> _ /\ exit_result r /\ create_size_exit_ok ctx (INR ex) r /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon cx _ H _ ==> gas_origin_ptr_path _ _ [] _`
        (drule_then assume_tac) >>
      drule gas_origin_ptr_path_append >>
      disch_then (qspecl_then [`at_body`,`Gl`,`tnl`] mp_tac) >> simp[]) >>
  qpat_x_assum `res = INR ex` SUBST_ALL_TAC >>
  qpat_x_assum `INR ex = (case _ of _ => _ | _ => _)`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  BETA_TAC >> asm_rewrite_tac[]
QED
Finalise selected_compose_native_terminal[local]

Theorem selected_immutable_frame_after_clear[local]:
  immutable_frame_mods fn ce p ((e with gas_obs := obs) with scopes := []) u <=>
  immutable_frame_mods fn ce p (e with scopes := []) u
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutables_rel_def,
    immutable_alloca_sep_mods_def, exprLoweringPropsTheory.immutable_alloca_sep_def]
QED

Theorem selected_return_frame_empty[local]:
  same_frame body_ce site /\ immutable_frame_mods callee site p ee u ==>
  immutable_frame_mods callee body_ce p (ee with scopes := []) (return_unlock_state site u)
Proof
  strip_tac >>
  `body_ce.ce_modules = site.ce_modules /\ body_ce.ce_is_ctor = site.ce_is_ctor /\
   body_ce.ce_module_vars = site.ce_module_vars /\
   body_ce.ce_module_var_type = site.ce_module_var_type` by
    fs[same_frame_def, compile_env_component_equality] >>
  `(return_unlock_state site u).vs_memory = u.vs_memory /\
   (return_unlock_state site u).vs_data_section = u.vs_data_section /\
   (return_unlock_state site u).vs_alloca_next = u.vs_alloca_next` by
    (Cases_on `site.ce_nonreentrant` >> rename1 `site.ce_nonreentrant = (nr,info)` >>
     PairCases_on `info` >> Cases_on `nr` >> Cases_on `info1` >> Cases_on `info2` >>
     simp[return_unlock_state_def, venomStateTheory.tstore_def, venomStateTheory.sstore_def]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _`
        (qspecl_then [`src`,`tops`] (drule_then assume_tac)) >>
      fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (qspecl_then [`src`,`tops`] (drule_then assume_tac)) >>
  fs[exprLoweringPropsTheory.immutable_alloca_sep_def,
     exprLoweringPropsTheory.immutable_decl_sep_def,
     loweringStateRelDefsTheory.local_region_def, vyperStateTheory.lookup_scopes_def,
     return_unlock_state_frames] >>
  Cases_on `site.ce_is_ctor` >> fs[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!n ty tv off. _ /\ _ /\ _ ==> _` (drule_all_then strip_assume_tac) >>
      asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!n tv v off. _ /\ _ ==> _` (drule_all_then strip_assume_tac) >> asm_rewrite_tac[]
QED

val qstmt = ``\(H : (bool # bytes32 # type_value) list # num list) res ee G tn u. ?site.
  stmt_lands NoLoop z res u /\ ~u.vs_halted /\
  (res = INL () ==> ~block_is_terminated z /\ site = out_ce) /\
  cenv_top_ext body_ce site ee.scopes /\
  stmt_state_rel H ctx callee site ^pushed ee u /\
  immutable_frame_mods callee site ^pushed ee u /\
  storage_well_formed_on ^pushed ee (FST H) /\
  return_buf_frame d site z u /\ alloca_history callee u /\
  return_buf_sep d site ee u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  at_body.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d site ^pushed ee G tn u /\
  (!x w. not_fresh_at a x /\ lookup_var x at_body = SOME w ==>
              lookup_var x u = SOME w) /\
  (!aid b0. FLOOKUP at_body.vs_allocas aid = SOME b0 ==>
              FLOOKUP u.vs_allocas aid = SOME b0) /\
  (!x. not_fresh_at a x ==> FLOOKUP G x = FLOOKUP Gl x /\
              op_taint tn (Var x) = op_taint tnl (Var x)) /\
  alloca_frame body_ce locked a at_body site ee u /\
  (!aid off sz i. FLOOKUP at_body.vs_allocas aid = SOME (off,sz) /\ aid < a.cs_next_id /\
     (!n b0 sz0. local_region body_ce locked.scopes at_body n b0 sz0 ==>
               off + sz <= b0 \/ b0 + sz0 <= off) /\
     off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tnl.t_mem)``;

Theorem selected_compose_void_fallthrough[local]:
  ^return_input /\ ^whole_source_run /\ answer = INL NoneV /\
  rc = 0 /\ rbs = 0 /\
  stmts_env body_ce NoLoop (BaseT BoolT) body_stmts a = (out_ce,z) /\
  body_ce.ce_return_pc = SOME (PtrVar (Var rpc) sz) /\
  body_ce.ce_nonreentrant = (nr,key,T,view) /\
  body_ce.ce_returns_count = 0 /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  (nr /\ ~view ==> ~cx.txn.is_static) /\ ret_pc_ok body_ce a at_body /\
  (if block_is_terminated z then ((),z)
   else comp_ignore_bind
     (if nr then compile_nonreentrant_unlock key T view else comp_return ())
     (emit_inst RET [Var rpc] []) z) = ((),final) /\
  fn_has_code z final callee /\
  unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),released_state) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  storage_trace_domain ^pushed st0 ee.storage_trace /\
  (!(H : (bool # bytes32 # type_value) list # num list).
    dead_lo_ok_mods H (DF H) lo body_ce ^pushed) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon ^pushed st0 H ee.storage_trace /\ storage_well_formed_on cx released_state (FST H)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path ^native_code ^entry_start marks (OK u,Gb,tnb)) /\
  (!H. valid_horizon ^pushed st0 H ee.storage_trace ==>
     (^qstmt) H (INL ()) (ee with gas_obs := []) Gb tnb u) ==>
  ^callee_outcome
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`p` |-> `^pushed`,
    `out` |-> `out_ce`, `ee` |-> `ee with gas_obs := []`, `released` |-> `released_state`,
    `t` |-> `u`, `G` |-> `Gb`, `tn` |-> `tnb`, `rtv` |-> `ret_tv`,
    `explicit` |-> `^explicit_sites`, `PG` |-> `^callee_pins`]
      selected_fallthrough_suffix_run_mods) >> BETA_TAC >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     TRY (strip_tac >> fs[] >> NO_TAC) >>
     `unlock_if_nr ^pushed nr view = unlock_if_nr cx nr (is_view_mut mut)` by
       (Cases_on `nr` >> fs[vyperInterpreterTheory.unlock_if_nr_def, Excl "is_view_mut_def"]) >>
     simp[Excl "unlock_if_nr_def", Excl "is_view_mut_def"])) >>
  disch_then (qx_choose_then `ir` (qx_choose_then `cs`
              (qx_choose_then `J` (qx_choose_then `N` strip_assume_tac)))) >>
  qpat_x_assum `answer = INL NoneV` SUBST_ALL_TAC >>
  irule selected_complete_intret >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac >- (qexistsl_tac [`bb`,`inst`,`lbl`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`J`,`body_ce`,`cs`,`ee`,`exps`,`ir`,`marks`,`released_state`,`ret_tv`,`N`,`NoneV`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon cx _ h _ ==> valid_horizon _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. valid_horizon cx _ h _ ==> gas_origin_ptr_path _ _ _ _`
    (drule_then assume_tac) >>
  conj_tac
  >- (drule gas_origin_ptr_path_append >>
      disch_then (qspecl_then [`u`,`Gb`,`tnb`] mp_tac) >>
      disch_then (qspecl_then [`[]`,`IntRet ir cs`,`J`,`N`] mp_tac) >>
      asm_rewrite_tac[listTheory.APPEND_NIL]) >>
  qpat_assum `!h. _ ==> state_rel _ _ _ _ _ _ /\ _` (qspec_then `H` mp_tac) >>
  simp_tac bool_ss [vyperStateTheory.evaluation_state_accessors] >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (drule_all_then mp_tac constructor_exit_state_rel >>
      simp[result_rel_def, intret_vals_match_def]) >>
  conj_tac
  >- (qpat_assum `!h. _ ==> ?site. stmt_lands _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >>
      `site = out_ce` by fs[] >>
      qpat_x_assum `site = out_ce` SUBST_ALL_TAC >>
      drule_all_then mp_tac selected_return_frame_empty >>
      pure_rewrite_tac[selected_immutable_frame_after_clear] >>
      qpat_assum `cs = _` (pure_rewrite_tac o single) >> disch_then ACCEPT_TAC) >>
  `body_ce.ce_modules = out_ce.ce_modules /\
   body_ce.ce_module_vars = out_ce.ce_module_vars` by
    fs[same_frame_def, compile_env_component_equality] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  qpat_assum `!i. _ ==> imm_section_dead_mods out_ce _ i` mp_tac >>
  qpat_assum `body_ce.ce_modules = _` (pure_rewrite_tac o cons imm_section_dead_mods_def o single) >>
  qpat_assum `body_ce.ce_module_vars = _` (pure_rewrite_tac o single) >>
  disch_then ACCEPT_TAC
QED

val native_rstmt = ``\(H : (bool # bytes32 # type_value) list # num list)
    (res : unit + exception) ee (gt : (string |-> num # num) # taint) r.
  (!tail. stmt_exit_ptr ((^callee_retq) H) (ee with gas_obs := tail) res gt r) /\
  halt_exit H ^pushed ee res r /\
  (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
      allocas_below_fmp s)``;
val native_outcome = ``gas_outcome_full_mods (DF,lo,^explicit_sites,ctx,callee,^callee_pins)
  mods ^pushed st0 (eval_stmts ^pushed ss) (locked,^native_start) ^qstmt ^native_rstmt``;
val locked_source = ``!tail. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := tail) =
    (INL (),locked with gas_obs := tail)``;
val lock_path = ``!(H : (bool # bytes32 # type_value) list # num list).
    gas_origin_ptr_path ^native_code ^entry_start [] (OK at_body,Gl,tnl)``;

Theorem selected_entry_gas_readings[local]:
  gas_origin_ptr_path (D,lo,X,ctx,callee,PG) (s,G,tn) [] (OK u,J,N) ==>
  u.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> drule_then strip_assume_tac gas_origin_ptr_path_projections >>
  drule_then strip_assume_tac fragGasOriginTheory.gas_origin_path_erase >>
  fs[fragGasModeTheory.gas_marked_path_def] >> drule gas_path_mem_ok_suffix >> simp[]
QED

Theorem selected_native_focus_to_callee[local]:
  ^locked_source /\ ^lock_path /\
  (storage_trace_domain cx st0 es1.storage_trace ==>
   storage_trace_domain ^pushed st0 locked.storage_trace) /\
  (storage_trace_domain ^pushed st0 locked.storage_trace ==>
   valid_horizon ^pushed st0 H locked.storage_trace) /\
  gas_origin_ptr_focus ^native_code ^native_start marks (leaf,leaf_pg,leaf_g,leaf_tn,endpoint) /\
  (gas_bad_storage_at ^pushed st0 (eval_stmts ^pushed ss) locked at_body marks \/
   ?err ee. gas_exempt_cert_mods T mods (ctx,callee)
      (ignore_bind (eval_stmts ^pushed ss) (return ()))
      (locked,at_body) marks (err,ee) (leaf,endpoint)) ==>
  ^callee_outcome
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`X` |-> `^explicit_sites`, `PGc` |-> `^callee_pins`,
    `G` |-> `FEMPTY:(string |-> num # num)`, `tn` |-> `tn with t_var := FEMPTY`,
    `Q` |-> `\H res ee J N u. F`, `R` |-> `^selected_exit`]
      (SPEC_ALL selected_qualified_body_focus_mods)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [BETA_THM]
QED

val fallthrough_code = ``
  rc = 0 /\ rbs = 0 /\
  stmts_env body_ce NoLoop (BaseT BoolT) body_stmts a = (out_ce,z) /\
  body_ce.ce_return_pc = SOME (PtrVar (Var rpc) sz) /\
  (if block_is_terminated z then ((),z)
   else comp_ignore_bind
     (if nr then compile_nonreentrant_unlock key T view else comp_return ())
     (emit_inst RET [Var rpc] []) z) = ((),final) /\ fn_has_code z final callee``;

Theorem selected_attach_locked_body[local]:
  ^return_input /\ ^locked_source /\ ^lock_path /\ ^native_outcome /\
  (storage_trace_domain cx st0 es1.storage_trace ==>
   storage_trace_domain ^pushed st0 locked.storage_trace) /\
  body_ce.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  (nr /\ ~view ==> ~cx.txn.is_static) /\
  body_ce.ce_returns_count = rc /\ (0 < rc \/ 0 < rbs ==> ret_tv = rtv) /\
  (ret = NoneT ==> ^fallthrough_code) /\ ret_pc_ok body_ce a at_body /\
  (!(H : (bool # bytes32 # type_value) list # num list).
    dead_lo_ok_mods H (DF H) lo body_ce ^pushed) /\
  (!H. valid_horizon ^pushed st0 H locked.storage_trace ==>
       storage_well_formed_on ^pushed locked (FST H)) /\
  type_stmts env ret ss = SOME env_after /\ runtime_consistent env ^pushed locked /\
  functions_well_typed ^pushed /\ call_evaluation_safe ^pushed (int_calls_stmts ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  gas_admissible (do lock_if_nr cx nr (is_view_mut mut);
    rv <- finally_unless_halt
        (finally (try (do eval_stmts ^pushed ss; return NoneV od) handle_function)
                 (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return (Value crv) od) expr_vv_res_ok es1 ==>
  ^callee_outcome
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_outcome_full_mods_def]) >> BETA_TAC >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- suspend "bad" >- suspend "finished" >> suspend "exempt"
QED

Resume selected_attach_locked_body[bad]:
  irule selected_native_focus_to_callee >>
  rpt (goal_assum (drule_at Any)) >>
  disj1_tac >> first_assum ACCEPT_TAC
QED

Resume selected_attach_locked_body[exempt]:
  irule selected_native_focus_to_callee >>
  rpt (goal_assum (drule_at Any)) >>
  disj2_tac >> qexistsl_tac [`err`,`ee`] >> first_assum ACCEPT_TAC
QED

Resume selected_attach_locked_body[finished]:
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (at_body,Gl,tnl) marks (r,Gb,tnb)` >>
  `at_body.vs_gas_readings = entered.vs_gas_readings` by
    (qpat_assum `!h. gas_origin_ptr_path _ _ [] _` (qspec_then `storage_trace_horizon locked.storage_trace` assume_tac) >>
     drule_then ACCEPT_TAC selected_entry_gas_readings) >>
  qpat_assum `at_body.vs_gas_readings = _` (fn eq =>
    qpat_x_assum `!tail. eval_stmts _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [eq])) >>
  drule_all selected_qualified_body_source_mods >>
  disch_then (qspec_then `st0` strip_assume_tac) >>
  qabbrev_tac `answer = ^terminal_answer` >>
  `^whole_source_run` by
    (qpat_assum `!tail. (^selected_src) _ = _` mp_tac >>
     pop_assum (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     Cases_on `res` >- simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
     qmatch_goalsub_rename_tac `INR errval : unit + exception` >> Cases_on `errval` >>
     simp[handle_function_def, return_def, raise_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `storage_trace_domain cx st0 ee.storage_trace` by fs[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon cx _ h _ ==> _ /\ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!h. valid_horizon _ _ h locked.storage_trace ==> _`
       (drule_then assume_tac) >>
     qpat_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all selected_reached_body_storage >> simp[storage_well_formed_on_stk]) >>
  `!H out. valid_horizon cx st0 H ee.storage_trace /\
     unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) ==>
     storage_well_formed_on cx out (FST H)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!h. valid_horizon cx _ h _ ==> storage_well_formed_on _ _ _`
       (drule_then assume_tac) >>
     qpat_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all_then ACCEPT_TAC selected_release_at_body_horizon) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path ^native_code ^entry_start marks (r,Gb,tnb)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. valid_horizon cx _ h _ ==> _ /\ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     qpat_assum `!h. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ _ [] _` (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`at_body`,`Gl`,`tnl`] mp_tac) >> simp[]) >>
  Cases_on `?u. r = OK u`
  >- (qpat_x_assum `?u. r = OK u` (qx_choose_then `u` SUBST_ALL_TAC) >>
      qpat_x_assum `!h. valid_horizon _ _ h _ ==> gas_origin_ptr_path _ _ _ (OK u,Gb,tnb) /\ _`
        (strip_assume_tac o SIMP_RULE bool_ss [fragExecTheory.exit_result_def,
          venomExecSemanticsTheory.exec_result_11, EXISTS_REFL, UNWIND_THM2]) >>
      `res = INL ()` by
        (`valid_horizon ^pushed st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
           fs[storage_trace_domain_def] >>
         qpat_assum `!h. valid_horizon _ _ h _ ==> _ /\ (?site. stmt_lands _ _ _ _ /\ _)`
           (drule_then strip_assume_tac) >>
         qpat_x_assum `stmt_lands NoLoop _ _ _` mp_tac >> simp[loweringPostsTheory.stmt_lands_def]) >>
      qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
      drule_all_then (strip_assume_tac o SPEC_ALL) selected_qualified_fallthrough_void_mods >>
      qpat_assum `ret = NoneT ==> _` (drule_then strip_assume_tac) >>
      irule selected_compose_void_fallthrough >>
      rpt (goal_assum (drule_at Any)) >>
      conj_tac >- (qexistsl_tac [`bb`,`inst`,`lbl`] >> asm_rewrite_tac[]) >>
      qexistsl_tac [`Gb`,`Gl`,`a`,`INL NoneV`,`at_body`,`body_ce`,`body_stmts`,`d`,`ee`,
        `exps`,`final`,`key`,`locked`,`marks`,`out_ce`,`out`,`rpc`,`sz`,`tnb`,`tnl`,`u`,`view`,`z`] >>
      BETA_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]) >>
  irule selected_compose_native_terminal >>
  rpt (goal_assum (drule_at Any)) >>
  conj_tac >- (qexistsl_tac [`bb`,`inst`,`lbl`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`Gl`,`Gb`,`answer`,`at_body`,`body_ce`,`ee`,`exps`,`key`,`marks`,
    `r`,`res`,`ret_tv`,`tnb`,`tnl`,`view`] >>
  BETA_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  TRY (simp[Abbr `answer`, Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then mp_tac) >>
  disch_then strip_assume_tac
  >- (qpat_x_assum `~(?u. r = OK u)` mp_tac >>
      qmatch_asmsub_rename_tac `r = OK landed` >>
      simp_tac bool_ss [NOT_EXISTS_THM] >>
      disch_then (qspec_then `landed` mp_tac) >> asm_rewrite_tac[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise selected_attach_locked_body[local]

val caller_rest = ``do lock_if_nr cx nr (is_view_mut mut);
    rv <- finally_unless_halt
        (finally (try (do eval_stmts ^pushed ss; return NoneV od) handle_function)
                 (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return (Value crv) od``;

Theorem selected_lock_under_push[local]:
  (nr ==> view = is_view_mut mut) ==>
  lock_if_nr ^pushed nr view = lock_if_nr cx nr (is_view_mut mut)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, check_not_static_def, Excl "is_view_mut_def"]
QED

Theorem selected_pushed_trace_domain[local]:
  storage_trace_domain ^pushed st0 tr <=> storage_trace_domain cx st0 tr
Proof
  simp[storage_trace_domain_def, valid_horizon_def,
    storage_well_formed_on_stk, storage_observations_ok_stk]
QED

Theorem selected_acquired_trace_domain[local]:
  (nr ==> cx.nonreentrant_slot = SOME key) /\
  (nr ==> storage_trace_domain ^pushed st0 (es1.storage_trace ++ [StorageLock key])) /\
  lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := []) =
    (INL (),locked with gas_obs := []) /\
  storage_trace_domain cx st0 es1.storage_trace ==>
  storage_trace_domain ^pushed st0 locked.storage_trace
Proof
  Cases_on `nr`
  >- (simp_tac bool_ss [] >> strip_tac >> drule_all lock_if_nr_success_trace >> simp[]) >>
  simp[lock_if_nr_def, return_def, selected_pushed_trace_domain,
       evaluation_state_component_equality] >> strip_tac >>
  qpat_assum `es1.storage_trace = _` (fn eq => pure_rewrite_tac [GSYM eq]) >>
  first_assum ACCEPT_TAC
QED

val prologue_path = ``!D. gas_origin_ptr_path (D,lo,^explicit_sites,ctx,callee,^callee_pins)
    ^entry_start [] (OK at_pro,Gpro,tnpro)``;
val bad_lock = ``nr /\ ~storage_trace_domain ^pushed st0 (es1.storage_trace ++ [StorageLock key]) /\
  (!(k : evaluation_state -> value evaluation_result) tail. storage_trace_frame k ==>
      ~storage_trace_domain ^pushed st0
        (SND (ignore_bind (lock_if_nr ^pushed nr (is_view_mut mut)) k
                (es1 with gas_obs := tail))).storage_trace)``;
val abort_lock = ``?msg ab ee u P N.
    nr /\ ((msg = "nonreentrant lock" /\ ab = Revert_abort) \/
            (msg = "write in static context" /\ ab = ExHalt_abort)) /\
    lock_if_nr ^pushed nr (is_view_mut mut) es1 = (INR (Error (RuntimeError msg)),ee) /\
    (!tail. lock_if_nr ^pushed nr (is_view_mut mut) (es1 with gas_obs := tail) =
            (INR (Error (RuntimeError msg)),ee with gas_obs := tail)) /\
    (!D. gas_origin_ptr_path (D,lo,^explicit_sites,ctx,callee,^callee_pins)
       (at_pro,Gpro,tnpro) [] (Abort ab u,P,N)) /\
    (^pushed).nonreentrant_slot = SOME key /\
    compile_nonreentrant_lock key T (is_view_mut mut) prologue = ((),a) /\
    fn_has_code prologue a callee /\ at_pro.vs_current_bb = prologue.cs_current_bb /\
    at_pro.vs_inst_idx = LENGTH prologue.cs_current_insts /\
    (!H. valid_horizon ^pushed st0 H es1.storage_trace ==>
          stmt_state_rel H ctx callee body_ce ^pushed es1 at_pro)``;

val qual_lock_short = Q.INST [`R` |-> `^selected_exit`] (SPEC_ALL selected_qualified_lock_short_circuit_mods)
  |> PURE_REWRITE_RULE [LET_THM] |> BETA_RULE;

Theorem selected_no_entry_domain[local]:
  ~entered.vs_halted /\ ~storage_trace_domain cx st0 es1.storage_trace ==> ^callee_outcome
Proof
  strip_tac >> irule qual_lock_short >>
  goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> disj1_tac >> asm_rewrite_tac[]) >>
  qpat_assum `~storage_trace_domain _ _ _` (simp_tac bool_ss o single)
QED

Theorem selected_lock_nonbody[local]:
  ~entered.vs_halted /\ ~at_pro.vs_halted /\ ^prologue_path /\
  (^bad_lock \/ ^abort_lock) ==> ^callee_outcome
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule qual_lock_short >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> disj1_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`Gpro`,`a`,`at_pro`,`body_ce`,`key`,`prologue`,`tnpro`] >>
  disj2_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* A successful source lock can still be observed at an invalid storage horizon.
   In that case only the lock focus is usable, not the landed statement run. *)
Theorem selected_acquired_bad_domain[local]:
  nr /\ (^pushed).nonreentrant_slot = SOME key /\
  ~storage_trace_domain ^pushed st0 (es1.storage_trace ++ [StorageLock key]) /\
  (!tail. lock_if_nr ^pushed nr (is_view_mut mut) (es1 with gas_obs := tail) =
     (INL (),locked with gas_obs := tail)) ==>
  ^bad_lock
Proof
  Cases_on `nr` >> simp_tac bool_ss [] >> strip_tac >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!tail. lock_if_nr _ _ _ _ = _` (qspec_then `tail` assume_tac) >>
  drule_all_then assume_tac lock_if_nr_success_trace >>
  simp_tac bool_ss [ignore_bind_def, bind_def] >> asm_rewrite_tac[] >>
  Cases_on `k (locked with gas_obs := tail)` >> simp_tac bool_ss [pairTheory.SND] >>
  rename1 `k (locked with gas_obs := tail) = (kr,ks)` >>
  irule (Q.INST_TYPE [`:'a` |-> `:value`]
    gasStorageTheory.storage_trace_frame_preserves_bad_domain) >>
  qexistsl_tac [`k`,`kr`,`locked with gas_obs := tail`] >>
  fs[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem selected_append_prologue_lock[local]:
  ^prologue_path /\
  (!D. gas_origin_ptr_path (D,lo,^explicit_sites,ctx,callee,^callee_pins)
      (at_pro,Gpro,tnpro) [] (OK at_body,Gl,tnl)) ==>
  ^lock_path
Proof
  strip_tac >> gen_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ ^entry_start _ _`
    (qspec_then `DF H` mp_tac) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`at_pro`,`Gpro`,`tnpro`,`[]`,`OK at_body`,`Gl`,`tnl`] mp_tac) >>
  simp[]
QED

(* Keep the lock cut's actual postcondition intact. Its reached witnesses are
   opened by the success branch, not chosen by the body proof. *)
val lock_landing_rule = Q.INST [
  `p` |-> `^pushed`, `PG` |-> `^callee_pins`, `explicit` |-> `^explicit_sites`,
  `pro` |-> `prologue`, `ce` |-> `body_ce`, `es` |-> `es1`, `s` |-> `at_pro`,
  `G` |-> `Gpro`, `tn` |-> `tnpro`]
  (SPEC_ALL (Q.INST_TYPE [`:'a` |-> `:value`] selected_lock_landing_run_mods));
val (lock_pre,lock_cases) = dest_imp (concl lock_landing_rule);
val lock_landed = snd (strip_exists (List.last (strip_disj lock_cases)));

Theorem selected_case_at_prologue[local]:
  ~entered.vs_halted /\ ^prologue_path /\ ^lock_pre /\
  (nr ==> view = is_view_mut mut) /\
  (!locked at_body P N.
    ^lock_landed /\ (nr ==> storage_trace_domain ^pushed st0
      (es1.storage_trace ++ [StorageLock key])) /\
    storage_trace_domain cx st0 es1.storage_trace ==> ^callee_outcome) ==>
  ^callee_outcome
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  reverse (Cases_on `storage_trace_domain cx st0 es1.storage_trace`)
  >- (irule selected_no_entry_domain >> asm_rewrite_tac[]) >>
  `lock_if_nr ^pushed nr view = lock_if_nr ^pushed nr (is_view_mut mut)` by
    (Cases_on `nr` >> fs[lock_if_nr_def, Excl "is_view_mut_def"]) >>
  `^bad_lock \/ ^abort_lock ==> ^callee_outcome` by
    (disch_tac >> irule selected_lock_nonbody >>
     rpt (goal_assum (drule_at Any))) >>
  mp_tac lock_landing_rule >> (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (DISJ_CASES_THEN2
      (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac))
      strip_assume_tac))
  >- (qpat_assum `(_ \/ _) ==> ^callee_outcome` MATCH_MP_TAC >> disj1_tac >>
      conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `lock_if_nr _ _ view = _` (pure_once_rewrite_tac o single o SYM) >>
      first_assum ACCEPT_TAC)
  >- (qpat_assum `(_ \/ _) ==> ^callee_outcome` MATCH_MP_TAC >> disj2_tac >>
      rename1 `lock_if_nr _ _ view es1 = (INR (Error (RuntimeError msg)),ee)` >>
      rename1 `!D. gas_origin_ptr_path (D,_,_,_,_,_) (at_pro,Gpro,tnpro) [] (Abort ab u,J,tc)` >>
      qexistsl_tac [`msg`,`ab`,`ee`,`u`,`J`,`tc`] >>
      qpat_assum `lock_if_nr _ _ view = _` (pure_rewrite_tac o single o SYM) >>
      simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]
      >- (qpat_assum `nr ==> view = _` (drule_then (pure_once_rewrite_tac o single o SYM)) >>
          qpat_assum `(if nr then _ else _) prologue = _` mp_tac >>
          qpat_assum `nr` (simp_tac bool_ss o single)) >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rename1 `lock_if_nr _ _ view es1 = (INL (),locked)` >>
  rename1 `!D. gas_origin_ptr_path (D,_,_,_,_,_) (at_pro,Gpro,tnpro) [] (OK at_body,Gl,tnl)` >>
  Cases_on `nr ==> storage_trace_domain ^pushed st0 (es1.storage_trace ++ [StorageLock key])`
  >- (qpat_assum `!locked s J tc. _ ==> ^callee_outcome`
        (qspecl_then [`locked`,`at_body`,`Gl`,`tnl`] MATCH_MP_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `(_ \/ _) ==> ^callee_outcome` MATCH_MP_TAC >> disj1_tac >>
  MATCH_MP_TAC (Q.INST [`locked` |-> `locked`] selected_acquired_bad_domain) >>
  fs[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  qpat_assum `lock_if_nr _ T view = _` (pure_once_rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED

(* The reached prologue supplies the concrete lock-success inputs.  Keep the
   body-fragment and return contracts as premises of this local adapter; the
   adapter itself supplies the outcome callback required by selected_case_at_prologue. *)
val selected_native_run_input = ``stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,^callee_pins,callee,shadow_callee)
    ^pushed NoLoop ^callee_retq body_ce
    (stmts_env body_ce NoLoop ret b)
    (stmts_env (gas_shadow_env T body_ce) NoLoop ret
      (MAP gas_shadow_stmt b))
    (eval_stmts ^pushed ss) locked /\
  body_ce.ce_modules = mods /\
  (stmts_env body_ce NoLoop ret b) a = (out_ce,z) /\
  (stmts_env (gas_shadow_env T body_ce) NoLoop ret
    (MAP gas_shadow_stmt b)) aS = (gas_shadow_env T out_ce,zS) /\
  gas_shadow_state a aS /\ gas_shadow_state z zS /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function callee shadow_callee /\
  MEM callee ctx.ctx_functions /\ MEM shadow_callee shadow_ctx.ctx_functions /\
  fn_has_code a z callee /\ fn_has_code aS zS shadow_callee /\
  (!H. dead_lo_ok_mods H (DF H) lo body_ce ^pushed) /\
  fn_inst_ids_distinct callee /\ local_ptrs_reserved body_ce a /\
  ret_pc_ok body_ce a at_body /\
  (!x sz. body_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at a x) /\
  ~block_is_terminated a /\
  gas_admissible (eval_stmts ^pushed ss) (stmt_res_ok NoLoop) locked /\
  return_buf_frame d body_ce a at_body /\
  return_buf_sep d body_ce locked at_body /\
  alloca_history callee at_body /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp at_body) /\
  (!fn inst s. frag_reachable ctx callee at_body fn inst s ==>
     dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon ^pushed st0 H locked.storage_trace ==>
    stmt_state_rel H ctx callee body_ce ^pushed locked at_body /\
    immutable_frame_mods callee body_ce ^pushed locked at_body /\
    storage_well_formed_on ^pushed locked (FST H) /\
    ghost_inv_at_mods (DF H) lo d body_ce ^pushed locked P N at_body) /\
  ~at_body.vs_halted /\ at_body.vs_current_bb = a.cs_current_bb /\
  at_body.vs_inst_idx = LENGTH a.cs_current_insts``;

val selected_attach_local = ``
  storage_trace_domain cx st0 es1.storage_trace ==>
    storage_trace_domain ^pushed st0 locked.storage_trace /\
  body_ce.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  (nr /\ ~view ==> ~cx.txn.is_static) /\
  body_ce.ce_returns_count = rc /\
  (0 < rc \/ 0 < rbs ==> ret_tv = rtv) /\
  (ret = NoneT ==> ^fallthrough_code) /\
  ret_pc_ok body_ce a at_body /\
  (!(H : (bool # bytes32 # type_value) list # num list).
    dead_lo_ok_mods H (DF H) lo body_ce ^pushed) /\
  (!H. valid_horizon ^pushed st0 H locked.storage_trace ==>
       storage_well_formed_on ^pushed locked (FST H)) /\
  type_stmts env ret ss = SOME env_after /\
  runtime_consistent env ^pushed locked /\
  functions_well_typed ^pushed /\
  call_evaluation_safe ^pushed (int_calls_stmts ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  gas_admissible (do lock_if_nr cx nr (is_view_mut mut);
    rv <- finally_unless_halt
        (finally (try (do eval_stmts ^pushed ss; return NoneV od) handle_function)
                 (pop_function prev)) (unlock_if_nr cx nr (is_view_mut mut));
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return (Value crv) od) expr_vv_res_ok es1``;

Theorem selected_prologue_outcome[local]:
  ~entered.vs_halted ==>
  ^prologue_path ==>
  ^lock_pre ==>
  (nr ==> view = is_view_mut mut) ==>
  ^return_input ==>
  ^locked_source ==>
  (!locked at_body P N.
    ^lock_landed /\
    (nr ==> storage_trace_domain ^pushed st0
      (es1.storage_trace ++ [StorageLock key])) /\
    storage_trace_domain cx st0 es1.storage_trace ==>
      ^selected_native_run_input /\ ^selected_attach_local) ==>
  ^callee_outcome
Proof
  disch_tac >> disch_tac >> disch_tac >> disch_tac >>
  disch_tac >> disch_tac >>
  disch_then (mk_asm "callback") >>
  `!locked at_body P N.
    ^lock_landed /\
    (nr ==> storage_trace_domain ^pushed st0
      (es1.storage_trace ++ [StorageLock key])) /\
    storage_trace_domain cx st0 es1.storage_trace ==>
      ^callee_outcome` by
    (rpt gen_tac >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     asm "callback"
       (qspecl_then [`locked`,`at_body`,`P`,`N`]
          (drule_all_then strip_assume_tac)) >>
     `!D. gas_origin_ptr_path (D,lo,^explicit_sites,ctx,callee,^callee_pins)
         (at_pro,Gpro,tnpro) [] (OK at_body,P,N)` by
       first_assum ACCEPT_TAC >>
     `!H. gas_origin_ptr_path (DF H,lo,^explicit_sites,ctx,callee,^callee_pins)
         ^entry_start [] (OK at_body,P,N)` by
       (irule (Q.INST [`Gl` |-> `P`, `tnl` |-> `N`] selected_append_prologue_lock) >>
        qexistsl_tac [`Gpro`,`at_pro`,`tnpro`] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        first_assum ACCEPT_TAC) >>
     mp_tac (Q.INST [`p` |-> `^pushed`, `PGc` |-> `^callee_pins`,
       `Gl` |-> `P`, `tnl` |-> `N`, `RetQ` |-> `^callee_retq`,
       `out` |-> `out_ce`, `locked` |-> `locked'`] selected_locked_body_run_mods |> BETA_RULE) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_tac >>
     `!tail. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := tail) =
          (INL (),locked' with gas_obs := tail)` by
       (mp_tac selected_lock_under_push >>
        impl_tac >- first_assum ACCEPT_TAC >>
        disch_then (fn eq =>
          qpat_assum `!tail. lock_if_nr ^pushed nr view _ =
                         (INL (),locked' with gas_obs := tail)`
            (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
     qpat_x_assum `storage_trace_domain cx st0 es1.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     mp_tac (Q.INST [`Gl` |-> `P`, `tnl` |-> `N`, `locked` |-> `locked'`]
              selected_attach_locked_body |> BETA_RULE) >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then ACCEPT_TAC) >>
  mp_tac selected_case_at_prologue >>
  (impl_tac >-
    ((conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)) >>
  strip_tac >> first_assum ACCEPT_TAC
QED
