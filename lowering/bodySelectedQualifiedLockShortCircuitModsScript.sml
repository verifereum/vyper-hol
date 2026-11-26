(* Bad entry and lock exits of the selected qualified call, before the body. *)
Theory bodySelectedQualifiedLockShortCircuitMods
Ancestors
  gasOutcomeFullZeroPrefixMods gasOutcomeFullMods fragGasOriginPtr fragGasOrigin
  fragGasSeqAbort fragGasPath fragGasMode gasSummary gasStorage fragExec
  nonreentrantEntryPath nonreentrantEquiv transientLockProps
  stateRelProj bodyFullPostsMods loweringStateRelDefs exprSimDefs createSizeExit
  vyperFiniteStoragePreservation vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState venomExecSemantics venomState venomInst list finite_map
Libs
  monadsyntax

val body_src = ``try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                        return NoneV od) handle_function``;
val callee_src = ``ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (^body_src)``;

Theorem qualified_body_trace_frame[local]:
  storage_trace_frame (^body_src)
Proof
  irule storage_trace_frame_try >> simp[storage_trace_frame_function_handler] >>
  irule storage_trace_frame_ignore_bind >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_return]
QED

Theorem qualified_lock_bad_focus[local]:
  ~s.vs_halted /\ gas_bad_storage_at cx st0 source es s [] ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,callee,PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[]` >> disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`callee`,`PG`,`G`,`tn`,`s`] >>
  conj_tac >- simp[GSYM storage_trace_domain_def] >>
  irule (cj 1 gas_origin_ptr_focus_rules) >>
  irule (cj 1 gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC
QED

Theorem qualified_lock_static_source[local]:
  cx.nonreentrant_slot = SOME key /\
  lock_if_nr cx T view es = (INR (Error (RuntimeError "write in static context")),ee) ==>
  ~view /\ cx.txn.is_static
Proof
  strip_tac >> Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  Cases_on `lookup_storage (n2w key) (es.tStorage cx.txn.target) = 1w` >>
  gvs[lock_if_nr_def, acquire_nonreentrant_lock_execution, check_not_static_def,
      ignore_bind_def, bind_def, check_def, assert_def, return_def, raise_def]
QED

(* The completed path is the very same abort as the concrete lock sequence. *)
Theorem qualified_lock_static_exit[local]:
  compile_nonreentrant_lock key T F pro = ((),a) /\ fn_has_code pro a callee /\
  ~s.vs_halted /\ s.vs_current_bb = pro.cs_current_bb /\
  s.vs_inst_idx = LENGTH pro.cs_current_insts /\ s.vs_call_ctx.cc_static /\
  gas_path ctx callee s n (Abort ExHalt_abort t) ==>
  t.vs_call_ctx.cc_static
Proof
  strip_tac >> drule_all_then strip_assume_tac compile_nonreentrant_lock_transient_prefix >>
  `?ab u. run_inst_seq (transient_lock_code key F pro) s = Abort ab u /\
          u.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tload (n2w key) s = 1w` >>
     simp[transient_lock_code_execution, transient_lock_checked_state_def,
          revert_state_def, halt_state_def, set_returndata_def, update_var_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) (transient_lock_code key F pro)` by
    simp[transient_lock_code_def, mk_inst_def, is_terminator_def] >>
  `?j. gas_marked_path F ctx callee s 0 (Abort ab (u with vs_inst_idx := j))` by
    (irule run_inst_seq_abort_zero_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`bb`,`transient_lock_code key F pro`] >> simp[]) >>
  drule gas_marked_path_exec >> strip_tac >>
  `?f. run_from f ctx callee s = Abort ab (u with vs_inst_idx := j)` by
    (irule gas_path_exit >> conj_tac >- simp[exit_result_def] >>
     qexists_tac `0` >> first_assum ACCEPT_TAC) >>
  `?g. run_from g ctx callee s = Abort ExHalt_abort t` by
    (irule gas_path_exit >> conj_tac >- simp[exit_result_def] >>
     qexists_tac `n` >> first_assum ACCEPT_TAC) >>
  `Abort ab (u with vs_inst_idx := j) = Abort ExHalt_abort t` by
    (Cases_on `f <= g` >>
     metis_tac[gas_run_from_fuel_mono, exec_result_distinct, arithmeticTheory.NOT_LESS_EQUAL,
               arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  gvs[]
QED

Theorem qualified_lock_domain_stk[local]:
  storage_trace_domain (cx with stk updated_by f) st0 tr <=>
  storage_trace_domain cx st0 tr
Proof
  simp[storage_trace_domain_def, valid_horizon_def,
       storage_well_formed_on_stk, storage_observations_ok_stk]
QED

Theorem qualified_lock_on_stack[local]:
  lock_if_nr (cx with stk updated_by f) nr view = lock_if_nr cx nr view
Proof
  simp[lock_if_nr_def, check_not_static_def]
QED

Theorem selected_qualified_lock_short_circuit_mods:
  (let p = cx with stk updated_by CONS (src,name) in
   let PGc = MAP (op_prov G) arg_ops in
   let X = gas_explicit_sites ctx shadow_ctx in
   ~entered.vs_halted /\
   (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r ==> R H res ee gt r) /\
   (~storage_trace_domain cx st0 es1.storage_trace \/
    (~at_pro.vs_halted /\
     (!D. gas_origin_ptr_path (D,lo,X,ctx,callee,PGc)
       (entered,FEMPTY,tn with t_var := FEMPTY) [] (OK at_pro,Gpro,tnpro)) /\
     ((nr /\ ~storage_trace_domain p st0 (es1.storage_trace ++ [StorageLock key]) /\
       (!(k : evaluation_state -> value evaluation_result) tail. storage_trace_frame k ==>
         ~storage_trace_domain p st0
           (SND (ignore_bind (lock_if_nr p nr (is_view_mut mut)) k
                   (es1 with gas_obs := tail))).storage_trace)) \/
      (?msg ab ee t P N.
        nr /\ ((msg = "nonreentrant lock" /\ ab = Revert_abort) \/
               (msg = "write in static context" /\ ab = ExHalt_abort)) /\
        lock_if_nr p nr (is_view_mut mut) es1 = (INR (Error (RuntimeError msg)),ee) /\
        (!tail. lock_if_nr p nr (is_view_mut mut) (es1 with gas_obs := tail) =
          (INR (Error (RuntimeError msg)),ee with gas_obs := tail)) /\
        (!D. gas_origin_ptr_path (D,lo,X,ctx,callee,PGc) (at_pro,Gpro,tnpro) []
          (Abort ab t,P,N)) /\
        p.nonreentrant_slot = SOME key /\
        compile_nonreentrant_lock key T (is_view_mut mut) pro = ((),a) /\
        fn_has_code pro a callee /\ at_pro.vs_current_bb = pro.cs_current_bb /\
        at_pro.vs_inst_idx = LENGTH pro.cs_current_insts /\
        (!H. valid_horizon p st0 H es1.storage_trace ==>
          stmt_state_rel H ctx callee ce p es1 at_pro))))) ==>
   gas_outcome_full_mods (DF,lo,X,ctx,callee,PGc) mods cx st0 (^callee_src)
     (es1,entered,FEMPTY,tn with t_var := FEMPTY) (\H res ee G' tn' t'. F) R)
Proof
  simp_tac bool_ss [LET_THM, qualified_lock_domain_stk, qualified_lock_on_stack] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (DISJ_CASES_THEN2 assume_tac (REPEAT_TCL CONJUNCTS_THEN assume_tac))))
  >- (irule qualified_lock_bad_focus >> conj_tac >- first_assum ACCEPT_TAC >>
      irule gas_bad_storage_at_initial >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      irule storage_trace_frame_ignore_bind >>
      simp[Excl "lock_if_nr_def", Excl "is_view_mut_def",
           storage_trace_frame_optional_locks, qualified_body_trace_frame]) >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
       MAP (op_prov G) arg_ops) mods cx st0 (^callee_src)
       (es1,at_pro,Gpro,tnpro) (\H res ee G' tn' t'. F) R` suffices_by
    (strip_tac >> irule gas_outcome_full_mods_zero_prefix >>
     qexistsl_tac [`Gpro`,`at_pro`,`tnpro`] >> simp[]) >>
  qpat_x_assum `(_ /\ ~storage_trace_domain _ _ _ /\ _) \/ _`
    (DISJ_CASES_THEN2 strip_assume_tac
       (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
  >- (irule qualified_lock_bad_focus >> conj_tac >- first_assum ACCEPT_TAC >>
      simp[gas_bad_storage_at_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      gen_tac >>
      qpat_assum `!k tail. storage_trace_frame k ==> _`
        (qspecl_then [`^body_src`,`tail`] mp_tac) >>
      (impl_tac >- ACCEPT_TAC qualified_body_trace_frame) >>
      simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `!tail. (^callee_src) (es1 with gas_obs := tail) =
           (INR (Error (RuntimeError msg)),ee with gas_obs := tail)` by
    (gen_tac >> pure_rewrite_tac[ignore_bind_def, bind_def] >>
     simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >- suspend "completed" >>
  irule qualified_lock_bad_focus >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[gas_bad_storage_at_def]
QED

Resume selected_qualified_lock_short_circuit_mods[completed]:
  `create_size_exit_ok ctx (INR (Error (RuntimeError msg)) : value + exception) (Abort ab t)` by
    (qpat_x_assum `(msg = _ /\ ab = _) \/ _` strip_assume_tac
     >- gvs[] >>
     qpat_x_assum `ab = ExHalt_abort` SUBST_ALL_TAC >>
     qpat_x_assum `msg = "write in static context"` SUBST_ALL_TAC >>
     irule create_size_exit_ok_static >>
     `cx.nonreentrant_slot = SOME key /\
      lock_if_nr cx T (is_view_mut mut) es1 =
        (INR (Error (RuntimeError "write in static context")),ee)` by
       gvs[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
     drule_all_then strip_assume_tac qualified_lock_static_source >>
     qabbrev_tac `p = cx with stk updated_by CONS (src,name)` >>
     `valid_horizon p st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
       simp[GSYM storage_trace_domain_def, Abbr `p`, qualified_lock_domain_stk] >>
     `valid_horizon p st0 (storage_trace_horizon ee.storage_trace) es1.storage_trace` by
       (qpat_assum `lock_if_nr _ nr _ es1 = _`
          (mp_then Any mp_tac valid_horizon_frame) >>
        simp[storage_trace_frame_optional_locks, Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ _`
       (drule_then assume_tac) >>
     drule stmt_state_rel_state_rel >> strip_tac >>
     drule state_rel_call_ctx_rel >> strip_tac >>
     `at_pro.vs_call_ctx.cc_static` by fs[call_ctx_rel_def, Abbr `p`] >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] (Abort ExHalt_abort t,_,_)`
       (qspec_then `ARB:dead` assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     `compile_nonreentrant_lock key T F pro = ((),a)` by
       fs[Excl "is_view_mut_def"] >>
     drule_all_then ACCEPT_TAC qualified_lock_static_exit) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`,`ee`,`Abort ab t`,`P`,`N`] >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def", exit_result_def] >>
  gen_tac >> disch_tac >>
  first_x_assum irule >> simp[expr_exit_def, halt_exit_def]
QED

Finalise selected_qualified_lock_short_circuit_mods
