(* Actual-oracle call boundaries for remove-unused context reconstruction. *)
Theory removeUnusedCrossContextProofs
Ancestors
  removeUnusedFnProofs removeUnusedGasProofs stateFrame stateEquivProps
  venomExecSemantics venomState stateEquiv gasOracleReplay list rich_list

(* Relocated from CorrectnessProofs so call boundaries can reuse it. *)
Theorem merge_callee_execution_equiv:
  !V s1 s2 caller.
    execution_equiv V s1 s2 ==>
    merge_callee_state caller s1 = merge_callee_state caller s2
Proof
  rpt strip_tac >>
  irule stateFrameTheory.execution_frame_projection >>
  conj_tac
  >- simp[merge_callee_state_def, stateFrameTheory.execution_frame_def] >>
  fs[Excl "core_complete_mask_equality", execution_equiv_def]
QED

Theorem remove_unused_actual_returning_invoke:
  !inst name ops ctx ctx' fn fn' args s cs N n ret v hs V.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    eval_operands ops s = SOME args /\
    setup_callee fn args s = SOME cs /\ setup_callee fn' args s = SOME cs /\
    run_blocks N ctx' fn' cs = IntRet ret v /\
    gas_replay_at n (run_blocks N ctx' fn') cs /\
    (!t. run_blocks N ctx' fn'
       (cs with vs_gas_readings := gas_prefix n cs.vs_gas_readings ++ hs) = IntRet ret t ==>
       ?gs:(256 word) list.
         LENGTH (FILTER (\w. w <> 0w) gs) <=
           LENGTH (FILTER (\w. w <> 0w) (gas_prefix n cs.vs_gas_readings ++ hs)) /\
         ((?e. run_blocks N ctx fn (cs with vs_gas_readings := gs) = Error e) \/
          ?u. run_blocks N ctx fn (cs with vs_gas_readings := gs) = IntRet ret u /\
              execution_equiv V u t)) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix n cs.vs_gas_readings)) +
        LENGTH (FILTER (\w. w <> 0w) hs) /\
      ((?e. step_inst N ctx inst (s with vs_gas_readings := gs) = Error e) \/
       ?r. bind_outputs inst.inst_outputs ret.iret_values
              (adopt_return_fmp ret (merge_callee_state s v)) = SOME r /\
           step_inst N ctx inst (s with vs_gas_readings := gs) =
             OK (r with vs_gas_readings := hs))
Proof
  rpt gen_tac >> strip_tac >>
  `run_blocks N ctx' fn'
    (cs with vs_gas_readings := gas_prefix n cs.vs_gas_readings ++ hs) =
      IntRet ret (v with vs_gas_readings := hs)` by
    (qpat_x_assum `gas_replay_at n _ cs` mp_tac >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `hs` mp_tac) >>
     Cases_on `run_blocks N ctx' fn'
       (cs with vs_gas_readings := gas_prefix n cs.vs_gas_readings ++ hs)` >>
     gvs[lift_result_def]) >>
  first_x_assum drule >>
  disch_then (qx_choose_then `gs` assume_tac) >>
  qexists_tac `gs` >> conj_tac >- gvs[FILTER_APPEND] >>
  pop_assum strip_assume_tac >>
  simp[step_inst_def, gas_setup_callee] >>
  `merge_callee_state (s with vs_gas_readings := gs) u =
    (merge_callee_state s v with vs_gas_readings := hs)` by
    (drule merge_callee_execution_equiv >>
     disch_then (qspec_then `s with vs_gas_readings := gs` mp_tac) >>
     simp[gas_merge_callee]) >>
  simp[gas_adopt_return, gas_bind_outputs] >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s v))` >> simp[]
QED

(* The generic replay alignment interface is already exported as
   remove_unused_blocks_replay_threshold; do not duplicate it here. *)
Theorem remove_unused_actual_invoke_error_reflection:
  !inst name ops ctx ctx' fn fn' args s cs N ret v gs.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    eval_operands ops s = SOME args /\
    setup_callee fn args s = SOME cs /\ setup_callee fn' args s = SOME cs /\
    run_blocks N ctx' fn' cs = IntRet ret v /\
    ((!e. step_inst N ctx inst (s with vs_gas_readings := gs) <> Error e) ==>
       ?r. bind_outputs inst.inst_outputs ret.iret_values
         (adopt_return_fmp ret (merge_callee_state s v)) = SOME r) /\
    (!k. k <= N /\ (?e. run_blocks k ctx' fn' cs = Error e) ==>
       ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e) ==>
    !k. k <= N /\ (?e. step_inst k ctx' inst s = Error e) ==>
      ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `?e. run_blocks k ctx' fn' cs = Error e`
  >- (first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
      strip_tac >> simp[step_inst_def, gas_setup_callee]) >>
  `run_blocks k ctx' fn' cs = IntRet ret v` by
    (Cases_on `run_blocks k ctx' fn' cs` >> gvs[] >>
     drule (cj 3 venomExecPropsTheory.fuel_mono) >>
     disch_then (qspec_then `N` mp_tac) >> simp[]) >>
  spose_not_then assume_tac >> gvs[] >>
  `!e. step_inst N ctx inst (s with vs_gas_readings := gs) <> Error e` by
    (Cases_on `step_inst k ctx inst (s with vs_gas_readings := gs)` >> gvs[] >>
     drule (cj 1 venomExecPropsTheory.fuel_mono) >>
     disch_then (qspec_then `N` mp_tac) >> simp[] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  gvs[step_inst_def]
QED

Theorem remove_unused_actual_call_continuation_error_reflection:
  !N ctx ctx' inst s t u v (src_cont:num -> venom_state -> exec_result) dst_cont.
    step_inst N ctx' inst t = OK v /\
    ((!e. step_inst N ctx inst s <> Error e) ==> step_inst N ctx inst s = OK u) /\
    (!k. k <= N /\ (?e. step_inst k ctx' inst t = Error e) ==>
      ?e. step_inst k ctx inst s = Error e) /\
    (!k. k <= N /\ (?e. dst_cont k v = Error e) ==>
      ?e. src_cont k u = Error e) ==>
    !k. k <= N /\
      (?e. gas_bind_ok (step_inst k ctx' inst t) (dst_cont k) = Error e) ==>
      ?e. gas_bind_ok (step_inst k ctx inst s) (src_cont k) = Error e
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `?e. step_inst k ctx inst s = Error e`
  >- (gvs[gas_bind_ok_def]) >>
  `step_inst k ctx inst s = OK u` by
    (Cases_on `step_inst k ctx inst s` >> gvs[] >>
     drule (cj 1 venomExecPropsTheory.fuel_mono) >>
     disch_then (qspec_then `N` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  Cases_on `?e. step_inst k ctx' inst t = Error e`
  >- metis_tac[] >>
  `step_inst k ctx' inst t = OK v` by
    (Cases_on `step_inst k ctx' inst t` >> gvs[] >>
     drule (cj 1 venomExecPropsTheory.fuel_mono) >>
     disch_then (qspec_then `N` mp_tac) >> simp[]) >>
  gvs[gas_bind_ok_def] >> metis_tac[]
QED

Theorem remove_unused_actual_invoke_permanent_error:
  !inst name ops ctx fn args s cs gs.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    (!k. ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e) ==>
    !k. ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e
Proof
  rpt strip_tac >> first_x_assum (qspec_then `k` strip_assume_tac) >>
  simp[step_inst_def, gas_setup_callee]
QED

Theorem remove_unused_context_uniform_from_reconstruction:
  !ctx ctx' fn fn' s V b.
    (!N. (!k. k <= N ==> ?e. run_blocks k ctx' fn' s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
        !k. k <= N ==> ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e) /\
    (!N. ~(?e. run_blocks N ctx' fn' s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
        ((!k. ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e) \/
         lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
           (run_blocks N ctx fn (s with vs_gas_readings := gs))
           (run_blocks N ctx' fn' s)) /\
        (!k. k <= N /\ (?e. run_blocks k ctx' fn' s = Error e) ==>
          ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e)) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
      !fuel.
        (?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (run_blocks fuel ctx fn (s with vs_gas_readings := gs))
          (run_blocks fuel ctx' fn' s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?N. ~(?e. run_blocks N ctx' fn' s = Error e)`
  >- (pop_assum (qx_choose_then `N` assume_tac) >>
      qpat_x_assum `!N. ~_ ==> _` drule >>
      disch_then (qx_choose_then `gs` strip_assume_tac)
      >- (qexists_tac `gs` >> simp[]) >>
      qexists_tac `gs` >> simp[] >> gen_tac >>
      suspend "successful") >>
  `?gs:(256 word) list. LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
      !k. ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e` by
    (ho_match_mp_tac remove_unused_sparse_oracle_compactness >>
     simp[remove_unused_gas_error_finite_dependence] >> metis_tac[]) >>
  qexists_tac `gs` >> simp[]
QED

Resume remove_unused_context_uniform_from_reconstruction[successful]:
  qpat_x_assum `!N. (!k. _ ==> _) ==> _` kall_tac >>
  `~(?e. run_blocks N ctx fn (s with vs_gas_readings := gs) = Error e)` by
    (Cases_on `run_blocks N ctx fn (s with vs_gas_readings := gs)` >>
     Cases_on `run_blocks N ctx' fn' s` >> gvs[lift_result_def]) >>
  Cases_on `fuel <= N`
  >- (Cases_on `?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e`
      >- simp[] >>
      Cases_on `?e. run_blocks fuel ctx' fn' s = Error e`
      >- metis_tac[] >>
      `run_blocks N ctx fn (s with vs_gas_readings := gs) =
       run_blocks fuel ctx fn (s with vs_gas_readings := gs)` by
        (gvs[] >> metis_tac[cj 3 venomExecPropsTheory.fuel_mono]) >>
      `run_blocks N ctx' fn' s = run_blocks fuel ctx' fn' s` by
        (gvs[] >> metis_tac[cj 3 venomExecPropsTheory.fuel_mono]) >>
      metis_tac[]) >>
  `N <= fuel` by decide_tac >>
  `run_blocks fuel ctx fn (s with vs_gas_readings := gs) =
   run_blocks N ctx fn (s with vs_gas_readings := gs)` by
    (gvs[] >> `N <= fuel` by decide_tac >>
     metis_tac[cj 3 venomExecPropsTheory.fuel_mono]) >>
  `run_blocks fuel ctx' fn' s = run_blocks N ctx' fn' s` by
    (gvs[] >> `N <= fuel` by decide_tac >>
     metis_tac[cj 3 venomExecPropsTheory.fuel_mono]) >>
  simp[]
QED

Finalise remove_unused_context_uniform_from_reconstruction

Theorem remove_unused_merge_caller_readings[local]:
  merge_callee_state (s with vs_gas_readings := gs) t = merge_callee_state s t
Proof
  simp[merge_callee_state_def]
QED

(* Constructor-complete transport at a decoded, successfully set-up call.
   The caller's continuing state is exact; terminal callee locals stay hidden. *)
Theorem remove_unused_actual_invoke_result_transfer:
  !inst name ops ctx ctx' fn fn' args s cs N gs V.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    eval_operands ops s = SOME args /\
    setup_callee fn args s = SOME cs /\ setup_callee fn' args s = SOME cs /\
    lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
      (run_blocks N ctx fn (cs with vs_gas_readings := gs))
      (run_blocks N ctx' fn' cs) ==>
    lift_result (state_equiv {}) (execution_equiv V) (execution_equiv V)
      (step_inst N ctx inst (s with vs_gas_readings := gs))
      (step_inst N ctx' inst s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `run_blocks N ctx fn (cs with vs_gas_readings := gs)` >>
  Cases_on `run_blocks N ctx' fn' cs` >> gvs[lift_result_def] >>
  simp[step_inst_def, gas_setup_callee, lift_result_def] >>
  drule merge_callee_execution_equiv >>
  disch_then (qspec_then `s with vs_gas_readings := gs` mp_tac) >>
  simp[remove_unused_merge_caller_readings] >> disch_then SUBST1_TAC >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v'))` >>
  simp[lift_result_def, stateEquivPropsTheory.state_equiv_refl]
QED

Theorem remove_unused_actual_invoke_nonerror_reflection:
  !inst name ops ctx ctx' fn fn' args s cs N gs.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    eval_operands ops s = SOME args /\
    setup_callee fn args s = SOME cs /\ setup_callee fn' args s = SOME cs /\
    ~(?e. step_inst N ctx' inst s = Error e) /\
    (!k. k <= N /\ (?e. run_blocks k ctx' fn' cs = Error e) ==>
      ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e) ==>
    !k. k <= N /\ (?e. step_inst k ctx' inst s = Error e) ==>
      ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `?e. run_blocks k ctx' fn' cs = Error e`
  >- (first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
      simp[step_inst_def, gas_setup_callee]) >>
  `run_blocks N ctx' fn' cs = run_blocks k ctx' fn' cs` by
    (Cases_on `run_blocks k ctx' fn' cs` >> gvs[] >>
     drule (cj 3 venomExecPropsTheory.fuel_mono) >>
     disch_then (qspec_then `N` mp_tac) >> simp[]) >>
  gvs[step_inst_def]
QED

Theorem remove_unused_actual_invoke_success_reconstruction:
  !inst name ops ctx ctx' fn fn' args s cs N V b.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    eval_operands ops s = SOME args /\
    setup_callee fn args s = SOME cs /\ setup_callee fn' args s = SOME cs /\
    ~(?e. step_inst N ctx' inst s = Error e) /\
    (~(?e. run_blocks N ctx' fn' cs = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
        ((!k. ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e) \/
         lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
           (run_blocks N ctx fn (cs with vs_gas_readings := gs))
           (run_blocks N ctx' fn' cs)) /\
        (!k. k <= N /\ (?e. run_blocks k ctx' fn' cs = Error e) ==>
          ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e)) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
      ((!k. ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e) \/
       lift_result (state_equiv {}) (execution_equiv V) (execution_equiv V)
         (step_inst N ctx inst (s with vs_gas_readings := gs))
         (step_inst N ctx' inst s)) /\
      (!k. k <= N /\ (?e. step_inst k ctx' inst s = Error e) ==>
        ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e)
Proof
  rpt gen_tac >> strip_tac >>
  `~(?e. run_blocks N ctx' fn' cs = Error e)` by
    (strip_tac >> gvs[step_inst_def]) >>
  first_x_assum drule >>
  disch_then (qx_choose_then `gs` strip_assume_tac)
  >- (qexists_tac `gs` >> simp[] >>
      `!k. ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e` by
        (irule remove_unused_actual_invoke_permanent_error >>
         goal_assum (drule_at Any) >> simp[]) >> simp[]) >>
  qexists_tac `gs` >> simp[] >> conj_tac
  >- (disj2_tac >> irule remove_unused_actual_invoke_result_transfer >>
      goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule remove_unused_actual_invoke_nonerror_reflection >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`N`, `ctx'`, `fn'`] >> gvs[]
QED

Theorem remove_unused_actual_invoke_error_reconstruction:
  !inst name ops ctx ctx' fn fn' args s cs N V b.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    eval_operands ops s = SOME args /\
    setup_callee fn args s = SOME cs /\ setup_callee fn' args s = SOME cs /\
    (?e. step_inst N ctx' inst s = Error e) /\
    (?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
      ((?e. run_blocks N ctx fn (cs with vs_gas_readings := gs) = Error e) \/
       lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
         (run_blocks N ctx fn (cs with vs_gas_readings := gs))
         (run_blocks N ctx' fn' cs))) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <= b /\
      ?e. step_inst N ctx inst (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac
  >- (qexists_tac `gs` >> simp[step_inst_def, gas_setup_callee]) >>
  qexists_tac `gs` >> simp[] >>
  `lift_result (state_equiv {}) (execution_equiv V) (execution_equiv V)
    (step_inst N ctx inst (s with vs_gas_readings := gs))
    (step_inst N ctx' inst s)` by
    (irule remove_unused_actual_invoke_result_transfer >>
     goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `step_inst N ctx inst (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def]
QED

Theorem remove_unused_invoke_static_error:
  !inst ctx s.
    inst.inst_opcode = INVOKE /\
    (decode_invoke inst = NONE \/
     ?name ops. decode_invoke inst = SOME (name,ops) /\
       (lookup_function name ctx.ctx_functions = NONE \/
        eval_operands ops s = NONE \/
        ?fn args. lookup_function name ctx.ctx_functions = SOME fn /\
          eval_operands ops s = SOME args /\ setup_callee fn args s = NONE)) ==>
    !k gs. ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e
Proof
  rpt strip_tac >> simp[step_inst_def, gas_setup_callee] >>
  Cases_on `lookup_function name ctx.ctx_functions` >>
  simp[step_inst_def, gas_setup_callee]
QED

(* A successful prefix cannot evade a permanently failing continuation by
   choosing a different fuel: any non-Error prefix result is stable. *)
Theorem remove_unused_bind_permanent_continuation_error:
  !prefix cont (N:num) s u.
    (!k m. k <= m /\ ~(?e. prefix k s = Error e) ==>
      prefix m s = prefix k s) /\
    prefix N s = OK u /\
    (!k. ?e. cont k u = Error e) ==>
    !k. ?e. gas_bind_ok (prefix k s) (cont k) = Error e
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `N <= k`
  >- (`prefix k s = OK u` by
        (qpat_x_assum `!k m. _` (qspecl_then [`N`, `k`] mp_tac) >> simp[]) >>
      simp[gas_bind_ok_def]) >>
  `k <= N` by decide_tac >>
  Cases_on `?e. prefix k s = Error e`
  >- (gvs[gas_bind_ok_def]) >>
  `prefix k s = OK u` by metis_tac[] >> simp[gas_bind_ok_def]
QED

(* Quotation-only schemas: no HOL constants or definitions are introduced. *)
val ru_context_compat = ``
  (!name. (lookup_function name ctx.ctx_functions = NONE <=>
           lookup_function name ctx'.ctx_functions = NONE)) /\
  (!name fn fn' args s.
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' ==>
    setup_callee fn args s = setup_callee fn' args s)``;

val ru_callee_error = ``
  !name fn fn' args s cs.
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    setup_callee fn args s = SOME cs /\
    (?e. run_blocks N ctx' fn' cs = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) cs.vs_gas_readings) /\
      ?e. run_blocks N ctx fn (cs with vs_gas_readings := gs) = Error e``;

val ru_callee_success = ``
  !name fn fn' args s cs.
    lookup_function name ctx.ctx_functions = SOME fn /\
    lookup_function name ctx'.ctx_functions = SOME fn' /\
    setup_callee fn args s = SOME cs /\
    ~(?e. run_blocks N ctx' fn' cs = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) cs.vs_gas_readings) /\
      ((!k. ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e) \/
       lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
         (run_blocks N ctx fn (cs with vs_gas_readings := gs))
         (run_blocks N ctx' fn' cs)) /\
      (!k. k <= N /\ (?e. run_blocks k ctx' fn' cs = Error e) ==>
        ?e. run_blocks k ctx fn (cs with vs_gas_readings := gs) = Error e)``;

Theorem remove_unused_step_context_success_reconstruction:
  !N ctx ctx' inst V.
    ^ru_context_compat /\ ^ru_callee_success ==>
    !s. ~(?e. step_inst N ctx' inst s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <=
          LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        ((!k. ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e) \/
         lift_result (state_equiv {}) (execution_equiv V) (execution_equiv V)
           (step_inst N ctx inst (s with vs_gas_readings := gs))
           (step_inst N ctx' inst s)) /\
        (!k. k <= N /\ (?e. step_inst k ctx' inst s = Error e) ==>
          ?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  qexists_tac `s.vs_gas_readings` >>
  simp[step_inst_def] >> Cases_on `step_inst_base inst s` >>
  simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
QED

Resume remove_unused_step_context_success_reconstruction[invoke]:
  Cases_on `decode_invoke inst` >- gvs[step_inst_def] >>
  rename1 `decode_invoke inst = SOME call` >> PairCases_on `call` >>
  rename1 `decode_invoke inst = SOME (name,ops)` >>
  Cases_on `lookup_function name ctx'.ctx_functions` >- gvs[step_inst_def] >>
  rename1 `lookup_function name ctx'.ctx_functions = SOME fn'` >>
  Cases_on `eval_operands ops s` >- gvs[step_inst_def] >>
  rename1 `eval_operands ops s = SOME args` >>
  Cases_on `setup_callee fn' args s` >- gvs[step_inst_def] >>
  rename1 `setup_callee fn' args s = SOME cs` >>
  Cases_on `lookup_function name ctx.ctx_functions`
  >- (qpat_x_assum `!name. (_ = NONE <=> _)` (qspec_then `name` mp_tac) >> simp[]) >>
  rename1 `lookup_function name ctx.ctx_functions = SOME fn` >>
  `setup_callee fn args s = SOME cs` by metis_tac[] >>
  `cs.vs_gas_readings = s.vs_gas_readings` by metis_tac[gas_setup_callee_readings] >>
  irule remove_unused_actual_invoke_success_reconstruction >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[] >> strip_tac >>
  qpat_x_assum `cs.vs_gas_readings = s.vs_gas_readings`
    (fn th => rewrite_tac[GSYM th]) >> first_x_assum irule >>
  simp[] >> metis_tac[]
QED

Finalise remove_unused_step_context_success_reconstruction

Theorem remove_unused_step_context_error_reconstruction:
  !N ctx ctx' inst V.
    ^ru_context_compat /\ ^ru_callee_error /\ ^ru_callee_success ==>
    !s. (?e. step_inst N ctx' inst s = Error e) ==>
      ?gs:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) gs) <=
          LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
        ?e. step_inst N ctx inst (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  qexists_tac `s.vs_gas_readings` >> gvs[step_inst_def]
QED

Resume remove_unused_step_context_error_reconstruction[invoke]:
  Cases_on `decode_invoke inst`
  >- (qexists_tac `[]` >> simp[step_inst_def]) >>
  rename1 `decode_invoke inst = SOME call` >> PairCases_on `call` >>
  rename1 `decode_invoke inst = SOME (name,ops)` >>
  Cases_on `lookup_function name ctx.ctx_functions`
  >- (qexists_tac `[]` >> simp[step_inst_def]) >>
  rename1 `lookup_function name ctx.ctx_functions = SOME fn` >>
  Cases_on `lookup_function name ctx'.ctx_functions`
  >- (qpat_x_assum `!name. (_ = NONE <=> _)` (qspec_then `name` mp_tac) >> simp[]) >>
  rename1 `lookup_function name ctx'.ctx_functions = SOME fn'` >>
  Cases_on `eval_operands ops s`
  >- (qexists_tac `[]` >> simp[step_inst_def]) >>
  rename1 `eval_operands ops s = SOME args` >>
  Cases_on `setup_callee fn args s`
  >- (qexists_tac `[]` >> simp[step_inst_def, gas_setup_callee]) >>
  rename1 `setup_callee fn args s = SOME cs` >>
  `setup_callee fn' args s = SOME cs` by metis_tac[] >>
  `cs.vs_gas_readings = s.vs_gas_readings` by metis_tac[gas_setup_callee_readings] >>
  irule remove_unused_actual_invoke_error_reconstruction >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`V`, `ctx'`, `fn'`] >> simp[] >>
  Cases_on `?e. run_blocks N ctx' fn' cs = Error e`
  >- (qpat_x_assum `!name fn fn' args s cs. _ ==> ?gs. _ /\ ?e. _` drule_all >>
      disch_then (qx_choose_then `gs` strip_assume_tac) >>
      qexists_tac `gs` >> gvs[]) >>
  qpat_x_assum `!name fn fn' args s cs. _ ==> ?gs. _ /\ (_ \/ _) /\ _` drule_all >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> gvs[] >> metis_tac[]
QED

Finalise remove_unused_step_context_error_reconstruction

val ru_error_contract = ``\N (F:num -> venom_state -> exec_result) G.
  !s. (?e. G N s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      ?e. F N (s with vs_gas_readings := gs) = Error e``;

val ru_success_contract = ``\N (F:num -> venom_state -> exec_result) G V.
  !s. ~(?e. G N s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      ((!k. ?e. F k (s with vs_gas_readings := gs) = Error e) \/
       lift_result (state_equiv {}) (execution_equiv V) (execution_equiv V)
         (F N (s with vs_gas_readings := gs)) (G N s)) /\
      (!k. k <= N /\ (?e. G k s = Error e) ==>
        ?e. F k (s with vs_gas_readings := gs) = Error e)``;

val ru_fuel_stable = ``\(H:num -> venom_state -> exec_result).
  !k m s. k <= m /\ ~(?e. H k s = Error e) ==> H m s = H k s``;

Theorem remove_unused_bind_context_error_reconstruction:
  !N P Q C D V.
    ^ru_error_contract N P Q /\ ^ru_success_contract N P Q V /\
    ^ru_error_contract N C D /\
    (!s. ~(?e. Q N s = Error e) ==> ?n. gas_replay_at n (Q N) s) ==>
    ^ru_error_contract N (\k s. gas_bind_ok (P k s) (C k))
      (\k s. gas_bind_ok (Q k s) (D k))
Proof
  simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >> Cases_on `Q N s`
  >- suspend "ok" >>
  gvs[gas_bind_ok_def] >>
  qpat_x_assum `!s. (?e. Q N s = Error e) ==> _` (qspec_then `s` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[gas_bind_ok_def]
QED

Resume remove_unused_bind_context_error_reconstruction[ok]:
  gvs[gas_bind_ok_def] >>
  qpat_x_assum `!s. (?e. D N s = Error e) ==> _` (qspec_then `v` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `hs` strip_assume_tac) >>
  qpat_x_assum `!s. (!e. Q N s <> Error e) ==> ?n. gas_replay_at n (Q N) s` (qspec_then `s` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `n` assume_tac) >>
  drule_all remove_unused_replay_ok >> strip_tac >>
  qpat_x_assum `!s. (!e. Q N s <> Error e) ==> ?gs. _ /\ _`
    (qspec_then `s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ hs` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `gs` strip_assume_tac) >>
  (qexists_tac `gs` >> conj_tac
   >- (qspec_then `n` (qspec_then `s.vs_gas_readings` mp_tac)
         remove_unused_actual_oracle_nonzero >>
       gvs[FILTER_APPEND] >> decide_tac))
  >- (qpat_x_assum `!k. ?e. P k _ = Error e` (qspec_then `N` mp_tac) >>
      strip_tac >> gvs[]) >>
  Cases_on `P N (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  drule stateEquivPropsTheory.state_equiv_empty_eq >> strip_tac >> gvs[]
QED

Finalise remove_unused_bind_context_error_reconstruction

Theorem remove_unused_bind_context_success_reconstruction:
  !N P Q C D V.
    ^ru_success_contract N P Q V /\ ^ru_success_contract N C D V /\
    ^ru_fuel_stable P /\ ^ru_fuel_stable Q /\
    ^ru_fuel_stable C /\ ^ru_fuel_stable D /\
    (!s. ~(?e. Q N s = Error e) ==>
      ?n. gas_replay_at n (Q N) s /\
        !hs k. k <= N ==>
          ((?e. Q k (s with vs_gas_readings :=
             gas_prefix n s.vs_gas_readings ++ hs) = Error e) <=>
           (?e. Q k s = Error e))) ==>
    ^ru_success_contract N (\k s. gas_bind_ok (P k s) (C k))
      (\k s. gas_bind_ok (Q k s) (D k)) V
Proof
  all_tac >> simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >> Cases_on `Q N s`
  >- suspend "ok" >>
  gvs[gas_bind_ok_def] >>
  qpat_x_assum `!s. (!e. Q N s <> Error e) ==> ?gs. LENGTH _ <= _ /\ _`
    (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[] >>
  (conj_tac
   >- ((Cases_on `!k. ?e. P k (s with vs_gas_readings := gs) = Error e`
        >- (disj1_tac >> gen_tac >>
            first_x_assum (qspec_then `k` strip_assume_tac) >> simp[])) >>
       gvs[] >> disj2_tac >>
       Cases_on `P N (s with vs_gas_readings := gs)` >> gvs[lift_result_def])) >>
  rpt strip_tac >>
  `?e. Q k s = Error e` by
    (spose_not_then assume_tac >>
     `Q N s = Q k s` by metis_tac[] >> gvs[]) >>
  qpat_x_assum `!k. k <= N /\ _ ==> ?e. P k _ = Error e`
    (qspec_then `k` mp_tac) >> (impl_tac >- simp[]) >>
  strip_tac >> simp[]
QED

Resume remove_unused_bind_context_success_reconstruction[ok]:
  gvs[gas_bind_ok_def] >>
  qpat_x_assum `!s. (!e. D N s <> Error e) ==> ?gs. _`
    (qspec_then `v` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `hs` strip_assume_tac) >>
  qpat_x_assum `!s. (!e. Q N s <> Error e) ==> ?n. gas_replay_at n _ _ /\ _`
    (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `n` strip_assume_tac) >>
  drule_all remove_unused_replay_ok >> strip_tac >>
  qpat_x_assum `!s. (!e. Q N s <> Error e) ==> ?gs. LENGTH _ <= _ /\ _`
    (qspec_then `s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ hs` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `gs` strip_assume_tac) >>
  (qexists_tac `gs` >> conj_tac
   >- (qspec_then `n` (qspec_then `s.vs_gas_readings` mp_tac)
         remove_unused_actual_oracle_nonzero >>
       gvs[FILTER_APPEND] >> decide_tac)) >>
  (conj_tac
   >- ((Cases_on `!k. ?e. P k (s with vs_gas_readings := gs) = Error e`
        >- (disj1_tac >> gen_tac >>
            first_x_assum (qspec_then `k` strip_assume_tac) >> simp[])) >>
       gvs[] >>
       Cases_on `P N (s with vs_gas_readings := gs)` >> gvs[lift_result_def] >>
       drule stateEquivPropsTheory.state_equiv_empty_eq >> strip_tac >> gvs[] >>
       disj1_tac >> rewrite_tac[GSYM gas_bind_ok_def] >>
       irule remove_unused_bind_permanent_continuation_error >>
       conj_tac >> metis_tac[])) >>
  rpt strip_tac >>
  (Cases_on `!j. ?e. P j (s with vs_gas_readings := gs) = Error e`
   >- (qpat_x_assum `!j. ?e. P j _ = Error e`
         (qspec_then `k` strip_assume_tac) >> simp[])) >>
  gvs[] >>
  (Cases_on `?e. P k (s with vs_gas_readings := gs) = Error e`
   >- (pop_assum (qx_choose_then `err` assume_tac) >> simp[])) >>
  `P N (s with vs_gas_readings := gs) =
     P k (s with vs_gas_readings := gs)` by metis_tac[] >>
  (Cases_on `?e. Q k s = Error e`
   >- (qpat_x_assum `!k. k <= N /\ _ ==> ?e. P k _ = Error e`
         (qspec_then `k` mp_tac) >>
       gvs[] >> metis_tac[])) >>
  `Q N s = Q k s` by metis_tac[] >>
  Cases_on `P k (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  drule stateEquivPropsTheory.state_equiv_empty_eq >> strip_tac >> gvs[] >>
  qpat_x_assum `!k. k <= N /\ _ ==> ?e. C k _ = Error e`
    (qspec_then `k` mp_tac) >> (impl_tac >- simp[]) >> simp[]
QED

Finalise remove_unused_bind_context_success_reconstruction

Theorem remove_unused_error_contract_preupdate:
  !N F G h.
    (!s gs. h (s with vs_gas_readings := gs) =
      (h s with vs_gas_readings := gs)) /\
    (!s. (h s).vs_gas_readings = s.vs_gas_readings) /\
    ^ru_error_contract N F G ==>
    ^ru_error_contract N (\k s. F k (h s)) (\k s. G k (h s))
Proof
  simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!s. (?e. G N s = Error e) ==> _`
    (qspec_then `h s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[]
QED

Theorem remove_unused_success_contract_preupdate:
  !N F G V h.
    (!s gs. h (s with vs_gas_readings := gs) =
      (h s with vs_gas_readings := gs)) /\
    (!s. (h s).vs_gas_readings = s.vs_gas_readings) /\
    ^ru_success_contract N F G V ==>
    ^ru_success_contract N (\k s. F k (h s)) (\k s. G k (h s)) V
Proof
  simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!s. (!e. G N s <> Error e) ==> _`
    (qspec_then `h s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[]
QED

Theorem remove_unused_fuel_stable_preupdate:
  !F h. ^ru_fuel_stable F ==> ^ru_fuel_stable (\k s. F k (h s))
Proof
  simp_tac std_ss [BETA_THM] >> metis_tac[]
QED

Theorem remove_unused_error_contract_inst_idx:
  !N F G i. ^ru_error_contract N F G ==>
    ^ru_error_contract N (\k s. F k (s with vs_inst_idx := i))
      (\k s. G k (s with vs_inst_idx := i))
Proof
  rpt gen_tac >> strip_tac >>
  irule remove_unused_error_contract_preupdate >> simp[]
QED

Theorem remove_unused_success_contract_inst_idx:
  !N F G V i. ^ru_success_contract N F G V ==>
    ^ru_success_contract N (\k s. F k (s with vs_inst_idx := i))
      (\k s. G k (s with vs_inst_idx := i)) V
Proof
  rpt gen_tac >> strip_tac >>
  irule remove_unused_success_contract_preupdate >> simp[]
QED

Theorem remove_unused_fuel_stable_inst_idx:
  !F i. ^ru_fuel_stable F ==>
    ^ru_fuel_stable (\k s. F k (s with vs_inst_idx := i))
Proof
  metis_tac[remove_unused_fuel_stable_preupdate]
QED

Theorem remove_unused_terminator_error_contract:
  !N. ^ru_error_contract N
    (\k s. if s.vs_halted then Halt s else OK s)
    (\k s. if s.vs_halted then Halt s else OK s)
Proof
  simp_tac std_ss [BETA_THM] >> rpt gen_tac >>
  Cases_on `s.vs_halted` >> simp[]
QED

Theorem remove_unused_terminator_success_contract:
  !N V. ^ru_success_contract N
    (\k s. if s.vs_halted then Halt s else OK s)
    (\k s. if s.vs_halted then Halt s else OK s) V
Proof
  simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >>
  qexists_tac `s.vs_gas_readings` >>
  Cases_on `s.vs_halted` >>
  simp[lift_result_def, stateEquivPropsTheory.state_equiv_refl,
       stateEquivPropsTheory.execution_equiv_refl]
QED

Theorem remove_unused_terminator_fuel_stable:
  ^ru_fuel_stable (\k s. if s.vs_halted then Halt s else OK s)
Proof
  simp_tac std_ss [BETA_THM]
QED

Theorem remove_unused_exec_block_context_reconstruction:
  !N ctx ctx' bb V.
    (!inst. MEM inst bb.bb_instructions ==>
      ^ru_error_contract N (\k s. step_inst k ctx inst s)
        (\k s. step_inst k ctx' inst s) /\
      ^ru_success_contract N (\k s. step_inst k ctx inst s)
        (\k s. step_inst k ctx' inst s) V) ==>
    !i.
      ^ru_error_contract N (\k s. exec_block k ctx bb (s with vs_inst_idx := i))
        (\k s. exec_block k ctx' bb (s with vs_inst_idx := i)) /\
      ^ru_success_contract N (\k s. exec_block k ctx bb (s with vs_inst_idx := i))
        (\k s. exec_block k ctx' bb (s with vs_inst_idx := i)) V
Proof
  rpt gen_tac >> strip_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - i` >>
  Cases_on `get_instruction bb i`
  >- (simp_tac std_ss [BETA_THM] >> conj_tac
      >- (rpt strip_tac >> qexists_tac `[]` >> simp[Once exec_block_def]) >>
      gen_tac >> simp[Once exec_block_def]) >>
  rename1 `get_instruction bb i = SOME inst` >>
  `MEM inst bb.bb_instructions /\ i < LENGTH bb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def, EL_MEM] >>
  qpat_x_assum `!inst. MEM inst _ ==> _` (qspec_then `inst` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qabbrev_tac `P = (\k s. step_inst k ctx inst (s with vs_inst_idx := i))` >>
  qabbrev_tac `Q = (\k s. step_inst k ctx' inst (s with vs_inst_idx := i))` >>
  qabbrev_tac `C = (\k s. if is_terminator inst.inst_opcode then
    (if s.vs_halted then Halt s else OK s)
    else exec_block k ctx bb (s with vs_inst_idx := SUC i))` >>
  qabbrev_tac `D = (\k s. if is_terminator inst.inst_opcode then
    (if s.vs_halted then Halt s else OK s)
    else exec_block k ctx' bb (s with vs_inst_idx := SUC i))` >>
  `^ru_error_contract N P Q` by
    (unabbrev_all_tac >> ho_match_mp_tac remove_unused_error_contract_inst_idx >> fs[]) >>
  `^ru_success_contract N P Q V` by
    (unabbrev_all_tac >> ho_match_mp_tac remove_unused_success_contract_inst_idx >> fs[]) >>
  `^ru_error_contract N C D /\ ^ru_success_contract N C D V` by
    (qspec_then `N` assume_tac remove_unused_terminator_error_contract >>
     qspecl_then [`N`, `V`] assume_tac remove_unused_terminator_success_contract >>
     Cases_on `is_terminator inst.inst_opcode` >> fs[Abbr `C`, Abbr `D`]) >>
  qpat_x_assum `^ru_error_contract N (\k s. step_inst k ctx inst s) _` kall_tac >>
  qpat_x_assum `^ru_success_contract N (\k s. step_inst k ctx inst s) _ _` kall_tac >>
  qpat_x_assum `^ru_error_contract N (\k s. exec_block k ctx bb (s with vs_inst_idx := SUC i)) _` kall_tac >>
  qpat_x_assum `^ru_success_contract N (\k s. exec_block k ctx bb (s with vs_inst_idx := SUC i)) _ _` kall_tac >>
  `^ru_fuel_stable P /\ ^ru_fuel_stable Q /\
   ^ru_fuel_stable C /\ ^ru_fuel_stable D` by
    (unabbrev_all_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac std_ss [BETA_THM] >> rpt conj_tac >> rpt strip_tac >>
     metis_tac[cj 1 venomExecPropsTheory.fuel_mono,
               cj 2 venomExecPropsTheory.fuel_mono]) >>
  `!s. ~(?e. Q N s = Error e) ==> ?n. gas_replay_at n (Q N) s /\
    !hs k. k <= N ==>
      ((?e. Q k (s with vs_gas_readings :=
        gas_prefix n s.vs_gas_readings ++ hs) = Error e) <=>
       (?e. Q k s = Error e))` by suspend "prefix_replay" >>
  `(!k s. exec_block k ctx bb (s with vs_inst_idx := i) =
      gas_bind_ok (P k s) (C k)) /\
   (!k s. exec_block k ctx' bb (s with vs_inst_idx := i) =
      gas_bind_ok (Q k s) (D k))` by
    (unabbrev_all_tac >> conj_tac >> rpt gen_tac >>
     simp[Once exec_block_def] >>
     Cases_on `step_inst k ctx inst (s with vs_inst_idx := i)` >>
     simp[gas_bind_ok_def]) >>
  qpat_x_assum `MEM _ _` kall_tac >>
  qpat_x_assum `i < _` kall_tac >>
  asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac remove_unused_bind_context_error_reconstruction >>
      qexists_tac `V` >> fs[] >> metis_tac[]) >>
  ho_match_mp_tac remove_unused_bind_context_success_reconstruction >> fs[]
QED


Resume remove_unused_exec_block_context_reconstruction[prefix_replay]:
  rpt (qpat_x_assum `^ru_error_contract _ _ _` kall_tac) >>
  rpt (qpat_x_assum `^ru_success_contract _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `^ru_fuel_stable _` kall_tac) >>
  simp[Abbr `Q`] >> gen_tac >> strip_tac >>
  qspec_then `N` (qspec_then `ctx'` (qspec_then `inst`
    (qspec_then `s with vs_inst_idx := i` mp_tac)))
      remove_unused_step_successful_replay_count >>
  simp[] >> strip_tac >>
  qexists_tac `gas_count_step N ctx' inst (s with vs_inst_idx := i)` >>
  conj_tac
  >- (irule remove_unused_replay_count_preupdate >> simp[]) >>
  drule remove_unused_step_replay_threshold >> simp[]
QED

Finalise remove_unused_exec_block_context_reconstruction

Theorem remove_unused_run_block_context_reconstruction:
  !N ctx ctx' bb V.
    (!inst. MEM inst bb.bb_instructions ==>
      ^ru_error_contract N (\k s. step_inst k ctx inst s)
        (\k s. step_inst k ctx' inst s) /\
      ^ru_success_contract N (\k s. step_inst k ctx inst s)
        (\k s. step_inst k ctx' inst s) V) ==>
    ^ru_error_contract N (\k s. run_block k ctx bb s)
      (\k s. run_block k ctx' bb s) /\
    ^ru_success_contract N (\k s. run_block k ctx bb s)
      (\k s. run_block k ctx' bb s) V
Proof
  rpt gen_tac >> strip_tac >>
  drule remove_unused_exec_block_context_reconstruction >>
  disch_then (qspec_then `phi_prefix_length bb.bb_instructions` strip_assume_tac) >>
  qpat_x_assum `!inst. _` kall_tac >>
  fs[] >> simp_tac std_ss [BETA_THM] >>
  conj_tac >- suspend "error" >> suspend "success"
QED

Resume remove_unused_run_block_context_reconstruction[error]:
  gen_tac >> strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      drule remove_unused_phi_replay_ok >> strip_tac >>
      qpat_x_assum `!s. (?e. exec_block _ _ _ _ = Error e) ==> _`
        (qspec_then `sp` mp_tac) >>
      gvs[run_block_def] >>
      disch_then (qx_choose_then `gs` strip_assume_tac) >>
      qexists_tac `gs` >> simp[run_block_def]) >>
  qexists_tac `s.vs_gas_readings` >> gvs[run_block_def]
QED

Resume remove_unused_run_block_context_reconstruction[success]:
  gen_tac >> strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      drule remove_unused_phi_replay_ok >> strip_tac >>
      qpat_x_assum `!s. (!e. exec_block _ _ _ _ <> Error e) ==> _`
        (qspec_then `sp` mp_tac) >>
      gvs[run_block_def] >>
      disch_then (qx_choose_then `gs` strip_assume_tac) >>
      qexists_tac `gs` >> simp[run_block_def]) >>
  gvs[run_block_def]
QED

Finalise remove_unused_run_block_context_reconstruction

Theorem remove_unused_runner_continuation_contracts:
  !N ctx ctx' fn V.
    ^ru_error_contract N (\k s. run_blocks k ctx fn s)
      (\k s. run_blocks k ctx' fn s) /\
    ^ru_success_contract N (\k s. run_blocks k ctx fn s)
      (\k s. run_blocks k ctx' fn s) V ==>
    ^ru_error_contract N
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx fn s)
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx' fn s) /\
    ^ru_success_contract N
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx fn s)
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx' fn s) V
Proof
  simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (gen_tac >> Cases_on `s.vs_halted` >> simp[] >> strip_tac >>
      qpat_x_assum `!s. (?e. run_blocks _ _ _ _ = Error e) ==> _` drule >>
      disch_then (qx_choose_then `gs` strip_assume_tac) >>
      qexists_tac `gs` >> simp[]) >>
  gen_tac >> Cases_on `s.vs_halted`
  >- (simp[] >> qexists_tac `s.vs_gas_readings` >>
      simp[lift_result_def, stateEquivPropsTheory.execution_equiv_refl]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!s. ~(?e. run_blocks _ _ _ _ = Error e) ==> _`
    (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[]
QED

val ru_runner_layer = ``\ctx fn bb k s.
  gas_bind_ok (run_block k ctx bb s)
    (\u. if u.vs_halted then Halt u else run_blocks k ctx fn u)``;

Theorem remove_unused_runner_layer_contracts:
  !N ctx ctx' fn bb V.
    ^ru_error_contract N (\k s. run_block k ctx bb s) (\k s. run_block k ctx' bb s) /\
    ^ru_success_contract N (\k s. run_block k ctx bb s) (\k s. run_block k ctx' bb s) V /\
    ^ru_error_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) /\
    ^ru_success_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) V ==>
    ^ru_error_contract N (^ru_runner_layer ctx fn bb) (^ru_runner_layer ctx' fn bb) /\
    ^ru_success_contract N (^ru_runner_layer ctx fn bb) (^ru_runner_layer ctx' fn bb) V
Proof
  rpt gen_tac >> strip_tac >>
  `^ru_error_contract N
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx fn s)
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx' fn s) /\
   ^ru_success_contract N
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx fn s)
      (\k s. if s.vs_halted then Halt s else run_blocks k ctx' fn s) V` by
    (irule remove_unused_runner_continuation_contracts >> simp[]) >>
  qpat_x_assum `^ru_error_contract N (\k s. run_blocks k ctx fn s) _` kall_tac >>
  qpat_x_assum `^ru_success_contract N (\k s. run_blocks k ctx fn s) _ _` kall_tac >>
  `!s. ~(?e. run_block N ctx' bb s = Error e) ==>
    ?n. gas_replay_at n (run_block N ctx' bb) s /\
      !hs k. k <= N ==>
        ((?e. run_block k ctx' bb (s with vs_gas_readings :=
          gas_prefix n s.vs_gas_readings ++ hs) = Error e) <=>
         (?e. run_block k ctx' bb s = Error e))` by suspend "replay" >>
  `^ru_fuel_stable (\k s. run_block k ctx bb s) /\
   ^ru_fuel_stable (\k s. run_block k ctx' bb s) /\
   ^ru_fuel_stable (\k s. if s.vs_halted then Halt s else run_blocks k ctx fn s) /\
   ^ru_fuel_stable (\k s. if s.vs_halted then Halt s else run_blocks k ctx' fn s)` by
    (POP_ASSUM_LIST (K all_tac) >> simp_tac std_ss [BETA_THM] >>
     rpt conj_tac >> rpt strip_tac >>
     metis_tac[venomExecPropsTheory.run_block_fuel_mono,
               cj 3 venomExecPropsTheory.fuel_mono]) >>
  qabbrev_tac `P = (\k s. run_block k ctx bb s)` >>
  qabbrev_tac `Q = (\k s. run_block k ctx' bb s)` >>
  qabbrev_tac `C = (\k s. if s.vs_halted then Halt s else run_blocks k ctx fn s)` >>
  qabbrev_tac `D = (\k s. if s.vs_halted then Halt s else run_blocks k ctx' fn s)` >>
  qsuff_tac `^ru_error_contract N (\k s. gas_bind_ok (P k s) (C k))
      (\k s. gas_bind_ok (Q k s) (D k)) /\
    ^ru_success_contract N (\k s. gas_bind_ok (P k s) (C k))
      (\k s. gas_bind_ok (Q k s) (D k)) V`
  >- simp[Abbr `P`, Abbr `Q`, Abbr `C`, Abbr `D`] >>
  simp_tac std_ss [BETA_THM] >> conj_tac
  >- (ho_match_mp_tac (SIMP_RULE std_ss [BETA_THM] remove_unused_bind_context_error_reconstruction) >>
      qexists_tac `V` >> fs[Abbr `P`, Abbr `Q`, Abbr `C`, Abbr `D`] >> metis_tac[]) >>
  ho_match_mp_tac (SIMP_RULE std_ss [BETA_THM] remove_unused_bind_context_success_reconstruction) >>
  fs[Abbr `P`, Abbr `Q`, Abbr `C`, Abbr `D`] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> metis_tac[]
QED

Resume remove_unused_runner_layer_contracts[replay]:
  POP_ASSUM_LIST (K all_tac) >> gen_tac >> strip_tac >>
  `?n. gas_replay_at n (run_block N ctx' bb) s` by
    (rewrite_tac[GSYM gas_replay_def] >> irule gas_run_block >>
     metis_tac[cj 3 gas_replay_fuel]) >>
  qexists_tac `n` >> simp[] >>
  drule remove_unused_run_block_replay_threshold >> simp[] >> metis_tac[]
QED

Finalise remove_unused_runner_layer_contracts

Theorem remove_unused_runner_layer_unfold[local]:
  run_blocks (SUC n) ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb => ^ru_runner_layer ctx fn bb n s
Proof
  simp[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  Cases_on `run_block n ctx x s` >> simp[gas_bind_ok_def]
QED

Theorem remove_unused_runner_context_contracts:
  !N ctx ctx' fn V.
    (!m bb. m < N /\ MEM bb fn.fn_blocks ==>
      ^ru_error_contract m (\k s. run_block k ctx bb s) (\k s. run_block k ctx' bb s) /\
      ^ru_success_contract m (\k s. run_block k ctx bb s) (\k s. run_block k ctx' bb s) V) ==>
    ^ru_error_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) /\
    ^ru_success_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) V
Proof
  Induct_on `N`
  >- (simp_tac std_ss [BETA_THM] >> rpt gen_tac >> strip_tac >>
      simp[Once run_blocks_def] >> gen_tac >>
      qexists_tac `[]` >> simp[Once run_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  `^ru_error_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) /\
   ^ru_success_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) V` by
    (first_x_assum irule >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!m bb. _` (qspecl_then [`m`,`bb`] mp_tac) >> simp[]) >>
  `!bb. MEM bb fn.fn_blocks ==>
    ^ru_error_contract N (^ru_runner_layer ctx fn bb) (^ru_runner_layer ctx' fn bb) /\
    ^ru_success_contract N (^ru_runner_layer ctx fn bb) (^ru_runner_layer ctx' fn bb) V` by
    (gen_tac >> strip_tac >> irule remove_unused_runner_layer_contracts >> simp[] >>
     qpat_x_assum `!m bb. _` (qspecl_then [`N`,`bb`] mp_tac) >> simp[]) >>
  qpat_x_assum `!m bb. _` kall_tac >>
  qpat_x_assum `!ctx ctx' fn V. _` kall_tac >>
  simp_tac std_ss [BETA_THM] >> conj_tac
  >- suspend "error" >>
  suspend "success"
QED

Resume remove_unused_runner_context_contracts[error]:
  gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qexists_tac `[]` >> simp[remove_unused_runner_layer_unfold]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >> simp[] >>
  simp_tac std_ss [BETA_THM] >> strip_tac >>
  qpat_x_assum `run_blocks (SUC N) ctx' fn s = Error e` mp_tac >>
  simp[remove_unused_runner_layer_unfold] >> strip_tac >>
  qpat_x_assum `!s. (?e. gas_bind_ok _ _ = Error e) ==> _` drule >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[remove_unused_runner_layer_unfold]
QED

Resume remove_unused_runner_context_contracts[success]:
  gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- gvs[remove_unused_runner_layer_unfold] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >> simp[] >>
  simp_tac std_ss [BETA_THM] >> strip_tac >>
  `~(?e. ^ru_runner_layer ctx' fn bb N s = Error e)` by
    (gvs[remove_unused_runner_layer_unfold]) >> fs[] >>
  qpat_x_assum `!s. (!e. gas_bind_ok _ _ <> Error e) ==> _`
    (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gs`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  qexists_tac `gs` >> simp[] >> conj_tac
  >- suspend "terminal" >>
  rpt strip_tac >> Cases_on `k`
  >- simp[Once run_blocks_def] >>
  rename1 `SUC j <= SUC N` >>
  qpat_x_assum `!k. k <= N /\ _ ==> _` (qspec_then `j` mp_tac) >>
  gvs[remove_unused_runner_layer_unfold] >> metis_tac[]
QED

Resume remove_unused_runner_context_contracts[terminal]:
  qpat_x_assum `(!k. ?e. gas_bind_ok _ _ = Error e) \/ _`
    (DISJ_CASES_THEN assume_tac)
  >- (disj1_tac >> gen_tac >> Cases_on `k`
      >- simp[Once run_blocks_def] >>
      simp[remove_unused_runner_layer_unfold]) >>
  disj2_tac >> simp[remove_unused_runner_layer_unfold]
QED

Finalise remove_unused_runner_context_contracts

Theorem remove_unused_runner_context_bounded_errors:
  !N ctx ctx' fn V s.
    (!m bb. m < N /\ MEM bb fn.fn_blocks ==>
      ^ru_error_contract m (\k s. run_block k ctx bb s) (\k s. run_block k ctx' bb s) /\
      ^ru_success_contract m (\k s. run_block k ctx bb s) (\k s. run_block k ctx' bb s) V) /\
    (!k. k <= N ==> ?e. run_blocks k ctx' fn s = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) s.vs_gas_readings) /\
      !k. k <= N ==> ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >>
  drule remove_unused_runner_context_contracts >>
  simp_tac std_ss [BETA_THM] >> strip_tac >>
  `?e. run_blocks N ctx' fn s = Error e` by
    (qpat_x_assum `!k. k <= N ==> _` (qspec_then `N` mp_tac) >> simp[]) >>
  qpat_x_assum `!s. (?e. run_blocks N ctx' fn s = Error e) ==> _`
    (qspec_then `s` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  `run_blocks N ctx fn (s with vs_gas_readings := gs) =
   run_blocks k ctx fn (s with vs_gas_readings := gs)` by
    (irule (cj 3 venomExecPropsTheory.fuel_mono) >> simp[] >>
     qexists_tac `k` >> simp[]) >>
  gvs[]
QED

Theorem remove_unused_runner_from_callee_contracts:
  !N ctx ctx' fn V.
    ^ru_context_compat /\
    (!m. m < N ==> (\N. ^ru_callee_error) m /\ (\N. ^ru_callee_success) m) ==>
    ^ru_error_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) /\
    ^ru_success_contract N (\k s. run_blocks k ctx fn s) (\k s. run_blocks k ctx' fn s) V
Proof
  rpt gen_tac >> strip_tac >> irule remove_unused_runner_context_contracts >>
  rpt gen_tac >> strip_tac >> irule remove_unused_run_block_context_reconstruction >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `m` mp_tac) >> simp[] >>
  simp_tac std_ss [BETA_THM] >> strip_tac >> conj_tac
  >- (ho_match_mp_tac remove_unused_step_context_error_reconstruction >>
      qexists_tac `V` >> fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ho_match_mp_tac (SRULE [] remove_unused_step_context_success_reconstruction) >>
  fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
