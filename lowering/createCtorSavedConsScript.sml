(* A saved head is transported across the actual successful suffix. *)
Theory createCtorSavedCons
Ancestors
  bodyFullExtCallPosList bodyFullExtCallPosTransport bodyFullExtCallPosAggregate
  bodyInvCodeProps targetPureWalkSource vyperMachineFrame exprSimWordArgs
  allocaSiteResource freshWrites vyperStorageFootprint vyperStorageTrace
  exprLoweringProps wordArgsPtr stateRelProj list exprSimProps
  loweringPosts compileEnv vyperInterpreter vyperState exprSimMemDefs bodyPtrDefs
  exprLowering venomState loweringStateRelDefs context bodyFullExtCallSavedOperand
  ptrDiscipline exprSimUnwrap

(* Positional success is independent of the unused exception tag type. *)
Theorem extcall_positional_post_INL:
  extcall_positional_post p DF lo d ctx func ce cx env kw xs svs
    sa sb es s g h H (INL vs : value list + 'a) ee G tn t <=>
  extcall_positional_post p DF lo d ctx func ce cx env kw xs svs
    sa sb es s g h H (INL vs : value list + exception) ee G tn t
Proof
  simp[extcall_positional_post_def]
QED

Theorem extcall_saved_rows_cons:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv cut /\
  ci_mono sa cut /\ ci_mono cut sb /\ u.vs_labels = t.vs_labels /\
  (!K. dead_lo_ok K (DF K) lo cenv cx) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs xs) /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := out) /\
  (!K. valid_horizon cx st0 K es.storage_trace ==>
       stmt_state_rel K ctx func cenv cx es s0) /\
  (!K. valid_horizon cx st0 K mid.storage_trace ==>
       valid_horizon cx st0 K es.storage_trace) /\
  (!K. valid_horizon cx st0 K mid.storage_trace ==>
       extcall_positional_post keep_pure DF lo d ctx func cenv cx env
         (xs ++ kw) [e] [sv] sa cut es s0 G0 tn0 K (INL [v]) mid G1 tn1 t) /\
  (!K. valid_horizon cx st0 K ee.storage_trace ==>
       extcall_positional_post keep_pure DF lo d ctx func cenv cx env
         kw xs svs cut sb mid t G1 tn1 K (INL vs) ee G2 tn2 u) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  extcall_positional_post keep_pure DF lo d ctx func cenv cx env
    kw (e::xs) (sv::svs) sa sb es s0 G0 tn0 H (INL (v::vs)) ee G2 tn2 u
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_exprs _ _ _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
     simp[cj 6 evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by simp[] >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
              SIMP_RULE (srw_ss()) [extcall_positional_post_def]) >>
  qpat_x_assum `!K. _ ==> extcall_positional_post _ _ _ _ _ _ _ _ _ _ [e] _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
              SIMP_RULE (srw_ss()) [extcall_positional_post_def]) >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee cut t u` (irule_at Any) >>
     simp[ci_mono_def] >> fs[ci_mono_def]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid cut G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     simp[] >> fs[ci_mono_def]) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=>
             local_region cenv ee.scopes u n b sz` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx mid t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee cut t u` (irule_at Any) >> simp[]) >>
  `alloca_inv t /\ alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid t`
        (mp_then Any assume_tac stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
        (mp_then Any assume_tac stmt_state_rel_local_ptrs_alloca) >> fs[]) >>
  qpat_x_assum `?si sm ss vv raw copy. compile_expr _ _ _ _ = _ /\ _`
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`]
      (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `~copy ==> ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
            !tr. get_storage cx ee tr = get_storage cx mid tr` by
    (strip_tac >> `~exprs_can_mutate cenv xs` by fs[exprs_can_mutate_append] >>
     drule_all nonmutating_exprs_source_frame >>
     simp[machine_frame_def] >> strip_tac >> gen_tac >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) t` by
    (`?w. eval_operand (vv_operand sv) t = SOME w` by
       (Cases_on `sv` >> fs[vv_operand_def, vv_holds_def, expr_val_rel_def]) >>
     Cases_on `vv_operand sv` >> fs[eval_operand_def]) >>
  `(?r. read_result cx r ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) r sv ee u /\
        vv_at cenv cx (lowered_value_type cenv e) si ss ee r sv u /\
        ptr_vv_ok cx (lowered_value_type cenv e) r sv ee G2 tn2 u /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
          ee r sv u) /\
   vv_storage_live H cx sv ee u /\
   (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
             ptr_buf_ok cenv e op G2 u) /\
   (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv e p.ptr_operand G2 u) /\
   (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand sv) u = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            !mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
                  val_in_memory rt v (w2n w) mem)` by (suspend "head") >>
  simp[extcall_positional_post_def] >> rpt conj_tac
  >- suspend "row"
  >- (pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      qpat_assum `cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==> !rt w. _ ==> _ /\ _`
        (ACCEPT_TAC o cj 1))
  >- suspend "tail"
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `cut` >> fs[ci_mono_def])
  >- suspend "pure"
  >- suspend "vars"
  >> metis_tac[]
QED

Resume extcall_saved_rows_cons[head]:
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
      lowered_value_type cenv e` by drule_all_then ACCEPT_TAC extcall_operand_snapshot_type >>
  `si.cs_next_var <= ss.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    (drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
     `ci_mono sm ss` by
       (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`]
          mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
     fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    (rpt strip_tac >> irule extcall_saved_operand_not_fresh >>
     qpat_assum `compile_expr _ _ _ si = _` (irule_at Any) >>
     qpat_assum `compile_snapshot_vv _ _ _ sm = _` (irule_at Any) >> simp[]) >>
  `!x. not_fresh_at ss x ==> not_fresh_at cut x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `wb_frame cenv mid ee ss t u /\ ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2 /\
   (!x w. not_fresh_at ss x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w)` by
     (rpt conj_tac
      >- (qpat_assum `wb_frame cenv mid ee cut t u`
            (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
          rewrite_tac[wb_frame_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (rpt strip_tac >> rename1 `lookup_var x u = SOME w` >>
              `not_fresh_at cut x` by simp[] >> simp[]) >>
          qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
          `aid < cut.cs_next_id` by decide_tac >>
          qpat_assum `!aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[])
      >- (qpat_assum `ghost_kept_at lo cenv mid cut G1 tn1 t G2 tn2`
            (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
          rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- (qx_gen_tac `x` >> strip_tac >> `not_fresh_at cut x` by simp[] >> simp[]) >>
          qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
          `aid < cut.cs_next_id` by decide_tac >>
          qpat_assum `!aid off sz i. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
      rpt strip_tac >> rename1 `lookup_var x u = SOME w` >>
      `not_fresh_at cut x` by simp[] >> simp[]) >>
  namedCases_on `sv` ["tag op", "tag p"]
  >- suspend "stack"
  >> `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `(?tag' op0. LocatedValue tag p = StackValue tag' op0) \/ _`
       mp_tac >> simp[NoAsms] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `copy` >- suspend "copy" >> suspend "retain_memory") >>
  `~copy` by
    (Cases_on `copy` >> fs[vv_location_def]) >>
  Cases_on `?tr. p.ptr_location = slot_loc tr`
  >- suspend "slot"
  >> Cases_on `p.ptr_location = LocCode`
  >- suspend "code"
  >> `p.ptr_location = LocCalldata` by (Cases_on `p.ptr_location` >> fs[] >> metis_tac[slot_loc_def]) >>
  fs[vv_holds_def]
QED
Resume extcall_saved_rows_cons[stack]:
  simp[vv_location_def, vv_storage_live_def] >>
  irule extcall_request_saved_stack_endpoint >>
  simp[] >> qexistsl_tac [`G1`,`func`,`lo`,`mid`,`ss`,`t`,`tn1`] >>
  fs[vv_operand_def, ci_mono_refl] >> conj_tac
  >- (qexists_tac `raw` >> simp[]) >>
  Cases_on `is_word_type (lowered_value_type cenv e)` >> simp[] >>
  `~copy` by (Cases_on `copy` >> fs[vv_location_def]) >>
  disj2_tac >> qexistsl_tac [`env`,`H`,`H`,`ctx`] >> simp[]
QED
Resume extcall_saved_rows_cons[copy]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qpat_assum `_ ==> ?x w tv. vv_location (LocatedValue _ p) = SOME LocMemory /\ _`
    (mp_tac o REWRITE_RULE [vv_location_def, vv_operand_def]) >>
  (impl_tac >- simp[]) >>
  disch_then (REPEAT_TCL CHOOSE_THEN strip_assume_tac) >>
  rename [`p.ptr_operand = Var x`, `eval_operand p.ptr_operand t = SOME w`,
          `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv`] >>
  `ptr_val_ok cx (lowered_value_type cenv e) v (Var x) G1 tn1 t /\
   val_in_memory tv v (w2n w) t.vs_memory` by
    gvs[vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  `lookup_var x t = SOME w` by
    (qpat_assum `p.ptr_operand = Var x` (fn eq =>
       qpat_assum `eval_operand p.ptr_operand t = SOME w`
         (ACCEPT_TAC o REWRITE_RULE [eq, venomStateTheory.eval_operand_def]))) >>
  `w2n w + type_memory_size tv <= t.vs_alloca_next` by
    (irule alloca_site_registered_below >> simp[] >> qexists_tac `sm.cs_next_id` >> simp[]) >>
  `ptr_buf_ok cenv e (Var x) G1 t` by fs[] >>
  simp[vv_storage_live_def, vv_location_def] >>
  `read_result cx (Value v) ee = (INL v,ee) /\
   vv_holds cenv cx (lowered_value_type cenv e) (Value v)
     (LocatedValue (lowered_value_type cenv e) p) ee u /\
   vv_at cenv cx (lowered_value_type cenv e) si ss ee (Value v)
     (LocatedValue (lowered_value_type cenv e) p) u /\
   ptr_vv_ok cx (lowered_value_type cenv e) (Value v)
     (LocatedValue (lowered_value_type cenv e) p) ee G2 tn2 u /\
   vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
     ee (Value v) (LocatedValue (lowered_value_type cenv e) p) u /\
   ptr_buf_ok cenv e (Var x) G2 u` by
    (irule extcall_request_materialized_endpoint >>
     qpat_assum `compile_snapshot_vv cenv T _ sm = _` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee ss t u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv)`
       (irule_at Any) >>
     simp[vv_operand_def, exprSimPropsTheory.val_footprint_le, regions_disjoint_def] >>
     fs[vv_operand_def, regions_disjoint_def] >> metis_tac[]) >>
  simp[] >> qexists_tac `Value v` >> simp[]
QED
Resume extcall_saved_rows_cons[retain_memory]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  simp[vv_location_def, vv_storage_live_def] >>
  irule extcall_request_saved_memory_endpoint >>
  simp[] >> qexistsl_tac [`G1`,`func`,`lo`,`mid`,`ss`,`t`,`tn1`] >>
  fs[vv_operand_def, ci_mono_refl] >> conj_tac
  >- (qexists_tac `raw` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`env`,`H`,`H`,`ctx`] >> simp[]
QED
Resume extcall_saved_rows_cons[slot]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qpat_x_assum `?tr. p.ptr_location = slot_loc tr` (qx_choose_then `tr` assume_tac) >>
  `slot_loc tr <> LocCode /\ slot_loc tr <> LocMemory` by
    (Cases_on `tr` >> simp[slot_loc_def]) >>
  simp[vv_location_def, Excl "vv_storage_live_def"] >>
  irule extcall_request_saved_slot_endpoint >>
  qpat_assum `stmt_state_rel H ctx func cenv cx ee u` (irule_at Any) >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
  qexists_tac `tr` >> simp[vv_operand_def, Excl "vv_storage_live_def"] >>
  qexists_tac `raw` >> simp[GSYM AND_IMP_INTRO] >> metis_tac[]
QED
Resume extcall_saved_rows_cons[code]:
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  simp[vv_location_def, vv_storage_live_def, vv_operand_def] >>
  conj_asm1_tac
  >- (irule (cj 1 extcall_request_saved_code_endpoint) >>
      qpat_assum `ghost_kept_at lo cenv mid ss G1 tn1 t G2 tn2` (irule_at Any) >>
      simp[vv_operand_def] >> qexists_tac `raw` >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand p.ptr_operand u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
                 val_in_memory rt v (w2n w) mem)` suffices_by
    (qpat_assum `eval_operand (vv_operand _) u = _` (fn eq =>
       pure_once_rewrite_tac[REWRITE_RULE [vv_operand_def] eq]) >> metis_tac[]) >>
  `dead_lo_ok H (DF H) lo cenv cx` by simp[] >>
  `ee.immutables = mid.immutables` by simp[] >>
  `?r. read_result cx r ee = (INL v,ee) /\
       vv_holds cenv cx (lowered_value_type cenv e) r
         (LocatedValue (lowered_value_type cenv e) p) ee u` by
    (qpat_assum `?r. read_result cx r ee = (INL v,ee) /\ _`
       (qx_choose_then `r` strip_assume_tac) >> qexists_tac `r` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:256``] extcall_request_saved_ctor_read) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx ee u` (irule_at Any) >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u` (irule_at Any) >>
  qpat_assum `body_inv tops ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx env mid` (irule_at Any) >>
  qpat_assum `eval_operand p.ptr_operand u = SOME _` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME _`
    (irule_at Any) >>
  simp[] >> qexists_tac `r` >> simp[]
QED
Resume extcall_saved_rows_cons[row]:
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`r`,`copy`] >> simp[] >>
  `sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
   ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id` by
     (fs[ci_mono_def] >> decide_tac) >>
  `~copy ==> ~exprs_can_mutate cenv kw` by
    (strip_tac >> qpat_assum `~copy ==> ~exprs_can_mutate cenv (xs ++ kw)`
       (drule_then (mp_tac o REWRITE_RULE [exprs_can_mutate_append])) >> simp[]) >>
  simp[expr_can_mutate_def] >> strip_tac >>
  qpat_assum `copy /\ _ ==> ?p w tv. _` mp_tac >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac) >>
  qexistsl_tac [`x`,`w`,`tv`] >> simp[] >> rpt strip_tac >>
  `local_region cenv mid.scopes t n b sz` by
    (qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz <=> _`
       (qspecl_then [`n`,`b`,`sz`] SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!n b sz. local_region cenv mid.scopes t n b sz ==> _`
    (drule_then ACCEPT_TAC)
QED
Resume extcall_saved_rows_cons[tail]:
  irule LIST_REL_mono >>
  qpat_assum `LIST_REL _ (ZIP (xs,svs)) vs` (irule_at Any) >>
  `!a. cut.cs_next_var <= a.cs_next_var /\ cut.cs_next_id <= a.cs_next_id ==>
       sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id` by
    (fs[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  pop_assum (fn bounds => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac bounds) >>
  Cases >> simp[] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2
    (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS))
    (K ALL_TAC)) >>
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`raw`,`copy`] >> simp[]
QED
Resume extcall_saved_rows_cons[pure]:
  strip_tac >> irule pure_frame_trans >> simp[] >>
  qexistsl_tac [`mid`,`cut`,`t`] >> fs[ci_mono_def] >> simp[EQ_SYM_EQ]
QED
Resume extcall_saved_rows_cons[vars]:
  rpt strip_tac >>
  rename1 `lookup_var x u = SOME w` >>
  `not_fresh_at cut x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `lookup_var x t = SOME w` by simp[] >> simp[]
QED
Finalise extcall_saved_rows_cons

Theorem ctor_saved_rows_cons =
  SIMP_RULE bool_ss [APPEND_NIL]
    (Q.INST [`keep_pure` |-> `T`, `kw` |-> `[]`] extcall_saved_rows_cons)
