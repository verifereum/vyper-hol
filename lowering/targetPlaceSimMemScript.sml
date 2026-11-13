(* Memory-counted place-target simulation: the gas_outcome T twin of
   targetPlaceSimDefs.target_sim, which also keeps the alloca history and
   the allocation frontier, as the memory expression simulations need at
   their entry. *)
Theory targetPlaceSimMem
Ancestors
  bodyMemoryPreds targetPlaceSimCases targetPlaceSim exprSimMemDefs
  allocaHistory exprSimDefs targetPlaceSimDefs gasContext gasOutcome gasSummary
  gasExemptCert stmtSimProps loweringPosts exprLowering compileEnv
  supportedTargets vyperAST vyperInterpreter vyperState vyperTypeSystem
  venomState
Libs
  pairLib

Definition target_sim_mem_def:
  target_sim_mem ctx func cenv cx env bt es <=>
    !vt sa sb op s0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es, s0)
        (\res ee t. ?pv. res = INL pv /\
          target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)
End

(* Held: the subscript case waits on S1's proved
   targetSubscriptSplit.target_subscript_main_case, which this base
   predates; the name, toplevel and attribute cases are in reach. *)
Theorem body_target_sim_mem:
  !t cx tops ctx func cenv env es.
    body_base_target_mem_ok cx t /\ body_inv tops ctx cenv cx /\
    target_pre cenv cx env t es ==>
    target_sim_mem ctx func cenv cx env t es
Proof
  cheat
QED

(* The judgment for eval_target_place: a target typed by a value type
   evaluates to a place, at the pointer. *)
Theorem target_place_sim_mem:
  !ctx func cenv cx env bt es ty sa sb r s0.
    target_sim_mem ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\
    alloca_history func s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx, func) (eval_target_place cx bt) (es, s0)
      (\res ee t. ?p. res = INL p /\
        target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty) r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  `eval_target_place cx bt = bind (eval_base_place cx bt) get_place` by (
    simp[Once evaluate_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  pop_assum (fn th =>
    qpat_x_assum `gas_admissible _ _ _`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
    pure_rewrite_tac [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by (
    qpat_x_assum `gas_admissible _ target_place_res_ok _` mp_tac >>
    rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
    first_x_assum (qspec_then `gs` mp_tac) >>
    Cases_on `res` >> simp[bind_def, target_res_ok_def] >>
    simp[target_place_res_ok_def]) >>
  qpat_x_assum `target_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_mem_def]) >>
  disch_then (qspecl_then [`Type ty`, `sa`, `sb`, `r`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def] >>
      disch_then (qx_choosel_then [`res`, `fin`, `rr`] strip_assume_tac) >>
      Cases_on `res` >> gvs[expr_exit_def]
      >- (rename1 `target_post _ _ _ _ _ _ _ _ _ pv` >>
          `?p. pv = PlaceR p` by (
            qpat_x_assum `gas_admissible _ target_place_res_ok _` mp_tac >>
            rewrite_tac[gas_admissible_def] >>
            disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings`
                          mp_tac) >>
            first_x_assum (qspec_then `[]` mp_tac) >>
            simp[bind_def] >> strip_tac >>
            Cases_on `pv` >>
            simp[get_place_def, raise_def, target_place_res_ok_def]) >>
          gvs[] >> qexistsl_tac [`INL p`, `fin`, `OK t`] >>
          simp[bind_def, get_place_def, return_def]) >>
      rename1 `expr_exit (INR exc) rr` >>
      qexistsl_tac [`INR exc`, `fin`, `rr`] >> simp[bind_def] >>
      metis_tac[expr_exit_INR_type]) >>
  disj2_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_result)
QED

(* What a pure target (supported_target_pure) keeps: every live local's
   region whole, dynamic-array length words included (locals_kept exempts
   them), storage, transient storage, and the constructor's staged
   immutables.  Its scratch ALLOCAs can be reused in a loop, so the bytes
   below the frontier are not all kept, only these. *)
Definition target_pure_frame_def:
  target_pure_frame cenv cx (es : evaluation_state) (s0 : venom_state)
    (t : venom_state) <=>
    (!n b sz. local_region cenv es.scopes s0 n b sz ==>
              mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s0.vs_memory) /\
    contract_storage t = contract_storage s0 /\
    contract_transient t = contract_transient s0 /\
    (!name off itv iv.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module, name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables cenv.ce_module imms)
               name = SOME (itv, iv) ==>
       mem_bytes_at off (type_memory_size itv) t.vs_memory =
         mem_bytes_at off (type_memory_size itv) s0.vs_memory)
End

(* target_sim_mem with the pure-target frame on success. *)
Definition target_sim_mem_pure_def:
  target_sim_mem_pure ctx func cenv cx env bt es <=>
    !vt sa sb op s0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\
      alloca_history func s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome T (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es, s0)
        (\res ee t. ?pv. res = INL pv /\
          target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          target_pure_frame cenv cx es s0 t)
        (\res ee r. expr_exit res r)
End

(* Held with body_target_sim_mem: the subscript case waits on the same
   S1 target_subscript_main_case. *)
Theorem body_target_sim_mem_pure:
  !t cx tops ctx func cenv env es.
    supported_target_pure tops t /\
    body_base_target_mem_ok cx t /\ body_inv tops ctx cenv cx /\
    target_pre cenv cx env t es ==>
    target_sim_mem_pure ctx func cenv cx env t es
Proof
  cheat
QED

Theorem target_place_sim_mem_pure:
  !ctx func cenv cx env bt es ty sa sb r s0.
    target_sim_mem_pure ctx func cenv cx env bt es /\
    type_place_target env bt = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\
    alloca_history func s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx, func) (eval_target_place cx bt) (es, s0)
      (\res ee t. ?p. res = INL p /\
        target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty) r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        target_pure_frame cenv cx es s0 t)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  `eval_target_place cx bt = bind (eval_base_place cx bt) get_place` by (
    simp[Once evaluate_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC) >>
  pop_assum (fn th =>
    qpat_x_assum `gas_admissible _ _ _`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
    pure_rewrite_tac [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by (
    qpat_x_assum `gas_admissible _ target_place_res_ok _` mp_tac >>
    rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
    first_x_assum (qspec_then `gs` mp_tac) >>
    Cases_on `res` >> simp[bind_def, target_res_ok_def] >>
    simp[target_place_res_ok_def]) >>
  qpat_x_assum `target_sim_mem_pure _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_mem_pure_def]) >>
  disch_then (qspecl_then [`Type ty`, `sa`, `sb`, `r`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def] >>
      disch_then (qx_choosel_then [`res`, `fin`, `rr`] strip_assume_tac) >>
      Cases_on `res` >> gvs[expr_exit_def]
      >- (rename1 `target_post _ _ _ _ _ _ _ _ _ pv` >>
          `?p. pv = PlaceR p` by (
            qpat_x_assum `gas_admissible _ target_place_res_ok _` mp_tac >>
            rewrite_tac[gas_admissible_def] >>
            disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings`
                          mp_tac) >>
            first_x_assum (qspec_then `[]` mp_tac) >>
            simp[bind_def] >> strip_tac >>
            Cases_on `pv` >>
            simp[get_place_def, raise_def, target_place_res_ok_def]) >>
          gvs[] >> qexistsl_tac [`INL p`, `fin`, `OK t`] >>
          simp[bind_def, get_place_def, return_def]) >>
      rename1 `expr_exit (INR exc) rr` >>
      qexistsl_tac [`INR exc`, `fin`, `rr`] >> simp[bind_def] >>
      metis_tac[expr_exit_INR_type]) >>
  disj2_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_result)
QED
