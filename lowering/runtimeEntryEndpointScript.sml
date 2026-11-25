(*
 * The state where the runtime entry hands over to an external body, on
 * finite horizons: the conclusion of externalEntryJoint's
 * external_entry_subst_consts_joint, with the body placed either among the selected
 * external packages or at the __default__ fallback.  The body's joint
 * proof (loweringRuntimeCorrect's runtime_body_joint_from_start) starts
 * from it, so every entry that reaches it (canonical, any dispatched
 * encoding, the fallback) shares that proof.
 *
 * TOP-LEVEL:
 *   runtime_entry_endpoint_def
 *   external_entry_joint_endpoint -- the canonical entry reaches it
 *)
Theory runtimeEntryEndpoint
Ancestors
  externalEntryJoint runtimeBodyStartDefs entryDispatchProps constSubst
  externalEntryBound bodySim exprSimHypsDefs stmtSimDefs vyperTypeCallGraph
  gasShadowRunLowering gasShadowUnit gasShadowState gasShadow gasSummary

Definition runtime_entry_endpoint_def:
  runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody <=>
    ?lbl cenv_ext cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
       s0 G0 tn0.
        set_external_package_target rpolicy.rpol_target
          (package_external_fn tops T (K global_nonreentrant_slot)
             (mut, F, lookup_raw_return_or_F (NONE : num option)
                         tx.function_name External tops,
              tx.function_name, args, ([] : expr list), ret, fbody)) =
          (lbl, cenv_ext, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
           rt) /\
        ((cenv0 = cenv_ext /\
          runtime_selected_body_start tops rpolicy
            (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt)
            st) \/
         (tx.function_name = "__default__" /\ args = [] /\
          pos_args = [] /\ min_cds = 4 /\
          cenv_ext =
            (if ret <> NoneT then update_cenv_ret_abi cenv0 ret else cenv0) /\
          runtime_fallback_body_start tops rpolicy
            (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt)
            st)) /\
        compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
        compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
        fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        unit.cu_context.ctx_entry = SOME "__entry" /\
        lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
        fn_entry_label func = SOME "__entry" /\
        gas_path unit.cu_context func
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>) 0 (OK s0) /\
        gas_path_mem unit.cu_context func
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>) 0 (OK s0) /\
        alloca_history func s0 /\
        return_buf_frame NONE cenv sa s0 /\
        ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
        s0.vs_gas_readings = vs.vs_gas_readings /\
        s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
        (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                  (!e. r <> Error e) ==>
                  ?fuel'. run_context fuel' unit.cu_context vs = r) /\
        !st0 H.
          valid_horizon
            (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
            es0.storage_trace ==>
          ((!fuel. ptr_safe_run
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
              0 fuel unit.cu_context func [] G0 tn0 s0) ==>
            !fuel. ptr_safe_blocks
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
              0 fuel unit.cu_context func [] FEMPTY entry_taint
              (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                          vs_inst_idx := 0 |>)) /\
          ghost_inv_at
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 NONE cenv
            (initial_evaluation_context am.sources am.layouts tx NONE) es0
            G0 tn0 s0 /\
          stmt_state_rel H unit.cu_context func cenv
            (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
          !explicit.
            gas_origin_ptr_path
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
               0, explicit, unit.cu_context, func, [])
              (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                          vs_inst_idx := 0 |>, FEMPTY, entry_taint)
              [] (OK s0, G0, tn0)
End

(* Post-binding endpoint: what any dispatcher hands the body. *)
Definition runtime_body_endpoint_def:
  runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args dflts ret fbody <=>
    ?marks0 cenv0 cenv sa st' func s0 G0 tn0 shadow_unit shadow_func shadow_sa
     shadow_st'.
      (* source: bound state, for every observation stream after the
         entry's own explicit gas reads (marks0: msg.gas in a default) *)
      (!gx. external_entry_bound tops am tx vs.vs_outcomes
              (gas_explicit marks0 vs.vs_gas_readings ++ gx) mut args dflts
              (es with gas_obs := gx)) /\
      (* frame metadata: cenv is the package's environment with only
         ce_vars changed (positional and keyword registration touch nothing
         else); both dispatchers build this same package
         (package_external_group).  Not same_frame: registration rebinds
         arguments from MemLoc (allocate_args) to PtrVar. *)
      (?lbl pos_args min_cds is_payable nkey ut iv rt.
         set_external_package_target rpolicy.rpol_target
           (package_external_fn tops T (K global_nonreentrant_slot)
              (mut, nr, lookup_raw_return_or_F (NONE : num option)
                          tx.function_name External tops,
               tx.function_name, args, dflts, ret, fbody)) =
           (lbl, cenv0, pos_args, min_cds, is_payable, nr, nkey, ut, iv,
            fbody, rt)) /\
      cenv with ce_vars := cenv0.ce_vars = cenv0 /\
      (* code: the guarded body runs from sa *)
      compile_guarded_body cenv nr global_nonreentrant_slot T (mut = View)
        fbody (if ret = NoneT then NONE else SOME ret) sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      (* static frame: external_source_body_frame's conclusion *)
      body_inv tops unit.cu_context cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) /\
      cenv.ce_return_pc = NONE /\
      (?bindings env_t env'.
         supported_stmts tops bindings fbody /\
         expr_sim_inv cenv
           (initial_evaluation_context am.sources am.layouts tx NONE) env_t es /\
         ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
         type_stmts env_t ret fbody = SOME env' /\
         stmts_exprs_ok cenv fbody /\
         call_evaluation_safe
           (initial_evaluation_context am.sources am.layouts tx NONE)
           (int_calls_stmts fbody)) /\
      (* gas shadow of the same code *)
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      gas_shadow_context unit.cu_context shadow_unit.cu_context /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_unit.cu_context.ctx_functions /\
      gas_shadow_state sa shadow_sa /\
      compile_guarded_body (gas_shadow_env T cenv) nr global_nonreentrant_slot T
        (mut = View) (MAP gas_shadow_stmt fbody) (if ret = NoneT then NONE else SOME ret)
        shadow_sa = ((), shadow_st') /\
      fn_has_code shadow_sa shadow_st' shadow_func /\
      (* run: the entry reaches s0 at sa *)
      gas_path unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) (LENGTH marks0) (OK s0) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) (LENGTH marks0) (OK s0) /\
      alloca_history func s0 /\
      return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      (* nonreentrant: the strong pre-lock forms selected_entry_after_lock takes *)
      (nr ==>
         fresh_vars_wrt sa s0 /\
         (!D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context func [] G0 tn0 s0) ==>
              !fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY
                entry_taint
                (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0 |>)) /\
         (!H : (bool # bytes32 # type_value) list # num list.
            stmt_state_rel H unit.cu_context func cenv
              (initial_evaluation_context am.sources am.layouts tx NONE) es s0 /\
            ghost_inv H NONE cenv
              (initial_evaluation_context am.sources am.layouts tx NONE) es
              G0 tn0 s0) /\
         !D.
           gas_origin_ptr_path
             (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
              unit.cu_context,func,[])
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>, FEMPTY, entry_taint)
             marks0 (OK s0,G0,tn0)) /\
      storage_trace_domain
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am []) es.storage_trace /\
      (* horizon form, as runtime_entry_endpoint has it, marks0 for [] *)
      !st0 H.
        valid_horizon
          (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
          es.storage_trace ==>
        ((!fuel. ptr_safe_run
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] G0 tn0 s0) ==>
          !fuel. ptr_safe_blocks
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] FEMPTY entry_taint
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>)) /\
        ghost_inv_at
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es
          G0 tn0 s0 /\
        stmt_state_rel H unit.cu_context func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es s0 /\
        gas_origin_ptr_path
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, gas_explicit_sites unit.cu_context shadow_unit.cu_context,
             unit.cu_context, func, [])
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>, FEMPTY, entry_taint)
            marks0 (OK s0, G0, tn0)
End

(* Decorate the selected registration interval within the same existential
   witnesses. Reuse the public endpoint's body so the other facts stay in sync. *)
local
  val (witnesses, endpoint_body) = boolSyntax.strip_exists
    (boolSyntax.rhs (concl (SPEC_ALL runtime_body_endpoint_def)))
  fun witness name =
    valOf (List.find (fn v => fst (dest_var v) = name) witnesses)
  val sa = witness "sa"
  val st = witness "st'"
  val decorated_body = boolSyntax.list_mk_exists
    (witnesses, ``L ^sa ^st /\ ^endpoint_body``)
in
Definition runtime_body_endpoint_with_def:
  runtime_body_endpoint_with L tops rpolicy unit am tx vs es mut nr args dflts ret fbody <=>
    ^decorated_body
End
end

Theorem runtime_body_endpoint_unrestricted_def:
  runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args dflts ret fbody <=>
    runtime_body_endpoint_with (\a b. T) tops rpolicy unit am tx vs es mut nr
      args dflts ret fbody
Proof
  simp[runtime_body_endpoint_def, runtime_body_endpoint_with_def]
QED

Theorem external_entry_joint_endpoint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  rpt strip_tac >>
  drule_all (INST_TYPE [alpha |-> ``:expr``] external_entry_subst_consts_joint) >>
  strip_tac >> gvs[] >> pure_rewrite_tac[runtime_entry_endpoint_def] >>
  qexistsl_tac [`lbl`, `cenv0`, `cenv0`, `pos_args`, `min_cds`, `is_payable`, `nkey`,
                `ut'`, `iv`, `rt`, `st`, `cenv`, `sa`, `st'`, `func`, `s0`,
                `G0`, `tn0`] >>
  simp[] >> conj_tac
  >- fs[subst_consts_fn_def, subst_consts_expr_def] >>
  first_assum ACCEPT_TAC
QED

Theorem runtime_entry_endpoint_body_projection:
  runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody ==>
  ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
        runtime_entry_body_start tops rpolicy
          (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st /\
        compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
        compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
        fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        unit.cu_context.ctx_entry = SOME "__entry" /\
        lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
        fn_entry_label func = SOME "__entry" /\
        gas_path unit.cu_context func
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>) 0 (OK s0) /\
        gas_path_mem unit.cu_context func
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>) 0 (OK s0) /\
        alloca_history func s0 /\
        return_buf_frame NONE cenv sa s0 /\
        ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
        s0.vs_gas_readings = vs.vs_gas_readings /\
        s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
        (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                  (!e. r <> Error e) ==>
                  ?fuel'. run_context fuel' unit.cu_context vs = r) /\
        !st0 H.
          valid_horizon
            (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
            es0.storage_trace ==>
          ((!fuel. ptr_safe_run
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
              0 fuel unit.cu_context func [] G0 tn0 s0) ==>
            !fuel. ptr_safe_blocks
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
              0 fuel unit.cu_context func [] FEMPTY entry_taint
              (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                          vs_inst_idx := 0 |>)) /\
          ghost_inv_at
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 NONE cenv
            (initial_evaluation_context am.sources am.layouts tx NONE) es0
            G0 tn0 s0 /\
          stmt_state_rel H unit.cu_context func cenv
            (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
          !explicit.
            gas_origin_ptr_path
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
               0, explicit, unit.cu_context, func, [])
              (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                          vs_inst_idx := 0 |>, FEMPTY, entry_taint)
              [] (OK s0, G0, tn0)
Proof
  pure_rewrite_tac[runtime_entry_endpoint_def] >> strip_tac >>
  qexistsl_tac [`lbl`, `cenv0`, `pos_args`, `min_cds`, `is_payable`,
    `nkey`, `ut'`, `iv`, `rt`, `st`, `cenv`, `sa`, `st'`, `func`,
    `s0`, `G0`, `tn0`] >>
  fs[runtime_entry_body_start_def] >> first_assum ACCEPT_TAC
QED
