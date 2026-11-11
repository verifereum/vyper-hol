Theory loadElimIterationReadiness
Ancestors
  loadElimDefs loadElimKeyShapeInvariant loadElimRoundUniqueness
  loadElimRoundWf loadElimCoupledExecution loadElimRoundNames
  loadElimRoundReachableSSA loadElimRoundStructure cfgTransform
  removeUnusedSsaProofs venomWfProps venomWf venomInst list pred_set

(* The wrapper caches BP and aliases, but may rebuild DFG at every round. *)
Theorem le_mk_load_context_projections[simp]:
  (mk_load_context bp aliases dfg config).lctx_bp = bp /\
  (mk_load_context bp aliases dfg config).lctx_aliases = aliases /\
  (mk_load_context bp aliases dfg config).lctx_dfg = dfg /\
  (mk_load_context bp aliases dfg config).lctx_config = config /\
  (mk_load_context bp aliases dfg config).lctx_addr_space = config_addr_space config
Proof
  simp[mk_load_context_def]
QED

Theorem le_mk_load_context_configured:
  MEM config [memory_config; transient_config; storage_config;
              dload_config; calldataload_config] ==>
  le_configured_context (mk_load_context bp aliases dfg config)
Proof
  simp[MEM] >> strip_tac >>
  gvs[le_configured_context_def, config_addr_space_def,
      memory_config_def, transient_config_def, storage_config_def,
      dload_config_def, calldataload_config_def]
QED

(* Cached-alias well-formedness is already exported, without hypotheses, by
   le_function_alias_maps_wf.  Structural preservation is already exported by
   le_round_preserves_wf_function and le_round_preserves_fn_inst_wf; consumers
   use those interfaces directly rather than duplicate them here. *)

Definition le_iteration_ready_def:
  le_iteration_ready original fn ops <=>
    wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
    cfg_analyze fn = cfg_analyze original /\
    fn_entry_label fn = fn_entry_label original /\
    EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts fn) /\
    le_round_name_bound original fn ops
End

Theorem le_iteration_ready_initial:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts fn) ==>
  le_iteration_ready fn fn []
Proof
  simp[le_iteration_ready_def, le_round_name_bound_initial]
QED

Theorem le_iteration_fresh_disjoint:
  wf_function original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  le_iteration_ready original fn ops /\ le_configured_context ctx /\
  ~MEM ctx.lctx_config.lc_load ops ==>
  DISJOINT (load_elim_one_fresh ctx g fn) (set (fn_all_vars fn))
Proof
  strip_tac >> irule le_round_name_bound_disjoint >>
  gvs[le_iteration_ready_def, wf_function_def, le_configured_context_def,
      memory_config_def, transient_config_def, storage_config_def,
      dload_config_def, calldataload_config_def] >>
  qexistsl [`ops`, `original`] >> simp[]
QED

Theorem le_iteration_ready_step:
  wf_function original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  le_iteration_ready original fn ops /\ le_configured_context ctx /\
  ctx.lctx_dfg = dfg_build_function fn /\
  ctx.lctx_config.lc_load = op /\ ~MEM op ops ==>
  le_iteration_ready original (load_elim_one ctx (cfg_analyze original) fn)
    (op::ops)
Proof
  strip_tac >> gvs[Excl "isPREFIX"] >>
  `DISJOINT (load_elim_one_fresh ctx (cfg_analyze original) fn)
    (set (fn_all_vars fn))` by
    (irule le_iteration_fresh_disjoint >> metis_tac[]) >>
  `!pa i. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx
       (cfg_analyze fn) (load_analyze ctx fn) fn) /\
     MEM i (fn_insts fn) ==> ~MEM pa.pa_phi_out i.inst_outputs` by
    (rpt strip_tac >>
     `pa.pa_phi_out IN load_elim_one_fresh ctx (cfg_analyze original) fn` by
       (gvs[le_iteration_ready_def, load_elim_one_fresh_def,
           load_elim_fresh_vars_def, MEM_MAP, Excl "isPREFIX"] >> metis_tac[]) >>
     `~MEM pa.pa_phi_out (fn_all_vars fn)` by
       (qpat_x_assum `DISJOINT _ _` mp_tac >>
        simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
     `MEM pa.pa_phi_out (fn_all_vars fn)` suffices_by metis_tac[] >>
     simp[NoAsms, fn_all_vars_def, MEM_FLAT, MEM_MAP, MEM_APPEND, PULL_EXISTS] >>
     gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP,
         Excl "isPREFIX"] >>
     qexistsl [`bb`, `i`] >> simp[]) >>
  gvs[le_iteration_ready_def] >>
  rpt conj_tac
  >- metis_tac[le_round_preserves_wf_function]
  >- metis_tac[le_round_preserves_fn_inst_wf]
  >- metis_tac[le_round_preserves_reachable_ssa]
  >- metis_tac[le_round_cfg]
  >- simp[le_round_entry]
  >- metis_tac[le_round_no_memtop] >>
  irule le_round_name_bound_step >>
  gvs[le_configured_context_def, memory_config_def, transient_config_def,
      storage_config_def, dload_config_def, calldataload_config_def]
QED

Theorem le_iteration_ready_config_step:
  wf_function original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  le_iteration_ready original fn ops /\
  MEM config [memory_config; transient_config; storage_config;
              dload_config; calldataload_config] /\
  config.lc_load = op /\ ~MEM op ops ==>
  le_iteration_ready original
    (load_elim_one (mk_load_context bp aliases (dfg_build_function fn) config)
      (cfg_analyze original) fn) (op::ops)
Proof
  strip_tac >> irule le_iteration_ready_step >>
  simp[le_mk_load_context_configured] >> metis_tac[]
QED

Definition le_memory_round_def:
  le_memory_round bp ma fn = load_elim_one
    (mk_load_context bp ma (dfg_build_function fn) memory_config)
    (cfg_analyze fn) fn
End

Definition le_transient_round_def:
  le_transient_round bp ma ta fn = load_elim_one
    (mk_load_context bp ta (dfg_build_function (le_memory_round bp ma fn)) transient_config)
    (cfg_analyze fn) (le_memory_round bp ma fn)
End

Definition le_storage_round_def:
  le_storage_round bp ma ta sa fn = load_elim_one
    (mk_load_context bp sa (dfg_build_function (le_transient_round bp ma ta fn)) storage_config)
    (cfg_analyze fn) (le_transient_round bp ma ta fn)
End

Definition le_data_round_def:
  le_data_round bp ma ta sa fn = load_elim_one
    (mk_load_context bp ma (dfg_build_function (le_storage_round bp ma ta sa fn)) dload_config)
    (cfg_analyze fn) (le_storage_round bp ma ta sa fn)
End

Theorem le_load_elim_function_rounds:
  load_elim_function fn = clear_nops_function
    (load_elim_one
      (mk_load_context (bp_analyze (cfg_analyze fn) fn)
        (memory_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
        (dfg_build_function
          (le_data_round (bp_analyze (cfg_analyze fn) fn)
            (memory_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
            (transient_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
            (storage_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn) fn))
        calldataload_config)
      (cfg_analyze fn)
      (le_data_round (bp_analyze (cfg_analyze fn) fn)
        (memory_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
        (transient_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
        (storage_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn) fn))
Proof
  simp[load_elim_function_def, le_memory_round_def, le_transient_round_def,
       le_storage_round_def, le_data_round_def]
QED

Theorem le_memory_round_ready:
  le_iteration_ready fn fn [] /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  le_iteration_ready fn (le_memory_round bp ma fn) [MLOAD]
Proof
  strip_tac >> simp[le_memory_round_def] >>
  irule le_iteration_ready_config_step >>
  gvs[le_iteration_ready_def, memory_config_def, Excl "isPREFIX"]
QED

Theorem le_transient_round_ready:
  le_iteration_ready fn fn [] /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  le_iteration_ready fn (le_transient_round bp ma ta fn) [TLOAD; MLOAD]
Proof
  strip_tac >> simp[le_transient_round_def] >>
  irule le_iteration_ready_config_step >>
  simp[transient_config_def, le_memory_round_ready] >>
  gvs[le_iteration_ready_def]
QED

Theorem le_storage_round_ready:
  le_iteration_ready fn fn [] /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  le_iteration_ready fn (le_storage_round bp ma ta sa fn) [SLOAD; TLOAD; MLOAD]
Proof
  strip_tac >> simp[le_storage_round_def] >>
  irule le_iteration_ready_config_step >>
  simp[storage_config_def, le_transient_round_ready] >>
  gvs[le_iteration_ready_def]
QED

Theorem le_data_round_ready:
  le_iteration_ready fn fn [] /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  le_iteration_ready fn (le_data_round bp ma ta sa fn) [DLOAD; SLOAD; TLOAD; MLOAD]
Proof
  strip_tac >> simp[le_data_round_def] >>
  irule le_iteration_ready_config_step >>
  simp[dload_config_def, le_storage_round_ready] >>
  gvs[le_iteration_ready_def]
QED

Theorem le_iteration_generated_output:
  MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx g
    (load_analyze ctx fn) fn) ==>
  pa.pa_phi_out IN load_elim_one_fresh ctx g fn
Proof
  simp[load_elim_one_fresh_def, load_elim_fresh_vars_def, MEM_MAP] >>
  metis_tac[]
QED

Theorem le_iteration_fresh_prefix:
  load_elim_one_fresh ctx g fn SUBSET {v | isPREFIX "$le_phi_" v}
Proof
  simp[SUBSET_DEF] >> rpt strip_tac >>
  drule le_round_fresh_origin >> strip_tac >> gvs[fresh_phi_var_def]
QED

(* This is the complete state-independent part of the public round boundary.
   Its entry premise can subsequently be instantiated with any initial state. *)
Theorem le_iteration_structural_requirements:
  wf_function original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  le_iteration_ready original fn ops /\
  MEM config [memory_config; transient_config; storage_config;
              dload_config; calldataload_config] /\
  ~MEM config.lc_load ops /\
  ctx = mk_load_context bp aliases (dfg_build_function fn) config /\
  (!v. bp_get_ptrs bp v = []) /\ wf_alias_sets aliases ==>
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\ wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = fn_entry_label original /\
  cfg_analyze original = cfg_analyze fn /\
  DISJOINT (load_elim_one_fresh ctx (cfg_analyze original) fn)
    (set (fn_all_vars fn)) /\
  (!pa. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx
     (cfg_analyze original) (load_analyze ctx fn) fn) ==>
     pa.pa_phi_out IN load_elim_one_fresh ctx (cfg_analyze original) fn) /\
  EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts fn) /\
  load_elim_one_fresh ctx (cfg_analyze original) fn SUBSET
    {v | isPREFIX "$le_phi_" v}
Proof
  strip_tac >>
  `le_configured_context ctx` by
    (gvs[] >> irule le_mk_load_context_configured >> simp[]) >>
  `DISJOINT (load_elim_one_fresh ctx (cfg_analyze original) fn)
     (set (fn_all_vars fn))` by
    (irule le_iteration_fresh_disjoint >> simp[] >>
     qexistsl [`ops`, `original`] >> gvs[]) >>
  gvs[le_iteration_ready_def, le_iteration_generated_output,
      le_iteration_fresh_prefix, Excl "isPREFIX"]
QED
