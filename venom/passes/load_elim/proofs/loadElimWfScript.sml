(*
 * Load Elimination — structural well-formedness and SSA preservation.
 *
 * Each of the five rounds keeps labels and terminators, replaces loads
 * by ASSIGNs and redundant stores by NOPs (same inst_id), and inserts
 * PHIs right after a block's PHI prefix with ids above the round's
 * fn_max_inst_id; clear_nops_function then drops the NOPs.
 *)

Theory loadElimWf
Ancestors
  loadElimDefs analysisSimDefs passSharedDefs passSharedProps venomWf
  venomInst cfgTransform removeUnusedSsaProofs loadElimRoundUniqueness
  loadElimRoundNames loadElimIterationReadiness list pred_set

Theorem load_elim_function_preserves_wf:
  !fn. wf_function fn ==> wf_function (load_elim_function fn)
Proof
  simp[load_elim_function_def] >> rpt strip_tac >>
  irule clear_nops_function_preserves_wf >>
  rpt (irule le_round_preserves_wf_function >>
       simp[le_mk_load_context_configured])
QED

Theorem le_round_preserves_ssa_disjoint:
  !ctx g fn.
    wf_function fn /\ ssa_form fn /\
    DISJOINT (load_elim_one_fresh ctx g fn) (set (fn_all_vars fn)) ==>
    ssa_form (load_elim_one ctx g fn)
Proof
  rpt strip_tac >>
  irule le_round_preserves_ssa_form >> simp[] >>
  rpt strip_tac >>
  `pa.pa_phi_out IN load_elim_one_fresh ctx g fn` by
    metis_tac[le_iteration_generated_output] >>
  `~MEM pa.pa_phi_out (fn_all_vars fn)` by
    (qpat_x_assum `DISJOINT _ _` mp_tac >>
     simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `MEM pa.pa_phi_out (fn_all_vars fn)` suffices_by metis_tac[] >>
  simp[NoAsms, fn_all_vars_def, MEM_FLAT, MEM_MAP, MEM_APPEND, PULL_EXISTS] >>
  gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  qexistsl [`bb`, `i`] >> simp[]
QED

(* New variables are the PHI outputs "$le_phi_<load id>", one per load
   rewritten through a PHI.  The five rounds rewrite disjoint load
   opcodes and instruction ids are distinct (wf_function), so these
   names are distinct, and the prefix premise keeps them apart from
   fn's own variables.  Rewritten loads keep their single output. *)
Theorem load_elim_function_preserves_ssa:
  !fn. wf_function fn /\ ssa_form fn /\
       EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
       ssa_form (load_elim_function fn)
Proof
  rpt strip_tac >>
  simp[load_elim_function_def] >>
  qabbrev_tac `g = cfg_analyze fn` >>
  qabbrev_tac `bp = bp_analyze g fn` >>
  qabbrev_tac `ma = memory_alias_analyze bp fn` >>
  qabbrev_tac `sa = storage_alias_analyze bp fn` >>
  qabbrev_tac `ta = transient_alias_analyze bp fn` >>
  qabbrev_tac `c1 = mk_load_context bp ma (dfg_build_function fn) memory_config` >>
  qabbrev_tac `f1 = load_elim_one c1 g fn` >>
  qabbrev_tac `c2 = mk_load_context bp ta (dfg_build_function f1) transient_config` >>
  qabbrev_tac `f2 = load_elim_one c2 g f1` >>
  qabbrev_tac `c3 = mk_load_context bp sa (dfg_build_function f2) storage_config` >>
  qabbrev_tac `f3 = load_elim_one c3 g f2` >>
  qabbrev_tac `c4 = mk_load_context bp ma (dfg_build_function f3) dload_config` >>
  qabbrev_tac `f4 = load_elim_one c4 g f3` >>
  qabbrev_tac `c5 = mk_load_context bp ma (dfg_build_function f4) calldataload_config` >>
  `wf_function f1` by
    (qunabbrev_tac `f1` >> qunabbrev_tac `c1` >>
     irule le_round_preserves_wf_function >>
     simp[le_mk_load_context_configured]) >>
  `wf_function f2` by
    (qunabbrev_tac `f2` >> qunabbrev_tac `c2` >>
     irule le_round_preserves_wf_function >>
     simp[le_mk_load_context_configured]) >>
  `wf_function f3` by
    (qunabbrev_tac `f3` >> qunabbrev_tac `c3` >>
     irule le_round_preserves_wf_function >>
     simp[le_mk_load_context_configured]) >>
  `wf_function f4` by
    (qunabbrev_tac `f4` >> qunabbrev_tac `c4` >>
     irule le_round_preserves_wf_function >>
     simp[le_mk_load_context_configured]) >>
  `DISJOINT (load_elim_one_fresh c1 g fn) (set (fn_all_vars fn)) /\
   DISJOINT (load_elim_one_fresh c2 g f1) (set (fn_all_vars f1)) /\
   DISJOINT (load_elim_one_fresh c3 g f2) (set (fn_all_vars f2)) /\
   DISJOINT (load_elim_one_fresh c4 g f3) (set (fn_all_vars f3)) /\
   DISJOINT (load_elim_one_fresh c5 g f4) (set (fn_all_vars f4))` by
    (irule le_five_round_name_separation >>
     simp[Abbr `c1`, Abbr `c2`, Abbr `c3`, Abbr `c4`, Abbr `c5`,
          Abbr `f1`, Abbr `f2`, Abbr `f3`, Abbr `f4`,
          memory_config_def, transient_config_def, storage_config_def,
          dload_config_def, calldataload_config_def]) >>
  `ssa_form f1` by metis_tac[le_round_preserves_ssa_disjoint] >>
  `ssa_form f2` by metis_tac[le_round_preserves_ssa_disjoint] >>
  `ssa_form f3` by metis_tac[le_round_preserves_ssa_disjoint] >>
  `ssa_form f4` by metis_tac[le_round_preserves_ssa_disjoint] >>
  irule clear_nops_function_preserves_ssa >>
  irule le_round_preserves_ssa_disjoint >> simp[]
QED
