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
  cfgTransform loadElimRoundWf loadElimInstWf

Theorem load_elim_function_preserves_wf:
  !fn. wf_function fn ==> wf_function (load_elim_function fn)
Proof
  simp[load_elim_function_def] >> rpt strip_tac >>
  irule clear_nops_function_preserves_wf >>
  rpt (irule le_load_elim_one_wf >>
    simp[mk_load_context_def, le_supported_config_def])
QED

(* Package the three already-validated round invariants for composition. *)
Theorem le_round_invariants[local]:
  !ctx cfg fn ops.
    le_supported_config ctx.lctx_config /\ wf_function fn /\ ssa_form fn /\
    EVERY (\op. MEM op le_load_opcodes) ops /\
    ~MEM ctx.lctx_config.lc_load ops /\
    le_reserved_names (ctx.lctx_config.lc_load::ops) fn ==>
    wf_function (load_elim_one ctx cfg fn) /\
    ssa_form (load_elim_one ctx cfg fn) /\
    le_reserved_names ops (load_elim_one ctx cfg fn)
Proof
  rpt strip_tac
  >- metis_tac[le_load_elim_one_wf]
  >- (irule le_load_elim_one_ssa >> simp[] >>
      irule le_reserved_names_subset >>
      qexists `ctx.lctx_config.lc_load::ops` >> simp[]) >>
  irule le_load_elim_one_reserved >> simp[] >>
  irule le_reserved_names_subset >>
  qexists `ctx.lctx_config.lc_load::ops` >> simp[]
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
  `le_reserved_names le_load_opcodes fn` by
    metis_tac[le_initial_reserved_names] >>
  simp[load_elim_function_def] >>
  qpat_abbrev_tac `f1 = load_elim_one (mk_load_context _ _ _ memory_config) _ fn` >>
  qpat_abbrev_tac `f2 = load_elim_one (mk_load_context _ _ _ transient_config) _ f1` >>
  qpat_abbrev_tac `f3 = load_elim_one (mk_load_context _ _ _ storage_config) _ f2` >>
  qpat_abbrev_tac `f4 = load_elim_one (mk_load_context _ _ _ dload_config) _ f3` >>
  `wf_function f1 /\ ssa_form f1 /\
   le_reserved_names [TLOAD; SLOAD; DLOAD; CALLDATALOAD] f1` by
    (simp[Abbr `f1`] >> irule le_round_invariants >>
     fs[mk_load_context_def, le_supported_config_def, memory_config_def,
        le_load_opcodes_def]) >>
  `wf_function f2 /\ ssa_form f2 /\
   le_reserved_names [SLOAD; DLOAD; CALLDATALOAD] f2` by
    (simp[Abbr `f2`] >> irule le_round_invariants >>
     fs[mk_load_context_def, le_supported_config_def, transient_config_def,
        le_load_opcodes_def]) >>
  `wf_function f3 /\ ssa_form f3 /\
   le_reserved_names [DLOAD; CALLDATALOAD] f3` by
    (simp[Abbr `f3`] >> irule le_round_invariants >>
     fs[mk_load_context_def, le_supported_config_def, storage_config_def,
        le_load_opcodes_def]) >>
  `wf_function f4 /\ ssa_form f4 /\
   le_reserved_names [CALLDATALOAD] f4` by
    (simp[Abbr `f4`] >> irule le_round_invariants >>
     fs[mk_load_context_def, le_supported_config_def, dload_config_def,
        le_load_opcodes_def]) >>
  irule clear_nops_function_preserves_ssa >>
  irule le_load_elim_one_ssa >>
  simp[mk_load_context_def, le_supported_config_def, calldataload_config_def]
QED
