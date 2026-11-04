Theory makeSsaCurrentTreeTrace
Ancestors
  makeSsaCurrentCertificate makeSsaCurrentAllocation makeSsaCurrentRenameTrace
  makeSsaCurrentEdgeTrace makeSsaCurrentInduct makeSsaCurrentDefs
  makeSsaCurrentProps list pair

(* Sibling calls retain global counters/history but restore the lexical
   stacks and environment of their parent. These boundaries do not equate
   the sibling's final stacks with those of the parent. *)
Theorem current_env_realizes_restore:
  current_env_realizes H E (ctrs,stacks) V ==>
  current_env_realizes (H ++ tail) E (ctrs',stacks) V
Proof
  simp[current_env_realizes_def, latest_current_name_def] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (mp_tac o MATCH_MP current_token_name_append_stable) >> simp[]
QED

Theorem current_allocation_consistent_restore:
  current_allocation_consistent V H' s' (ctrs',stacks') /\
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  current_allocation_consistent V H' s' (ctrs',stacks)
Proof
  simp[current_allocation_consistent_def, current_counter_def] >>
  metis_tac[ssa_stacks_covered_mono]
QED

Theorem current_sibling_restore:
  current_env_realizes H E (ctrs,stacks) V /\
  current_allocation_consistent V (H ++ tail) s' (ctrs',stacks') /\
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  current_env_realizes (H ++ tail) E (ctrs',stacks) V /\
  current_allocation_consistent V (H ++ tail) s' (ctrs',stacks)
Proof
  metis_tac[current_env_realizes_restore, current_allocation_consistent_restore]
QED

(* The same annotated allocation trace works whether an incoming predecessor
   has already updated this block's PHI slots or does so after block visitation. *)
Theorem current_inst_trace_edge:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  current_inst_trace anns (current_edge_inst rt p inst) s rs H E
    (current_edge_inst rt p inst') s' rs' H' E'
Proof
  simp[current_inst_trace_def, current_edge_inst_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  qexists_tac `names` >> simp[]
QED

Theorem current_local_trace_edge:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  current_local_trace annss (MAP (current_edge_inst rt p) insts) s rs H E
    (MAP (current_edge_inst rt p) insts') s' rs' H' E'
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  drule current_inst_trace_edge >> strip_tac >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED
