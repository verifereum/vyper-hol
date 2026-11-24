(* Join the same raw executions that supply the semantic endpoint. *)
Theory bodyFullMappingRunSeq
Ancestors
  exprLoweringProps fragExec instIdxIndep venomInst venomState

Theorem mapping_inst_seq_join:
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  c.cs_current_insts = b.cs_current_insts ++ emitted_insts b c /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b c) /\
  run_inst_seq (emitted_insts a b) s = OK u /\
  run_inst_seq (emitted_insts b c)
    (u with vs_inst_idx := LENGTH b.cs_current_insts) = OK v ==>
  ?raw. run_inst_seq (emitted_insts a c) s = OK raw /\
        (raw with vs_inst_idx := LENGTH c.cs_current_insts) =
        (v with vs_inst_idx := LENGTH c.cs_current_insts)
Proof
  strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    metis_tac[emitted_insts_append] >>
  `run_inst_seq (emitted_insts a c) s = run_inst_seq (emitted_insts b c) u` by
    metis_tac[run_inst_seq_append] >>
  `OK v = exec_result_map (\r. r with vs_inst_idx := LENGTH b.cs_current_insts)
    (run_inst_seq (emitted_insts b c) u)` by metis_tac[run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq (emitted_insts b c) u` >>
  gvs[exec_result_map_def]
QED

Definition mapping_raw_endpoint_def:
  mapping_raw_endpoint a b s t <=>
    ?raw. run_inst_seq (emitted_insts a b) s = OK raw /\
          t = raw with vs_inst_idx := LENGTH b.cs_current_insts
End

Theorem mapping_raw_endpoint_join:
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  c.cs_current_insts = b.cs_current_insts ++ emitted_insts b c /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts b c) /\
  mapping_raw_endpoint a b s u /\ mapping_raw_endpoint b c u v ==>
  mapping_raw_endpoint a c s v
Proof
  pure_rewrite_tac[mapping_raw_endpoint_def] >> strip_tac >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  drule_all mapping_inst_seq_join >> metis_tac[]
QED
