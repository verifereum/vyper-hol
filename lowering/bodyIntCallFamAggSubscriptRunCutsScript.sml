(* Raw straight-line cuts with the instruction index normalized at the cut. *)
Theory bodyIntCallFamAggSubscriptRunCuts
Ancestors
  exprLoweringProps fragExec venomState venomInst

Theorem subscript_run_cut:
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb) /\
  run_inst_seq (emitted_insts sa sm) s = OK mid /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  run_inst_seq (emitted_insts sm sb)
    (mid with vs_inst_idx := LENGTH sm.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts sm sb) mid = OK t` by metis_tac[] >>
  simp[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def]
QED

Theorem subscript_run_split:
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?mid. run_inst_seq (emitted_insts sa sm) s = OK mid /\
    run_inst_seq (emitted_insts sm sb)
      (mid with vs_inst_idx := LENGTH sm.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `run_inst_seq (emitted_insts sa sm) s`
  >- (drule_all subscript_run_cut >> simp[]) >>
  `!u. run_inst_seq (emitted_insts sa sm) s <> OK u` by simp[] >>
  drule_all run_inst_seq_chain_err >> simp[]
QED
