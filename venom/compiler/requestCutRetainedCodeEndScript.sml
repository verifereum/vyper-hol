Theory requestCutRetainedCodeEnd
Ancestors
  requestCutCfgCodeEnd requestCutReplaySuffix requestCutAbortObservation
  dftGasOracleDefs dftGasInvCrossingProbe dftGasToListReachBoundary dftRunRel dftDefs o1LabelFlowLateDft
  o1PassContract unitShapeDefs codegenSymRel codegenEntrySim contextCodegenRel
  frameJointTransition stateFrame venomInst venomState finite_map list words

(* A CODECOPY guard is evaluated before the stopped walk takes a step. *)
Theorem request_cut_retained_code_end_at:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  raw_reachable v7 C7 fn7 inst8 (u with vs_gas_readings := ws) /\ fn8 = dft_fn fn7 /\
  u.vs_current_bb = s8.vs_current_bb /\
  ev_reachable orc initial C7 p d fn7 inst8 u /\
  ev_reachable orc initial C8 p d fn8 inst8 (s8 with vs_gas_readings := initial.vs_gas_readings) /\
  code_end_offset_ok (\ctx fn i s. raw_reachable v7 ctx fn i s /\ LENGTH s.vs_requests <= k) C7 /\
  LENGTH s9.vs_requests <= k /\
  inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
  code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
  FLOOKUP initial.vs_labels "code_end" = SOME (n2w off) ==>
  w2n (src - n2w off) < dimword (:256) DIV 2
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (Var x) inst9.inst_operands` by simp[] >>
  drule_all_then strip_assume_tac request_cut_cfg_codecopy >>
  qpat_x_assum `inst8 = inst9` SUBST_ALL_TAC >>
  `MEM fn7 C7.ctx_functions` by metis_tac[ev_reachable_function_member] >>
  `o1_fn_shape C7 fn7` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `EVERY label_positions_ok (fn_insts fn7)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
  `code_end_var fn7 x` by metis_tac[dft_code_end_var_reflect] >>
  `u.vs_requests = s8.vs_requests /\ eval_operand (Var x) u = eval_operand (Var x) s8` by
    (mp_tac (Q.INST [`src` |-> `fn7`, `dst` |-> `fn8`,
      `u` |-> `u`,
      `t` |-> `s8 with vs_gas_readings := initial.vs_gas_readings`,
      `inst` |-> `inst9`] request_cut_retained_abort_observation) >>
     impl_tac >- (simp[inv_memory_observation_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[eval_operand_def] >> metis_tac[eval_operand_def]) >>
  `s8.vs_requests = s9.vs_requests` by
    (drule cfg_norm_joint_cursor_execution_frame >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_requests`) >> simp[execution_frame_def]) >>
  `u.vs_labels = initial.vs_labels` by
    (qpat_assum `ev_reachable orc initial C7 _ _ _ _ _`
       (mp_tac o MATCH_MP ev_reachable_labels) >> simp[]) >>
  `FLOOKUP u.vs_labels "code_end" = SOME (n2w off)` by simp[] >>
  qpat_x_assum `code_end_offset_ok _ C7` mp_tac >>
  simp[code_end_offset_ok_def] >>
  disch_then (qspecl_then [`fn7`, `inst9`, `u with vs_gas_readings := ws`,
    `dst`, `x`, `sz`, `src`, `n2w off`] mp_tac) >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem request_cut_retained_code_end:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  raw_reachable v7 C7 fn7 inst8 (u with vs_gas_readings := ws) /\ fn8 = dft_fn fn7 /\
  u.vs_current_bb = s8.vs_current_bb /\
  ev_reachable orc initial C7 p d fn7 inst8 u /\
  ev_reachable orc initial C8 p d fn8 inst8 (s8 with vs_gas_readings := initial.vs_gas_readings) /\
  code_end_offset_ok (\ctx fn i s. raw_reachable v7 ctx fn i s /\ LENGTH s.vs_requests <= k) C7 /\
  LENGTH s9.vs_requests <= k /\
  codegen_asm_entry_rel cpl prog initial a0 /\
  inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
  code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
  FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
  w2n (src - n2w off) < dimword (:256) DIV 2
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP initial.vs_labels "code_end" = SOME (n2w off)` by
    fs[codegen_asm_entry_rel_def] >>
  drule_all request_cut_retained_code_end_at >> simp[]
QED
