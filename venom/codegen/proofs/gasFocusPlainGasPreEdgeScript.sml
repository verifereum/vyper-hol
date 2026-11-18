Theory gasFocusPlainGasPreEdge
Ancestors
  fnFramePrefixDriver fnFramePrefix asmFrameRun blockSimHelpers
  frameJointTransition asmSem contextCodegenRel venomState venomInst words

(* Normalization reaches the GAS PC without executing the IR instruction. *)
Theorem focus_plain_frame_gas_available:
  asm_frame_prog_ok prog /\
  asm_frame_rel_tail [] prog vs0.vs_data_section es0 (entry_asm_state vs0 es0) es0 /\
  run_call es0 = SOME (result,final) /\ ~frame_resource_starved es0 result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es0) = AsmOK ast /\
  normal_frame_plan rpolicy unit cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
               vs_return_pc_token := 0w; vs_inst_idx := 0|>) es0
    (JointConfig stk PG G tn fn inst s oms om hs h) ast /\
  active_inst fn inst s /\ inst.inst_opcode = GAS ==>
  s.vs_gas_readings <> [] /\
  ?k ready.
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog k ast = AsmOK ready /\
    ready.as_pc < LENGTH prog /\ EL ready.as_pc prog = AsmOp "GAS" /\
    ready.as_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  `~is_param_opcode inst.inst_opcode` by simp[is_param_opcode_def] >>
  drule_all normal_frame_plan_active >>
  disch_then (qx_choosel_then [`k`, `ready`] strip_assume_tac) >>
  drule_all active_frame_gas_ready >> strip_tac >>
  `asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n + k) (entry_asm_state vs0 es0) = AsmOK ready` by
    (irule asm_steps_compose_ok >> qexists `ast` >> simp[]) >>
  drule_all asm_frame_prefix_gas_available_tail >> simp[] >> strip_tac >>
  conj_tac >- (strip_tac >> fs[]) >>
  qexistsl [`k`, `ready`] >> simp[]
QED
