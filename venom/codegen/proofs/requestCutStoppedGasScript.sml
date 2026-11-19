Theory requestCutStoppedGas
Ancestors
  gasFocusGasPreEdge gasFocusPlainGasPreEdge requestCutReplaySuffix
  o1ContractCfgNormJointCursors
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  asmFrameRel asmOptimizer asmDataEnv asmSem asmSymSem
  contextCodegenRel stateFrame venomState venomInst vfmExecution words

(* At a paired GAS cursor the accepted finalizer supplies the next reading.
   This readiness check does not use the raw request bound. *)
Theorem request_cut_stopped_gas_available:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    ((entry_asm_state vs0 es) with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rp unit = SOME prog /\ unit_shape_ok unit /\
  codegen_ready unit.cu_context /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  q9 = JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9 /\
  (fin = K SOME ==> normal_frame_plan rp unit cpl prog
    (vs0 with <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp;
               vs_return_pc_token := 0w; vs_inst_idx := 0|>) es q9 ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) n
      (sym_init (entry_asm_state vs0 es)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rp unit cpl prog
      vs0 es q9 ast ss /\ focus_s7_symbolic_context unit prog) /\
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) q9 /\
  active_inst fn9 inst9 s9 /\ inst9.inst_opcode = GAS ==>
  s8.vs_gas_readings <> []
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `q9 = _` SUBST_ALL_TAC >>
  drule cfg_norm_joint_cursor_execution_frame >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.vs_gas_readings`) >>
  simp[execution_frame_def] >> disch_then SUBST1_TAC >>
  Cases_on `fin = asm_opt_finalizer`
  >- (fs[] >> drule_all focus_normal_frame_gas_available >>
      disch_then (qx_choose_then `max_cost` (mp_tac o Q.SPECL
        [`n`,`ast`,`ss`,`stk9`,`PG9`,`G9`,`tn9`,`fn9`,`inst9`,`s9`,
         `oms9`,`om9`,`hs9`,`hist9`])) >> simp[]) >>
  `fin = K SOME` by fs[accepted_finalizers_def] >>
  `prog' = prog` by fs[] >>
  `(entry_asm_state vs0 es with as_code := assemble prog ++ vs0.vs_data_section) =
    entry_asm_state vs0 es` by
    simp[entry_asm_state_def] >>
  fs[] >>
  mp_tac (Q.INST [`prog` |-> `prog`, `unit` |-> `unit`, `vs0` |-> `vs0`,
    `es0` |-> `es`, `rpolicy` |-> `rp`, `cpl` |-> `cpl`, `n` |-> `n`, `ast` |-> `ast`,
    `stk` |-> `stk9`, `PG` |-> `PG9`, `G` |-> `G9`, `tn` |-> `tn9`,
    `fn` |-> `fn9`, `inst` |-> `inst9`, `s` |-> `s9`,
    `oms` |-> `oms9`, `om` |-> `om9`, `hs` |-> `hs9`, `h` |-> `hist9`]
    focus_plain_frame_gas_available) >> simp[]
QED
