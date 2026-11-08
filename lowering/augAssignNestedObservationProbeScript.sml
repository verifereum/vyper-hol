(* Observation audit for the nested saved-slot subtraction candidate. *)
Theory augAssignNestedObservationProbe
Ancestors
  augAssignNestedPremiseProbe augAssignEffectfulContractProbe
  gasExemptCert vyperInterpreter vyperState vyperValue
  stmtLowering compileVyper context venomExecSemantics venomState
  fragExec fragGasPath gasSummary stmtSimDefs
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_initial_source_replay:
  !obs. FST (eval_stmt nested_initial_cx
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)))
    (nested_premise_es with gas_obs := obs)) = INL ()
Proof
  gen_tac >>
  `7 - 1 = (6:int)` by intLib.COOPER_TAC >>
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[return_def, get_place_def, combinTheory.APPLY_UPDATE_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem nested_initial_no_exempt_cert:
  ~gas_exempt_cert memory tops (ctx,func)
    (eval_stmt nested_initial_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (nested_premise_es,s0) marks (err,ee) (leaf,finish_state)
Proof
  irule source_replay_excludes_gas_exempt_cert >>
  rpt strip_tac >>
  qspec_then `obs` mp_tac nested_initial_source_replay >> simp[]
QED

Definition nested_observation_state_def:
  nested_observation_state = SND
    (compile_stmt nested_premise_cenv NoLoop NoneT
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)))
      (initial_compile_state "entry"))
End

Definition nested_observation_function_def:
  nested_observation_function = mk_raw_function "probe"
    (REVERSE nested_observation_state.cs_blocks ++
      [<|bb_label := nested_observation_state.cs_current_bb;
         bb_instructions := nested_observation_state.cs_current_insts ++
           [<|inst_id := nested_observation_state.cs_next_id;
              inst_opcode := STOP; inst_operands := []; inst_outputs := []|>]|>])
End

Definition nested_observation_start_def:
  nested_observation_start =
    sstore 0w 1w (sstore 1w 1w (sstore 2w 7w (init_venom_state "entry")))
End

Theorem nested_observation_target_probe:
  ?t. run_from 100 nested_premise_unit.cu_context nested_observation_function
      nested_observation_start =
    Abort Revert_abort t
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> simp[]
QED

Theorem nested_observation_endpoint_halts:
  !t. t.vs_current_bb = nested_observation_state.cs_current_bb /\
      t.vs_inst_idx = LENGTH nested_observation_state.cs_current_insts ==>
    run_from 0 nested_premise_unit.cu_context nested_observation_function t =
      Halt (halt_state (t with vs_returndata := []))
Proof
  gen_tac >>
  CONV_TAC (LAND_CONV EVAL) >> strip_tac >>
  simp[run_from_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``exec_block``, ``run_blocks``, ``halt_state``, ``nested_premise_unit``]) >>
  simp[Once exec_block_def, venomInstTheory.get_instruction_def, step_inst_non_invoke] >>
  simp[Once step_inst_base_def, venomInstTheory.is_terminator_def]
QED
