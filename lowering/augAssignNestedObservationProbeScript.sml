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

Theorem observation_run_unique[local]:
  run_from n ctx fn s = r /\ (!e. r <> Error e) /\
  run_from m ctx fn s = q /\ (!e. q <> Error e) ==> r = q
Proof
  strip_tac >>
  `run_from (n + m) ctx fn s = r` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `n` >> simp[]) >>
  `run_from (n + m) ctx fn s = q` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `m` >> simp[]) >>
  metis_tac[]
QED

Theorem nested_observation_no_endpoint_path:
  !n t. ~(gas_path nested_premise_unit.cu_context nested_observation_function
    nested_observation_start n (OK t) /\
    t.vs_current_bb = nested_observation_state.cs_current_bb /\
    t.vs_inst_idx = LENGTH nested_observation_state.cs_current_insts)
Proof
  rpt strip_tac >>
  drule gas_path_normal >> strip_tac >>
  drule_all nested_observation_endpoint_halts >> strip_tac >>
  first_x_assum (qspecl_then [`0`, `Halt (halt_state (t with vs_returndata := []))`] mp_tac) >>
  simp[] >> strip_tac >>
  mp_tac nested_observation_target_probe >> strip_tac >>
  spose_not_then assume_tac >>
  `Halt (halt_state (t with vs_returndata := [])) = Abort Revert_abort t'` by
    (irule observation_run_unique >> simp[] >> metis_tac[]) >> gvs[]
QED

Theorem nested_observation_no_summary:
  ~gas_summary (nested_premise_unit.cu_context, nested_observation_function)
    (eval_stmt nested_initial_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (nested_premise_es, nested_observation_start)
    (stmt_post nested_premise_unit.cu_context nested_observation_function
      nested_initial_cx lctx nested_premise_cenv cenv' sa
      nested_observation_state nested_observation_start)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  pure_rewrite_tac[gas_summary_def] >>
  rpt strip_tac >>
  `res = INL ()` by
    (qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o AP_TERM ``FST : (unit + exception) # evaluation_state -> unit + exception``) >>
     simp[nested_initial_source_replay]) >>
  gvs[stmt_post_def, loweringPostsTheory.stmt_lands_def,
      stmt_exit_loop_ctl] >>
  metis_tac[nested_observation_no_endpoint_path]
QED

Theorem nested_observation_no_outcome:
  ~gas_outcome memory tops
    (nested_premise_unit.cu_context, nested_observation_function)
    (eval_stmt nested_initial_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (nested_premise_es, nested_observation_start)
    (stmt_post nested_premise_unit.cu_context nested_observation_function
      nested_initial_cx lctx nested_premise_cenv cenv' sa
      nested_observation_state nested_observation_start)
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  rpt strip_tac
  >- metis_tac[gas_summary_at_summary, nested_observation_no_summary] >>
  qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[GSYM IMP_F] >>
  irule source_replay_excludes_gas_exempt_cert >>
  rpt gen_tac >>
  qspec_then `obs` mp_tac nested_initial_source_replay >>
  Cases_on `eval_stmt nested_initial_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)))
      (nested_premise_es with gas_obs := obs)` >>
  simp[ignore_bind_def, bind_def, return_def] >>
  strip_tac >> gvs[]
QED
