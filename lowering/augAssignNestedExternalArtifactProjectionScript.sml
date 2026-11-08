(* Finite artifact projections for the common External runtime entry audit. *)
Theory augAssignNestedExternalArtifactProjection
Ancestors
  augAssignNestedExternalRelatedEntryProbe augAssignNestedExternalCallerProbe
  augAssignNestedExternalEntryProbe
  moduleLowering compileVyper exprLoweringProps vyperInterpreter vyperState
  vyperValue gasContext stmtSimDefs loweringPosts
Libs finite_mapLib computeLib supportedEvalLib

val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])

Theorem nested_external_functions:
  nested_external_unit.cu_context.ctx_functions =
  [mk_raw_function "__entry"
    [<|bb_label := "__entry"; bb_instructions :=
       [mk_inst 0 CALLDATASIZE [] ["%0"];
        mk_inst 1 LT [Var "%0";Lit 4w] ["%1"];
        mk_inst 2 ISZERO [Var "%1"] ["%2"];
        mk_inst 3 JNZ [Var "%2";Label "@dispatch_1";Label "@fallback_0"] []]|>;
     <|bb_label := "@dispatch_1"; bb_instructions :=
       [mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
        mk_inst 5 SHR [Lit 224w;Var "%3"] ["%4"];
        mk_inst 6 EQ [Var "%4";Lit 3075143081w] ["%5"];
        mk_inst 7 JNZ [Var "%5";Label "@match_2";Label "@next_3"] []]|>;
     <|bb_label := "@match_2"; bb_instructions :=
       [mk_inst 8 JMP [Label "fn_probe"] []]|>;
     <|bb_label := "@next_3"; bb_instructions :=
       [mk_inst 9 JMP [Label "@fallback_0"] []]|>;
     <|bb_label := "fn_probe"; bb_instructions :=
       nested_external_insts ++ [mk_inst 49 STOP [] []]|>;
     <|bb_label := "@fallback_0"; bb_instructions :=
       [mk_inst 50 REVERT [Lit 0w;Lit 0w] []]|>];
   (mk_raw_function "internal 0 f()_runtime"
    [<|bb_label := "internal 0 f()_runtime"; bb_instructions :=
       [mk_inst 51 RETPC_PARAM [Lit 0w] ["%38"];
        mk_inst 52 ALLOCA [Lit 32w] ["%39"];
        mk_inst 53 ALLOCA [Lit 96w] ["%40"];
        mk_inst 54 MSTORE [Var "%40";Lit 1w] [];
        mk_inst 55 ALLOCA [Lit 64w] ["%41"];
        mk_inst 56 MSTORE [Var "%41";Lit 0w] [];
        mk_inst 57 ADD [Var "%40";Lit 32w] ["%42"];
        mk_inst 58 MCOPY [Var "%42";Var "%41";Lit 64w] [];
        mk_inst 59 MLOAD [Var "%40"] ["%43"];
        mk_inst 60 ASSIGN [Lit 0w] ["%44"];
        mk_inst 61 JMP [Label "@dyn_cond_4"] []]|>;
     <|bb_label := "@dyn_cond_4"; bb_instructions :=
       [mk_inst 62 LT [Var "%44";Var "%43"] ["%45"];
        mk_inst 63 ISZERO [Var "%45"] ["%46"];
        mk_inst 64 JNZ [Var "%46";Label "@dyn_exit_6";Label "@dyn_body_5"] []]|>;
     <|bb_label := "@dyn_body_5"; bb_instructions :=
       [mk_inst 65 MUL [Var "%44";Lit 64w] ["%47"];
        mk_inst 66 ADD [Lit 32w;Var "%47"] ["%48"];
        mk_inst 67 ADD [Var "%40";Var "%48"] ["%49"];
        mk_inst 68 MUL [Var "%44";Lit 2w] ["%50"];
        mk_inst 69 ADD [Lit 1w;Var "%50"] ["%51"];
        mk_inst 70 ADD [Lit 0w;Var "%51"] ["%52"];
        mk_inst 71 ASSIGN [Lit 0w] ["%53"];
        mk_inst 72 JMP [Label "@wcopy_cond_7"] []]|>;
     <|bb_label := "@wcopy_cond_7"; bb_instructions :=
       [mk_inst 73 EQ [Var "%53";Lit 2w] ["%54"];
        mk_inst 74 JNZ [Var "%54";Label "@wcopy_exit_9";Label "@wcopy_body_8"] []]|>;
     <|bb_label := "@wcopy_body_8"; bb_instructions :=
       [mk_inst 75 MUL [Var "%53";Lit 32w] ["%55"];
        mk_inst 76 ADD [Var "%49";Var "%55"] ["%56"];
        mk_inst 77 MLOAD [Var "%56"] ["%57"];
        mk_inst 78 ADD [Var "%52";Var "%53"] ["%58"];
        mk_inst 79 SSTORE [Var "%58";Var "%57"] [];
        mk_inst 80 ADD [Var "%53";Lit 1w] ["%59"];
        mk_inst 81 ASSIGN [Var "%59"] ["%53"];
        mk_inst 82 JMP [Label "@wcopy_cond_7"] []]|>;
     <|bb_label := "@wcopy_exit_9"; bb_instructions :=
       [mk_inst 83 ADD [Var "%44";Lit 1w] ["%60"];
        mk_inst 84 ASSIGN [Var "%60"] ["%44"];
        mk_inst 85 JMP [Label "@dyn_cond_4"] []]|>;
     <|bb_label := "@dyn_exit_6"; bb_instructions :=
       [mk_inst 86 SSTORE [Lit 0w;Var "%43"] [];
        mk_inst 87 RET [Lit 0w;Var "%38"] []]|>]) with
      fn_call_abi := <|ica_has_memory_return_buffer := SOME F;
                       ica_user_return_count := SOME 1|>]
Proof
  rewrite_tac[nested_external_unit_def, lower_vyper_runtime_unit_def,
    nested_external_classify, nested_external_immutables,
    nested_external_package, nested_external_compile_env] >>
  CONV_TAC (LAND_CONV (RESTR_EVAL_CONV [``function_selector``])) >>
  EVAL_TAC >> simp[]
QED

Theorem nested_external_runtime_artifact_numbers:
  nested_external_entry_fn.fn_name = "__entry" /\
  lookup_function "__entry" nested_external_unit.cu_context.ctx_functions =
    SOME nested_external_entry_fn /\
  pending_alloca_size nested_external_entry_fn nested_external_runtime_entry = 32 /\
  unit_alloca_frame nested_external_unit.cu_context = 224 /\
  fn_inst_ids_distinct nested_external_entry_fn /\
  EVERY (\f. ~EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f))
    nested_external_unit.cu_context.ctx_functions
Proof
  rewrite_tac[nested_external_entry_fn_def, pending_alloca_size_def,
    unit_alloca_frame_def, nested_external_functions] >> EVAL_TAC >> simp[]
QED

Theorem nested_external_direct_calls:
  !a b. fn_directly_calls nested_external_unit.cu_context a b <=>
    a = "__entry" /\ b = "internal 0 f()_runtime"
Proof
  rpt gen_tac >>
  Cases_on `a = "__entry"`
  >- (gvs[] >>
      rewrite_tac[fcgDefsTheory.fn_directly_calls_def, nested_external_functions] >>
      EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def, listTheory.MEM_APPEND,
        RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM]) >>
  Cases_on `a = "internal 0 f()_runtime"` >>
  gvs[] >>
  rewrite_tac[fcgDefsTheory.fn_directly_calls_def, nested_external_functions] >>
  EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def, listTheory.MEM_APPEND,
        RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM] >>
  rpt strip_tac >> gvs[]
QED

Theorem nested_external_call_closure:
  TC (fn_directly_calls nested_external_unit.cu_context) =
     fn_directly_calls nested_external_unit.cu_context
Proof
  irule relationTheory.transitive_TC_identity >>
  simp[relationTheory.transitive_def, nested_external_direct_calls] >>
  rpt strip_tac >> gvs[]
QED

Theorem nested_external_runtime_alloca_room:
  alloca_room nested_external_unit.cu_context nested_external_entry_fn
    nested_external_runtime_entry
Proof
  simp[alloca_room_def, nested_external_runtime_artifact_numbers,
    nested_external_runtime_position, nested_external_call_closure,
    nested_external_direct_calls] >>
  simp[SF wordsLib.SIZES_ss, pred_setTheory.GSPEC_EQ]
QED

Theorem nested_external_runtime_fmp_room:
  fmp_room nested_external_unit.cu_context nested_external_entry_fn
    nested_external_runtime_entry
Proof
  mp_tac nested_external_runtime_artifact_numbers >>
  rewrite_tac[fmp_room_def] >>
  simp[listTheory.EVERY_MEM] >> strip_tac >>
  `MEM nested_external_entry_fn nested_external_unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  simp[listTheory.EXISTS_MEM] >> metis_tac[]
QED

Theorem nested_external_runtime_stmt_state_rel:
  stmt_state_rel nested_external_unit.cu_context nested_external_entry_fn
    nested_external_slice_cenv nested_external_cx nested_premise_es
    nested_external_runtime_entry
Proof
  simp[stmt_state_rel_def, nested_external_runtime_state_rel,
    nested_external_runtime_alloca_room, nested_external_runtime_fmp_room,
    nested_external_runtime_allocation_local, nested_external_runtime_position]
QED

Theorem nested_external_source_replay:
  !obs. FST (eval_stmt nested_external_cx
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)))
    (nested_premise_es with gas_obs := obs)) = INL ()
Proof
  gen_tac >>
  `7 - 1 = (6:int)` by intLib.COOPER_TAC >>
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[return_def, get_place_def, combinTheory.APPLY_UPDATE_THM] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem nested_external_runtime_gas_admissible:
  gas_admissible
    (eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (stmt_res_ok NoLoop) nested_premise_es
Proof
  rw[gas_admissible_def] >>
  qspec_then `gs` mp_tac nested_external_source_replay >>
  simp[] >> strip_tac >> gvs[stmt_res_ok_def]
QED

(* All nontrivial antecedents of stmt_frag, at one common entry. *)
Theorem nested_external_runtime_entry_domain:
  (?cenv'.
    stmt_env nested_external_slice_cenv NoLoop NoneT
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))) nested_external_slice_start =
      (cenv', nested_external_slice_end)) /\
  fn_has_code nested_external_slice_start nested_external_slice_end
    nested_external_entry_fn /\
  fn_inst_ids_distinct nested_external_entry_fn /\
  local_ptrs_reserved nested_external_slice_cenv nested_external_slice_start /\
  ret_pc_ok nested_external_slice_cenv nested_external_slice_start
    nested_external_runtime_entry /\
  ~block_is_terminated nested_external_slice_start /\
  gas_admissible
    (eval_stmt nested_external_cx
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))))
    (stmt_res_ok NoLoop) nested_premise_es /\
  stmt_state_rel nested_external_unit.cu_context nested_external_entry_fn
    nested_external_slice_cenv nested_external_cx nested_premise_es
    nested_external_runtime_entry /\
  ~nested_external_runtime_entry.vs_halted /\
  nested_external_runtime_entry.vs_current_bb =
    nested_external_slice_start.cs_current_bb /\
  nested_external_runtime_entry.vs_inst_idx =
    LENGTH nested_external_slice_start.cs_current_insts
Proof
  simp[nested_external_slice_code, nested_external_runtime_artifact_numbers,
    nested_external_runtime_local_reserved, nested_external_runtime_ret_pc,
    nested_external_slice_position, nested_external_runtime_gas_admissible,
    nested_external_runtime_stmt_state_rel, nested_external_runtime_position] >>
  rewrite_tac[nested_external_slice_end_def] >>
  qmatch_goalsub_abbrev_tac `SND result` >>
  qexists `FST result` >> simp[]
QED
