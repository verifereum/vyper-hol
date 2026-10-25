(* Caller/callee interference across one call and between two calls. A buffer
   whose final read precedes the only call can reuse the callee frame. *)
Theory concretizeCallFrameRegression
Ancestors
  concretizeMemLocDefs venomInst list option
Libs
  finite_mapLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset


fun frame_arity ty = case total dom_rng ty of NONE => 0
  | SOME (_,range) => 1 + frame_arity range
fun frame_stage name = CONV_TAC (LAND_CONV (CHANGED_CONV
  (ONCE_DEPTH_CONV (fn tm => let val (h,args) = strip_comb tm in
    if is_const h andalso #Name (dest_thy_const h) = name andalso
       List.length args >= frame_arity (type_of h) andalso
       List.null (free_vars tm)
    then CHANGED_CONV (computeLib.WEAK_CBV_CONV (computeLib.the_compset())) tm
    else NO_CONV tm
  end))))

Definition frame_callee_def:
  frame_callee =
    (mk_raw_function "callee"
      [<|bb_label := "callee"; bb_instructions :=
          [mk_inst 10 RETPC_PARAM [] ["pc"];
           mk_inst 11 MSTORE [Lit 0w; Lit 9w] [];
           mk_inst 12 RET [Var "pc"] []]|>]) with fn_eom := SOME 32
End

Definition frame_caller_def:
  frame_caller live = mk_raw_function "caller"
    [<|bb_label := "caller"; bb_instructions :=
       [mk_inst 0 ALLOCA [Lit 32w] ["buf"];
        mk_inst 1 MSTORE [Var "buf"; Lit 7w] []] ++
       (if live then
          [mk_inst 2 INVOKE [Label "callee"] [];
           mk_inst 3 MLOAD [Var "buf"] ["value"]]
        else
          [mk_inst 2 MLOAD [Var "buf"] ["value"];
           mk_inst 3 INVOKE [Label "callee"] []]) ++
       [mk_inst 4 STOP [] []]|>]
End

Definition frame_result_def:
  frame_result live =
    OPTION_MAP
      (\out. ((HD (fn_insts out)).inst_opcode,
              (HD (fn_insts out)).inst_operands, out.fn_eom))
      (concretize_function_fuel_in_context
        (concretize_memloc_fuel (frame_caller live))
        (mk_venom_context [frame_caller live; frame_callee] (SOME "caller"))
        [] (frame_caller live))
End

Theorem live_caller_buffer_avoids_callee_frame:
  frame_result T = SOME (ASSIGN, [Lit 32w], SOME 64)
Proof
  simp_tac pure_ss [frame_result_def, concretize_function_fuel_in_context_def] >>
  frame_stage "concretize_memloc_fuel" >> frame_stage "fn_has_static_layout" >>
  simp_tac pure_ss [COND_CLAUSES] >> frame_stage "fn_needs_liveness_allocation" >>
  simp_tac pure_ss [COND_CLAUSES, compute_function_layout_fuel_in_context_def] >>
  frame_stage "static_alloca_items" >> simp_tac pure_ss [optionTheory.option_case_def] >>
  frame_stage "forced_candidate_positions" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "cfg_analyze" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "bp_analyze_fuel" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "compute_alloc_map_fuel_in_context" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "complete_alloc_positions_with_items" >>
  simp_tac pure_ss [optionTheory.option_case_def] >>
  frame_stage "mk_concretize_layout" >> simp_tac pure_ss [optionTheory.option_case_def] >>
  frame_stage "apply_concretize_layout" >> EVAL_TAC
QED

Theorem dead_caller_buffer_reuses_callee_frame:
  frame_result F = SOME (ASSIGN, [Lit 0w], SOME 32)
Proof
  simp_tac pure_ss [frame_result_def, concretize_function_fuel_in_context_def] >>
  frame_stage "concretize_memloc_fuel" >> frame_stage "fn_has_static_layout" >>
  simp_tac pure_ss [COND_CLAUSES] >> frame_stage "fn_needs_liveness_allocation" >>
  simp_tac pure_ss [COND_CLAUSES, compute_function_layout_fuel_in_context_def] >>
  frame_stage "static_alloca_items" >> simp_tac pure_ss [optionTheory.option_case_def] >>
  frame_stage "forced_candidate_positions" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "cfg_analyze" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "bp_analyze_fuel" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "compute_alloc_map_fuel_in_context" >> simp_tac pure_ss [Once LET_THM] >>
  frame_stage "complete_alloc_positions_with_items" >>
  simp_tac pure_ss [optionTheory.option_case_def] >>
  frame_stage "mk_concretize_layout" >> simp_tac pure_ss [optionTheory.option_case_def] >>
  frame_stage "apply_concretize_layout" >> EVAL_TAC
QED

Definition between_calls_caller_def:
  between_calls_caller = mk_raw_function "caller"
    [<|bb_label := "caller"; bb_instructions :=
       [mk_inst 0 ALLOCA [Lit 32w] ["buf"];
        mk_inst 1 INVOKE [Label "callee"] [];
        mk_inst 2 MSTORE [Var "buf"; Lit 7w] [];
        mk_inst 3 MLOAD [Var "buf"] ["value"];
        mk_inst 4 INVOKE [Label "callee"] [];
        mk_inst 5 STOP [] []]|>]
End

Theorem buffer_between_calls_avoids_callee_frame:
  OPTION_MAP
    (\out. ((HD (fn_insts out)).inst_opcode,
            (HD (fn_insts out)).inst_operands, out.fn_eom))
    (concretize_function_fuel_in_context
      (concretize_memloc_fuel between_calls_caller)
      (mk_venom_context [between_calls_caller; frame_callee] (SOME "caller"))
      [] between_calls_caller) =
    SOME (ASSIGN, [Lit 32w], SOME 64)
Proof
  EVAL_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("call frame regression is not kernel closed: " ^ name)
  end) (DB.thms "concretizeCallFrameRegression");
