(* Caller/callee interference across one call and between two calls. A buffer
   whose final read precedes the only call can reuse the callee allocation.
   Concretized fixtures retain allocation identity/position/size metadata. *)
Theory concretizeCallFrameRegression
Ancestors
  concretizeMemLocDefs venomInst list option
Libs
  finite_mapLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset


Definition frame_callee_def:
  frame_callee =
    (mk_raw_function "callee"
      [<|bb_label := "callee"; bb_instructions :=
          [mk_inst 10 RETPC_PARAM [] ["pc"];
           mk_inst 11 MSTORE [Lit 0w; Lit 9w] [];
           mk_inst 12 RET [Var "pc"] []]|>]) with
      <|fn_eom := SOME 32; fn_mems_used := [(Allocation 13,0,32)]|>
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
  EVAL_TAC
QED

Theorem dead_caller_buffer_reuses_callee_frame:
  frame_result F = SOME (ASSIGN, [Lit 0w], SOME 32)
Proof
  EVAL_TAC
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

(* An eom is an upper bound, not a dense occupied frame. A live caller can
   use the gap below a fixed callee allocation; synthetic whole-frame
   reservations would incorrectly move it to 96. *)
Definition gap_callee_def:
  gap_callee =
    (mk_raw_function "callee"
      [<|bb_label := "callee"; bb_instructions :=
        [mk_inst 10 RETPC_PARAM [] ["pc"];
         mk_inst 11 MSTORE [Lit 64w; Lit 9w] [];
         mk_inst 12 RET [Var "pc"] []]|>]) with
      <|fn_eom := SOME 96; fn_mems_used := [(Allocation 13,64,32)]|>
End

Theorem live_caller_reuses_callee_gap:
  OPTION_MAP
    (\layout. (FLOOKUP layout.cl_positions (Allocation 0), layout.cl_eom))
    (compute_function_layout_fuel_in_context 20
      (mk_venom_context [gap_callee] (SOME "caller")) [] (frame_caller T)) =
    SOME (SOME 0,96)
Proof
  EVAL_TAC
QED

(* Transitive imports share identity even across different immediate callees.
   Their lifetime must span both calls, not merely either INVOKE instruction. *)
Definition frame_wrapper_def:
  frame_wrapper =
    (mk_raw_function "other"
      [<|bb_label := "other"; bb_instructions :=
        [mk_inst 14 RETPC_PARAM [] ["pc"];
         mk_inst 15 INVOKE [Label "callee"] [];
         mk_inst 16 RET [Var "pc"] []]|>]) with
      <|fn_eom := SOME 32; fn_mems_used := frame_callee.fn_mems_used|>
End

Theorem shared_import_between_different_calls:
  OPTION_MAP
    (\layout. (FLOOKUP layout.cl_positions (Allocation 0), layout.cl_eom))
    (compute_function_layout_fuel_in_context 20
      (mk_venom_context
        [frame_callee; frame_wrapper] (SOME "caller")) []
      (mk_raw_function "caller"
        [<|bb_label := "caller"; bb_instructions :=
          [mk_inst 0 ALLOCA [Lit 32w] ["buf"];
           mk_inst 1 INVOKE [Label "callee"] [];
           mk_inst 2 MSTORE [Var "buf"; Lit 7w] [];
           mk_inst 3 MLOAD [Var "buf"] ["value"];
           mk_inst 4 INVOKE [Label "other"] [];
           mk_inst 5 STOP [] []]|>])) =
    SOME (SOME 32,64)
Proof
  EVAL_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("call frame regression is not kernel closed: " ^ name)
  end) (DB.thms "concretizeCallFrameRegression");
