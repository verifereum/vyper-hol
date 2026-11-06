Theory fnPlanLineageTargetProbe
Ancestors
  fnPlanLineageEntryProduction codegenReadyCompute stackPlanGen livenessDefs
Libs wordsLib

(* Actual analyzed many-to-one target candidate.  Readiness is tested, not
   assumed; no successful function plan is asserted by this fixture. *)
Definition repeated_target_names_def:
  repeated_target_names =
    ["v00";"v01";"v02";"v03";"v04";"v05";"v06";"v07";"v08";
     "v09";"v10";"v11";"v12";"v13";"v14";"v15";"v16";"v17"]
End

Definition repeated_target_fn_def:
  repeated_target_fn = mk_raw_function "repeated_target"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["x"];
         mk_inst 1 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        MAPi (\i v. mk_inst (2+i) PHI
          [Label "E"; Var "x"; Label "L"; Var v] [v])
          repeated_target_names ++
        MAPi (\i v. mk_inst (20+i) MSTORE [Lit (n2w i); Var v] [])
          repeated_target_names ++
        [mk_inst 38 JMP [Label "L"] []] |>;
     <| bb_label := "L"; bb_instructions :=
        [mk_inst 39 JMP [Label "J"] []] |>]
End

Definition repeated_target_ready_flags_def:
  repeated_target_ready_flags =
    [canonical_param_prefix repeated_target_fn;
     wf_function repeated_target_fn;
     fn_inst_wf repeated_target_fn;
     ssa_form repeated_target_fn;
     def_dominates_uses repeated_target_fn;
     single_use_form repeated_target_fn;
     cfg_is_normalized (cfg_analyze repeated_target_fn) repeated_target_fn;
     block_entries_ready (cfg_analyze repeated_target_fn) repeated_target_fn;
     phi_operands_ready repeated_target_fn;
     EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions)
       repeated_target_fn.fn_blocks]
End

Theorem repeated_target_disjoint_obstruction:
  ~phi_uses_disjoint (collect_phis
    (THE (lookup_block "J" repeated_target_fn.fn_blocks)).bb_instructions) /\
  ~phi_operands_ready repeated_target_fn /\
  ~codegen_ready_fn repeated_target_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem repeated_target_ready_flags:
  repeated_target_ready_flags = [T;T;T;T;T;T;T;T;F;T]
Proof
  EVAL_TAC >> simp[]
QED

Theorem repeated_target_marker_free:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) repeated_target_fn.fn_blocks
Proof
  EVAL_TAC
QED

Theorem repeated_target_shared_input:
  MEM "x" (inst_uses (EL 0 (THE
    (lookup_block "J" repeated_target_fn.fn_blocks)).bb_instructions)) /\
  MEM "x" (inst_uses (EL 1 (THE
    (lookup_block "J" repeated_target_fn.fn_blocks)).bb_instructions))
Proof
  EVAL_TAC
QED

(* The repeated entry operand already violates phi_uses_disjoint, before
   any question about restored-stack capacity or unspecified EL selectors.
   All other readiness flags above hold.  Per the bounded probe contract,
   stop at this exact obstruction: this is not a frozen-task counterexample,
   nor a proof that all native target lists are distinct. *)
