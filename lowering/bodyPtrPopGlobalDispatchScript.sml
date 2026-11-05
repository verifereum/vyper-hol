Theory bodyPtrPopGlobalDispatch
Ancestors
  bodyPtrPopGlobalLoweringBoundary compileEnv moduleLowering vyperCompiler
  emitHelper venomInst
Libs monadsyntax

(* Explicit computed dispatch/fallback cut bounds later body computation. *)
Definition pop_global_dispatch_state_def:
  pop_global_dispatch_state =
    <| cs_next_var := 5; cs_next_label := 2; cs_next_id := 8;
       cs_current_bb := "@fallback_0";
       cs_current_insts := [mk_inst 7 REVERT [Lit 0w; Lit 0w] []];
       cs_blocks :=
         [<| bb_label := "@dispatch_1";
             bb_instructions :=
               [mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
                mk_inst 5 SHR [Lit 224w; Var "%3"] ["%4"];
                mk_inst 6 JMP [Label "@fallback_0"] []] |>;
          <| bb_label := "__entry";
             bb_instructions :=
               [mk_inst 0 CALLDATASIZE [] ["%0"];
                mk_inst 1 LT [Var "%0"; Lit 4w] ["%1"];
                mk_inst 2 ISZERO [Var "%1"] ["%2"];
                mk_inst 3 JNZ
                  [Var "%2"; Label "@dispatch_1"; Label "@fallback_0"] []] |>];
       cs_data_sections := [] |>
End

Theorem pop_global_dispatch_computed:
  (do fallback_lbl <- fresh_label "fallback";
      compile_selector_dispatch_linear [] fallback_lbl;
      compile_external_fn_bodies [];
      new_block fallback_lbl;
      emit_inst REVERT [Lit 0w; Lit 0w] []
   od) (initial_compile_state "__entry") = ((),pop_global_dispatch_state)
Proof
  EVAL_TAC
QED

Theorem pop_global_runtime_suffix:
  compile_generate_runtime [] [] pop_global_packages NONE Linear 0 0
    ([] : dense_bucket list) (K ("",0,F)) (initial_compile_state "__entry") =
  compile_internal_fn_bodies pop_global_packages pop_global_dispatch_state
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``compile_internal_fn_bodies``, ``pop_global_packages``]) >>
  qmatch_goalsub_abbrev_tac `compile_internal_fn_bodies pop_global_packages st` >>
  Cases_on `compile_internal_fn_bodies pop_global_packages st` >> simp[]
QED
