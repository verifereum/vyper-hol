Theory algebraicOptSimulationProps
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner unitShapeDefs

(* Concrete chain probes: the observation is either truthy or value-sensitive. *)
Definition ao_chain_probe_def:
  ao_chain_probe observe = mk_raw_function "probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 OR [Lit 2w; Lit 4w] ["x"];
       mk_inst 1 ISZERO [Var "x"] ["a"];
       mk_inst 2 ISZERO [Var "a"] ["b"];
       mk_inst 3 ISZERO [Var "b"] ["c"]] ++ observe |>]
End

Definition ao_probe_supply_def:
  ao_probe_supply = <| irs_next_inst := 20; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2;3;4;5];
    irs_used_vars := ["x";"a";"b";"c"];
    irs_used_labels := ["entry"] |>
End

Theorem ao_chain_probe_transform:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (fn_insts (FST (ao_transform_function_supply ao_probe_supply
      (ao_chain_probe [mk_inst 4 ASSERT [Var "b"] [];
                       mk_inst 5 STOP [] []])))) =
  [(ASSIGN,[Lit 1w]); (ISZERO,[Var "x"]);
   (ISZERO,[Var "a"]); (ISZERO,[Var "b"]);
   (ASSERT,[Var "x"]); (STOP,[])]
Proof
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_chain_probe_value_transform:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (fn_insts (FST (ao_transform_function_supply ao_probe_supply
      (ao_chain_probe [mk_inst 4 MSTORE [Lit 0w; Var "c"] [];
                       mk_inst 5 STOP [] []])))) =
  [(ASSIGN,[Lit 1w]); (ISZERO,[Var "x"]);
   (ISZERO,[Var "a"]); (ISZERO,[Var "b"]);
   (MSTORE,[Lit 0w; Var "a"]); (STOP,[])]
Proof
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_chain_probe_runs:
  !observe.
    observe = [mk_inst 4 ASSERT [Var "b"] []; mk_inst 5 STOP [] []] \/
    observe = [mk_inst 4 MSTORE [Lit 0w; Var "c"] []; mk_inst 5 STOP [] []] ==>
    lift_result (state_equiv {}) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks 1 (mk_venom_context [] NONE) (ao_chain_probe observe)
        (init_venom_state "entry"))
      (run_blocks 1 (mk_venom_context [] NONE)
        (FST (ao_transform_function_supply ao_probe_supply (ao_chain_probe observe)))
        (init_venom_state "entry"))
Proof
  rpt strip_tac >> gvs[] >>
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED


Definition ao_cmp_probe_def:
  ao_cmp_probe observe = mk_raw_function "cmp_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 GT [Var "input"; Lit 5w] ["x"]] ++ observe |>]
End

Theorem ao_cmp_probe_transform:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (fn_insts (FST (ao_transform_function_supply ao_probe_supply
      (ao_cmp_probe [mk_inst 1 ISZERO [Var "x"] ["a"];
        mk_inst 4 MSTORE [Lit 0w; Var "a"] []; mk_inst 5 STOP [] []])))) =
  [(LT,[Var "input"; Lit 6w]); (ASSIGN,[Var "x"]);
   (MSTORE,[Lit 0w; Var "a"]); (STOP,[])]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_cmp_assert_probe_transform:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (fn_insts (FST (ao_transform_function_supply ao_probe_supply
      (ao_cmp_probe [mk_inst 4 ASSERT [Var "x"] []; mk_inst 5 STOP [] []])))) =
  [(LT,[Var "input"; Lit 6w]); (ISZERO,[Var "x"]);
   (ASSERT,[Var "formal_var_6"]); (STOP,[])]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_cmp_probe_runs:
  !observe w.
    (observe = [mk_inst 1 ISZERO [Var "x"] ["a"];
       mk_inst 4 MSTORE [Lit 0w; Var "a"] []; mk_inst 5 STOP [] []] \/
     observe = [mk_inst 4 ASSERT [Var "x"] []; mk_inst 5 STOP [] []]) /\
    (w = 3w \/ w = 8w) ==>
    lift_result (state_equiv {}) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks 1 (mk_venom_context [] NONE) (ao_cmp_probe observe)
        (update_var "input" w (init_venom_state "entry")))
      (run_blocks 1 (mk_venom_context [] NONE)
        (FST (ao_transform_function_supply ao_probe_supply (ao_cmp_probe observe)))
        (update_var "input" w (init_venom_state "entry")))
Proof
  rpt strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC >> simp[]
QED
