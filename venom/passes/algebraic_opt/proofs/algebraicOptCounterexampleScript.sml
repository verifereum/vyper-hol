Theory algebraicOptCounterexample
Ancestors
  algebraicOptDefs venomWf venomFnScheduleRunner unitShapeDefs

Theorem ao_signed_width_guard:
  (0w:bytes32) >= (0w-1w)
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem ao_signed_width_values:
  sign_extend (0w-1w) 128w = 128w /\
  sign_extend 0w 128w <> 128w
Proof
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Definition ao_bad_fn_def:
  ao_bad_fn = mk_raw_function "bad"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 SIGNEXTEND [Lit (0w-1w); Lit 128w] ["x"];
       mk_inst 1 SIGNEXTEND [Lit 0w; Var "x"] ["y"];
       mk_inst 2 MSTORE [Lit 0w; Var "y"] [];
       mk_inst 3 STOP [] []] |>]
End

Definition ao_bad_supply_def:
  ao_bad_supply = <| irs_next_inst := 20; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2;3];
    irs_used_vars := ["x";"y"]; irs_used_labels := ["bad"; "entry"] |>
End

Theorem ao_bad_transform:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (fn_insts (FST (ao_transform_function_supply ao_bad_supply ao_bad_fn))) =
  [(SIGNEXTEND,[Lit (0w-1w); Lit 128w]); (ASSIGN,[Var "x"]);
   (MSTORE,[Lit 0w; Var "y"]); (STOP,[])]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC
QED

Theorem ao_bad_basic_premises:
  wf_function ao_bad_fn /\ fn_inst_wf ao_bad_fn /\
  EVERY label_positions_ok (fn_insts ao_bad_fn) /\
  ir_supply_inst_ok ao_bad_supply /\ ir_supply_covers_fn ao_bad_supply ao_bad_fn /\
  (init_venom_state "entry").vs_inst_idx = 0 /\
  (init_venom_state "entry").vs_prev_bb = NONE /\
  fn_entry_label ao_bad_fn = SOME (init_venom_state "entry").vs_current_bb /\
  (!inst x. MEM inst (fn_insts ao_bad_fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (init_venom_state "entry") = NONE)
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem ao_bad_ssa:
  wf_ssa ao_bad_fn
Proof
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
  >~ [`MEM "x" _`]
  >- (qexists_tac `mk_inst 0 SIGNEXTEND [Lit (0w-1w); Lit 128w] ["x"]` >>
      simp[venomInstTheory.mk_inst_def] >> conj_tac
      >- (rpt strip_tac >> Cases_on `path` >> gvs[]) >>
      qexistsl_tac [`0`, `1`] >> EVAL_TAC)
  >> qexists_tac `mk_inst 1 SIGNEXTEND [Lit 0w; Var "x"] ["y"]` >>
  simp[venomInstTheory.mk_inst_def] >> conj_tac
  >- (rpt strip_tac >> Cases_on `path` >> gvs[]) >>
  qexistsl_tac [`1`, `2`] >> EVAL_TAC
QED

Theorem ao_bad_observable:
  ~((?e. run_blocks 1 (mk_venom_context [] NONE) ao_bad_fn
       (init_venom_state "entry") = Error e) \/
    lift_result
      (state_equiv
        (set (SND (ao_transform_function_supply ao_bad_supply ao_bad_fn)).irs_used_vars
         DIFF set ao_bad_supply.irs_used_vars))
      (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks 1 (mk_venom_context [] NONE) ao_bad_fn (init_venom_state "entry"))
      (run_blocks 1 (mk_venom_context [] NONE)
        (FST (ao_transform_function_supply ao_bad_supply ao_bad_fn))
        (init_venom_state "entry")))
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >>
  simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  EVAL_TAC >> simp[]
QED

(* A closed counterexample to the exact frozen implication. *)
Theorem ao_transform_function_counterexample:
  wf_function ao_bad_fn /\
  wf_ssa ao_bad_fn /\
  fn_inst_wf ao_bad_fn /\
  EVERY label_positions_ok (fn_insts ao_bad_fn) /\
  ir_supply_inst_ok ao_bad_supply /\
  ir_supply_covers_fn ao_bad_supply ao_bad_fn /\
  ao_transform_function_supply ao_bad_supply ao_bad_fn =
    (FST (ao_transform_function_supply ao_bad_supply ao_bad_fn),
     SND (ao_transform_function_supply ao_bad_supply ao_bad_fn)) /\
  (init_venom_state "entry").vs_inst_idx = 0 /\
  (init_venom_state "entry").vs_prev_bb = NONE /\
  fn_entry_label ao_bad_fn = SOME (init_venom_state "entry").vs_current_bb /\
  (!inst x. MEM inst (fn_insts ao_bad_fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (init_venom_state "entry") = NONE) /\
  ~((?e. run_blocks 1 (mk_venom_context [] NONE) ao_bad_fn
       (init_venom_state "entry") = Error e) \/
    lift_result
      (state_equiv
        (set (SND (ao_transform_function_supply ao_bad_supply ao_bad_fn)).irs_used_vars
         DIFF set ao_bad_supply.irs_used_vars))
      (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks 1 (mk_venom_context [] NONE) ao_bad_fn (init_venom_state "entry"))
      (run_blocks 1 (mk_venom_context [] NONE)
        (FST (ao_transform_function_supply ao_bad_supply ao_bad_fn))
        (init_venom_state "entry")))
Proof
  metis_tac[ao_bad_basic_premises, ao_bad_ssa, ao_bad_observable, pairTheory.PAIR]
QED

(* Narrow repair for this defect (not applied): compare SIGNEXTEND widths
   using w2n, not signed word >=. More precisely the producer rewrite is
   safe for arbitrary input values if the outer width is >= 31, or if
   w2n inner_width <= w2n outer_width. This does not certify other rules. *)
