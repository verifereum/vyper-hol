(* Concrete candidate for the frozen memory-contract counterexample.
   These quotations are only source abbreviations, not new HOL definitions. *)
Theory lowerDloadZeroSiteContractProbe
Ancestors
  lowerDloadZeroSiteProbe o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomExecSemantics venomInst venomState irSupply list
  valueEncodingProofs contextCodegenRel contextRawReachable

val candidate_fn = ``mk_raw_function "main"
  [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 ALLOCA [Lit 0w] ["p"];
        mk_inst 1 DLOAD [Lit 0w] ["x"];
        mk_inst 2 ALLOCA [Lit 0w] ["q"];
        mk_inst 3 EQ [Var "p"; Var "q"] ["e"];
        mk_inst 4 JNZ [Var "e"; Label "safe"; Label "bad"] []] |>;
   <| bb_label := "safe"; bb_instructions := [mk_inst 5 STOP [] []] |>;
   <| bb_label := "bad"; bb_instructions :=
       [mk_inst 6 MSTORE [Lit 64w; Lit 0w] [];
        mk_inst 7 STOP [] []] |>]``;
val candidate_ctx = ``<| ctx_functions := [^candidate_fn];
                        ctx_entry := SOME "main";
                        ctx_global_reserved := [] |>``;
val candidate_state = ``(init_venom_state "entry") with
                          vs_labels := FEMPTY |+ ("code_end",0w)``;
val candidate_supply = ``<| irs_next_inst := 8; irs_next_var := 0;
  irs_next_label := 0; irs_used_inst_ids := [0;1;2;3;4;5;6;7];
  irs_used_vars := ["p";"x";"q";"e"];
  irs_used_labels := ["entry";"safe";"bad";"code_end"] |>``;
val candidate_target = ``FST (lower_dload_context_supply
                              ^candidate_supply ^candidate_ctx)``;

val source_s0 = candidate_state;
val source_s1 = ``^candidate_state with <|
  vs_vars := FEMPTY |+ ("p",0w);
  vs_allocas := FEMPTY |+ (0,(0,0)); vs_inst_idx := 1 |>``;
val source_s2 = ``^source_s1 with <|
  vs_vars := FEMPTY |+ ("p",0w) |+ ("x",0w); vs_inst_idx := 2 |>``;
val source_s3 = ``^source_s2 with <|
  vs_vars := FEMPTY |+ ("p",0w) |+ ("x",0w) |+ ("q",0w);
  vs_allocas := FEMPTY |+ (0,(0,0)) |+ (2,(0,0)); vs_inst_idx := 3 |>``;
val source_s4 = ``^source_s3 with <|
  vs_vars := FEMPTY |+ ("p",0w) |+ ("x",0w) |+ ("q",0w) |+ ("e",1w);
  vs_inst_idx := 4 |>``;

Theorem candidate_source_alloca_p:
  step_inst fuel ^candidate_ctx (mk_inst 0 ALLOCA [Lit 0w] ["p"])
    ^source_s0 = OK (^source_s1 with vs_inst_idx := 0)
Proof
  rewrite_tac[step_inst_non_invoke |> SIMP_RULE (srw_ss()) [mk_inst_def]] >>
  EVAL_TAC >> simp[]
QED

Theorem candidate_source_dload:
  step_inst fuel ^candidate_ctx (mk_inst 1 DLOAD [Lit 0w] ["x"])
    ^source_s1 = OK (^source_s2 with vs_inst_idx := 1)
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  rewrite_tac[step_inst_non_invoke |> SIMP_RULE (srw_ss()) [mk_inst_def]] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem candidate_source_alloca_q:
  step_inst fuel ^candidate_ctx (mk_inst 2 ALLOCA [Lit 0w] ["q"])
    ^source_s2 = OK (^source_s3 with vs_inst_idx := 2)
Proof
  rewrite_tac[step_inst_non_invoke |> SIMP_RULE (srw_ss()) [mk_inst_def]] >>
  EVAL_TAC >> simp[]
QED

Theorem candidate_source_eq:
  step_inst fuel ^candidate_ctx (mk_inst 3 EQ [Var "p"; Var "q"] ["e"])
    ^source_s3 = OK (^source_s4 with vs_inst_idx := 3)
Proof
  rewrite_tac[step_inst_non_invoke |> SIMP_RULE (srw_ss()) [mk_inst_def]] >>
  EVAL_TAC >> simp[bool_to_word_def]
QED

val source_jump = ``^source_s4 with <|
  vs_prev_bb := SOME "entry"; vs_current_bb := "safe"; vs_inst_idx := 0 |>``;

Theorem candidate_source_jump:
  step_inst fuel ^candidate_ctx
    (mk_inst 4 JNZ [Var "e"; Label "safe"; Label "bad"] [])
    ^source_s4 = OK ^source_jump
Proof
  rewrite_tac[step_inst_non_invoke |> SIMP_RULE (srw_ss()) [mk_inst_def]] >>
  EVAL_TAC >> simp[]
QED

Theorem candidate_source_stop:
  step_inst fuel ^candidate_ctx (mk_inst 5 STOP [] []) ^source_jump =
    Halt (^source_jump with vs_halted := T)
Proof
  rewrite_tac[step_inst_non_invoke |> SIMP_RULE (srw_ss()) [mk_inst_def]] >>
  EVAL_TAC >> simp[]
QED

Theorem candidate_source_entry:
  enters_block ^candidate_fn ^source_s0 s <=> s = ^source_s0
Proof
  EVAL_TAC >> simp[eval_phis_def, phi_prefix_length_def]
QED

