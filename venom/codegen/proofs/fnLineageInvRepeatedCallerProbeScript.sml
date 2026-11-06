Theory fnLineageInvRepeatedCallerProbe
Ancestors
  fnLineageInvTerminal fnPlanLineage codegenReadyCompute cfgTransform
  stackPlanGen livenessDefs venomInst
Libs wordsLib

Definition repeated_caller_vars_def:
  repeated_caller_vars = ["a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";
    "a8";"a9";"a10";"a11";"a12";"a13";"a14";"a15"]
End

Definition repeated_caller_fn_def:
  repeated_caller_fn = mk_raw_function "repeated_caller"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 ADD [Lit 1w; Lit 2w] ["x"]] ++
        MAPi (\i v. mk_inst (1+i) ADD [Lit 1w; Lit 2w] [v]) repeated_caller_vars ++
        [mk_inst 17 JMP [Label "U"] []] |>;
     <| bb_label := "U"; bb_instructions :=
        [mk_inst 18 ADD [Var "x"; Var "x"] ["ux"]] ++
        GENLIST (\i. mk_inst (19+i) ADD
          [Var (EL (2*i) repeated_caller_vars);
           Var (EL (2*i+1) repeated_caller_vars)] ["u" ++ toString i]) 8 ++
        [mk_inst 27 STOP [] []] |>]
End

Theorem repeated_caller_ready:
  codegen_ready_fn repeated_caller_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem repeated_caller_live:
  live_vars_at (liveness_analyze repeated_caller_fn) "U" 0 =
    ["a15";"a14";"a13";"a12";"a11";"a10";"a9";"a8";
     "a7";"a6";"a5";"a4";"a3";"a2";"a1";"a0";"x";"x"]
Proof
  EVAL_TAC
QED

(* The actual entry block is rejected, independently of the totalized HD []. *)
Theorem repeated_caller_plan_rejected:
  generate_block_plan (liveness_analyze repeated_caller_fn)
    (dfg_build_function repeated_caller_fn) (cfg_analyze repeated_caller_fn)
    repeated_caller_fn (HD repeated_caller_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0) = NONE
Proof
  CONV_TAC (LAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV EVAL))))))) >>
  CONV_TAC (LAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV EVAL)))))) >>
  CONV_TAC (LAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``])) >>
  simp[]
QED

Theorem repeated_caller_target:
  join_target_ops (liveness_analyze repeated_caller_fn) repeated_caller_fn
    "E" (mk_inst 17 JMP [Label "U"] []) =
    SOME (MAP Var ["a15";"a14";"a13";"a12";"a11";"a10";"a9";"a8";
     "a7";"a6";"a5";"a4";"a3";"a2";"a1";"a0";"x";"x"])
Proof
  EVAL_TAC
QED

Theorem repeated_caller_raw_terminal_stack:
  (SND (generate_regular_inst_plan (liveness_analyze repeated_caller_fn)
    (dfg_build_function repeated_caller_fn) (cfg_analyze repeated_caller_fn)
    repeated_caller_fn (mk_inst 17 JMP [Label "U"] [])
    (live_vars_at (liveness_analyze repeated_caller_fn) "E" 18) F F "E"
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      MAP Var (repeated_caller_vars ++ ["x"])))).ps_stack =
    [HD []; Var "a14"; Var "a13"; Var "a12"; Var "a11"; Var "a10";
     Var "a9"; Var "a8"; Var "a7"; Var "a6"; Var "a5"; Var "a4";
     Var "a3"; Var "a2"; Var "a1"; Var "a0"; Var "x"; Var "a15"]
Proof
  CONV_TAC (LAND_CONV EVAL) >> simp[]
QED

Theorem repeated_caller_prefix:
  ?ops. generate_block_insts_plan (liveness_analyze repeated_caller_fn)
    (dfg_build_function repeated_caller_fn) (cfg_analyze repeated_caller_fn)
    repeated_caller_fn "E" F 0 18 0
    (TAKE 17 (HD repeated_caller_fn.fn_blocks).bb_instructions)
    (init_cleanup_plan_state NONE [] 0 0) =
    SOME (ops, (init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      MAP Var (repeated_caller_vars ++ ["x"]))
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[Once generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]) >>
  simp[generate_block_insts_plan_def]
QED

Theorem repeated_caller_join_guard_rejected:
  ~join_reached (liveness_analyze repeated_caller_fn) repeated_caller_fn "E"
    (mk_inst 17 JMP [Label "U"] [])
    (SND (generate_regular_inst_plan (liveness_analyze repeated_caller_fn)
      (dfg_build_function repeated_caller_fn) (cfg_analyze repeated_caller_fn)
      repeated_caller_fn (mk_inst 17 JMP [Label "U"] [])
      (live_vars_at (liveness_analyze repeated_caller_fn) "E" 18) F F "E"
      ((init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
        MAP Var (repeated_caller_vars ++ ["x"]))))
Proof
  simp[join_reached_def, repeated_caller_target,
    repeated_caller_raw_terminal_stack, stackModelTheory.stack_pop_def]
QED
