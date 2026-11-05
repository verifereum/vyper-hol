Theory fnPlanLineageEntryProbe
Ancestors
  fnPlanLineageDemandSupport codegenReadyCompute stackPlanGen livenessDefs
  stackPlanOps stackPlanTypes stackModel venomInst cfgTransform
Libs wordsLib

(* Actual small native diamond: local incoming names need not dominate J. *)
Definition entry_probe_fn_def:
  entry_probe_fn = mk_raw_function "entry_probe"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Lit 1w; Label "L"; Label "R"] []] |>;
     <| bb_label := "L"; bb_instructions :=
        [mk_inst 1 ADD [Lit 10w; Lit 1w] ["a"];
         mk_inst 2 JMP [Label "J"] []] |>;
     <| bb_label := "R"; bb_instructions :=
        [mk_inst 3 ADD [Lit 20w; Lit 1w] ["b"];
         mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 5 PHI [Label "L"; Var "a"; Label "R"; Var "b"] ["x"];
         mk_inst 6 ADD [Var "x"; Lit 1w] ["y"];
         mk_inst 7 JMP [Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 8 STOP [] []] |>]
End

Theorem entry_probe_ready:
  codegen_ready_fn entry_probe_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) entry_probe_fn.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

Definition entry_probe_step_def:
  entry_probe_step n ps = SND (THE (generate_block_plan
    (liveness_analyze entry_probe_fn) (dfg_build_function entry_probe_fn)
    (cfg_analyze entry_probe_fn) entry_probe_fn
    (EL n entry_probe_fn.fn_blocks) ps))
End

Definition entry_probe_start_def:
  entry_probe_start = init_cleanup_plan_state NONE [] 0 0
End

Theorem entry_probe_plan_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze entry_probe_fn) (dfg_build_function entry_probe_fn)
    (cfg_analyze entry_probe_fn) NONE [] entry_probe_fn 0 0)
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Theorem entry_probe_path_stacks:
  (entry_probe_step 0 entry_probe_start).ps_stack = [] /\
  (entry_probe_step 1 (entry_probe_step 0 entry_probe_start)).ps_stack = [Var "a"] /\
  (entry_probe_step 2 (entry_probe_step 0 entry_probe_start)).ps_stack = [Var "b"]
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Definition entry_probe_incoming_def:
  entry_probe_incoming side = entry_probe_step side (entry_probe_step 0 entry_probe_start)
End

Definition entry_probe_phi_def:
  entry_probe_phi side = SND (generate_phi_plan
    (HD (EL 3 entry_probe_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze entry_probe_fn) "J" 1) F
    (entry_probe_incoming side))
End

Theorem entry_probe_boundary_inventory:
  EVERY (\side.
    IS_SOME (generate_block_plan (liveness_analyze entry_probe_fn)
      (dfg_build_function entry_probe_fn) (cfg_analyze entry_probe_fn)
      entry_probe_fn (EL side entry_probe_fn.fn_blocks)
      (entry_probe_step 0 entry_probe_start)) /\
    clean_stack_plan (liveness_analyze entry_probe_fn) (cfg_analyze entry_probe_fn)
      entry_probe_fn (EL 3 entry_probe_fn.fn_blocks) (entry_probe_incoming side) =
      ([], entry_probe_incoming side) /\
    (entry_probe_phi side).ps_stack = [Var "x"] /\
    (entry_probe_phi side).ps_spilled = FEMPTY /\
    (entry_probe_step 3 (entry_probe_incoming side)).ps_stack = [] /\
    (entry_probe_step 3 (entry_probe_incoming side)).ps_spilled = FEMPTY)
    [1;2]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem entry_probe_post_phi_support:
  !v. MEM (Var v) (entry_probe_phi 1).ps_stack \/
      Var v IN FDOM (entry_probe_phi 1).ps_spilled ==>
    demand_available entry_probe_fn (EL 3 entry_probe_fn.fn_blocks) 1 v
Proof
  mp_tac entry_probe_boundary_inventory >>
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> strip_tac >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule (Q.SPECL [`entry_probe_fn`, `EL 3 entry_probe_fn.fn_blocks`, `0`]
    current_output_demand_available_suc |> SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac
  >- metis_tac[entry_probe_ready, codegen_ready_fn_def]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> simp[venomWfTheory.fn_reachable_def] >> qexists_tac `"entry"` >>
  conj_tac >- EVAL_TAC >>
  irule relationTheory.RTC_TRANS >> qexists_tac `"L"` >>
  conj_tac
  >- (irule relationTheory.RTC_SINGLE >> simp[venomWfTheory.fn_cfg_edge_def] >>
      qexists_tac `EL 0 entry_probe_fn.fn_blocks` >> EVAL_TAC)
  >> irule relationTheory.RTC_SINGLE >> simp[venomWfTheory.fn_cfg_edge_def] >>
  qexists_tac `EL 1 entry_probe_fn.fn_blocks` >> EVAL_TAC
QED

(* The R bypass witnesses why the selected L input is not dominance-supported. *)
Theorem entry_probe_incoming_not_supported:
  ~demand_available entry_probe_fn (EL 3 entry_probe_fn.fn_blocks) 0 "a"
Proof
  strip_tac >> gvs[demand_available_def] >>
  gvs[entry_probe_fn_def, mk_raw_function_def, mk_inst_def] >>
  gvs[venomWfTheory.fn_dominates_def] >>
  first_x_assum (qspec_then `["entry"; "R"; "J"]` mp_tac) >>
  EVAL_TAC >> simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  EVAL_TAC
QED

Definition entry_loop_fn_def:
  entry_loop_fn = mk_raw_function "entry_loop"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ADD [Lit 0w; Lit 1w] ["a"];
         mk_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "a"; Label "back"; Var "n"] ["x"];
         mk_inst 3 ADD [Var "x"; Lit 1w] ["n"];
         mk_inst 4 JNZ [Lit 1w; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions := [mk_inst 5 JMP [Label "H"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Theorem entry_loop_ready:
  codegen_ready_fn entry_loop_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) entry_loop_fn.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

Theorem entry_loop_plan_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze entry_loop_fn) (dfg_build_function entry_loop_fn)
    (cfg_analyze entry_loop_fn) NONE [] entry_loop_fn 0 0)
Proof
  EVAL_TAC
QED

Definition entry_loop_step_def:
  entry_loop_step n ps = SND (THE (generate_block_plan
    (liveness_analyze entry_loop_fn) (dfg_build_function entry_loop_fn)
    (cfg_analyze entry_loop_fn) entry_loop_fn
    (EL n entry_loop_fn.fn_blocks) ps))
End

Definition entry_loop_incoming_def:
  entry_loop_incoming revisit =
    if revisit then entry_loop_step 2 (entry_loop_step 1
      (entry_loop_step 0 entry_probe_start))
    else entry_loop_step 0 entry_probe_start
End

Definition entry_loop_phi_def:
  entry_loop_phi revisit = SND (generate_phi_plan
    (HD (EL 1 entry_loop_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze entry_loop_fn) "H" 1) F
    (entry_loop_incoming revisit))
End

Theorem entry_loop_inventories:
  (entry_loop_incoming F).ps_stack = [Var "a"] /\
  (entry_loop_incoming T).ps_stack = [Var "n"] /\
  EVERY (\r.
    (entry_loop_incoming r).ps_spilled = FEMPTY /\
    clean_stack_plan (liveness_analyze entry_loop_fn) (cfg_analyze entry_loop_fn)
      entry_loop_fn (EL 1 entry_loop_fn.fn_blocks) (entry_loop_incoming r) =
        ([], entry_loop_incoming r) /\
    (entry_loop_phi r).ps_stack = [Var "x"] /\
    (entry_loop_phi r).ps_spilled = FEMPTY /\
    (entry_loop_step 1 (entry_loop_incoming r)).ps_stack = [Var "n"] /\
    (entry_loop_step 1 (entry_loop_incoming r)).ps_spilled = FEMPTY) [F;T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

(* Keeping a selected PHI input live is rejected at the readiness boundary. *)
Definition entry_live_input_fn_def:
  entry_live_input_fn = entry_probe_fn with fn_blocks :=
    LUPDATE ((EL 3 entry_probe_fn.fn_blocks) with bb_instructions :=
      [mk_inst 5 PHI [Label "L"; Var "a"; Label "R"; Var "b"] ["x"];
       mk_inst 6 ADD [Var "x"; Var "a"] ["y"];
       mk_inst 7 JMP [Label "exit"] []]) 3 entry_probe_fn.fn_blocks
End

Theorem entry_live_input_rejected:
  ~phi_operands_ready entry_live_input_fn
Proof
  EVAL_TAC
QED

Definition entry_probe_ordinary_def:
  entry_probe_ordinary side = generate_inst_plan
    (liveness_analyze entry_probe_fn) (dfg_build_function entry_probe_fn)
    (cfg_analyze entry_probe_fn) entry_probe_fn
    (EL 1 (EL 3 entry_probe_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze entry_probe_fn) "J" 2) F T "J"
    (entry_probe_phi side)
End

Definition entry_loop_ordinary_def:
  entry_loop_ordinary revisit = generate_inst_plan
    (liveness_analyze entry_loop_fn) (dfg_build_function entry_loop_fn)
    (cfg_analyze entry_loop_fn) entry_loop_fn
    (EL 1 (EL 1 entry_loop_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze entry_loop_fn) "H" 2) F T "H"
    (entry_loop_phi revisit)
End

Theorem entry_probe_ordinary_inventory:
  IS_SOME (entry_probe_ordinary 1) /\
  IS_SOME (entry_probe_ordinary 2) /\
  (SND (THE (entry_probe_ordinary 1))).ps_stack = [] /\
  (SND (THE (entry_probe_ordinary 2))).ps_stack = [] /\
  (SND (THE (entry_probe_ordinary 1))).ps_spilled = FEMPTY /\
  (SND (THE (entry_probe_ordinary 2))).ps_spilled = FEMPTY /\
  IS_SOME (entry_loop_ordinary F) /\
  IS_SOME (entry_loop_ordinary T) /\
  (SND (THE (entry_loop_ordinary F))).ps_stack = [Var "n"] /\
  (SND (THE (entry_loop_ordinary T))).ps_stack = [Var "n"] /\
  (SND (THE (entry_loop_ordinary F))).ps_spilled = FEMPTY /\
  (SND (THE (entry_loop_ordinary T))).ps_spilled = FEMPTY
Proof
  rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem entry_loop_revisit_not_supported:
  ~demand_available entry_loop_fn (EL 1 entry_loop_fn.fn_blocks) 0 "n"
Proof
  strip_tac >> gvs[demand_available_def] >>
  gvs[entry_loop_fn_def, mk_raw_function_def, mk_inst_def]
QED

Theorem entry_probe_native_success_and_freshness:
  IS_SOME (generate_block_plan (liveness_analyze entry_loop_fn)
    (dfg_build_function entry_loop_fn) (cfg_analyze entry_loop_fn)
    entry_loop_fn (EL 0 entry_loop_fn.fn_blocks) entry_probe_start) /\
  EVERY (\r.
    IS_SOME (generate_block_plan (liveness_analyze entry_loop_fn)
      (dfg_build_function entry_loop_fn) (cfg_analyze entry_loop_fn)
      entry_loop_fn (EL 1 entry_loop_fn.fn_blocks) (entry_loop_incoming r)) /\
    ~MEM (Var "n") (entry_loop_phi r).ps_stack /\
    Var "n" NOTIN FDOM (entry_loop_phi r).ps_spilled) [F;T] /\
  IS_SOME (generate_block_plan (liveness_analyze entry_loop_fn)
    (dfg_build_function entry_loop_fn) (cfg_analyze entry_loop_fn)
    entry_loop_fn (EL 2 entry_loop_fn.fn_blocks)
      (entry_loop_step 1 (entry_loop_incoming F))) /\
  EVERY (\side. ~MEM (Var "y") (entry_probe_phi side).ps_stack /\
    Var "y" NOTIN FDOM (entry_probe_phi side).ps_spilled /\
    (entry_probe_incoming side).ps_spilled = FEMPTY) [1;2]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

(* Diagnostic boundary table (all stacks shown in physical list order):
   Diamond L/R: entry [a]/[b], cleaning identity, PHI [x], ordinary ADD [],
     block end []; all spill maps empty. The L input a is not
     demand_available at J:0 (R bypass), but x is supported at J:1.
   Loop first/revisit: entry [a]/[n], cleaning identity, PHI [x],
     ordinary ADD [n], block end [n]; all spill maps empty. The revisit
     input n is not demand_available at H:0: its definition is later in H.
   At the actual ordinary boundary, y (diamond) and n (loop) are absent
     from both stack and spill domain. Hence these fixtures do not refute
     output freshness *after* PHIs. They do refute imposing ordinary
     dominance support on every stored name *before* PHIs.
   The selected-input-live-after-PHI variant fails phi_operands_ready;
     it is not a candidate reachable state under the frozen hypotheses.
   No example here certifies arbitrary residual prefixes or a universal
     support producer. In particular no emitted-code mismatch is claimed.
*)

(* Residual inventory diagnostics: an entry-defined live-through name. *)
Definition residual_diamond_fn_def:
  residual_diamond_fn = entry_probe_fn with fn_blocks :=
    LUPDATE ((EL 0 entry_probe_fn.fn_blocks) with bb_instructions :=
      [mk_inst 9 ADD [Lit 3w; Lit 4w] ["t"];
       mk_inst 0 JNZ [Lit 1w; Label "L"; Label "R"] []]) 0
    (LUPDATE ((EL 3 entry_probe_fn.fn_blocks) with bb_instructions :=
      [mk_inst 5 PHI [Label "L"; Var "a"; Label "R"; Var "b"] ["x"];
       mk_inst 6 ADD [Var "x"; Var "t"] ["y"];
       mk_inst 7 JMP [Label "exit"] []]) 3 entry_probe_fn.fn_blocks)
End

Definition residual_loop_fn_def:
  residual_loop_fn = entry_loop_fn with fn_blocks :=
    LUPDATE ((EL 0 entry_loop_fn.fn_blocks) with bb_instructions :=
      [mk_inst 7 ADD [Lit 3w; Lit 4w] ["t"];
       mk_inst 0 ADD [Lit 0w; Lit 1w] ["a"];
       mk_inst 1 JMP [Label "H"] []]) 0
    (LUPDATE ((EL 1 entry_loop_fn.fn_blocks) with bb_instructions :=
      [mk_inst 2 PHI [Label "entry"; Var "a"; Label "back"; Var "n"] ["x"];
       mk_inst 8 ADD [Lit 5w; Lit 2w] ["obsolete"];
       mk_inst 3 ADD [Var "x"; Var "t"] ["n"];
       mk_inst 4 JNZ [Lit 1w; Label "back"; Label "exit"] []])
       1 entry_loop_fn.fn_blocks)
End

Theorem residual_small_ready:
  EVERY (\fn. codegen_ready_fn fn /\
    EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb.bb_instructions) fn.fn_blocks)
    [residual_diamond_fn; residual_loop_fn]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac >>
  EVAL_TAC >> simp[]
QED

Definition residual_step_def:
  residual_step fn n ps = SND (THE (generate_block_plan
    (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn) fn
    (EL n fn.fn_blocks) ps))
End

Definition residual_incoming_def:
  residual_incoming fn n = residual_step fn n (residual_step fn 0 entry_probe_start)
End

Definition residual_phi_def:
  residual_phi fn n ps = SND (generate_phi_plan
    (HD (EL n fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze fn) (EL n fn.fn_blocks).bb_label 1) F ps)
End

Theorem residual_small_plan_success:
  EVERY (\fn. IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn)
    NONE [] fn 0 0)) [residual_diamond_fn; residual_loop_fn]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> conj_tac >> EVAL_TAC
QED

Theorem residual_diamond_inventory:
  (residual_incoming residual_diamond_fn 1).ps_stack = [Var "t"; Var "a"] /\
  (residual_phi residual_diamond_fn 3
    (residual_incoming residual_diamond_fn 1)).ps_stack = [Var "t"; Var "x"]
Proof
  conj_tac >> EVAL_TAC
QED

Definition residual_loop_incoming_def:
  residual_loop_incoming r =
    if r then residual_step residual_loop_fn 2 (residual_step residual_loop_fn 1
      (residual_step residual_loop_fn 0 entry_probe_start))
    else residual_step residual_loop_fn 0 entry_probe_start
End

Theorem residual_loop_inventory:
  (residual_loop_incoming F).ps_stack = [Var "t"; Var "a"] /\
  (residual_loop_incoming T).ps_stack = [Var "t"; Var "n"] /\
  EVERY (\r. (residual_phi residual_loop_fn 1 (residual_loop_incoming r)).ps_stack =
    [Var "t"; Var "x"] /\
    (residual_loop_incoming r).ps_spilled = FEMPTY /\
    (residual_phi residual_loop_fn 1 (residual_loop_incoming r)).ps_spilled = FEMPTY)
    [F;T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac >> EVAL_TAC
QED

Definition residual_pressure_names_def:
  residual_pressure_names =
    ["v00";"v01";"v02";"v03";"v04";"v05";"v06";"v07";"v08";
     "v09";"v10";"v11";"v12";"v13";"v14";"v15";"v16"]
End

Definition residual_pressure_fn_def:
  residual_pressure_fn = entry_probe_fn with fn_blocks :=
    LUPDATE ((EL 0 entry_probe_fn.fn_blocks) with bb_instructions :=
      GENLIST (\n. mk_inst (10+n) ADD [Lit 3w; Lit 4w]
        [EL n residual_pressure_names]) 17 ++
      [mk_inst 0 JNZ [Lit 1w; Label "L"; Label "R"] []]) 0
    (LUPDATE ((EL 3 entry_probe_fn.fn_blocks) with bb_instructions :=
      [mk_inst 5 PHI [Label "L"; Var "a"; Label "R"; Var "b"] ["x"];
       mk_inst 6 ADD [Var "x"; Lit 1w] ["y"]] ++
      GENLIST (\n. mk_inst (100+n) ADD [Var (EL n residual_pressure_names); Lit 1w]
        [STRCAT "dead_" (EL n residual_pressure_names)]) 17 ++ [mk_inst 7 JMP [Label "exit"] []])
      3 entry_probe_fn.fn_blocks)
End

Theorem residual_pressure_ready:
  codegen_ready_fn residual_pressure_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) residual_pressure_fn.fn_blocks
Proof
  conj_tac >> EVAL_TAC >> simp[]
QED

Theorem residual_pressure_plan_result:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze residual_pressure_fn) (dfg_build_function residual_pressure_fn)
    (cfg_analyze residual_pressure_fn) NONE [] residual_pressure_fn 0 0)
Proof
  CONV_TAC (PAT_CONV ``IS_SOME (generate_fn_plan_with_cleanup_analyzed
    lv dg cg NONE [] residual_pressure_fn 0 0)`` EVAL) >>
  EVAL_TAC
QED


