(* TOP-LEVEL: original compiler stages and computed result; no oracle bytes. *)
Theory evalCompilerBytecodeScalarMinmaxIntStages
Ancestors
  evalCompilerBytecodeScalarMinmaxIntPlanningPrefix evalCompilerBytecodeScalarMinmaxIntPlanning
  evalCompilerBytecodeScalarMinmaxIntPipeline evalCompilerBytecodeScalarMinmaxIntReadiness
  evalCompilerBytecodeScalarMinmaxIntDft
  evalCompilerBytecodeScalarMinmaxIntLowering evalCompilerBytecodeScalarMinmaxIntPrefix
  evalCompilerSubsetScalars evalCompilerBytecodeStages venomSupplyEval
  venomMemLivenessEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val scalar_minmax_int_stage_goals = strip_conj (rhs (concl
  (SPEC ``scalar_minmax_int_program`` parity_stages_def)))
val () = if length scalar_minmax_int_stage_goals = 31 then ()
  else raise Fail "expected all31 original compiler stages"

val () = app evalCompilerBytecodeLib.restore_stage_values
  ["evalCompilerBytecodeScalarMinmaxIntLowering",
   "evalCompilerBytecodeScalarMinmaxIntPrefix",
   "evalCompilerBytecodeScalarMinmaxIntDft",
   "evalCompilerBytecodeScalarMinmaxIntPipeline",
   "evalCompilerBytecodeScalarMinmaxIntReadiness",
   "evalCompilerBytecodeScalarMinmaxIntPlanningPrefix",
   "evalCompilerBytecodeScalarMinmaxIntPlanning"]

Theorem scalar_minmax_int_stage_25[local]:
  ^(List.nth (scalar_minmax_int_stage_goals,25))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_26[local]:
  ^(List.nth (scalar_minmax_int_stage_goals,26))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_27[local]:
  ^(List.nth (scalar_minmax_int_stage_goals,27))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_28[local]:
  ^(List.nth (scalar_minmax_int_stage_goals,28))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_29[local]:
  ^(List.nth (scalar_minmax_int_stage_goals,29))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stage_30[local]:
  ^(List.nth (scalar_minmax_int_stage_goals,30))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_minmax_int_stages:
  parity_stages scalar_minmax_int_program
Proof
  rewrite_tac[parity_stages_def] >>
  ACCEPT_TAC (LIST_CONJ
    [scalar_minmax_int_stage_00,
     scalar_minmax_int_stage_01,
     scalar_minmax_int_stage_02,
     scalar_minmax_int_stage_03,
     scalar_minmax_int_stage_04,
     scalar_minmax_int_stage_05,
     scalar_minmax_int_stage_06,
     scalar_minmax_int_stage_07,
     scalar_minmax_int_stage_08,
     scalar_minmax_int_stage_09,
     scalar_minmax_int_stage_10,
     scalar_minmax_int_stage_11,
     scalar_minmax_int_stage_12,
     scalar_minmax_int_stage_13,
     scalar_minmax_int_stage_14,
     scalar_minmax_int_stage_15,
     scalar_minmax_int_stage_16,
     scalar_minmax_int_stage_17,
     scalar_minmax_int_stage_18,
     scalar_minmax_int_stage_19,
     scalar_minmax_int_stage_20,
     scalar_minmax_int_stage_21,
     scalar_minmax_int_stage_22,
     scalar_minmax_int_stage_23,
     scalar_minmax_int_stage_24,
     scalar_minmax_int_stage_25,
     scalar_minmax_int_stage_26,
     scalar_minmax_int_stage_27,
     scalar_minmax_int_stage_28,
     scalar_minmax_int_stage_29,
     scalar_minmax_int_stage_30])
QED

Theorem scalar_minmax_int_compiles:
  IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities) scalar_minmax_int_program)
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("FIXTURE_STAGE_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "compiler fixture has kernel assumptions or admission tags"
end) [("scalar_minmax_int_stages",scalar_minmax_int_stages),
       ("scalar_minmax_int_compiles",scalar_minmax_int_compiles)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (_,equation) => same_const
    (fst (strip_comb (lhs (concl equation))))
    (prim_mk_const {Thy="compileVyper",Name="compile_vyper"}))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = if null (!evalCompilerBytecodeLib.pending_stage_values) then
  raise Fail "completed compiler equation missing" else ()
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
