(* TOP-LEVEL: original compiler stages and computed result; no oracle bytes. *)
Theory evalCompilerBytecodeRaiseBareStages
Ancestors
  evalCompilerSubsetControlDeploy evalCompilerBytecodeStages venomSupplyEval
  venomMemLivenessEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val raise_bare_stage_goals = strip_conj (rhs (concl
  (SPEC ``raise_bare_program`` parity_stages_def)))
val () = if length raise_bare_stage_goals = 31 then ()
  else raise Fail "expected all31 original compiler stages"

Theorem raise_bare_stage_00[local]:
  ^(List.nth (raise_bare_stage_goals,0))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_01[local]:
  ^(List.nth (raise_bare_stage_goals,1))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_02[local]:
  ^(List.nth (raise_bare_stage_goals,2))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_03[local]:
  ^(List.nth (raise_bare_stage_goals,3))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_04[local]:
  ^(List.nth (raise_bare_stage_goals,4))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_05[local]:
  ^(List.nth (raise_bare_stage_goals,5))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_06[local]:
  ^(List.nth (raise_bare_stage_goals,6))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_07[local]:
  ^(List.nth (raise_bare_stage_goals,7))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_08[local]:
  ^(List.nth (raise_bare_stage_goals,8))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_09[local]:
  ^(List.nth (raise_bare_stage_goals,9))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_10[local]:
  ^(List.nth (raise_bare_stage_goals,10))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_11[local]:
  ^(List.nth (raise_bare_stage_goals,11))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_12[local]:
  ^(List.nth (raise_bare_stage_goals,12))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_13[local]:
  ^(List.nth (raise_bare_stage_goals,13))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_14[local]:
  ^(List.nth (raise_bare_stage_goals,14))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_15[local]:
  ^(List.nth (raise_bare_stage_goals,15))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_16[local]:
  ^(List.nth (raise_bare_stage_goals,16))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_17[local]:
  ^(List.nth (raise_bare_stage_goals,17))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_18[local]:
  ^(List.nth (raise_bare_stage_goals,18))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_19[local]:
  ^(List.nth (raise_bare_stage_goals,19))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_20[local]:
  ^(List.nth (raise_bare_stage_goals,20))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_21[local]:
  ^(List.nth (raise_bare_stage_goals,21))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_22[local]:
  ^(List.nth (raise_bare_stage_goals,22))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_23[local]:
  ^(List.nth (raise_bare_stage_goals,23))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_24[local]:
  ^(List.nth (raise_bare_stage_goals,24))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_25[local]:
  ^(List.nth (raise_bare_stage_goals,25))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_26[local]:
  ^(List.nth (raise_bare_stage_goals,26))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_27[local]:
  ^(List.nth (raise_bare_stage_goals,27))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_28[local]:
  ^(List.nth (raise_bare_stage_goals,28))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_29[local]:
  ^(List.nth (raise_bare_stage_goals,29))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stage_30[local]:
  ^(List.nth (raise_bare_stage_goals,30))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem raise_bare_stages:
  parity_stages raise_bare_program
Proof
  rewrite_tac[parity_stages_def] >>
  ACCEPT_TAC (LIST_CONJ
    [raise_bare_stage_00,
     raise_bare_stage_01,
     raise_bare_stage_02,
     raise_bare_stage_03,
     raise_bare_stage_04,
     raise_bare_stage_05,
     raise_bare_stage_06,
     raise_bare_stage_07,
     raise_bare_stage_08,
     raise_bare_stage_09,
     raise_bare_stage_10,
     raise_bare_stage_11,
     raise_bare_stage_12,
     raise_bare_stage_13,
     raise_bare_stage_14,
     raise_bare_stage_15,
     raise_bare_stage_16,
     raise_bare_stage_17,
     raise_bare_stage_18,
     raise_bare_stage_19,
     raise_bare_stage_20,
     raise_bare_stage_21,
     raise_bare_stage_22,
     raise_bare_stage_23,
     raise_bare_stage_24,
     raise_bare_stage_25,
     raise_bare_stage_26,
     raise_bare_stage_27,
     raise_bare_stage_28,
     raise_bare_stage_29,
     raise_bare_stage_30])
QED

Theorem raise_bare_compiles:
  IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities) raise_bare_program)
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("FIXTURE_STAGE_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "compiler fixture has kernel assumptions or admission tags"
end) [("raise_bare_stages",raise_bare_stages),
       ("raise_bare_compiles",raise_bare_compiles)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (_,equation) => same_const
    (fst (strip_comb (lhs (concl equation))))
    (prim_mk_const {Thy="compileVyper",Name="compile_vyper"}))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = if null (!evalCompilerBytecodeLib.pending_stage_values) then
  raise Fail "completed compiler equation missing" else ()
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
