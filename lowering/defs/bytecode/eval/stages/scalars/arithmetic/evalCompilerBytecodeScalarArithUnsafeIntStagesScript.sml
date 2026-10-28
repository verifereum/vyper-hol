(* TOP-LEVEL: original compiler stages and computed result; no oracle bytes. *)
Theory evalCompilerBytecodeScalarArithUnsafeIntStages
Ancestors
  evalCompilerBytecodeScalarWordEval
  evalCompilerSubsetScalars evalCompilerBytecodeStages venomSupplyEval
  venomMemLivenessEval compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (computeLib.add_thms [scalar_decimal_type_bounds_eval,
    w2n_scalar_decimal_lo_word_eval, w2n_scalar_decimal_hi_word_eval])
val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()
val () = evalCompilerBytecodeLib.configure_pass_stages ()
val scalar_arith_unsafe_int_stage_goals = strip_conj (rhs (concl
  (SPEC ``scalar_arith_unsafe_int_program`` parity_stages_def)))
val () = if length scalar_arith_unsafe_int_stage_goals = 31 then ()
  else raise Fail "expected all31 original compiler stages"

Theorem scalar_arith_unsafe_int_stage_00[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,0))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_01[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,1))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_02[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,2))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_03[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,3))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_04[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,4))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_05[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,5))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_06[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,6))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_07[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,7))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_08[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,8))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_09[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,9))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_10[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,10))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_11[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,11))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_12[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,12))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_13[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,13))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_14[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,14))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_15[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,15))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_16[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,16))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_17[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,17))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_18[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,18))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_19[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,19))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_20[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,20))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_21[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,21))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_22[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,22))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_23[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,23))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_24[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,24))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_25[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,25))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_26[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,26))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_27[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,27))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_28[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,28))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_29[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,29))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stage_30[local]:
  ^(List.nth (scalar_arith_unsafe_int_stage_goals,30))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_arith_unsafe_int_stages:
  parity_stages scalar_arith_unsafe_int_program
Proof
  rewrite_tac[parity_stages_def] >>
  ACCEPT_TAC (LIST_CONJ
    [scalar_arith_unsafe_int_stage_00,
     scalar_arith_unsafe_int_stage_01,
     scalar_arith_unsafe_int_stage_02,
     scalar_arith_unsafe_int_stage_03,
     scalar_arith_unsafe_int_stage_04,
     scalar_arith_unsafe_int_stage_05,
     scalar_arith_unsafe_int_stage_06,
     scalar_arith_unsafe_int_stage_07,
     scalar_arith_unsafe_int_stage_08,
     scalar_arith_unsafe_int_stage_09,
     scalar_arith_unsafe_int_stage_10,
     scalar_arith_unsafe_int_stage_11,
     scalar_arith_unsafe_int_stage_12,
     scalar_arith_unsafe_int_stage_13,
     scalar_arith_unsafe_int_stage_14,
     scalar_arith_unsafe_int_stage_15,
     scalar_arith_unsafe_int_stage_16,
     scalar_arith_unsafe_int_stage_17,
     scalar_arith_unsafe_int_stage_18,
     scalar_arith_unsafe_int_stage_19,
     scalar_arith_unsafe_int_stage_20,
     scalar_arith_unsafe_int_stage_21,
     scalar_arith_unsafe_int_stage_22,
     scalar_arith_unsafe_int_stage_23,
     scalar_arith_unsafe_int_stage_24,
     scalar_arith_unsafe_int_stage_25,
     scalar_arith_unsafe_int_stage_26,
     scalar_arith_unsafe_int_stage_27,
     scalar_arith_unsafe_int_stage_28,
     scalar_arith_unsafe_int_stage_29,
     scalar_arith_unsafe_int_stage_30])
QED

Theorem scalar_arith_unsafe_int_compiles:
  IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities) scalar_arith_unsafe_int_program)
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("FIXTURE_STAGE_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "compiler fixture has kernel assumptions or admission tags"
end) [("scalar_arith_unsafe_int_stages",scalar_arith_unsafe_int_stages),
       ("scalar_arith_unsafe_int_compiles",scalar_arith_unsafe_int_compiles)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (_,equation) => same_const
    (fst (strip_comb (lhs (concl equation))))
    (prim_mk_const {Thy="compileVyper",Name="compile_vyper"}))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = if null (!evalCompilerBytecodeLib.pending_stage_values) then
  raise Fail "completed compiler equation missing" else ()
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
