(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeControlForBreakStages
Ancestors evalCompiler compileVyper evalCompilerBytecodeStages concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

val () = evalCompilerBytecodeLib.configure_pass_stages ()

Theorem for_break_stages:
  parity_stages for_break_program
Proof
  rewrite_tac[parity_stages_def] >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >-
   (evalCompilerBytecodeLib.prepare_function_analysis ``liveness_analyze`` >> evalCompilerBytecodeLib.prepare_function_analysis ``cfg_analyze`` >>
    evalCompilerBytecodeLib.cache_checkpoint) >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >-
   (evalCompilerBytecodeLib.prepare_closed_call ``def_dominates_uses (HD ((FST (parity_walk_result for_break_program)).cu_context.ctx_functions))`` >>
    evalCompilerBytecodeLib.cache_checkpoint) >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >-
   (evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.cache_checkpoint) >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >-
   (evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >> evalCompilerBytecodeLib.warm_planner_step >>
    evalCompilerBytecodeLib.cache_checkpoint) >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()
