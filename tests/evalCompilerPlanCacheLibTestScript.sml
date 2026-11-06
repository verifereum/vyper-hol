(* Cleanup guards must compute regional growth and numeric height bounds while
   preserving the large immutable IR/analysis records. *)
Theory evalCompilerPlanCacheLibTest
Ancestors
  compileVyper stackPlanGen
Libs
  evalCompilerBoundedLib

val halt_block = rhs (concl (EVAL
  ``<|bb_label := "entry"; bb_instructions := [mk_inst 0 STOP [] []]|>``));
val halt_function = rhs (concl (EVAL
  ``mk_raw_function "halt" [^halt_block]``));
val halt_cfg = rhs (concl (EVAL ``cfg_analyze ^halt_function``));
val () = entry_plan_summary_thms := [];
val () = entry_plan_cache_call "must_halt_labels" [halt_cfg,halt_function];

Theorem cleanup_guard_computes_regional_growth:
  (if cleanup_elision_safe (SOME 0) [] ^halt_cfg ^halt_function ^halt_block 0
   then T else F) = T
Proof
  CONV_TAC (LAND_CONV entry_plan_cleanup_guard) >> simp[]
QED

Theorem cleanup_guard_checks_height_bound:
  (if cleanup_elision_safe (SOME 0) [] ^halt_cfg ^halt_function ^halt_block 1022
   then T else F) = T /\
  (if cleanup_elision_safe (SOME 0) [] ^halt_cfg ^halt_function ^halt_block 1023
   then T else F) = F /\
  (if cleanup_elision_safe NONE [] ^halt_cfg ^halt_function ^halt_block 0
   then T else F) = F
Proof
  rpt CONJ_TAC >> CONV_TAC (LAND_CONV entry_plan_cleanup_guard) >> simp[]
QED

(* The guard's new regional summary must be cached, not expanded by the
   read-only evaluator. This assertion fails under the obsolete staging. *)
val cached_region_growth = valOf (List.find (fn th =>
  same_const (fst (strip_comb (lhs (concl th))))
    ``stackPlanGen$cleanup_region_growth``) (!entry_plan_summary_thms));
val _ = save_thm ("cleanup_region_growth_cached", cached_region_growth);
