(* Checked runtime-pipeline staging for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEventsPipeline
Ancestors
  evalCompilerBytecodeAbiEventsCodegenReady
  evalCompilerBytecodeAbiEventsWalkPipeline
  evalCompilerBytecodeAbiEventsPrePipeline
  evalCompilerBytecodeAbiEventsLowering
  evalCompilerSubsetAbiEvents
  compileVyper
  concretizeMemLocDefs
  alist
  byte
  integer_word
  option
  cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_mixed_event_types,
     word_of_bytes_bytes32_mixed_event_types,
     w2n_mixed_event_types_n2w,
     contextTheory.compile_copy_memory_def])

Definition mixed_event_types_runtime_pipeline_def:
  mixed_event_types_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

Definition mixed_event_types_runtime_compile_def:
  mixed_event_types_runtime_compile tops =
    case mixed_event_types_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

Definition mixed_event_types_deploy_compile_def:
  mixed_event_types_deploy_compile tops runtime =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_deploy_unit tops rpolicy runtime of
          NONE => NONE
        | SOME unit =>
            checked_unit_pipeline
              (λrp u. run_venom_pipeline (K T) (K T) (K T)
                 rp o1_pipeline_spec u)
              (K SOME) rpolicy unit
End

val mixed_event_types_rpolicy = optionSyntax.dest_some
  (rhs (concl mixed_event_types_policy_eval))
val mixed_event_types_runtime_unit = optionSyntax.dest_some
  (rhs (concl mixed_event_types_runtime_unit_eval))
val mixed_event_types_pre_pair = optionSyntax.dest_some
  (rhs (concl mixed_event_types_pre_walk_eval))
val mixed_event_types_pre_unit = #1 (pairSyntax.dest_pair mixed_event_types_pre_pair)
val mixed_event_types_fcg = rhs (concl mixed_event_types_fcg_eval)
val mixed_event_types_walk_unit = rhs (concl mixed_event_types_walk_unit_eval)
val mixed_event_types_names = rhs (concl mixed_event_types_names_eval)
val mixed_event_types_walk_pair = optionSyntax.dest_some
  (rhs (concl mixed_event_types_walk_eval))
val mixed_event_types_final_unit =
  #1 (pairSyntax.dest_pair mixed_event_types_walk_pair)
val mixed_event_types_final_supply =
  #2 (pairSyntax.dest_pair mixed_event_types_walk_pair)
val mixed_event_types_initial_checks_eval = EVAL
  ``pipeline_spec_wf ^mixed_event_types_rpolicy o1_pipeline_spec /\
    unit_wf ^mixed_event_types_runtime_unit /\
    raw_static_inputs_wf (^mixed_event_types_runtime_unit).cu_context``
val mixed_event_types_pre_acyclic_eval = EVAL
  ``reachable_fcg_acyclic (^mixed_event_types_pre_unit).cu_context
      ^mixed_event_types_fcg``
val mixed_event_types_entry_eval = EVAL
  ``(^mixed_event_types_pre_unit).cu_context.ctx_entry``
val mixed_event_types_post_walk_eval = EVAL
  ``run_pipeline_stages ^mixed_event_types_rpolicy
      o1_pipeline_spec.ps_post_walk_stages
      ^mixed_event_types_final_unit ^mixed_event_types_final_supply``
val mixed_event_types_final_unit_wf_eval =
  EVAL ``unit_wf ^mixed_event_types_final_unit``
val mixed_event_types_final_labels_wf_eval =
  EVAL ``unit_labels_wf ^mixed_event_types_final_unit``
val mixed_event_types_final_target_safe_eval = EVAL
  ``context_target_safe (^mixed_event_types_rpolicy).rpol_target
      (^mixed_event_types_final_unit).cu_context``
val mixed_event_types_final_static_layout_eval = EVAL
  ``concretized_static_layouts_wf
      (^mixed_event_types_final_unit).cu_context``
val mixed_event_types_final_fmp_eval = EVAL
  ``fmp_lowered_context_wf (^mixed_event_types_final_unit).cu_context``
val mixed_event_types_final_fcg_eval = EVAL
  ``fcg_analyze (^mixed_event_types_final_unit).cu_context``
val mixed_event_types_final_acyclic_eval = EVAL
  ``reachable_fcg_acyclic (^mixed_event_types_final_unit).cu_context
      ^(rhs (concl mixed_event_types_final_fcg_eval))``
val () = computeLib.upd_compset (computeLib.add_thms
  [mixed_event_types_initial_checks_eval,
   mixed_event_types_supply_eval,
   mixed_event_types_pre_walk_eval,
   mixed_event_types_fcg_eval,
   mixed_event_types_walk_unit_eval,
   mixed_event_types_pre_acyclic_eval,
   mixed_event_types_entry_eval,
   mixed_event_types_names_eval,
   mixed_event_types_walk_eval,
   mixed_event_types_post_walk_eval,
   mixed_event_types_final_unit_wf_eval,
   mixed_event_types_final_labels_wf_eval,
   mixed_event_types_final_target_safe_eval,
   mixed_event_types_final_static_layout_eval,
   mixed_event_types_final_fmp_eval,
   mixed_event_types_final_fcg_eval,
   mixed_event_types_final_acyclic_eval,
   mixed_event_types_final_codegen_ready_eval])
val mixed_event_types_post_stages_stage_eval =
  EVAL ``o1_pipeline_spec.ps_post_walk_stages``
val mixed_event_types_rpolicy_target_stage_eval =
  EVAL ``(^mixed_event_types_rpolicy).rpol_target``
val mixed_event_types_pipeline_stage_rules =
  [mixed_event_types_initial_checks_eval,
   mixed_event_types_supply_eval,
   mixed_event_types_pre_walk_eval,
   mixed_event_types_fcg_eval,
   mixed_event_types_walk_unit_eval,
   mixed_event_types_pre_acyclic_eval,
   mixed_event_types_entry_eval,
   mixed_event_types_names_eval,
   SIMP_RULE pure_ss [venomPassScheduleTheory.o1_fn_passes_def]
     mixed_event_types_walk_eval,
   REWRITE_RULE [mixed_event_types_post_stages_stage_eval]
     mixed_event_types_post_walk_eval,
   mixed_event_types_final_unit_wf_eval,
   mixed_event_types_final_labels_wf_eval,
   REWRITE_RULE [mixed_event_types_rpolicy_target_stage_eval]
     mixed_event_types_final_target_safe_eval,
   mixed_event_types_final_static_layout_eval,
   mixed_event_types_final_fmp_eval,
   mixed_event_types_final_fcg_eval,
   mixed_event_types_final_acyclic_eval,
   mixed_event_types_final_codegen_ready_eval]
val mixed_event_types_pipeline_stage_rules =
  map EQT_INTRO (CONJUNCTS
    (EQT_ELIM (hd mixed_event_types_pipeline_stage_rules))) @
  tl mixed_event_types_pipeline_stage_rules
val mixed_event_types_pipeline_stage_rules =
  map (fn th => if boolSyntax.is_eq (concl th) then th else EQT_INTRO th)
    mixed_event_types_pipeline_stage_rules
val mixed_event_types_spec_prune_eval =
  EVAL ``o1_pipeline_spec.ps_prune_unreachable``
val mixed_event_types_spec_require_acyclic_eval =
  EVAL ``o1_pipeline_spec.ps_require_acyclic_calls``
val mixed_event_types_spec_fn_passes_eval =
  EVAL ``o1_pipeline_spec.ps_fn_passes``
val mixed_event_types_spec_post_stages_eval =
  EVAL ``o1_pipeline_spec.ps_post_walk_stages``
val mixed_event_types_spec_final_assembly_eval =
  EVAL ``o1_pipeline_spec.ps_final_assembly``
val mixed_event_types_rpolicy_target_eval =
  EVAL ``(^mixed_event_types_rpolicy).rpol_target``
val mixed_event_types_pipeline_admin_rules =
  [mixed_event_types_spec_prune_eval,
   mixed_event_types_spec_require_acyclic_eval,
   mixed_event_types_spec_fn_passes_eval,
   mixed_event_types_spec_post_stages_eval,
   mixed_event_types_spec_final_assembly_eval,
   mixed_event_types_rpolicy_target_eval,
   LET_THM, COND_CLAUSES, NOT_CLAUSES,
   optionTheory.option_case_compute, pairTheory.pair_case_thm,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF]
val mixed_event_types_pipeline_admin_rewrites =
  List.concat (map (CONJUNCTS o SPEC_ALL)
    mixed_event_types_pipeline_admin_rules)
val mixed_event_types_admin_conv = FIRST_CONV
  (BETA_CONV :: map REWR_CONV mixed_event_types_pipeline_admin_rewrites)
fun mixed_event_types_repeat_admin 0 tm = REFL tm
  | mixed_event_types_repeat_admin n tm =
      (case total (ONCE_DEPTH_CONV mixed_event_types_admin_conv) tm of
         NONE => REFL tm
       | SOME th => TRANS th
           (mixed_event_types_repeat_admin (n - 1) (rhs (concl th))))
fun mixed_event_types_apply_stage stage_th current = let
  val current_rhs = rhs (concl current)
  val staged = ONCE_DEPTH_CONV (REWR_CONV stage_th) current_rhs
  val admin = mixed_event_types_repeat_admin 20 (rhs (concl staged))
in
  TRANS current (TRANS staged admin)
end
val mixed_event_types_pipeline_initial = SIMP_CONV pure_ss
  [venomPipelineDriverTheory.run_venom_pipeline_def]
  ``run_venom_pipeline (K T) (K T) (K T)
      ^mixed_event_types_rpolicy o1_pipeline_spec
      ^mixed_event_types_runtime_unit``
fun mixed_event_types_apply_stages _ current [] = current
  | mixed_event_types_apply_stages n current (stage_th::rest) = let
      val next = mixed_event_types_apply_stage stage_th current
    in mixed_event_types_apply_stages (n + 1) next rest end
val mixed_event_types_pipeline_result =
  mixed_event_types_apply_stages 0 mixed_event_types_pipeline_initial
    mixed_event_types_pipeline_stage_rules
val mixed_event_types_pipeline_run_eval = save_thm
  ("mixed_event_types_pipeline_run_eval",
   mixed_event_types_pipeline_result)
val mixed_event_types_runtime_admin_rules =
  [mixed_event_types_runtime_pipeline_def,
   mixed_event_types_policy_eval,
   mixed_event_types_runtime_unit_eval,
   optionTheory.option_case_compute, pairTheory.pair_case_thm,
   LET_THM, COND_CLAUSES]
fun mixed_event_types_repeat_runtime_admin tm =
  case total (SIMP_CONV pure_ss mixed_event_types_runtime_admin_rules) tm of
    NONE => REFL tm
  | SOME th =>
      let val next = rhs (concl th) in
        TRANS th (mixed_event_types_repeat_runtime_admin next)
      end
val mixed_event_types_runtime_pipeline_step1 =
  mixed_event_types_repeat_runtime_admin
    ``mixed_event_types_runtime_pipeline task090_mixed_event_types_program``
val mixed_event_types_runtime_pipeline_rhs1 =
  rhs (concl mixed_event_types_runtime_pipeline_step1)
val mixed_event_types_runtime_pipeline_step2 =
  (case total (PURE_REWRITE_CONV [mixed_event_types_pipeline_run_eval])
          mixed_event_types_runtime_pipeline_rhs1 of
     SOME th => th | NONE => REFL mixed_event_types_runtime_pipeline_rhs1)
val mixed_event_types_runtime_pipeline_rhs2 =
  rhs (concl mixed_event_types_runtime_pipeline_step2)
val mixed_event_types_runtime_actual_run = find_term
  (can (match_term ``run_venom_pipeline a b c rp spec unit``))
  mixed_event_types_runtime_pipeline_rhs2
fun mixed_event_types_pipeline_w2n_eval w =
  if same_const (#1 (strip_comb w)) ``set_byte`` then let
    val bytes_th = SIMP_CONV (srw_ss())
      [word_to_bytes_be_bytes32_genlist_mixed_event_types,
       get_byte_set_byte_bytes32_mixed_event_types,
       get_byte_set_byte_irrelevant_bytes32_mixed_event_types]
      ``word_to_bytes_be ^w``
    val roundtrip = INST [``w:bytes32`` |-> w]
      word_of_bytes_be_word_to_bytes_be_mixed_event_types
    val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x`` (SYM roundtrip))
    val step2 = BETA_RULE (AP_TERM
      ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
    val decoded = TRANS step1 step2
    val expose = SIMP_CONV bool_ss
      [word_of_bytes_be_bytes32_mixed_event_types,
       w2n_mixed_event_types_n2w] (rhs (concl decoded))
  in TRANS decoded (TRANS expose (EVAL (rhs (concl expose)))) end
  else EVAL ``w2n ^w``
fun mixed_event_types_pipeline_normalize_word w = let
  val w2n_th = mixed_event_types_pipeline_w2n_eval w
  val numeral = rhs (concl w2n_th)
  val normalized = ``mixed_event_types_n2w ^numeral``
  val norm_step = INST [``n:num`` |-> numeral] w2n_mixed_event_types_n2w
  val norm_w2n = TRANS norm_step (EVAL (rhs (concl norm_step)))
in
  EQ_MP (ISPECL [w,normalized] wordsTheory.w2n_11)
    (TRANS w2n_th (SYM norm_w2n))
end
fun mixed_event_types_pipeline_literal_words tm =
  List.foldl (fn (lit,ws) => let val w = #2 (dest_comb lit) in
      if List.exists (aconv w) ws then ws else w::ws end) []
    (find_terms (can (match_term ``Lit (set_byte a b w be : bytes32)``)) tm)
val mixed_event_types_runtime_expected_run =
  lhs (concl mixed_event_types_pipeline_run_eval)
val (mixed_event_types_runtime_actual_rator,
     mixed_event_types_runtime_actual_unit) =
  dest_comb mixed_event_types_runtime_actual_run
val (mixed_event_types_runtime_expected_rator,
     mixed_event_types_runtime_expected_unit) =
  dest_comb mixed_event_types_runtime_expected_run
val mixed_event_types_runtime_actual_fn = rhs (concl (EVAL
  ``HD (^mixed_event_types_runtime_actual_unit).cu_context.ctx_functions``))
val mixed_event_types_runtime_expected_fn = rhs (concl (EVAL
  ``HD (^mixed_event_types_runtime_expected_unit).cu_context.ctx_functions``))
val mixed_event_types_runtime_fn_words =
  mixed_event_types_pipeline_literal_words mixed_event_types_runtime_actual_fn @
  mixed_event_types_pipeline_literal_words mixed_event_types_runtime_expected_fn
val mixed_event_types_runtime_fn_normalizations =
  map mixed_event_types_pipeline_normalize_word
    (List.foldl (fn (w,ws) => if List.exists (aconv w) ws then ws else w::ws)
      [] mixed_event_types_runtime_fn_words)
val mixed_event_types_runtime_fn_eq_step = SIMP_CONV (srw_ss())
  mixed_event_types_runtime_fn_normalizations
  ``^mixed_event_types_runtime_actual_fn =
    ^mixed_event_types_runtime_expected_fn``
val mixed_event_types_runtime_fn_eq = EQT_ELIM
  (TRANS mixed_event_types_runtime_fn_eq_step
    (EVAL (rhs (concl mixed_event_types_runtime_fn_eq_step))))
val mixed_event_types_runtime_unit_reduce =
  EVAL mixed_event_types_runtime_actual_unit
val mixed_event_types_runtime_unit_eq_step = SIMP_CONV (srw_ss())
  [mixed_event_types_runtime_fn_eq]
  ``^(rhs (concl mixed_event_types_runtime_unit_reduce)) =
    ^mixed_event_types_runtime_expected_unit``
val mixed_event_types_runtime_unit_semantic_eq = EQT_ELIM
  (TRANS mixed_event_types_runtime_unit_eq_step
    (EVAL (rhs (concl mixed_event_types_runtime_unit_eq_step))))
val mixed_event_types_runtime_unit_eq =
  TRANS mixed_event_types_runtime_unit_reduce
    mixed_event_types_runtime_unit_semantic_eq
val mixed_event_types_runtime_actual_rator_eval =
  EVAL mixed_event_types_runtime_actual_rator
val mixed_event_types_runtime_expected_rator_eval =
  EVAL mixed_event_types_runtime_expected_rator
val mixed_event_types_runtime_rator_eq =
  TRANS mixed_event_types_runtime_actual_rator_eval
    (SYM mixed_event_types_runtime_expected_rator_eval)
val mixed_event_types_runtime_run_eq =
  MK_COMB (mixed_event_types_runtime_rator_eq,
           mixed_event_types_runtime_unit_eq)
val mixed_event_types_runtime_actual_run_eval =
  TRANS mixed_event_types_runtime_run_eq mixed_event_types_pipeline_run_eval
val mixed_event_types_runtime_pipeline_step2 = PURE_REWRITE_CONV
  [mixed_event_types_runtime_actual_run_eval]
  mixed_event_types_runtime_pipeline_rhs1
val mixed_event_types_runtime_pipeline_rhs2 =
  rhs (concl mixed_event_types_runtime_pipeline_step2)
val mixed_event_types_runtime_pipeline_step3 =
  (case total EVAL mixed_event_types_runtime_pipeline_rhs2 of
     SOME th => th | NONE => REFL mixed_event_types_runtime_pipeline_rhs2)
val mixed_event_types_runtime_pipeline_eval = save_thm
  ("mixed_event_types_runtime_pipeline_eval",
   TRANS mixed_event_types_runtime_pipeline_step1
     (TRANS mixed_event_types_runtime_pipeline_step2
       mixed_event_types_runtime_pipeline_step3))
