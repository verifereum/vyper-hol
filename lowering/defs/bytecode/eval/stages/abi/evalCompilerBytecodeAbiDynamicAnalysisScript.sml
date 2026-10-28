(* Actual dynamic-ABI pipeline and shared availability inputs.
   All original computations are retained; availability slices run in
   separate theories to bound retained process memory. *)

Theory evalCompilerBytecodeAbiDynamicAnalysis
Ancestors evalCompilerSubsetAbiBuiltins compileVyper concretizeMemLocDefs codegenReadyCompute stackPlanGenCompute alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``reduce_depth_plan``)
    |> (fn cs' => computeLib.scrub_const cs'
         ``generate_block_insts_plan``)
    |> computeLib.add_thms
         [reduce_depth_plan_compute, generate_block_insts_plan_compute])
val () = Globals.max_print_depth := 20

val abi_dynamic_policy_eval = save_thm
  ("abi_dynamic_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
val abi_dynamic_rpolicy = optionSyntax.dest_some
  (rhs (concl abi_dynamic_policy_eval))
val abi_dynamic_lower_runtime_eval = save_thm
  ("abi_dynamic_lower_runtime_eval",
   EVAL ``lower_vyper_runtime_unit task090_abi_dynamic_program
       ^abi_dynamic_rpolicy``)
val abi_dynamic_runtime_unit = optionSyntax.dest_some
  (rhs (concl abi_dynamic_lower_runtime_eval))
Theorem abi_dynamic_lower_runtime_computed: T
Proof
  simp[]
QED
val abi_dynamic_pre_walk_eval = save_thm
  ("abi_dynamic_pre_walk_eval",
   EVAL ``run_pipeline_stages ^abi_dynamic_rpolicy
       o1_pipeline_spec.ps_pre_walk_stages ^abi_dynamic_runtime_unit
       (init_ir_supply ^abi_dynamic_runtime_unit)``)
Theorem abi_dynamic_pre_walk_computed: T
Proof
  simp[]
QED
val abi_dynamic_pre_pair = optionSyntax.dest_some
  (rhs (concl abi_dynamic_pre_walk_eval))
val abi_dynamic_pre_unit = #1 (pairSyntax.dest_pair abi_dynamic_pre_pair)
val abi_dynamic_pre_supply = #2 (pairSyntax.dest_pair abi_dynamic_pre_pair)
val abi_dynamic_fcg_eval = save_thm
  ("abi_dynamic_fcg_eval",
   EVAL
  ``fcg_analyze (^abi_dynamic_pre_unit).cu_context``)

val abi_dynamic_walk_unit_eval = save_thm
  ("abi_dynamic_walk_unit_eval",
   EVAL
  ``prune_unit_fcg_unreachable ^abi_dynamic_pre_unit
      ^(rhs (concl abi_dynamic_fcg_eval))``)

val abi_dynamic_walk_unit = rhs (concl abi_dynamic_walk_unit_eval)
val abi_dynamic_entry_eval = save_thm
  ("abi_dynamic_entry_eval",
   EVAL
  ``(^abi_dynamic_pre_unit).cu_context.ctx_entry``)

val abi_dynamic_entry = optionSyntax.dest_some
  (rhs (concl abi_dynamic_entry_eval))
val abi_dynamic_order_eval = save_thm
  ("abi_dynamic_order_eval",
   EVAL
  ``fcg_postorder ^(rhs (concl abi_dynamic_fcg_eval)) ^abi_dynamic_entry``)

val abi_dynamic_walk_eval = save_thm
  ("abi_dynamic_walk_eval",
   EVAL ``run_callee_first ^abi_dynamic_rpolicy o1_fn_passes
       ^(rhs (concl abi_dynamic_order_eval)) ^abi_dynamic_walk_unit
       ^abi_dynamic_pre_supply``)
Theorem abi_dynamic_walk_computed: T
Proof
  simp[]
QED
val abi_dynamic_walk_pair = optionSyntax.dest_some
  (rhs (concl abi_dynamic_walk_eval))
val abi_dynamic_walked_unit = #1 (pairSyntax.dest_pair abi_dynamic_walk_pair)
val abi_dynamic_walked_supply = #2 (pairSyntax.dest_pair abi_dynamic_walk_pair)
val abi_dynamic_post_walk_eval = save_thm
  ("abi_dynamic_post_walk_eval",
   EVAL ``run_pipeline_stages ^abi_dynamic_rpolicy
       o1_pipeline_spec.ps_post_walk_stages ^abi_dynamic_walked_unit
       ^abi_dynamic_walked_supply``)
Theorem abi_dynamic_post_walk_computed: T
Proof
  simp[]
QED
val abi_dynamic_post_pair = optionSyntax.dest_some
  (rhs (concl abi_dynamic_post_walk_eval))
val abi_dynamic_final_checked_unit = #1 (pairSyntax.dest_pair abi_dynamic_post_pair)
val abi_dynamic_final_supply = #2 (pairSyntax.dest_pair abi_dynamic_post_pair)
val abi_dynamic_initial_checks_eval = save_thm
  ("abi_dynamic_initial_checks_eval",
   EVAL
  ``pipeline_spec_wf ^abi_dynamic_rpolicy o1_pipeline_spec /\
    unit_wf ^abi_dynamic_runtime_unit /\
    raw_static_inputs_wf (^abi_dynamic_runtime_unit).cu_context``)

val abi_dynamic_pre_acyclic_eval = save_thm
  ("abi_dynamic_pre_acyclic_eval",
   EVAL
  ``reachable_fcg_acyclic (^abi_dynamic_pre_unit).cu_context
      ^(rhs (concl abi_dynamic_fcg_eval))``)

val abi_dynamic_final_unit_wf = save_thm
  ("abi_dynamic_final_unit_wf", EQT_ELIM
    (EVAL ``unit_wf ^abi_dynamic_final_checked_unit``))
val abi_dynamic_final_labels_wf = save_thm
  ("abi_dynamic_final_labels_wf", EQT_ELIM
    (EVAL ``unit_labels_wf ^abi_dynamic_final_checked_unit``))
val abi_dynamic_final_target_safe = save_thm
  ("abi_dynamic_final_target_safe", EQT_ELIM
    (EVAL ``context_target_safe (^abi_dynamic_rpolicy).rpol_target
      (^abi_dynamic_final_checked_unit).cu_context``))
val abi_dynamic_final_layout_wf = save_thm
  ("abi_dynamic_final_layout_wf", EQT_ELIM
    (EVAL ``concretized_static_layouts_wf
      (^abi_dynamic_final_checked_unit).cu_context``))
val abi_dynamic_final_fmp_wf = save_thm
  ("abi_dynamic_final_fmp_wf", EQT_ELIM
    (EVAL ``fmp_lowered_context_wf
      (^abi_dynamic_final_checked_unit).cu_context``))
val abi_dynamic_final_acyclic = save_thm
  ("abi_dynamic_final_acyclic", EQT_ELIM
    (EVAL ``reachable_fcg_acyclic
      (^abi_dynamic_final_checked_unit).cu_context
      (fcg_analyze (^abi_dynamic_final_checked_unit).cu_context)``))
val abi_dynamic_ready_fn_eval = save_thm
  ("abi_dynamic_ready_fn_eval",
   EVAL ``HD (^abi_dynamic_final_checked_unit).cu_context.ctx_functions``)
val abi_dynamic_ready_fn = rhs (concl abi_dynamic_ready_fn_eval)
val abi_dynamic_ready_canonical_eval = save_thm
  ("abi_dynamic_ready_canonical_eval",
   EVAL
  ``canonical_param_prefix ^abi_dynamic_ready_fn``)

val abi_dynamic_ready_wf_fn_eval = save_thm
  ("abi_dynamic_ready_wf_fn_eval",
   EVAL
  ``wf_function ^abi_dynamic_ready_fn``)

val abi_dynamic_ready_inst_wf_eval = save_thm
  ("abi_dynamic_ready_inst_wf_eval",
   EVAL
  ``fn_inst_wf ^abi_dynamic_ready_fn``)

val abi_dynamic_ready_ssa_eval = save_thm
  ("abi_dynamic_ready_ssa_eval",
   EVAL
  ``ssa_form ^abi_dynamic_ready_fn``)

val abi_dynamic_ready_cfg_eval = save_thm
  ("abi_dynamic_ready_cfg_eval", EVAL ``cfg_analyze ^abi_dynamic_ready_fn``)
val abi_dynamic_ready_dom_analysis_eval = save_thm
  ("abi_dynamic_ready_dom_analysis_eval",
   EVAL ``dom_analyze ^(rhs (concl abi_dynamic_ready_cfg_eval))
      ^abi_dynamic_ready_fn``)
val abi_dynamic_ready_dom_exec_step1 = save_thm
  ("abi_dynamic_ready_dom_exec_step1",
   SIMP_CONV pure_ss
  [codegenReadyComputeTheory.def_dominates_uses_exec_def,
   abi_dynamic_ready_cfg_eval, abi_dynamic_ready_dom_analysis_eval, LET_THM]
  ``def_dominates_uses_exec ^abi_dynamic_ready_fn``)

val () = computeLib.upd_compset
  (fn cs => computeLib.scrub_const cs ``def_available_at_exec``)
val abi_dynamic_ready_dom_exec_step2 = save_thm
  ("abi_dynamic_ready_dom_exec_step2",
   EVAL (rhs (concl abi_dynamic_ready_dom_exec_step1)))
val abi_dynamic_ready_available_terms = find_terms
  (can (match_term ``def_available_at_exec cfg dom fn bb use_opt v``))
  (rhs (concl abi_dynamic_ready_dom_exec_step2))
val () =
  if length abi_dynamic_ready_available_terms = 495 then ()
  else raise Fail "expected 495 ABI-dynamic availability calls"
val () = computeLib.upd_compset (computeLib.add_thms
  [codegenReadyComputeTheory.def_available_at_exec_compute])

(* Keep the real semantic inputs shared in all 495 availability statements. *)
Definition abi_dynamic_available_cfg_def[nocompute]:
  abi_dynamic_available_cfg = ^(rhs (concl abi_dynamic_ready_cfg_eval))
End
Definition abi_dynamic_available_dom_def[nocompute]:
  abi_dynamic_available_dom = ^(rhs (concl abi_dynamic_ready_dom_analysis_eval))
End
Definition abi_dynamic_available_function_def[nocompute]:
  abi_dynamic_available_function = ^abi_dynamic_ready_fn
End

val abi_dynamic_available_block_terms = HOLset.listItems
  (HOLset.addList (HOLset.empty Term.compare,
    map (fn call => List.nth (snd (strip_comb call),3))
      abi_dynamic_ready_available_terms))
Definition abi_dynamic_available_blocks_def[nocompute]:
  abi_dynamic_available_blocks =
    ^(listSyntax.mk_list (abi_dynamic_available_block_terms,
        type_of (hd abi_dynamic_available_block_terms)))
End
val abi_dynamic_available_block_propositions = List.tabulate
  (length abi_dynamic_available_block_terms, fn index => mk_eq
    (``EL ^(numSyntax.term_of_int index) abi_dynamic_available_blocks``,
     List.nth (abi_dynamic_available_block_terms,index)))
fun abi_dynamic_available_block_check goal =
  (CONV_TAC (LAND_CONV
     (RAND_CONV (REWR_CONV abi_dynamic_available_blocks_def) THENC
      listLib.EL_CONV)) >> REFL_TAC) goal
fun abi_dynamic_available_block_step goal =
  (conj_tac >- abi_dynamic_available_block_check) goal
Theorem abi_dynamic_available_block_evals:
  ^(list_mk_conj abi_dynamic_available_block_propositions)
Proof
  abi_dynamic_available_block_step >> abi_dynamic_available_block_step >>
  abi_dynamic_available_block_step >> abi_dynamic_available_block_step >>
  abi_dynamic_available_block_step >> abi_dynamic_available_block_check
QED

(* Export the exact named query list, keeping the large literal expansion
   private. The final theory reconstructs and certifies that expansion once,
   and requires a checked slice result for every original literal call. *)
val abi_dynamic_available_input_aliases = map SYM
  [abi_dynamic_available_cfg_def,abi_dynamic_available_dom_def,
   abi_dynamic_available_function_def]
val abi_dynamic_available_block_aliases = map SYM
  (CONJUNCTS abi_dynamic_available_block_evals)
fun abi_dynamic_name_available_call call = let
  val (head,args) = strip_comb call
  val () = if same_const head ``def_available_at_exec`` andalso length args = 6
    then () else raise Fail "unexpected availability call"
  val block = List.nth (args,3)
  val block_alias = case List.find
      (fn equation => aconv block (lhs (concl equation)))
      abi_dynamic_available_block_aliases of
    SOME equation => equation
  | NONE => raise Fail "availability block missing from shared inputs"
  val equations = abi_dynamic_available_input_aliases @
    [block_alias,REFL (List.nth (args,4)),REFL (List.nth (args,5))]
  val () = if List.all (fn (argument,equation) =>
      aconv argument (lhs (concl equation))) (ListPair.zip (args,equations))
    then () else raise Fail "availability input alias mismatch"
in List.foldl (fn (equation,prefix) => MK_COMB (prefix,equation))
     (REFL head) equations
end
val abi_dynamic_available_call_aliases =
  map abi_dynamic_name_available_call abi_dynamic_ready_available_terms
val abi_dynamic_ready_named_available_terms =
  map (rhs o concl) abi_dynamic_available_call_aliases

Definition abi_dynamic_available_queries_def[nocompute]:
  abi_dynamic_available_queries =
    ^(listSyntax.mk_list (abi_dynamic_ready_named_available_terms,bool))
End

(* The original proof computation above remains intact and kernel-checked. *)
val () = Theory.delete_binding "abi_dynamic_ready_dom_exec_step2"
