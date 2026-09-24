(* Checked code-generation readiness for the mixed-event-types fixture. *)

Theory evalCompilerBytecodeAbiEventsCodegenReady
Ancestors
  evalCompilerBytecodeAbiEventsWalkPipeline
  evalCompilerBytecodeAbiEventsPrePipeline
  evalCompilerBytecodeAbiEventsLowering
  codegenReadyCompute
  stackPlanGen
  evalCompilerSubsetAbiEvents
  compileVyper
  concretizeMemLocDefs
  alist
  byte
  integer_word
  option
  cv_std
Libs
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_mixed_event_types,
     word_of_bytes_bytes32_mixed_event_types,
     w2n_mixed_event_types_n2w,
     contextTheory.compile_copy_memory_def])
val () = Globals.max_print_depth := 20

val mixed_event_types_walk_pair = optionSyntax.dest_some
  (rhs (concl mixed_event_types_walk_eval))
val mixed_event_types_final_unit =
  #1 (pairSyntax.dest_pair mixed_event_types_walk_pair)
val mixed_event_types_final_fn_eval = save_thm
  ("mixed_event_types_final_fn_eval",
   EVAL ``HD (^mixed_event_types_final_unit).cu_context.ctx_functions``)
val mixed_event_types_final_fn = rhs (concl mixed_event_types_final_fn_eval)

val mixed_event_types_ready_canonical_eval = save_thm
  ("mixed_event_types_ready_canonical_eval",
   EVAL ``canonical_param_prefix ^mixed_event_types_final_fn``)
val mixed_event_types_ready_wf_fn_eval = save_thm
  ("mixed_event_types_ready_wf_fn_eval",
   EVAL ``wf_function ^mixed_event_types_final_fn``)
val mixed_event_types_ready_inst_wf_eval = save_thm
  ("mixed_event_types_ready_inst_wf_eval",
   EVAL ``fn_inst_wf ^mixed_event_types_final_fn``)
val mixed_event_types_ready_ssa_eval = save_thm
  ("mixed_event_types_ready_ssa_eval",
   EVAL ``ssa_form ^mixed_event_types_final_fn``)

(* Stage the concrete CFG and dominator analysis before expanding the
   per-use availability checks. *)
val mixed_event_types_ready_cfg_eval = save_thm
  ("mixed_event_types_ready_cfg_eval",
   EVAL ``cfg_analyze ^mixed_event_types_final_fn``)
val mixed_event_types_ready_dom_analysis_eval = save_thm
  ("mixed_event_types_ready_dom_analysis_eval",
   EVAL ``dom_analyze ^(rhs (concl mixed_event_types_ready_cfg_eval))
      ^mixed_event_types_final_fn``)
val mixed_event_types_ready_dom_exec_step1 = SIMP_CONV pure_ss
  [codegenReadyComputeTheory.def_dominates_uses_exec_def,
   mixed_event_types_ready_cfg_eval,
   mixed_event_types_ready_dom_analysis_eval,
   LET_THM]
  ``def_dominates_uses_exec ^mixed_event_types_final_fn``

(* Keep def_available_at_exec opaque while the outer executable traversal is
   reduced, then evaluate each of the 218 resulting concrete calls alone. *)
val () = computeLib.upd_compset
  (fn cs => computeLib.scrub_const cs ``def_available_at_exec``)
val mixed_event_types_ready_dom_exec_step2 = save_thm
  ("mixed_event_types_ready_dom_exec_step2",
   EVAL (rhs (concl mixed_event_types_ready_dom_exec_step1)))
val mixed_event_types_ready_available_terms = find_terms
  (can (match_term ``def_available_at_exec cfg dom fn bb use_opt v``))
  (rhs (concl mixed_event_types_ready_dom_exec_step2))
val () =
  if length mixed_event_types_ready_available_terms = 218 then ()
  else raise Fail "expected 218 mixed-event def_available_at_exec calls"
val () = computeLib.upd_compset (computeLib.add_thms
  [codegenReadyComputeTheory.def_available_at_exec_def])
fun mixed_event_types_split_at n xs =
  (List.take (xs,n), List.drop (xs,n))
val (mixed_event_types_ready_terms0,mixed_event_types_ready_terms_rest0) =
  mixed_event_types_split_at 40 mixed_event_types_ready_available_terms
val (mixed_event_types_ready_terms1,mixed_event_types_ready_terms_rest1) =
  mixed_event_types_split_at 40 mixed_event_types_ready_terms_rest0
val (mixed_event_types_ready_terms2,mixed_event_types_ready_terms_rest2) =
  mixed_event_types_split_at 40 mixed_event_types_ready_terms_rest1
val (mixed_event_types_ready_terms3,mixed_event_types_ready_terms_rest3) =
  mixed_event_types_split_at 40 mixed_event_types_ready_terms_rest2
val (mixed_event_types_ready_terms4,mixed_event_types_ready_terms5) =
  mixed_event_types_split_at 40 mixed_event_types_ready_terms_rest3
fun mixed_event_types_eval_chunk name terms =
  save_thm (name, LIST_CONJ (map EVAL terms))
val mixed_event_types_ready_available_chunk0 = mixed_event_types_eval_chunk
  "mixed_event_types_ready_available_chunk0" mixed_event_types_ready_terms0
Theorem mixed_event_types_ready_available_chunk0_computed: T
Proof
  simp[]
QED
val mixed_event_types_ready_available_chunk1 = mixed_event_types_eval_chunk
  "mixed_event_types_ready_available_chunk1" mixed_event_types_ready_terms1
Theorem mixed_event_types_ready_available_chunk1_computed: T
Proof
  simp[]
QED
val mixed_event_types_ready_available_chunk2 = mixed_event_types_eval_chunk
  "mixed_event_types_ready_available_chunk2" mixed_event_types_ready_terms2
Theorem mixed_event_types_ready_available_chunk2_computed: T
Proof
  simp[]
QED
val mixed_event_types_ready_available_chunk3 = mixed_event_types_eval_chunk
  "mixed_event_types_ready_available_chunk3" mixed_event_types_ready_terms3
Theorem mixed_event_types_ready_available_chunk3_computed: T
Proof
  simp[]
QED
val mixed_event_types_ready_available_chunk4 = mixed_event_types_eval_chunk
  "mixed_event_types_ready_available_chunk4" mixed_event_types_ready_terms4
Theorem mixed_event_types_ready_available_chunk4_computed: T
Proof
  simp[]
QED
val mixed_event_types_ready_available_chunk5 = mixed_event_types_eval_chunk
  "mixed_event_types_ready_available_chunk5" mixed_event_types_ready_terms5
Theorem mixed_event_types_ready_available_chunk5_computed: T
Proof
  simp[]
QED
val mixed_event_types_ready_available_evals = List.concat
  (map CONJUNCTS
    [mixed_event_types_ready_available_chunk0,
     mixed_event_types_ready_available_chunk1,
     mixed_event_types_ready_available_chunk2,
     mixed_event_types_ready_available_chunk3,
     mixed_event_types_ready_available_chunk4,
     mixed_event_types_ready_available_chunk5])
val mixed_event_types_ready_dom_exec_step3 = PURE_REWRITE_CONV
  mixed_event_types_ready_available_evals
  (rhs (concl mixed_event_types_ready_dom_exec_step2))
val mixed_event_types_ready_dom_exec_eval =
  TRANS mixed_event_types_ready_dom_exec_step1
    (TRANS mixed_event_types_ready_dom_exec_step2
      (TRANS mixed_event_types_ready_dom_exec_step3
        (EVAL (rhs (concl mixed_event_types_ready_dom_exec_step3)))))
Theorem mixed_event_types_ready_dom_eval:
  def_dominates_uses ^mixed_event_types_final_fn
Proof
  simp[codegenReadyComputeTheory.def_dominates_uses_compute,
       mixed_event_types_ready_wf_fn_eval,
       mixed_event_types_ready_dom_exec_eval]
QED

val mixed_event_types_ready_sue_eval =
  EVAL ``single_use_form ^mixed_event_types_final_fn``
val mixed_event_types_ready_cfg_norm_eval = EVAL
  ``cfg_is_normalized ^(rhs (concl mixed_event_types_ready_cfg_eval))
      ^mixed_event_types_final_fn``
val mixed_event_types_ready_cfg_norm_exact_eval = EVAL
  ``cfg_is_normalized (cfg_analyze ^mixed_event_types_final_fn)
      ^mixed_event_types_final_fn``

(* Expand the outer EVERY traversal first, then simplify each concrete
   codegen_ready_inst call independently. *)
val () = computeLib.upd_compset (computeLib.add_thms
  [stackPlanGenTheory.codegen_ready_inst_def,
   stackPlanGenTheory.is_pre_codegen_opcode_def,
   stackPlanGenTheory.is_unlowered_fmp_opcode_def,
   stackPlanGenTheory.is_unlowered_internal_call_opcode_def,
   stackPlanGenTheory.invoke_operands_wf_def])
val mixed_event_types_ready_insts_term =
  ``EVERY (λbb. EVERY codegen_ready_inst bb.bb_instructions)
      (^mixed_event_types_final_fn).fn_blocks``
val mixed_event_types_ready_insts_step1 =
  TRY_CONV EVAL mixed_event_types_ready_insts_term
val mixed_event_types_ready_insts_step2 =
  TRY_CONV EVAL (rhs (concl mixed_event_types_ready_insts_step1))
val mixed_event_types_ready_insts_eval =
  TRANS mixed_event_types_ready_insts_step1
    mixed_event_types_ready_insts_step2
val mixed_event_types_codegen_shell = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.codegen_ready_def]
  ``codegen_ready (^mixed_event_types_final_unit).cu_context``
val mixed_event_types_actual_ready_call = find_term
  (can (match_term ``codegen_ready_fn fn``))
  (rhs (concl mixed_event_types_codegen_shell))
val mixed_event_types_actual_ready_fn = #2 (dest_comb mixed_event_types_actual_ready_call)
fun mixed_event_types_w2n_eval w =
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
  in
    TRANS decoded (TRANS expose (EVAL (rhs (concl expose))))
  end else EVAL ``w2n ^w``
fun mixed_event_types_normalize_word w = let
  val w2n_th = mixed_event_types_w2n_eval w
  val numeral = rhs (concl w2n_th)
  val normalized = ``mixed_event_types_n2w ^numeral``
  val normalized_w2n_step = INST [``n:num`` |-> numeral]
    w2n_mixed_event_types_n2w
  val normalized_w2n = TRANS normalized_w2n_step
    (EVAL (rhs (concl normalized_w2n_step)))
  val same_num = TRANS w2n_th (SYM normalized_w2n)
in
  EQ_MP (ISPECL [w, normalized] wordsTheory.w2n_11) same_num
end
fun mixed_event_types_literal_words tm =
  List.foldl (fn (lit,ws) => let val w = #2 (dest_comb lit) in
      if List.exists (aconv w) ws then ws else w::ws end) []
    (find_terms (can (match_term ``Lit (set_byte a b w be : bytes32)``)) tm)
val mixed_event_types_ready_words =
  mixed_event_types_literal_words mixed_event_types_actual_ready_fn @
  mixed_event_types_literal_words mixed_event_types_final_fn
val mixed_event_types_ready_word_normalizations =
  map mixed_event_types_normalize_word
    (List.foldl (fn (w,ws) => if List.exists (aconv w) ws then ws else w::ws)
      [] mixed_event_types_ready_words)
val mixed_event_types_ready_fn_eq_step = SIMP_CONV (srw_ss())
  mixed_event_types_ready_word_normalizations
  ``^mixed_event_types_actual_ready_fn = ^mixed_event_types_final_fn``
val mixed_event_types_ready_fn_eq = EQT_ELIM
  (TRANS mixed_event_types_ready_fn_eq_step
    (EVAL (rhs (concl mixed_event_types_ready_fn_eq_step))))
val mixed_event_types_final_fn_ready_rhs = LIST_CONJ
  [EQT_ELIM mixed_event_types_ready_canonical_eval,
   EQT_ELIM mixed_event_types_ready_wf_fn_eval,
   EQT_ELIM mixed_event_types_ready_inst_wf_eval,
   EQT_ELIM mixed_event_types_ready_ssa_eval,
   mixed_event_types_ready_dom_eval,
   EQT_ELIM mixed_event_types_ready_sue_eval,
   EQT_ELIM mixed_event_types_ready_cfg_norm_exact_eval,
   EQT_ELIM mixed_event_types_ready_insts_eval]
val mixed_event_types_final_fn_ready = prove
  (``codegen_ready_fn ^mixed_event_types_final_fn``,
   PURE_REWRITE_TAC [stackPlanGenTheory.codegen_ready_fn_def] >>
   ACCEPT_TAC mixed_event_types_final_fn_ready_rhs)
val mixed_event_types_actual_fn_ready = EQ_MP
  (SYM (AP_TERM ``codegen_ready_fn`` mixed_event_types_ready_fn_eq))
  mixed_event_types_final_fn_ready
val mixed_event_types_final_codegen_ready_eval = save_thm
  ("mixed_event_types_final_codegen_ready_eval",
   EQ_MP (SYM mixed_event_types_codegen_shell)
     mixed_event_types_actual_fn_ready)

val _ = export_theory()
