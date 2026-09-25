(* Exact pinned-Python bytecode parity for the reasoned-raise fixture. *)

Theory evalCompilerBytecodeRaiseReason
Ancestors evalCompilerSubsetControlDeploy compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

(* Keep concrete words in numeral form while evaluating the checked pipeline.
   The opaque wrapper is definitionally n2w, but avoids eagerly expanding a
   256-bit numeral into nested set_byte terms. *)
Definition raise_reason_n2w_def[nocompute]:
  raise_reason_n2w n : bytes32 = n2w n
End

Theorem word_of_bytes_be_bytes32_raise_reason:
  (word_of_bytes_be bs : bytes32) =
    raise_reason_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  PURE_REWRITE_TAC[raise_reason_n2w_def] >>
  irule word_of_bytes_be_eq_num_of_bytes >> EVAL_TAC
QED

Theorem word_of_bytes_bytes32_raise_reason:
  (word_of_bytes T 0w bs : bytes32) =
    raise_reason_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  simp[GSYM byteTheory.word_of_bytes_be_def,
       word_of_bytes_be_bytes32_raise_reason]
QED

Theorem w2n_raise_reason_n2w[compute]:
  w2n (raise_reason_n2w n) = n MOD dimword (:256)
Proof
  simp[raise_reason_n2w_def]
QED

Theorem get_byte_set_byte_bytes32_raise_reason:
  get_byte a (set_byte a b (w : bytes32) be) be = b
Proof
  simp[byteTheory.get_byte_set_byte]
QED

Theorem get_byte_set_byte_irrelevant_bytes32_raise_reason:
  w2n (a : bytes32) MOD 32 <> w2n a' MOD 32 ==>
  get_byte a' (set_byte a b (w : bytes32) be) be = get_byte a' w be
Proof
  simp[byteTheory.get_byte_set_byte_irrelevant]
QED

Theorem word_to_bytes_be_bytes32_genlist_raise_reason:
  word_to_bytes_be (w : bytes32) =
    GENLIST (λi. get_byte (n2w i) w T) 32
Proof
  simp[listTheory.LIST_EQ_REWRITE, byteTheory.word_to_bytes_be_def,
       byteTheory.word_to_bytes_def, byteTheory.EL_word_to_bytes_aux]
QED

Theorem word_of_bytes_be_word_to_bytes_be_raise_reason:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED

val () = computeLib.upd_compset
  (computeLib.add_thms
    [word_of_bytes_be_bytes32_raise_reason,
     word_of_bytes_bytes32_raise_reason,
     w2n_raise_reason_n2w,
     contextTheory.compile_copy_memory_def])

Definition raise_reason_runtime_pipeline_def:
  raise_reason_runtime_pipeline tops =
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

Definition raise_reason_runtime_compile_def:
  raise_reason_runtime_compile tops =
    case raise_reason_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

Definition raise_reason_deploy_compile_def:
  raise_reason_deploy_compile tops runtime =
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

val raise_reason_runtime_pipeline_eval =
  save_thm ("raise_reason_runtime_pipeline_eval",
    EVAL ``raise_reason_runtime_pipeline raise_reason_program``)

(* Stage the three analyses consumed again by stack planning.  Each theorem is
   kernel-produced from the checked pipeline result; no oracle data is used. *)
val raise_reason_pipeline_value =
  rhs (concl raise_reason_runtime_pipeline_eval)
val raise_reason_rp_out = optionSyntax.dest_some raise_reason_pipeline_value
val raise_reason_rpolicy = #1 (pairSyntax.dest_pair raise_reason_rp_out)
val raise_reason_out = #2 (pairSyntax.dest_pair raise_reason_rp_out)
val raise_reason_unit_eval = EVAL ``(^raise_reason_out).po_unit``
val raise_reason_unit = rhs (concl raise_reason_unit_eval)
val raise_reason_out_final_assembly_eval =
  EVAL ``(^raise_reason_out).po_final_assembly``
val raise_reason_rpolicy_final_assembly_eval =
  EVAL ``(^raise_reason_rpolicy).rpol_final_assembly``
val raise_reason_fn = rhs (concl (EVAL
  ``HD (^raise_reason_unit).cu_context.ctx_functions``))
val raise_reason_liveness_eval = save_thm
  ("raise_reason_liveness_eval", EVAL ``liveness_analyze ^raise_reason_fn``)
val raise_reason_dfg_eval = save_thm
  ("raise_reason_dfg_eval", EVAL ``dfg_build_function ^raise_reason_fn``)
val raise_reason_cfg_eval = save_thm
  ("raise_reason_cfg_eval", EVAL ``cfg_analyze ^raise_reason_fn``)
val raise_reason_liveness = rhs (concl raise_reason_liveness_eval)
val raise_reason_dfg = rhs (concl raise_reason_dfg_eval)
val raise_reason_cfg = rhs (concl raise_reason_cfg_eval)
val raise_reason_generate_fn_plan = save_thm
  ("raise_reason_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^raise_reason_fn spill labels =
        generate_fn_plan_analyzed ^raise_reason_liveness
          ^raise_reason_dfg ^raise_reason_cfg ^raise_reason_fn
          spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          raise_reason_liveness_eval,
          raise_reason_dfg_eval, raise_reason_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [raise_reason_liveness_eval, raise_reason_dfg_eval,
   raise_reason_cfg_eval, raise_reason_generate_fn_plan])
val raise_reason_analyzed_plan_eval = save_thm
  ("raise_reason_analyzed_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^raise_reason_liveness
       ^raise_reason_dfg ^raise_reason_cfg ^raise_reason_fn 256 0``)
val raise_reason_plan = rhs (concl raise_reason_analyzed_plan_eval)
val raise_reason_concrete_fn_plan = save_thm
  ("raise_reason_concrete_fn_plan", prove
    (``generate_fn_plan ^raise_reason_fn 256 0 = ^raise_reason_plan``,
     simp[raise_reason_generate_fn_plan,
          raise_reason_analyzed_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [raise_reason_concrete_fn_plan])
val raise_reason_context_plan_eval = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   stackPlanGenTheory.max_live_eom_def,
   stackPlanGenTheory.collect_fn_eoms_def,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def,
   raise_reason_concrete_fn_plan]
  ``generate_context_plan (^raise_reason_unit).cu_context``
val raise_reason_context_plan_eval = TRANS raise_reason_context_plan_eval
  (EVAL (rhs (concl raise_reason_context_plan_eval)))
val raise_reason_context_plan = optionSyntax.dest_some
  (rhs (concl raise_reason_context_plan_eval))
val raise_reason_plan_value = optionSyntax.dest_some raise_reason_plan
val raise_reason_plan_ops = #1 (pairSyntax.dest_pair raise_reason_plan_value)
val raise_reason_ops = #1 (listSyntax.dest_list raise_reason_plan_ops)
val raise_reason_sopush = #1 (dest_comb
  ``SOPush (Lit (0w : bytes32))``)
val raise_reason_lit = #1 (dest_comb ``Lit (0w : bytes32)``)
fun raise_reason_dest_push_word tm =
  case total dest_comb tm of
    SOME (c,arg) =>
      if same_const c raise_reason_sopush then
        (case total dest_comb arg of
           SOME (lc,w) => if same_const lc raise_reason_lit then SOME w
                          else NONE
         | NONE => NONE)
      else NONE
  | NONE => NONE
fun raise_reason_insert_word (w,ws) =
  if List.exists (aconv w) ws then ws else w :: ws
val raise_reason_push_words =
  List.foldl raise_reason_insert_word []
    (List.mapPartial raise_reason_dest_push_word raise_reason_ops)
fun raise_reason_w2n_eval w =
  if same_const (#1 (strip_comb w)) ``set_byte`` then let
    val bytes_th = SIMP_CONV (srw_ss())
      [word_to_bytes_be_bytes32_genlist_raise_reason,
       get_byte_set_byte_bytes32_raise_reason,
       get_byte_set_byte_irrelevant_bytes32_raise_reason]
      ``word_to_bytes_be ^w``
    val roundtrip = INST [``w:bytes32`` |-> w]
      word_of_bytes_be_word_to_bytes_be_raise_reason
    val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x``
      (SYM roundtrip))
    val step2 = BETA_RULE (AP_TERM
      ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
    val decoded = TRANS step1 step2
    val expose = SIMP_CONV bool_ss
      [word_of_bytes_be_bytes32_raise_reason,
       w2n_raise_reason_n2w] (rhs (concl decoded))
    val numeral = EVAL (rhs (concl expose))
  in
    TRANS decoded (TRANS expose numeral)
  end else
    EVAL ``w2n ^w``
val raise_reason_w2n_evals =
  map raise_reason_w2n_eval raise_reason_push_words
fun raise_reason_encode_eval w2n_th = let
  val step = BETA_RULE (AP_TERM
    ``λn. encode_num_bytes_fuel 32 n`` w2n_th)
  val concrete = EVAL (rhs (concl step))
in
  TRANS step concrete
end
val raise_reason_encode_evals =
  map raise_reason_encode_eval raise_reason_w2n_evals
val raise_reason_all_plan_ops_eval = EVAL
  ``context_plan_ops ^raise_reason_context_plan``
val raise_reason_all_plan_ops =
  rhs (concl raise_reason_all_plan_ops_eval)
val raise_reason_initial_fmp_eval = EVAL
  ``(^raise_reason_context_plan).cp_initial_fmp``
val raise_reason_initial_fmp =
  rhs (concl raise_reason_initial_fmp_eval)
val (raise_reason_plan_op_terms, _) =
  listSyntax.dest_list raise_reason_all_plan_ops
fun raise_reason_exec_op_eval sop = let
  val step = FIRST_CONV
    (map REWR_CONV (CONJUNCTS planExecTheory.exec_stack_op_def))
    ``exec_stack_op ^raise_reason_initial_fmp ^sop``
  val encoded = QCONV
    (PURE_REWRITE_CONV raise_reason_encode_evals)
    (rhs (concl step))
  val reduced = EVAL (rhs (concl encoded))
in
  TRANS step (TRANS encoded reduced)
end
val raise_reason_exec_op_evals =
  map raise_reason_exec_op_eval raise_reason_plan_op_terms
val raise_reason_execute_step = PURE_REWRITE_CONV
  ([planExecTheory.execute_plan_def, listTheory.MAP, listTheory.FLAT] @
   raise_reason_exec_op_evals)
  ``execute_plan ^raise_reason_initial_fmp ^raise_reason_all_plan_ops``
val raise_reason_execute_eval = TRANS raise_reason_execute_step
  (EVAL (rhs (concl raise_reason_execute_step)))
val raise_reason_execute_context_step = SIMP_CONV pure_ss
  [raise_reason_initial_fmp_eval, raise_reason_all_plan_ops_eval]
  ``execute_plan (^raise_reason_context_plan).cp_initial_fmp
      (context_plan_ops ^raise_reason_context_plan)``
val raise_reason_execute_context_eval =
  TRANS raise_reason_execute_context_step raise_reason_execute_eval
val raise_reason_execute_asm =
  rhs (concl raise_reason_execute_eval)
val raise_reason_data_asm_eval = EVAL
  ``data_segment_asm (^raise_reason_unit).cu_data_segment``
val raise_reason_raw_asm_eval = EVAL
  ``^raise_reason_execute_asm ++
    data_segment_asm (^raise_reason_unit).cu_data_segment ++
    [AsmDataHeader "code_end"]``
val raise_reason_raw_asm = rhs (concl raise_reason_raw_asm_eval)
val raise_reason_target_wf_eval = EVAL
  ``target_capabilities_wf (^raise_reason_rpolicy).rpol_target``
val raise_reason_context_safe_eval = EVAL
  ``context_target_safe (^raise_reason_rpolicy).rpol_target
      (^raise_reason_unit).cu_context``
val raise_reason_assembly_safe_eval = EVAL
  ``assembly_target_safe (^raise_reason_rpolicy).rpol_target
      ^raise_reason_raw_asm``
val raise_reason_codegen_step1 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def,
   raise_reason_target_wf_eval,
   raise_reason_context_safe_eval,
   raise_reason_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^raise_reason_rpolicy ^raise_reason_unit``
val raise_reason_codegen_step2 = SIMP_CONV pure_ss
  [raise_reason_execute_context_eval,
   raise_reason_data_asm_eval,
   raise_reason_raw_asm_eval,
   raise_reason_assembly_safe_eval]
  (rhs (concl raise_reason_codegen_step1))
val raise_reason_codegen_assembly_eval =
  TRANS raise_reason_codegen_step1 raise_reason_codegen_step2
val raise_reason_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors
Theorem raise_reason_runtime_matches_python_oracle:
  raise_reason_runtime_compile raise_reason_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes "raise_reason.hex"))
Proof
  simp_tac pure_ss
    ([raise_reason_runtime_compile_def,
      raise_reason_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      raise_reason_unit_eval,
      raise_reason_out_final_assembly_eval,
      raise_reason_rpolicy_final_assembly_eval] @
     raise_reason_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [raise_reason_codegen_assembly_eval] >>
  EVAL_TAC
QED

Theorem raise_reason_deploy_matches_python_oracle:
  raise_reason_deploy_compile raise_reason_program
    (SND ^(evalCompilerBytecodeLib.read_hex_bytes "raise_reason.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes "raise_reason.hex"))
Proof
  EVAL_TAC
QED

Theorem raise_reason_compile_staged:
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    case raise_reason_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (raise_reason_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       raise_reason_runtime_compile_def,
       raise_reason_runtime_pipeline_def,
       raise_reason_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem raise_reason_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    raise_reason_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "raise_reason.hex")
Proof
  PURE_REWRITE_TAC [raise_reason_compile_staged] >>
  PURE_REWRITE_TAC [raise_reason_runtime_matches_python_oracle] >>
  simp_tac pure_ss
    [optionTheory.option_case_compute,
     optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
     optionTheory.OPTION_MAP_DEF, LET_THM, COND_CLAUSES,
     raise_reason_deploy_matches_python_oracle] >>
  EVAL_TAC
QED
