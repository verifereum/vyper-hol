(*
 * S3, Milestone 5: the lowered unit's memory obligations, as bridges from
 * the memory-safe and pointer-safe runs from the unit's entry
 *
 * The runs themselves are the exit arm of loweringRuntimeCorrect's
 * lower_vyper_runtime_unit_body_joint; these theorems take them as
 * premises and carry no source premise.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_memory_ok -- S3, from the memory-safe run
 *     through mem_safe_raw_unit_memory_ok, and from the pointer-safe run
 *     through loweringPtrCorrect's lower_vyper_runtime_unit_ptr_taint
 *   lower_vyper_runtime_unit_dload_offset_ok -- S3's no-wrap bound on
 *     DLOAD/DLOADBYTES offsets, from the memory-safe run's DLOAD check
 *   lower_vyper_runtime_unit_dload_headroom_ok -- LowerDload's scratch
 *     headroom, from alloca_frontier_inv and lowering_context_ok
 *)
Theory loweringMemCorrect
Ancestors
  vyperLoweringCorrect vyperCompiler loweringPtrCorrect memSafeRun
  runtimePeakMemoryBound[ignore_grammar]
  allocaFrontierBound ptrDiscipline lowerDloadDefs contextCodegenRel venomWf
  venomInst unitMemInv unitTransformDefs rawReachableFmp ctxLookupAgree
  loweringShapeSource loweringShapeProps loweringUnitEntryShape moduleLowering
  supportedStmtTraverse supportedExprTraverse vyperTypeContract
  vyperAST vyperCalldata unitShapeDefs o1PassContract e2eDefs exprSimHypsDefs list

val _ = Parse.hide "body";
val _ = Parse.hide "tops";

(* ===== S3 ===== *)

(* S3, Milestone 5: the memory-safe run through the bridge
   mem_safe_raw_unit_memory_ok, with alloca_frontier_inv as the frontier
   bound, and the pointer-safe run through loweringPtrCorrect's
   lower_vyper_runtime_unit_ptr_taint, with the empty reserved region.  The
   bridge's structural premises (an entry function with an entry block,
   distinct labels, an acyclic reachable call graph, the allocation budget
   below the word size) are lowering_context_ok, which run_lowering checks.
   The other conjuncts come from run_lowering: no eom, and no reserved
   global region. The static wrapper proves the reachability premise from
   the absence of raw FMP operations and the entry floor. *)
Theorem lower_vyper_runtime_unit_memory_ok_from_no_wrap:
  !tops rpolicy unit am tx vs fn lbl D.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    (!f inst s. raw_reachable vs unit.cu_context f inst s ==>
       dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>)) /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_alloca_budget >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  `reachability_closed alloca_frontier_inv unit.cu_context` by
    (irule alloca_frontier_inv_closed >> simp[]) >>
  `fn_entry_inv alloca_frontier_inv unit.cu_context fn
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>)` by
    (irule alloca_frontier_inv_entry >>
     simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def, listTheory.MEM_MAP,
          reachable_call_graph_acyclic_def] >>
     fs[initial_venom_state_rel_def] >> metis_tac[]) >>
  `!f inst s. alloca_frontier_inv unit.cu_context f inst s ==>
              s.vs_alloca_next < dimword (:256)` by
    (rpt strip_tac >> drule alloca_frontier_inv_bound >> simp[]) >>
  drule_all mem_safe_raw_unit_memory_ok >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  drule_all loweringPtrCorrectTheory.lower_vyper_runtime_unit_ptr_taint >> strip_tac >>
  simp[fixed_region_reserved_def]
QED

Theorem lower_vyper_runtime_unit_memory_ok:
  !tops rpolicy unit am tx vs fn lbl D.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>)) /\
    (!fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within D unit.cu_context vs
Proof
  rpt strip_tac >>
  `EVERY no_raw_fmp_ops unit.cu_context.ctx_functions` by
    (drule_all lower_vyper_runtime_unit_fn_ptr_ok >> strip_tac >>
     simp[listTheory.EVERY_MEM, no_raw_fmp_ops_def] >> rpt strip_tac >>
     rename1 `MEM i (fn_insts f)` >>
     `fn_ptr_ok P f` by fs[listTheory.EVERY_MEM] >>
     `i.inst_opcode <> DRET /\ i.inst_opcode <> GETFMP /\
      i.inst_opcode <> SETFMP /\ i.inst_opcode <> RETFMP` by
       (fs[fn_ptr_ok_def] >> metis_tac[]) >>
     `i.inst_opcode <> DALLOCA` by
       (fs[ctx_has_dalloca_def, listTheory.EVERY_MEM,
           listTheory.EXISTS_MEM] >> metis_tac[]) >>
     qpat_x_assum `is_raw_fmp_opcode _` mp_tac >>
     rpt (qpat_x_assum `i.inst_opcode <> _` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `i.inst_opcode` >> simp[is_raw_fmp_opcode_def]) >>
  `!f inst s. raw_reachable vs unit.cu_context f inst s ==>
     dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (rpt strip_tac >> drule raw_reachable_no_raw_fmp_fixed >>
     simp[] >> strip_tac >>
     drule raw_reachable_initial_fmp >> strip_tac >> simp[] >>
     `~is_raw_fmp_opcode inst.inst_opcode` by
       (fs[listTheory.EVERY_MEM, no_raw_fmp_ops_def] >>
        imp_res_tac active_inst_mem_fn_insts >> metis_tac[]) >>
     `inst.inst_opcode <> DALLOCA` by
       (strip_tac >> gvs[is_raw_fmp_opcode_def]) >>
     simp[dalloca_no_wrap_def]) >>
  metis_tac[lower_vyper_runtime_unit_memory_ok_from_no_wrap]
QED

Theorem lower_vyper_runtime_unit_dynamic_source_unit_shape[local]:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE,tops)] = SOME art ==>
    o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  rpt gen_tac >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule (Q.INST [`static` |-> `F`]
          lower_vyper_runtime_unit_source_unit_ok_shape_with_no_params_mode) >>
  impl_tac
  >- (`raw_shape_free_program_mode F tops` by
        simp[raw_shape_free_program_mode_def, dynamic_raw_expr_shape,
             dynamic_raw_stmt_shape, EVERY_MEM] >>
      metis_tac[check_contract_runtime_bodies_shape_ok_mode,
                check_contract_internal_names_distinct]) >>
  strip_tac >> simp[] >>
  irule unit_entry_no_params_from_first >> simp[] >>
  fs[lowering_context_ok_def, ctx_fn_names_def]
QED

Theorem lower_vyper_runtime_unit_source_shape_raw_call_calldata:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    (?vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       vis <> Deploy /\
       (supported_stmts_expr_exists
          (\e. ?ty f es d. e = Call ty (RawCallCalldataTarget f) es d) body \/
        EXISTS (supported_expr_exists
          (\e. ?ty f es d. e = Call ty (RawCallCalldataTarget f) es d)) dflts)) ==>
    o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  metis_tac[lower_vyper_runtime_unit_dynamic_source_unit_shape]
QED

Theorem lower_vyper_runtime_unit_source_shape_create_copy:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    (?vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       vis <> Deploy /\
       (supported_stmts_expr_exists
          (\e. ?ty s r ks es d.
                 e = Call ty (CreateTarget CreateCopyOf s r ks) es d) body \/
        EXISTS (supported_expr_exists
          (\e. ?ty s r ks es d.
                 e = Call ty (CreateTarget CreateCopyOf s r ks) es d)) dflts)) ==>
    o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  metis_tac[lower_vyper_runtime_unit_dynamic_source_unit_shape]
QED

Theorem lower_vyper_runtime_unit_source_shape_create_blueprint:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    (?vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       vis <> Deploy /\
       (supported_stmts_expr_exists
          (\e. ?ty b s r ks es d.
                 e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
          body \/
        EXISTS (supported_expr_exists
          (\e. ?ty b s r ks es d.
                 e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d))
          dflts)) ==>
    o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  metis_tac[lower_vyper_runtime_unit_dynamic_source_unit_shape]
QED

Theorem lower_vyper_runtime_unit_blueprint_raw_fmp:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    (?vis mut nr rr name args dflts ret body.
       MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
       vis <> Deploy /\
       (supported_stmts_expr_exists
          (\e. ?ty b s r ks es d.
                 e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
          body \/
        EXISTS (supported_expr_exists
          (\e. ?ty b s r ks es d.
                 e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d))
          dflts)) ==>
    (!am tx vi. source_typing_ok tops am tx /\
      source_deployment_rel tops am tx /\
      initial_venom_state_rel tops am tx vi /\
      vi.vs_fmp = vi.vs_initial_fmp /\
      w2n vi.vs_initial_fmp < 2 ** 254 /\
      unit_alloca_budget unit.cu_context +
        32 * ctx_dload_count unit.cu_context <= w2n vi.vs_initial_fmp /\
      LENGTH vi.vs_outcomes < 2 ** 64 /\
      outcomes_accounts_typed (SOME vi.vs_outcomes) /\
      LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
      !fn inst s. raw_reachable vi unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s
Proof
  metis_tac[lower_vyper_runtime_unit_raw_headroom]
QED

Theorem runtime_raw_shape_cases[local]:
  ~raw_shape_free_program tops ==>
  (?vis mut nr rr name args dflts ret body.
     MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
     vis <> Deploy /\
     (supported_stmts_expr_exists
        (\e. ?ty f es d. e = Call ty (RawCallCalldataTarget f) es d) body \/
      EXISTS (supported_expr_exists
        (\e. ?ty f es d. e = Call ty (RawCallCalldataTarget f) es d)) dflts)) \/
  (?vis mut nr rr name args dflts ret body.
     MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
     vis <> Deploy /\
     (supported_stmts_expr_exists
        (\e. ?ty s r ks es d.
               e = Call ty (CreateTarget CreateCopyOf s r ks) es d) body \/
      EXISTS (supported_expr_exists
        (\e. ?ty s r ks es d.
               e = Call ty (CreateTarget CreateCopyOf s r ks) es d)) dflts)) \/
  (?vis mut nr rr name args dflts ret body.
     MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
     vis <> Deploy /\
     (supported_stmts_expr_exists
        (\e. ?ty b s r ks es d.
               e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
        body \/
      EXISTS (supported_expr_exists
        (\e. ?ty b s r ks es d.
               e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d))
        dflts))
Proof
  pure_rewrite_tac[raw_shape_free_program_def, EVERY_NOT_EXISTS] >>
  BETA_TAC >> pure_rewrite_tac[NOT_CLAUSES] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  `expr_raw_shape_root =
    (\e. (?ty f es d. e = Call ty (RawCallCalldataTarget f) es d) \/
         ((?ty s r ks es d. e = Call ty (CreateTarget CreateCopyOf s r ks) es d) \/
          (?ty b s r ks es d.
             e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)))` by
    simp[FUN_EQ_THM, expr_raw_shape_root_def, DISJ_ASSOC] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  simp_tac bool_ss [supported_stmt_expr_exists_disj, supported_expr_exists_disj,
                    listTheory.EXISTS_MEM, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[]
QED

Theorem lower_vyper_runtime_unit_checked_source_shape:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\ unit_fmp_unsealed unit
Proof
  strip_tac >> Cases_on `raw_shape_free_program tops`
  >- metis_tac[lower_vyper_runtime_unit_source_unit_ok_checked,
               lower_vyper_runtime_unit_o1_shape_extras] >>
  drule runtime_raw_shape_cases >>
  disch_then (DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN ASSUME_TAC)) >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  FIRST
    [drule_all lower_vyper_runtime_unit_source_shape_raw_call_calldata,
     drule_all lower_vyper_runtime_unit_source_shape_create_copy,
     drule_all lower_vyper_runtime_unit_source_shape_create_blueprint] >> simp[]
QED

Theorem lower_vyper_runtime_unit_dload_in_section:
  !tops rpolicy unit vs fn lbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                 s.vs_code = vs.vs_code /\
                                 s.vs_data_section = vs.vs_data_section)
          unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  rewrite_tac[unitMemInvTheory.mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `\c f i s. mem_safe_point c f i s /\
                         s.vs_code = vs.vs_code /\
                         s.vs_data_section = vs.vs_data_section` >>
  rpt conj_tac
  >- (qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `unit.cu_context`] mp_tac
        contextCodegenRelPropsTheory.reachability_closed_conj >>
      simp[mem_safe_point_closed, code_data_closed])
  >- (qexistsl_tac [`"__entry"`, `fn`, `lbl`] >> simp[] >>
      qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `unit.cu_context`, `fn`,
        `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>`] mp_tac
        contextCodegenRelPropsTheory.fn_entry_inv_conj >>
      impl_tac >- (
        conj_tac >- (irule mem_safe_point_entry >> simp[]) >>
        qspecl_then [`unit.cu_context`, `fn`,
          `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0 |>`] mp_tac code_data_entry >>
        simp[]) >>
      gvs[]) >>
  rw[] >> metis_tac[mem_safe_point_dload]
QED

(* S3's twin for LowerDload: every reachable DLOAD/DLOADBYTES offset,
   added to the length of the code before the data section, stays below
   2^256, so LowerDload's code_end-relative CODECOPY offset does not wrap.
   The memory-safe run checks that each offset is at most the data
   section's length (inst_dload_in_section); the code and the data section
   never change, and code_layout_valid keeps the code within 2^255
   bytes. *)
Theorem lower_vyper_runtime_unit_dload_offset_ok:
  !tops rpolicy unit vs fn lbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    code_layout_valid vs /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl /\
    (!fuel. mem_safe_blocks fuel unit.cu_context fn
       (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                   vs_inst_idx := 0 |>))
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[listTheory.EVERY_MEM] >>
  rewrite_tac[unitMemInvTheory.mem_inv_def, codegen_reachability_package_def] >>
  qexists_tac `\c f i s. mem_safe_point c f i s /\
                         s.vs_code = vs.vs_code /\
                         s.vs_data_section = vs.vs_data_section` >>
  rpt conj_tac
  >- (qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `unit.cu_context`] mp_tac
        contextCodegenRelPropsTheory.reachability_closed_conj >>
      simp[mem_safe_point_closed, code_data_closed])
  >- (qexistsl_tac [`"__entry"`, `fn`, `lbl`] >> simp[] >>
      qspecl_then [`mem_safe_point`,
        `\c f i s. s.vs_code = vs.vs_code /\
                   s.vs_data_section = vs.vs_data_section`,
        `unit.cu_context`, `fn`,
        `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>`] mp_tac
        contextCodegenRelPropsTheory.fn_entry_inv_conj >>
      impl_tac >- (
        conj_tac >- (irule mem_safe_point_entry >> simp[]) >>
        qspecl_then [`unit.cu_context`, `fn`,
          `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0 |>`] mp_tac code_data_entry >>
        simp[]) >>
      gvs[]) >>
  rw[dload_offset_ok_def] >>
  `inst_dload_in_section inst s` by metis_tac[mem_safe_point_dload] >>
  `w2n off <= LENGTH s.vs_data_section` by
    (fs[inst_dload_in_section_def] >> metis_tac[]) >>
  gvs[code_layout_valid_def, wordsTheory.dimword_def]
QED

(* Every reachable alloca frontier, plus 32 bytes per DLOAD in the unit,
   stays below 2^256, so LowerDload's scratch sites do not wrap:
   alloca_frontier_inv bounds the frontier by unit_alloca_budget, and
   lowering_context_ok, which run_lowering checks, leaves 32 bytes per
   DLOAD above that budget.  With a DALLOCA in the unit the scratch sites
   also stay below the initial free-memory pointer, which every reachable
   state keeps, given that budget fits below it. *)
Theorem lower_vyper_runtime_unit_dload_headroom_ok:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
     unit_alloca_budget unit.cu_context +
       32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp)
    ==> mem_inv dload_headroom_ok unit.cu_context vs
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule lowering_context_ok_bridge >> strip_tac >>
  drule lowering_context_ok_integrity >> strip_tac >>
  drule lowering_context_ok_static_integrity >> strip_tac >>
  drule lowering_context_ok_dload_budget >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions /\ fn.fn_name = "__entry"` by
    (imp_res_tac lookup_function_MEM >>
     imp_res_tac lookup_function_result_name >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn) /\ fn_has_entry fn` by fs[listTheory.EVERY_MEM] >>
  `?lbl. fn_entry_label fn = SOME lbl` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  `mem_inv (\ctx fn inst s. s.vs_alloca_next <= unit_alloca_budget ctx)
     unit.cu_context vs` by
    (simp[unitMemInvTheory.mem_inv_def, codegen_reachability_package_def] >>
     qexists_tac `alloca_frontier_inv` >> rpt conj_tac
     >- (irule alloca_frontier_inv_closed >> simp[])
     >- (irule alloca_frontier_inv_entry >>
         simp[ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def,
              listTheory.MEM_MAP, reachable_call_graph_acyclic_def] >>
         fs[initial_venom_state_rel_def] >> metis_tac[]) >>
     rw[alloca_frontier_inv_def] >> decide_tac) >>
  fs[unitMemInvTheory.mem_inv_raw_reachable] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ctxLookupAgreeTheory.raw_reachable_initial_fmp >> strip_tac >>
  fs[dload_headroom_ok_def, ctx_dload_count_def, ctx_has_dalloca_def,
     rich_listTheory.FILTER_FLAT, rich_listTheory.LENGTH_FLAT,
     listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  rw[] >> fs[] >> decide_tac
QED
