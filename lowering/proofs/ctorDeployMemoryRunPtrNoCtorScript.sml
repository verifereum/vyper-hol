(* Without a constructor, the deploy unit is compile_simple_deploy's: an
 * ALLOCA for the runtime code and the immutables section, a CODECOPY into
 * it and a RETURN of it.  Its run is pointer-safe: the ALLOCA site starts at
 * the frontier imm_len, the CODECOPY writes the whole returned range through
 * the site's pointer, so the RETURN returns no tainted byte.
 * TOP-LEVEL: deploy_no_ctor_run_ptr_safe.
 *)
Theory ctorDeployMemoryRunPtrNoCtor
Ancestors
  ctorDeployDefs ctorDeployMemoryRunMemNoCtor ctorDeployImmBudget
  ctorDeployShape gasSummary ptrSafeRun ptrDiscipline venomInst
  venomExecSemantics venomState codegenRel contextCodegenRel memLocDefs
  o1PassContract o1PipelineCorrect e2eEntry unitTransformDefs

(* One opcode's dispatch equation, keeping the simplification local. *)
fun opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

Theorem simple_deploy_entry_ptr_safe:
  !D lo ctx szword s.
    s.vs_allocas = FEMPTY /\ lo <= s.vs_alloca_next /\
    s.vs_alloca_next < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
    !fuel. ptr_safe_blocks D lo fuel ctx
      (mk_raw_function "__deploy"
        [<| bb_label := "__deploy"; bb_instructions :=
           [mk_inst 0 ALLOCA [Lit szword] ["%0"];
            mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit szword] [];
            mk_inst 2 RETURN [Var "%0"; Lit szword] []] |>])
      [] FEMPTY entry_taint
      (s with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >> Cases >- simp[Once ptr_safe_blocks_def] >>
  qabbrev_tac `i0 = mk_inst 0 ALLOCA [Lit szword] ["%0"]` >>
  qabbrev_tac `i1 = mk_inst 1 CODECOPY
                      [Var "%0"; Label "runtime_begin"; Lit szword] []` >>
  qabbrev_tac `i2 = mk_inst 2 RETURN [Var "%0"; Lit szword] []` >>
  qabbrev_tac `bb = <| bb_label := "__deploy";
                       bb_instructions := [i0; i1; i2] |>` >>
  qabbrev_tac `fn = mk_raw_function "__deploy" [bb]` >>
  qabbrev_tac `t0 = s with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                               vs_inst_idx := 0 |>` >>
  qabbrev_tac `b = s.vs_alloca_next` >> qabbrev_tac `N = w2n szword` >>
  `lookup_block t0.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[Abbr `fn`, Abbr `bb`, Abbr `t0`, mk_raw_function_def,
         lookup_block_def, listTheory.FIND_thm] >>
  `eval_phis t0 bb.bb_instructions = OK t0 /\
   phi_prefix_length bb.bb_instructions = 0` by
    simp[Abbr `bb`, Abbr `i0`, eval_phis_def, phi_prefix_length_def,
         mk_inst_def] >>
  drule_all ptr_safe_blocks_block >> disch_then (fn th => rewrite_tac [th]) >>
  qpat_assum `phi_prefix_length _ = 0` (fn th => rewrite_tac [th]) >>
  `t0 with vs_inst_idx := 0 = t0` by
    simp[Abbr `t0`, venom_state_component_equality] >>
  pop_assum (fn th => rewrite_tac [th]) >>
  (* the ALLOCA *)
  qabbrev_tac `s1 = update_var "%0" (n2w b)
     (t0 with <| vs_allocas := FEMPTY |+ (0, (b, N));
                 vs_alloca_next := b + N |>)` >>
  `step_inst n ctx i0 t0 = OK s1` by
    simp[Abbr `i0`, Abbr `s1`, Abbr `t0`, Abbr `b`, Abbr `N`, mk_inst_def,
         step_inst_non_invoke, opcode_eq ``ALLOCA``, exec_alloca_def] >>
  `get_instruction bb t0.vs_inst_idx = SOME i0` by
    simp[Abbr `bb`, Abbr `t0`, get_instruction_def] >>
  `~is_terminator i0.inst_opcode` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >> disch_then (fn th => rewrite_tac [th]) >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def] >>
      simp[Abbr `i0`, mk_inst_def, access_ok_def, taint_ok_def,
           allocas_from_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, op_taint_def, Abbr `t0`] >>
      rpt strip_tac >> gvs[entry_taint_def]) >>
  `i0.inst_opcode = ALLOCA /\ i0.inst_operands = [Lit szword] /\
   i0.inst_outputs = ["%0"] /\ i0.inst_id = 0 /\
   i1.inst_opcode = CODECOPY /\
   i1.inst_operands = [Var "%0"; Label "runtime_begin"; Lit szword] /\
   i1.inst_outputs = [] /\
   i2.inst_opcode = RETURN /\ i2.inst_operands = [Var "%0"; Lit szword] /\
   i2.inst_outputs = []` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def] >>
  qabbrev_tac `G1 = FEMPTY |+ ("%0", (b, N))` >>
  qabbrev_tac `tn1 = entry_taint with
     <| t_mem := {i | b <= i /\ i < b + N}; t_var := FEMPTY |+ ("%0", {}) |>` >>
  `ghost_step n ctx [] FEMPTY entry_taint i0 t0 = (G1, tn1)` by
    (simp[ghost_step_def] >>
     simp[Abbr `s1`, Abbr `t0`, Abbr `G1`, Abbr `tn1`, step_prov_def,
          set_prov_def, out_prov_def, step_taint_def, mem_taint_def,
          new_site_bytes_def, step_writes_def, written_taint_def,
          set_var_taint_def, out_taint_def, store_taint_def, imm_taint_def,
          adopt_reset_def, entry_taint_def, update_var_def, eval_operand_def,
          source_memory_write_ranges_def, range_bytes_def,
          finite_mapTheory.FLOOKUP_UPDATE, pred_setTheory.EXTENSION] >>
     rw[] >> eq_tac >> rw[]) >>
  pop_assum (fn th => rewrite_tac [th]) >> simp[] >>
  qabbrev_tac `t1 = s1 with vs_inst_idx := 1` >>
  `t0.vs_inst_idx = 0` by simp[Abbr `t0`] >>
  `SUC t0.vs_inst_idx = 1` by simp[] >>
  pop_assum (fn th => rewrite_tac [th]) >>
  `get_instruction bb 1 = SOME i1 /\ t1.vs_inst_idx = 1 /\
   lookup_var "%0" t1 = SOME (n2w b) /\ t1.vs_allocas = FEMPTY |+ (0, (b, N)) /\
   t1.vs_labels = s.vs_labels /\ t1.vs_requests = s.vs_requests` by
    simp[Abbr `t1`, Abbr `s1`, Abbr `t0`, Abbr `bb`, get_instruction_def,
         update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `w2n (n2w b : bytes32) = b` by simp[] >>
  `step_inst n ctx i1 t1 =
     case FLOOKUP s.vs_labels "runtime_begin" of
       NONE => Error "undefined operand"
     | SOME l => OK (write_memory_with_expansion b
                       (TAKE N (DROP (w2n l) t1.vs_code ++ REPLICATE N 0w)) t1)` by
    (simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [opcode_eq ``CODECOPY``] >>
     gvs[eval_operand_def, Abbr `N`] >>
     BasicProvers.every_case_tac >> simp[]) >>
  `!s_h. step_inst n ctx i1 t1 <> Halt s_h` by
    (pop_assum (fn th => rewrite_tac [th]) >>
     BasicProvers.every_case_tac >> simp[]) >>
  `ptr_safe_step D lo n ctx fn [] G1 tn1 i1 t1` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, sized_source_write_range_def,
          mem_write_ops_def, mem_read_ops_def, eval_operand_def, op_taint_def,
          Abbr `G1`, Abbr `tn1`, finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.FLOOKUP_DEF] >>
     rw[] >~ [`Lit szword`] >- (Cases_on `op` >> gvs[]) >>
     gvs[entry_taint_def]) >>
  (* the CODECOPY *)
  qpat_assum `get_instruction bb 1 = _`
    (fn th => simp[Once ptr_safe_block_def, th]) >>
  Cases_on `FLOOKUP s.vs_labels "runtime_begin"` >> simp[is_terminator_def] >>
  qmatch_goalsub_abbrev_tac `ptr_safe_block _ _ _ _ _ _ _ _ _ (t2 with vs_inst_idx := 2)` >>
  `step_inst n ctx i1 t1 = OK t2` by simp[Abbr `t2`] >>
  `t2.vs_allocas = t1.vs_allocas /\ t2.vs_fmp = t1.vs_fmp /\
   t2.vs_vars = t1.vs_vars /\ t2.vs_requests = t1.vs_requests` by
    simp[Abbr `t2`, write_memory_with_expansion_def] >>
  `~is_terminator i1.inst_opcode` by simp[is_terminator_def] >>
  simp[] >>
  qabbrev_tac `tn2 = tn1 with t_mem := {}` >>
  `ghost_step n ctx [] G1 tn1 i1 t1 = (G1, tn2)` by
    (simp[ghost_step_def] >>
     simp[Abbr `tn1`, Abbr `tn2`, step_prov_def, set_prov_def,
          step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
          written_taint_def, set_var_taint_def, store_taint_def,
          imm_taint_def, adopt_reset_def, entry_taint_def,
          source_memory_write_ranges_def, sized_source_write_range_def,
          eval_operand_def, range_bytes_def, pred_setTheory.EXTENSION,
          finite_mapTheory.DRESTRICT_UNIV] >>
     rw[] >> gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >>
     metis_tac[]) >>
  pop_assum (fn th => rewrite_tac [th]) >> simp[] >>
  (* the RETURN *)
  qabbrev_tac `t3 = t2 with vs_inst_idx := 2` >>
  `get_instruction bb 2 = SOME i2 /\ t3.vs_inst_idx = 2 /\
   lookup_var "%0" t3 = SOME (n2w b) /\ t3.vs_allocas = FEMPTY |+ (0, (b, N))` by
    gvs[Abbr `t3`, Abbr `bb`, get_instruction_def, lookup_var_def] >>
  `!t'. step_inst n ctx i2 t3 <> OK t'` by
    (simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [opcode_eq ``RETURN``] >>
     simp[] >> BasicProvers.every_case_tac >> simp[]) >>
  qpat_assum `get_instruction bb 2 = _`
    (fn th => simp[Once ptr_safe_block_def, th]) >>
  `ptr_safe_step D lo n ctx fn [] G1 tn2 i2 t3` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, memory_range_of_operands_def,
          mem_write_ops_def, mem_read_ops_def, eval_operand_def, op_taint_def,
          Abbr `G1`, Abbr `tn2`, Abbr `tn1`, finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.FLOOKUP_DEF] >>
     rw[] >~ [`Lit szword`] >- (Cases_on `op` >> gvs[]) >>
     gvs[entry_taint_def, step_taint_def, store_taint_def, imm_taint_def,
         adopt_reset_def, ret_taint_def, eval_operand_def]) >>
  simp[] >> BasicProvers.every_case_tac >> gvs[]
QED

Theorem deploy_no_ctor_run_ptr_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, NONE) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. ptr_safe_blocks (deploy_dead tops runtime_bc am tx) (imm_len tops)
             fuel dunit.cu_context fn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt strip_tac >>
  drule_all deploy_no_ctor_entry_shape >> strip_tac >> gvs[] >>
  `vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = imm_len tops` by
    (fs[gas_variant_def] >>
     qpat_x_assum `deploy_entry_state _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `\x. (x.vs_allocas, x.vs_alloca_next)`) >>
     simp[deploy_entry_state_def, entry_venom_state_def,
          init_venom_state_def]) >>
  drule deploy_imm_budget_ok >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  irule simple_deploy_entry_ptr_safe >>
  simp[o1_source_unit_ok_no_dalloca]
QED
