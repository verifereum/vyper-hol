(* When the source fails before the constructor body (deploy_ctor_start has
 * no witness), argument binding has succeeded, so the only failure left is
 * a value transfer into a non-payable constructor: the unit's first three
 * instructions (CALLVALUE, ISZERO, ASSERT) revert before the immutables
 * region, the argument decode or the lock.  They read no memory and taint
 * nothing, so the run is pointer-safe.
 * TOP-LEVEL: deploy_ctor_prefix_fail_run_ptr_safe.
 *)
Theory ctorDeployMemoryRunPtrPrefix
Ancestors
  ctorDeployLoweringDefs gasSummary ptrSafeRun ptrDiscipline venomInst
  ctorDeployDefs ctorDeployMemoryRunMemPrefixLayout
  ctorDeployMemoryRunMemPrefixSource ctorDeployShape o1PipelineCorrect
  fragExec compileEnv emitHelper vyperCompiler venomExecSemantics
  venomState e2eEntry rich_list contextCodegenRel codegenRel o1PassContract

(* One opcode's dispatch equation, keeping the simplification local. *)
fun opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

(* A block that starts with the non-payable check reverts at its ASSERT when
   the call carries value, and every step up to it is pointer-safe. *)
Theorem nonpayable_check_ptr_safe:
  !D lo ctx fn bb rest s j0 j1 j2 v0 v1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      mk_inst j0 CALLVALUE [] [v0] :: mk_inst j1 ISZERO [Var v0] [v1] ::
      mk_inst j2 ASSERT [Var v1] [] :: rest /\
    s.vs_call_ctx.cc_callvalue <> 0w /\ s.vs_allocas = FEMPTY /\
    ~ctx_has_dalloca ctx ==>
    !fuel. ptr_safe_blocks D lo fuel ctx fn [] FEMPTY entry_taint s
Proof
  rpt gen_tac >> strip_tac >> Cases >- simp[Once ptr_safe_blocks_def] >>
  qabbrev_tac `i0 = mk_inst j0 CALLVALUE [] [v0]` >>
  qabbrev_tac `i1 = mk_inst j1 ISZERO [Var v0] [v1]` >>
  qabbrev_tac `i2 = mk_inst j2 ASSERT [Var v1] []` >>
  `phi_prefix_length bb.bb_instructions = 0` by
    simp[Abbr `i0`, phi_prefix_length_def, mk_inst_def] >>
  `eval_phis s bb.bb_instructions = OK s` by simp[eval_phis_no_phi] >>
  drule_all ptr_safe_blocks_block >> disch_then (fn th => rewrite_tac [th]) >>
  qpat_assum `phi_prefix_length _ = 0` (fn th => rewrite_tac [th]) >>
  qabbrev_tac `t0 = s with vs_inst_idx := 0` >>
  `i0.inst_opcode = CALLVALUE /\ i0.inst_operands = [] /\
   i0.inst_outputs = [v0] /\
   i1.inst_opcode = ISZERO /\ i1.inst_operands = [Var v0] /\
   i1.inst_outputs = [v1] /\
   i2.inst_opcode = ASSERT /\ i2.inst_operands = [Var v1] /\
   i2.inst_outputs = []` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, mk_inst_def] >>
  (* the CALLVALUE *)
  qabbrev_tac `t1 = update_var v0 s.vs_call_ctx.cc_callvalue t0` >>
  `step_inst n ctx i0 t0 = OK t1` by
    (simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [opcode_eq ``CALLVALUE``, exec_read0_def] >>
     simp[Abbr `t1`, Abbr `t0`]) >>
  `get_instruction bb t0.vs_inst_idx = SOME i0` by
    simp[Abbr `t0`, get_instruction_def] >>
  `~is_terminator i0.inst_opcode` by simp[is_terminator_def] >>
  drule_all ptr_safe_block_step >> disch_then (fn th => rewrite_tac [th]) >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           allocas_from_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, entry_taint_def, Abbr `t0`] >>
      rpt strip_tac >> gvs[]) >>
  qabbrev_tac `tn1 = SND (ghost_step n ctx [] FEMPTY entry_taint i0 t0)` >>
  qabbrev_tac `G1 = FST (ghost_step n ctx [] FEMPTY entry_taint i0 t0)` >>
  `FLOOKUP tn1.t_var v0 = SOME {}` by
    simp[Abbr `tn1`, ghost_step_def, step_taint_def, set_var_taint_def,
         out_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  (* the ISZERO *)
  qabbrev_tac `t1' = t1 with vs_inst_idx := SUC t0.vs_inst_idx` >>
  `lookup_var v0 t1' = SOME s.vs_call_ctx.cc_callvalue /\
   t1'.vs_allocas = FEMPTY /\ t1'.vs_inst_idx = 1 /\
   t1'.vs_call_ctx = s.vs_call_ctx` by
    simp[Abbr `t1'`, Abbr `t1`, Abbr `t0`, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  qabbrev_tac `t2 = update_var v1 0w t1'` >>
  `step_inst n ctx i1 t1' = OK t2` by
    (simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [opcode_eq ``ISZERO``, exec_pure1_def,
                               eval_operand_def, bool_to_word_def] >>
     simp[Abbr `t2`]) >>
  `get_instruction bb t1'.vs_inst_idx = SOME i1` by
    simp[get_instruction_def] >>
  `~is_terminator i1.inst_opcode` by simp[is_terminator_def] >>
  drule_all ptr_safe_block_step >> disch_then (fn th => rewrite_tac [th]) >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           allocas_from_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def, op_taint_def] >>
      rpt strip_tac >> gvs[Abbr `t2`, update_var_def]) >>
  qabbrev_tac `tn2 = SND (ghost_step n ctx [] G1 tn1 i1 t1')` >>
  `FLOOKUP tn2.t_var v1 = SOME {}` by
    simp[Abbr `tn2`, ghost_step_def, step_taint_def, set_var_taint_def,
         out_taint_def, eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  (* the ASSERT *)
  qabbrev_tac `t2' = t2 with vs_inst_idx := SUC t1'.vs_inst_idx` >>
  `lookup_var v1 t2' = SOME 0w /\ t2'.vs_allocas = FEMPTY /\
   t2'.vs_inst_idx = 2` by
    simp[Abbr `t2'`, Abbr `t2`, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst n ctx i2 t2' =
     Abort Revert_abort (revert_state (set_returndata [] t2'))` by
    (simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [opcode_eq ``ASSERT``, eval_operand_def]) >>
  `get_instruction bb t2'.vs_inst_idx = SOME i2` by
    simp[get_instruction_def] >>
  simp[Once ptr_safe_block_def] >>
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
       allocas_from_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, op_taint_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem deploy_ctor_prefix_fail_run_ptr_safe:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   exts ints fb cf fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. ptr_safe_blocks (deploy_dead tops runtime_bc am tx) (imm_len tops)
             fuel dunit.cu_context fn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctor_prefix_rejecting_code >> strip_tac >>
  drule_all ctor_prefix_task_entry_label >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `ptr_safe_blocks _ _ _ _ _ _ _ _ s0` >>
  `s0.vs_call_ctx.cc_callvalue <> 0w` by
    (drule_all ctor_prefix_source_obstruction >>
     strip_tac >> drule_all ctor_prefix_entry_value >> simp[Abbr `s0`]) >>
  `s0.vs_allocas = FEMPTY` by
    (fs[gas_variant_def, Abbr `s0`] >>
     qpat_x_assum `deploy_entry_state _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `\x. x.vs_allocas`) >>
     simp[deploy_entry_state_def, entry_venom_state_def,
          init_venom_state_def]) >>
  `~ctx_has_dalloca dunit.cu_context` by
    (drule_all deploy_unit_shape_ok >> strip_tac >>
     simp[o1_source_unit_ok_no_dalloca]) >>
  `?bb rest j0 j1 j2 v0 v1.
     lookup_block "__deploy" fn.fn_blocks = SOME bb /\
     bb.bb_instructions =
       mk_inst j0 CALLVALUE [] [v0] :: mk_inst j1 ISZERO [Var v0] [v1] ::
       mk_inst j2 ASSERT [Var v1] [] :: rest` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
     qpat_x_assum `_ = emit_op CALLVALUE _ _` mp_tac >>
     simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, initial_compile_state_def, fn_has_code_def] >>
     rpt strip_tac >> gvs[] >>
     Cases_on `bb.bb_instructions` >> fs[] >>
     Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[] >>
     simp[mk_inst_def]) >>
  irule nonpayable_check_ptr_safe >> simp[Abbr `s0`] >> metis_tac[]
QED
