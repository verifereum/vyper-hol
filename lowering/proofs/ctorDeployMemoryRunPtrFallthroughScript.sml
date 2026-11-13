(* A constructor body that falls off its end at sb jumps to the exit block,
 * which runs the unlock and the epilogue pointer-safely to a halt.  The
 * pointer twin of deploy_ctor_fallthrough_mem_safe.
 * TOP-LEVEL: deploy_ctor_fallthrough_ptr.
 *)
Theory ctorDeployMemoryRunPtrFallthrough
Ancestors
  ctorDeployMemoryRunPtrFrameRet ctorDeployMemoryRunPtrDefs
  ctorDeployLoweringDefs ptrSafeRun ptrDiscipline fragExec exprLoweringProps
  bodySim venomExecSemantics venomState venomInst emitHelper compileEnv
  memLocDefs contextCodegenRel codegenRel

(* One opcode's dispatch equation, keeping the simplification local. *)
fun opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

(* The check passes a JMP into a block without PHIs with the ghost as it
   is. *)
Theorem ptr_safe_run_jmp:
  !D lo fuel ctx fn PG G tn s bb inst lbl bb'.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label lbl] /\
    ~s.vs_halted /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    lookup_block lbl fn.fn_blocks = SOME bb' /\
    phi_prefix_length bb'.bb_instructions = 0 /\
    ptr_safe_run D lo fuel ctx fn PG G tn (jump_to lbl s) ==>
    ptr_safe_run D lo (SUC fuel) ctx fn PG G tn s
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK (jump_to lbl s)` by
    asm_simp_tac (srw_ss()) [opcode_eq ``JMP``] >>
  `step_inst (SUC fuel) ctx inst s = OK (jump_to lbl s)` by
    simp[step_inst_non_invoke] >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `~(jump_to lbl s).vs_halted /\ (jump_to lbl s).vs_current_bb = lbl /\
   (jump_to lbl s with vs_inst_idx := 0) = jump_to lbl s` by
    simp[jump_to_def] >>
  `entry_prov fn (jump_to lbl s) G = G /\
   entry_taint_vars fn (jump_to lbl s) tn = tn` by
    (simp[entry_prov_def, entry_taint_vars_def] >>
     Cases_on `bb'.bb_instructions` >>
     gvs[phis_prov_def, phis_taint_def, phi_prefix_length_def, AllCaseEqs(),
         ptrDisciplineTheory.taint_component_equality]) >>
  `eval_phis (jump_to lbl s) bb'.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  simp[ptr_safe_run_def] >>
  drule_all ptr_safe_block_terminator >>
  disch_then (fn th => rewrite_tac [th]) >> asm_rewrite_tac [] >>
  conj_tac
  >- (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
           source_memory_read_ranges_def, source_memory_write_ranges_def,
           mem_write_ops_def, mem_read_ops_def, op_taint_def] >>
      simp[jump_to_def]) >>
  qspecl_then [`D`, `lo`, `fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `jump_to lbl s`,
               `bb'`, `jump_to lbl s`] mp_tac ptr_safe_blocks_block >>
  impl_tac >- asm_rewrite_tac [] >>
  disch_then (fn th => rewrite_tac [th]) >>
  gvs[ptr_safe_run_def]
QED

Theorem deploy_ptr_inv_jump_to:
  !tops runtime_bc am tx imm G tn s lbl.
    deploy_ptr_inv tops runtime_bc am tx imm G tn (jump_to lbl s) <=>
    deploy_ptr_inv tops runtime_bc am tx imm G tn s
Proof
  simp[deploy_ptr_inv_def, jump_to_def, allocas_from_def]
QED

Theorem deploy_ctor_fallthrough_ptr:
  !tops rpolicy runtime_bc am tx dunit body cenv nr nkey ut imm exit_lbl sa
   sb sj st_exit st_epilogue st_final func cenv' ee t G tn.
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    cenv.ce_is_ctor /\ cenv_top_ext cenv cenv' ee.scopes /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe (deploy_evaluation_context tops am tx) /\
       (deploy_evaluation_context tops am tx).nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    ~ctx_has_dalloca dunit.cu_context /\
    stmt_state_rel dunit.cu_context func cenv'
      (deploy_evaluation_context tops am tx) ee t /\ ~t.vs_halted /\
    ~block_is_terminated sb /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    deploy_ptr_inv tops runtime_bc am tx imm G tn t ==>
    ?fuel final.
      run_from fuel dunit.cu_context func t = Halt final /\
      ptr_safe_run (deploy_dead tops runtime_bc am tx) (imm_len tops) fuel
        dunit.cu_context func [] G tn t
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> strip_tac >>
  drule cenv_top_ext_same_frame >> strip_tac >>
  qspecl_then [`tops`, `runtime_bc`, `am`, `tx`, `dunit.cu_context`, `func`,
               `cenv`, `cenv'`, `deploy_evaluation_context tops am tx`, `ee`,
               `jump_to exit_lbl t`, `G`, `tn`, `nr`, `nkey`, `ut`,
               `st_exit`, `st_epilogue`, `st_final`, `imm`]
    mp_tac constructor_exit_run_ptr >>
  impl_tac
  >- gvs[new_block_def, jump_to_def, stmt_state_rel_jump_to,
         deploy_ptr_inv_jump_to] >>
  strip_tac >>
  `sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
   sj.cs_current_insts =
     sb.cs_current_insts ++ [mk_inst sb.cs_next_id JMP [Label exit_lbl] []]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb t.vs_inst_idx =
     SOME (mk_inst sb.cs_next_id JMP [Label exit_lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `?bb'. lookup_block exit_lbl func.fn_blocks = SOME bb' /\
         phi_prefix_length bb'.bb_instructions = 0` by
    (irule run_from_jump_target >>
     qexistsl_tac [`dunit.cu_context`, `fuel`, `t`] >> simp[]) >>
  `allocas_from (imm_len tops) t` by fs[deploy_ptr_inv_def] >>
  qexistsl_tac [`SUC fuel`, `final`] >>
  conj_tac
  >- (qspecl_then [`fuel`, `dunit.cu_context`, `func`, `t`, `bb`,
                   `mk_inst sb.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`,
                   `Halt final`] mp_tac run_from_jump_result >>
      impl_tac
      >- (simp[mk_inst_def, is_terminator_def] >>
          asm_simp_tac (srw_ss()) [opcode_eq ``JMP``]) >>
      simp[]) >>
  qspecl_then [`deploy_dead tops runtime_bc am tx`, `imm_len tops`, `fuel`,
               `dunit.cu_context`, `func`, `[]`, `G`, `tn`, `t`, `bb`,
               `mk_inst sb.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`,
               `bb'`] mp_tac ptr_safe_run_jmp >>
  impl_tac >- simp[mk_inst_def] >>
  simp[]
QED
