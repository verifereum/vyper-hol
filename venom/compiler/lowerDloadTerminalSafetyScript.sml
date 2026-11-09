(* Target-only safety of terminal revert-forwarding suffixes. *)
Theory lowerDloadTerminalSafety
Ancestors
  stepWriteFootprintForward unitMemInv unitTransformDefs
  lowerDloadConfiguredOrigins venomExecSemantics venomState memLocDefs
  contextCodegenRel codegenRel list arithmetic

Theorem ld_terminal_step_frontier:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY) /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def,
    AllCaseEqs(), update_var_def, write_memory_with_expansion_def]
QED

Theorem ld_forward_suffix_raw:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i <= s.vs_inst_idx /\ s.vs_inst_idx <= j /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  s.vs_alloca_next < dimword (:256) ==>
  raw_mem_ok ctx fn inst s
Proof
  strip_tac >> simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >>
  Cases_on `s.vs_inst_idx = i`
  >- (disj2_tac >>
      simp[revert_forward_at_def] >> metis_tac[]) >>
  Cases_on `s.vs_inst_idx = j`
  >- (disj2_tac >>
      simp[revert_forward_at_def] >> metis_tac[]) >>
  `inst.inst_opcode = ASSIGN` by
    (gvs[revert_forward_pair_def] >> first_x_assum irule >>
     qexists_tac `s.vs_inst_idx` >> simp[] >> decide_tac) >>
  disj1_tac >> simp[inst_mem_below_frontier_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    mem_read_ops_def, mem_write_ops_def]
QED

Theorem ld_forward_suffix_step_frontier:
  revert_forward_pair bb i j /\ i <= s.vs_inst_idx /\ s.vs_inst_idx <= j /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  Cases_on `s.vs_inst_idx = j`
  >- (`inst.inst_opcode = REVERT` by gvs[revert_forward_pair_def] >>
      drule step_revert_no_normal >> metis_tac[]) >>
  irule ld_terminal_step_frontier >> goal_assum (drule_at Any) >>
  Cases_on `s.vs_inst_idx = i`
  >- (gvs[revert_forward_pair_def]) >>
  disj1_tac >> gvs[revert_forward_pair_def] >> first_x_assum irule >>
  qexists_tac `s.vs_inst_idx` >> simp[] >> decide_tac
QED

Theorem ld_forward_run_blocks_no_normal:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  revert_forward_at bb (phi_prefix_length bb.bb_instructions) ==>
  run_blocks fuel ctx fn s <> OK t /\
  run_blocks fuel ctx fn s <> IntRet ret t
Proof
  strip_tac >> Cases_on `fuel`
  >- (conj_tac >> simp[Once run_blocks_def]) >>
  qspec_then `s` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      `!u rv. exec_block n ctx bb
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) <> OK u /\
        exec_block n ctx bb
          (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) <> IntRet rv u`
        by (rpt gen_tac >> irule revert_forward_at_no_normal >> simp[]) >>
      conj_tac >> once_rewrite_tac[run_blocks_def] >> simp[] >>
      Cases_on `exec_block n ctx bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[]) >>
  conj_tac >> once_rewrite_tac[run_blocks_def] >> simp[]
QED

Theorem ld_forward_suffix_prefix_frontier:
  revert_forward_pair bb i j ==> !s t.
  RTC (\x y. i <= x.vs_inst_idx /\ x.vs_inst_idx <= j /\
       ?inst u. get_instruction bb x.vs_inst_idx = SOME inst /\
         step_inst fuel ctx inst x = OK u /\
         y = u with vs_inst_idx := SUC x.vs_inst_idx) s t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule_all ld_forward_suffix_step_frontier >> simp[]
QED

Theorem ld_invoke_no_return:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  (!rv u. run_blocks fuel ctx callee cs <> IntRet rv u) ==>
  step_inst fuel ctx inst s <> OK t /\
  step_inst fuel ctx inst s <> IntRet ret t
Proof
  strip_tac >>
  conj_tac >> once_rewrite_tac[step_inst_def] >> simp[] >>
  Cases_on `run_blocks fuel ctx callee cs` >> gvs[]
QED

Theorem ld_forward_prefix_raw:
  revert_forward_pair bb i j /\ s.vs_alloca_next < dimword (:256) /\
  RTC (\x y. i <= x.vs_inst_idx /\ x.vs_inst_idx <= j /\
       ?cur u. get_instruction bb x.vs_inst_idx = SOME cur /\
         step_inst fuel ctx cur x = OK u /\
         y = u with vs_inst_idx := SUC x.vs_inst_idx) s t /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  i <= t.vs_inst_idx /\ t.vs_inst_idx <= j /\
  get_instruction bb t.vs_inst_idx = SOME inst ==>
  raw_mem_ok ctx fn inst t
Proof
  strip_tac >> drule_all ld_forward_suffix_prefix_frontier >> strip_tac >>
  irule ld_forward_suffix_raw >> conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `i`, `j`] >> simp[]
QED
