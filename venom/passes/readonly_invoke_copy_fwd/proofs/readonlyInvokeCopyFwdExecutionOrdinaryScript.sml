Theory readonlyInvokeCopyFwdExecutionOrdinary
Ancestors
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  o1LowerDloadJointScalar o1LowerDloadPtrDiscipline o1LowerDloadGhost
  o1LowerDloadRelocationKernel o1LowerDloadOccurrence
  internalReturnCopyFwdSim allocaFrontierBound taintAgree ptrDiscipline pointerConfinedDefs memLocDefs
  venomExecSemantics venomState venomInst codegenRel finite_map list pred_set words

Theorem ricf_execution_scalar_operand:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE] /\
  mem_read_ops inst = NONE /\ mem_write_ops inst = NONE /\
  MEM op inst.inst_operands /\ op_taint rt op = {} /\
  eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G op = NONE` by
    (irule ld_scalar_no_provenance >> metis_tac[]) >>
  `ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_frame_agree_operand >> strip_tac >>
  `x = y` by
    (irule ld_value_agree_clean >>
     qexists_tac `sites` >> gvs[ricf_value_agree_def]) >> gvs[]
QED

Theorem ricf_execution_scalar_result_next[local]:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
    SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD] /\
  inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK (update_var out value s) /\
  step_inst fuel Ct inst t = OK (update_var out value t) /\
  active_inst fn next ((update_var out value s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_execution_invariant vs C ctx0 log D stk PG
    (step_prov PG G inst (update_var out value s))
    (step_taint inst s (update_var out value s) tn) fn next
    ((update_var out value s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((update_var out value t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U (occurrence_sites_step a B inst (update_var out value s)) HP
    (occurrence_step a HP H inst (update_var out value s)) ledger E sites maps targets
    (step_taint inst s (update_var out value s) rt)
Proof
  strip_tac >>
  `inst.inst_opcode <> MSTORE /\ inst.inst_opcode <> ISTORE /\
   inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> MLOAD /\
   inst.inst_opcode <> ILOAD /\ inst.inst_opcode <> SLOAD /\
   inst.inst_opcode <> TLOAD /\ inst.inst_opcode <> ASSIGN /\
   inst.inst_opcode <> SHL /\ inst.inst_opcode <> SHR /\
   inst.inst_opcode <> SAR` by fs[MEM] >>
  `out_taint rt inst s = {} /\ written_taint rt inst s = {}` by
    (simp[out_taint_def, written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `{}`] ricf_execution_bind_next) >>
  simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def] >>
  fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED


Theorem ricf_execution_scalar_operands_clean[local]:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
    SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD] ==>
  !op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  rpt strip_tac >>
  `op_taint tn op = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `~is_pointer_preserving_op inst.inst_opcode /\
   ~MEM inst.inst_opcode [LT;GT;EQ;INVOKE] /\
   mem_read_ops inst = NONE /\ mem_write_ops inst = NONE` by
    (fs[MEM] >> gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  metis_tac[ricf_execution_scalar_operand]
QED

Theorem ricf_execution_unary_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO;NOT] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (`MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
       SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD]` by fs[MEM] >>
     metis_tac[ricf_execution_scalar_operands_clean]) >>
  `?out value. u = update_var out value s /\ inst.inst_outputs = [out] /\
    step_inst fuel Ct inst t = OK (update_var out value t)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure1_def,
          AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `update_var _ _ _ = u` (SUBST_ALL_TAC o SYM) >>
      qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexistsl_tac [`out`,`value`] >> simp[] >>
      simp[Abbr `value`] >> metis_tac[MEM])) >>
  qexists_tac `update_var out value t` >> simp[] >> gvs[] >>
  irule ricf_execution_scalar_result_next >> fs[MEM] >> metis_tac[]
QED

Theorem ricf_execution_binary_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [MUL;Div;Mod;SDIV;SMOD;Exp;SLT;SGT;AND;OR;XOR] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (`MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
       SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD]` by fs[MEM] >>
     metis_tac[ricf_execution_scalar_operands_clean]) >>
  `?out value. u = update_var out value s /\ inst.inst_outputs = [out] /\
    step_inst fuel Ct inst t = OK (update_var out value t)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
          AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `update_var _ _ _ = u` (SUBST_ALL_TAC o SYM) >>
      qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexistsl_tac [`out`,`value`] >> simp[] >>
      simp[Abbr `value`] >> metis_tac[MEM])) >>
  qexists_tac `update_var out value t` >> simp[] >> gvs[] >>
  irule ricf_execution_scalar_result_next >> fs[MEM] >> metis_tac[]
QED

Theorem ricf_execution_ternary_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADDMOD;MULMOD] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (`MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
       SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD]` by fs[MEM] >>
     metis_tac[ricf_execution_scalar_operands_clean]) >>
  `?out value. u = update_var out value s /\ inst.inst_outputs = [out] /\
    step_inst fuel Ct inst t = OK (update_var out value t)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure3_def,
          AllCaseEqs()] >> strip_tac >>
      qpat_x_assum `update_var _ _ _ = u` (SUBST_ALL_TAC o SYM) >>
      qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexistsl_tac [`out`,`value`] >> simp[] >>
      simp[Abbr `value`] >> metis_tac[MEM])) >>
  qexists_tac `update_var out value t` >> simp[] >> gvs[] >>
  irule ricf_execution_scalar_result_next >> fs[MEM] >> metis_tac[]
QED
