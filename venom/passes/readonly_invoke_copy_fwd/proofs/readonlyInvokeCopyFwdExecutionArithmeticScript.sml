Theory readonlyInvokeCopyFwdExecutionArithmetic
Ancestors
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  o1LowerDloadJointArithmetic o1LowerDloadPtrDiscipline o1LowerDloadGhost
  o1LowerDloadRelocationKernel o1LowerDloadOccurrence
  internalReturnCopyFwdSim allocaFrontierBound taintAgree ptrDiscipline
  pointerConfinedDefs memLocDefs venomExecSemantics venomState venomInst
  codegenRel contextCodegenRel finite_map list pred_set words

Theorem ricf_execution_arithmetic_operands[local]:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADD;SUB] /\ inst.inst_operands = [op1;op2] ==>
  (op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov G op2 = NONE) /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    ?y. eval_operand op t = SOME y /\
      ricf_value_agree sites (op_prov G op) {} x y)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[frame_reachable_prov_support] >>
  `affine_pointer_ops fn (ptr_roots P fn)` by
    (gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (fs[active_inst_def] >> metis_tac[MEM_EL]) >>
  `(op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
   (inst.inst_opcode = SUB ==> op_prov G op2 = NONE)` by
    (qpat_x_assum `affine_pointer_ops _ _`
       (mp_tac o SRULE [affine_pointer_ops_def, LET_THM]) >>
     disch_then (qspecl_then [`bb`,`inst`,`op1`,`op2`] mp_tac) >>
     simp[] >> strip_tac >>
     Cases_on `op1` >> Cases_on `op2` >>
     gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, fn_pv_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn op = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all ricf_frame_agree_operand >> gvs[]
QED

Theorem ricf_arithmetic_values[local]:
  ricf_value_agree sites p {} x1 y1 /\
  ricf_value_agree sites q {} x2 y2 /\
  (p = NONE \/ q = NONE) /\
  (is_sub ==> q = NONE) ==>
  ricf_value_agree sites (case p of NONE => q | SOME id => p) {}
    (if is_sub then x1-x2 else x1+x2)
    (if is_sub then y1-y2 else y1+y2)
Proof
  Cases_on `is_sub`
  >- (simp[] >> strip_tac >> Cases_on `p` >>
      gvs[ricf_value_agree_def] >> irule ld_value_agree_sub >> simp[]) >>
  simp[] >> strip_tac >> Cases_on `p`
  >- (gvs[ricf_value_agree_def] >>
      irule (SRULE [] (Q.INST [`h1` |-> `NONE`] ld_value_agree_add)) >> simp[]) >>
  gvs[ricf_value_agree_def] >>
  once_rewrite_tac[WORD_ADD_COMM] >>
  irule (SRULE [] (Q.INST [`h1` |-> `NONE`] ld_value_agree_add)) >> simp[]

QED

Theorem ricf_execution_arithmetic_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ADD;SUB] /\
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
  `?op1 op2 out x1 x2.
    inst.inst_operands = [op1;op2] /\ inst.inst_outputs = [out] /\
    eval_operand op1 s = SOME x1 /\ eval_operand op2 s = SOME x2 /\
    u = update_var out (if inst.inst_opcode = SUB then x1-x2 else x1+x2) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
         exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `(op_prov G op1 = NONE \/ op_prov G op2 = NONE) /\
   (inst.inst_opcode = SUB ==> op_prov G op2 = NONE) /\
   (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    ?y. eval_operand op t = SOME y /\
      ricf_value_agree sites (op_prov G op) {} x y)` by
    metis_tac[ricf_execution_arithmetic_operands] >>
  `?y1. eval_operand op1 t = SOME y1 /\
    ricf_value_agree sites (op_prov G op1) {} x1 y1` by metis_tac[MEM] >>
  `?y2. eval_operand op2 t = SOME y2 /\
    ricf_value_agree sites (op_prov G op2) {} x2 y2` by metis_tac[MEM] >>
  qabbrev_tac `value = if inst.inst_opcode = SUB then x1-x2 else x1+x2` >>
  qabbrev_tac `value' = if inst.inst_opcode = SUB then y1-y2 else y1+y2` >>
  `step_inst fuel Ct inst t = OK (update_var out value' t)` by
    (fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, Abbr `value'`]) >>
  qexists_tac `update_var out value' t` >> simp[] >>
  `ricf_value_agree sites (first_prov G inst.inst_operands) {} value value'` by
    (`first_prov G inst.inst_operands =
      (case op_prov G op1 of NONE => op_prov G op2 | SOME id => op_prov G op1)` by
       (Cases_on `op_prov G op1` >> Cases_on `op_prov G op2` >>
        gvs[first_prov_def]) >>
     pop_assum SUBST1_TAC >>
     simp_tac pure_ss [Abbr `value`, Abbr `value'`] >>
     irule ricf_arithmetic_values >> metis_tac[]) >>
  gvs[] >>
  `step_prov PG G inst (update_var out value s) =
     set_prov G [out] (first_prov G inst.inst_operands) /\
   step_taint inst s (update_var out value s) tn =
     (tn with t_var := set_var_taint tn.t_var [out] {}) /\
   occurrence_sites_step a B inst (update_var out value s) = B /\
   ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (fs[MEM] >>
     gvs[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
       mem_taint_def, adopt_reset_def, store_taint_def,
       imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
       range_bytes_def, taint_component_equality, occurrence_sites_step_def,
       source_memory_write_ranges_def, update_var_def,
       FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
     rpt CASE_TAC >> simp[]) >>
  irule (Q.INST [`p` |-> `first_prov G [op1;op2]`, `m` |-> `{}`]
    ricf_execution_bind_next) >> simp[] >> metis_tac[]

QED
