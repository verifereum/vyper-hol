(* TASK037: actual commutation/remapping simulations retain all old facts.
 * No additional semantic premise, no reconstruction or outcome consumption. *)
Theory passOracleSim
Ancestors
  passOracleFields passSharedFrame allocaRemapProofs allocaRemapDefs
  pointerConfinedDefs passSharedDefs venomExecSemantics venomState venomInst
  venomWf venomEffects stateEquiv passSimulationDefs
  list finite_map pred_set words

Theorem alloca_remap_step_oracle:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
    allocas_in_memory s1 /\ allocas_in_memory s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    affine_pointer_ops fn roots /\
    pointer_arith_in_region fn roots /\
    phi_pv_all_var fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> ISTORE /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2 /\
         v1.vs_outcomes = v2.vs_outcomes /\
         v1.vs_requests = v2.vs_requests
Proof
  rpt gen_tac >> strip_tac >> drule step_inst_base_preserves_remap >>
  disch_then (qspecl_then [`inst`, `v1`] mp_tac) >>
  impl_tac >- (simp[] >> qexists_tac `bb` >> simp[]) >>
  strip_tac >> qexists_tac `v2` >> simp[] >>
  drule_all alloca_remap_rel_oracle >> simp[]
QED

Theorem alloca_remap_run_block_oracle:
  !fn roots.
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    affine_pointer_ops fn roots /\
    pointer_arith_in_region fn roots /\
    phi_pv_all_var fn roots /\
    step_preserves_safety fn roots /\

    fn_inst_wf fn ==>
    !fuel ctx bb s1 remap s2.
      alloca_remap_rel fn roots remap s1 s2 /\
      allocas_in_memory s1 /\ allocas_in_memory s2 /\
      alloca_safe_access fn roots s1 /\
      alloca_safe_access fn roots s2 /\
      ptrs_in_alloca_bounds fn roots s1 /\
      ptrs_in_alloca_bounds fn roots s2 /\
      FDOM remap SUBSET FDOM s1.vs_allocas /\
      (!inst. MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> DRET /\
              ~is_ext_call_op inst.inst_opcode /\
              ~is_alloca_op inst.inst_opcode /\
              inst.inst_opcode <> ISTORE /\
              (!u. u IN pointer_derived_vars fn roots ==>
                   LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1)) /\
      (!inst. MEM inst bb.bb_instructions /\ is_alloca_op inst.inst_opcode ==>
              inst.inst_outputs = [HD inst.inst_outputs] /\
              HD inst.inst_outputs IN roots /\
              fn_alloca_id_of_var fn (HD inst.inst_outputs) = SOME inst.inst_id /\
              ?alloc_size. inst.inst_operands = [Lit alloc_size] /\
                0 < w2n alloc_size) /\
      (!inst s. MEM inst bb.bb_instructions /\ is_alloca_op inst.inst_opcode ==>
                !alloc_size. inst.inst_operands = [Lit alloc_size] ==>
                s.vs_alloca_next + w2n alloc_size < dimword (:256)) /\
      (!i. s1.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions ==>
           (EL i bb.bb_instructions).inst_id NOTIN FDOM s1.vs_allocas) /\
      MEM bb fn.fn_blocks ==>
      ?remap'.
        FDOM remap SUBSET FDOM remap' /\
        (!aid. aid IN FDOM remap ==> FLOOKUP remap' aid = FLOOKUP remap aid) /\
        lift_result
          (alloca_remap_rel fn roots remap')
          (alloca_remap_rel fn roots remap')
          (alloca_remap_rel fn roots remap')
          (exec_block fuel ctx bb s1)
          (exec_block fuel ctx bb s2) /\
      lift_result
          (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
          (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
          (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
          (exec_block fuel ctx bb s1)
          (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all run_block_preserves_remap >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  strip_tac >> qexists_tac `remap'` >> ASM_REWRITE_TAC[] >>
  drule_all alloca_remap_rel_lift_result_oracle >> simp[]
QED

Theorem effects_independent_commute_oracle:
  !fuel ctx inst1 inst2 s.
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\
    ~is_alloca_op inst2.inst_opcode ==>
    let r1 = (case step_inst fuel ctx inst1 s of
                OK s1 => step_inst fuel ctx inst2 s1
              | other => other) in
    let r2 = (case step_inst fuel ctx inst2 s of
                OK s2 => step_inst fuel ctx inst1 s2
              | other => other) in
    let defs = set (inst_defs inst1) UNION set (inst_defs inst2) in
    (case (r1, r2) of
      (OK s12, OK s21) => commute_equiv defs s12 s21
    | (Abort a1 s1, Abort a2 s2) =>
        a1 = a2 /\ s1.vs_returndata = s2.vs_returndata
    | (Halt s1, Halt s2) => s1.vs_returndata = s2.vs_returndata
    | (IntRet v1 _, IntRet v2 _) => v1 = v2
    | (Error _, _) => T
    | (_, Error _) => T
    | _ => F) /\
    (!s12 s21. r1 = OK s12 /\ r2 = OK s21 ==>
      s12.vs_outcomes = s21.vs_outcomes /\
      s12.vs_requests = s21.vs_requests)
Proof
  rpt gen_tac >> strip_tac >> drule_all effects_independent_commute >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp_tac std_ss [LET_THM] >> strip_tac >> ASM_REWRITE_TAC[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all commute_equiv_oracle >> simp[]
QED
