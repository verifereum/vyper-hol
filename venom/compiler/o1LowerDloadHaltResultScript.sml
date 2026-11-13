(* Terminal observations at a joint source instruction boundary. *)
Theory o1LowerDloadHaltResult
Ancestors
  o1LowerDloadJointRangeCopy o1LowerDloadShared o1LowerDloadJointRelation
  o1LowerDloadOccurrence ptrDiscipline venomExecSemantics opcodeClass
  venomState pred_set list o1LowerDloadJointScalar pointerConfinedDefs
  memLocDefs unitShapeDefs o1LowerDloadRangeTransport contextCodegenRel vfmState
  memSafeRun

Theorem ld_joint_final_taint:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Halt s1 ==>
  final_taint vs C s1 (step_taint inst s s1 tn) (ret_taint tn inst s)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  simp[final_taint_def] >> metis_tac[]
QED

Theorem ld_joint_halt_taint_within:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ taint_within D C vs /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Halt s1 ==>
  (step_taint inst s s1 tn).t_stor SUBSET
    D.d_stor s1.vs_call_ctx.cc_address
      (s1.vs_accounts s1.vs_call_ctx.cc_address).storage /\
  (step_taint inst s s1 tn).t_trans SUBSET
    D.d_trans s1.vs_call_ctx.cc_address
      (s1.vs_transient s1.vs_call_ctx.cc_address) /\
  (step_taint inst s s1 tn).t_imm SUBSET D.d_imm s1.vs_immutables /\
  ret_taint tn inst s SUBSET D.d_ret s1.vs_returndata
Proof
  strip_tac >>
  `final_taint vs C s1 (step_taint inst s s1 tn) (ret_taint tn inst s)` by
    (irule ld_joint_final_taint >> metis_tac[]) >>
  fs[taint_within_def] >> metis_tac[]
QED

Theorem ld_joint_stop_sink_result:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ taint_within D C vs /\
  active_inst fn inst s /\
  (inst.inst_opcode = STOP \/ inst.inst_opcode = SINK) /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  drule_all ld_joint_halt_taint_within >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_returndata = t.vs_returndata` by fs[ld_joint_boundary_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> strip_tac >> gvs[] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   irule (Q.INST [`A` |-> `s.vs_call_ctx.cc_address`,
                  `tn` |-> `tn`, `R` |-> `{}`] ld_shared_halt_result) >>
   gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, ret_taint_def, ld_shared_agree_def] >>
   qexists_tac `tn` >> simp[])
QED

Theorem ld_joint_selfdestruct_operand[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = SELFDESTRUCT ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  rpt strip_tac >> drule (cj 3 ld_joint_scalar_operands_clean) >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >>
  simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def,
       retpc_use_ok_def] >>
  (impl_tac >- (rpt strip_tac >> gvs[taint_ok_def] >> metis_tac[])) >>
  simp[]
QED

Theorem ld_joint_return_length[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sz] ==>
  eval_operand sz s = eval_operand sz t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn sz = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  drule ld_joint_nonaddress_operand >> disch_then irule >>
  gvs[is_pointer_preserving_op_def, retpc_use_ok_def] >>
  Cases_on `addr = sz` >> simp[mem_read_ops_def, mem_write_ops_def]
QED

Theorem ld_joint_return_slice[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sz] /\
  eval_operand addr s = SOME p /\ eval_operand sz s = SOME len ==>
  ?q. eval_operand addr t = SOME q /\ eval_operand sz t = SOME len /\
    (!k. k < w2n len /\ k NOTIN ret_taint tn inst s ==>
      EL k (read_memory (w2n p) (w2n len) s) =
      EL k (read_memory (w2n q) (w2n len) t))
Proof
  strip_tac >>
  `eval_operand sz s = eval_operand sz t` by
    (irule ld_joint_return_length >> metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?q. eval_operand addr t = SOME q /\
    (w2n len=0 \/ (w2n p=w2n q /\ w2n p+w2n len<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n len<=z /\
       w2n p=b+j /\ w2n q=c+j))` by
    (drule ld_joint_read_operand_range >>
     disch_then (qspecl_then [`p`,
       `<|iao_ofst := addr; iao_size := SOME sz; iao_max_size := SOME sz|>`,
       `addr`, `w2n len`] mp_tac) >>
     simp[mem_read_ops_def] >> disch_then irule >> simp[] >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, retpc_use_ok_def] >>
     gvs[]) >>
  qexists_tac `q` >> gvs[] >> rpt strip_tac >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`lo`,`tn.t_mem`,`sites`] >>
  gvs[ret_taint_def] >> fs[ld_joint_boundary_def] >> metis_tac[]
QED

Theorem ld_joint_return_result:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\ taint_within D C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = RETURN /\ step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  drule_all ld_joint_halt_taint_within >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[ld_joint_boundary_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> fs[] >>
  rename1 `inst.inst_operands = [addr;sizeop]` >>
  rename1 `eval_operand addr s = SOME p` >>
  rename1 `eval_operand sizeop s = SOME len` >>
  `?q. eval_operand addr t = SOME q /\ eval_operand sizeop t = SOME len /\
    (!k. k < w2n len /\ k NOTIN ret_taint tn inst s ==>
      EL k (read_memory (w2n p) (w2n len) s) =
      EL k (read_memory (w2n q) (w2n len) t))` by
    (irule ld_joint_return_slice >> metis_tac[]) >>
  gvs[] >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >> simp[] >>
  irule ld_shared_halt_result >>
  gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, ld_read_memory_length,
      GSYM read_memory_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`s.vs_call_ctx.cc_address`, `tn`] >> gvs[ld_shared_agree_def]
QED

Theorem ld_shared_balances[local]:
  ld_shared_agree D A tn s t ==>
  !a. (s.vs_accounts a).balance = (t.vs_accounts a).balance
Proof
  strip_tac >> gen_tac >> drule ld_shared_accounts_fields >>
  disch_then (qspec_then `a` (SUBST1_TAC o SYM)) >> simp[]
QED

Theorem ld_shared_selfdestruct_step[local]:
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  s.vs_call_ctx = t.vs_call_ctx /\ inst.inst_opcode = SELFDESTRUCT /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
    ld_shared_agree D s1.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    s1.vs_returndata = [] /\ t1.vs_returndata = [] /\
    s1.vs_halted = t1.vs_halted
Proof
  strip_tac >>
  `!a. (s.vs_accounts a).balance = (t.vs_accounts a).balance` by
    metis_tac[ld_shared_balances] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> fs[] >>
  rename1 `inst.inst_operands = [addr_op]` >>
  `eval_operand addr_op s = eval_operand addr_op t` by simp[] >>
  gvs[eval_operands_def, AllCaseEqs()] >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >> simp[] >>
  gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, lookup_account_def,
      vfmExecutionTheory.transfer_value_def, update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  qpat_x_assum `SOME _ = eval_operand _ _`
    (fn th => rewrite_tac[GSYM th]) >> simp[] >>
  gvs[ld_shared_agree_def, combinTheory.APPLY_UPDATE_THM] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[] >>
  simp[combinTheory.APPLY_UPDATE_THM] >> rpt IF_CASES_TAC >> gvs[] >>
  qpat_x_assum `!a. _ with storage := _ = _`
    (qspec_then `a` (SUBST1_TAC o SYM)) >> simp[] >>
  gvs[word_agree_except_def] >> metis_tac[]
QED

Theorem ld_joint_selfdestruct_result:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\ taint_within D C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = SELFDESTRUCT /\ step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  drule_all ld_joint_halt_taint_within >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_call_ctx = t.vs_call_ctx` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_joint_selfdestruct_operand >> metis_tac[]) >>
  drule_all ld_shared_selfdestruct_step >> disch_then (qspec_then `C'` strip_assume_tac) >>
  qexists_tac `t1` >> simp[] >>
  irule ld_shared_halt_result >> gvs[] >> conj_tac >- (qexists_tac `{}` >> simp[]) >>
  qexistsl_tac [`s1.vs_call_ctx.cc_address`, `step_taint inst s s1 tn`] >> simp[]
QED

Theorem ld_joint_halt_result:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  ptr_discipline lo C vs /\ taint_within D C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst) /\
  inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  drule step_inst_halt_opcodes >> strip_tac
  >- (irule ld_joint_stop_sink_result >> metis_tac[])
  >- (`~in_revert_forward fn s` by
        (simp[in_revert_forward_def] >> rpt strip_tac >> gvs[] >>
         drule_all revert_forward_at_opcode >> simp[]) >>
      irule ld_joint_return_result >> metis_tac[])
  >- (irule ld_joint_stop_sink_result >> metis_tac[])
  >- (irule ld_joint_selfdestruct_result >> metis_tac[]) >>
  gvs[]
QED
