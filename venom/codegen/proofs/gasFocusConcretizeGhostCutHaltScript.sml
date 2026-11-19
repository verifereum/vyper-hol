Theory gasFocusConcretizeGhostCutHalt
Ancestors
  concretizePtrDallocaHaltSteps concretizePtrDallocaObservationTransport
  concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrObservationInterface concretizePtrOwnershipErasure
  concretizePtrReturnTransport concretizePtrPairedPrefix concretizeStepShape
  lowerDloadTerminalObservation ptrDiscipline venomState finite_map pred_set
  contextCodegenRel words list pointerConfinedDefs memLocDefs
  concretizePtrPrefixLedger concretizeMemLocDefs
  concretizePtrDallocaGhostInterface concretizePtrChronologicalHistory
  concretizePtrOpaqueRetpc opcodeClass venomWf venomExecSemantics

(* The persistent fields and their masks come from the pre-instruction
   comparison, but the return mask is interpreted at the actual Halt posts. *)
Theorem focus_cut_halt_final_bounds[local]:
  dead_wf D /\ i.inst_opcode <> INVOKE /\ it.inst_opcode <> INVOKE /\
  step_inst fuel C i s = Halt sh /\ step_inst fuelt Ct it t = Halt th /\
  ptr_history_content tn s t /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  (step_taint i s sh tn).t_stor SUBSET D.d_stor sh.vs_call_ctx.cc_address
    (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
  (step_taint i s sh tn).t_trans SUBSET D.d_trans sh.vs_call_ctx.cc_address
    (sh.vs_transient sh.vs_call_ctx.cc_address) /\
  (step_taint i s sh tn).t_imm SUBSET D.d_imm sh.vs_immutables /\
  ret_taint tn i s SUBSET D.d_ret sh.vs_returndata /\
  ret_taint un it t SUBSET ret_taint tn i s /\
  LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
  (!k. k < LENGTH sh.vs_returndata /\ k NOTIN ret_taint tn i s ==>
    EL k sh.vs_returndata = EL k th.vs_returndata) ==>
  (step_taint it t th un).t_stor SUBSET D.d_stor th.vs_call_ctx.cc_address
    (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
  (step_taint it t th un).t_trans SUBSET D.d_trans th.vs_call_ctx.cc_address
    (th.vs_transient th.vs_call_ctx.cc_address) /\
  (step_taint it t th un).t_imm SUBSET D.d_imm th.vs_immutables /\
  ret_taint un it t SUBSET D.d_ret th.vs_returndata
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `step_inst fuel C i s = Halt sh`
    (mp_then (Pat `step_inst _ _ _ _ = Halt _`) mp_tac ld_noninvoke_halt_persistent) >>
  simp[] >> disch_then (qspec_then `tn` strip_assume_tac) >>
  qpat_assum `step_inst fuelt Ct it t = Halt th`
    (mp_then (Pat `step_inst _ _ _ _ = Halt _`) mp_tac ld_noninvoke_halt_persistent) >>
  simp[] >> disch_then (qspec_then `un` strip_assume_tac) >>
  drule ptr_history_content_call_ctx >> strip_tac >>
  qpat_assum `ptr_history_content tn s t`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [ptr_history_content_def, ptr_taint_content_def,
        contract_storage_def, contract_transient_def,
        vfmStateTheory.lookup_account_def]) >>
  `!k. k IN FDOM s.vs_immutables ==>
    word_agree_except {b | (k,b) IN tn.t_imm}
      (s.vs_immutables ' k) (t.vs_immutables ' k)` by
    ((rpt strip_tac >> first_x_assum irule >> fs[FLOOKUP_DEF] >> (gvs[FLOOKUP_DEF]))) >>
  mp_tac (Q.INST [`s` |-> `sh`, `t` |-> `th`, `tn` |-> `tn`, `tt` |-> `un`,
      `R` |-> `ret_taint tn i s`, `Rt` |-> `ret_taint un it t`]
    ptr_dalloca_final_taint_transport) >>
  gvs[]
QED

(* A slice of an allocation is compared at its allocation-relative index;
   unrelocated bytes use the shared absolute address instead. *)
Theorem focus_cut_halt_range_reflect[local]:
  (!i. (i < lo \/ dyn <= i) /\ i IN mt ==> i IN ms) /\
  (0 < len ==>
    (x = y /\ (x + len <= lo \/ dyn <= x)) \/
    (?base size pos.
      base <= x /\ x + len <= base + size /\ y = pos + (x - base) /\
      (!j. j < size /\ pos + j IN mt ==> base + j IN ms))) ==>
  !k. k < len /\ y + k IN mt ==> x + k IN ms
Proof
  strip_tac >> rpt strip_tac >>
  `0 < len` by decide_tac >>
  first_x_assum drule >>
  disch_then (DISJ_CASES_THEN2 (CONJUNCTS_THEN assume_tac) strip_assume_tac)
  >- (`x+k < lo \/ dyn <= x+k` by decide_tac >> metis_tac[]) >>
  rename1 `x + len <= obase + osize` >>
  qabbrev_tac `j = (x - obase) + k` >>
  `j < osize /\ pos + j = y + k /\ obase + j = x + k` by
    (simp[Abbr `j`] >> decide_tac) >>
  metis_tac[]
QED

(* SELFDESTRUCT has no pointer operand. Its operand is compared as a
   scalar, including on the path on which the halt itself is static. *)
Theorem focus_cut_selfdestruct_eval[local]:
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\ ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  taint_ok f tn i s /\ EVERY (ptr_nonopaque_operand f) i.inst_operands /\
  i.inst_opcode = SELFDESTRUCT ==>
  eval_operands i.inst_operands s = eval_operands i.inst_operands t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. MEM (Var v) i.inst_operands ==> v NOTIN pv` by
    (fs[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def,
        mem_read_ops_def] >> metis_tac[]) >>
  irule (INST_TYPE [alpha |-> ``:num``] ptr_mixed_scalar_operands_equal) >> simp[] >>
  qpat_assum `ptr_mixed_vars _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> fs[FLOOKUP_DEF, SUBSET_DEF] >>
     metis_tac[]) >>
  `op_prov TG op = NONE` by
    (drule ptr_owner_op_projection >> disch_then (qspec_then `op` mp_tac) >>
     Cases_on `op_prov TG op` >> simp[ptr_owner_erases_def, FLOOKUP_DEF]) >>
  fs[EVERY_MEM, taint_ok_def] >> metis_tac[]
QED

(* Invert the target RETURN and transport its two actually evaluated
   operands. The source slice and equal width are not extra assumptions. *)
Theorem focus_cut_return_operands[local]:
  ptr_ledger_erases dyn births TG G /\
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\ ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  taint_ok f tn i s /\ EVERY (ptr_nonopaque_operand f) i.inst_operands /\
  inst_wf i /\ i.inst_opcode = RETURN /\ step_inst fuelt Ct i t = Halt th ==>
  ?addr lenop x y sz.
    i.inst_operands = [addr;lenop] /\
    eval_operand addr s = SOME x /\ eval_operand addr t = SOME y /\
    eval_operand lenop s = SOME sz /\ eval_operand lenop t = SOME sz /\
    MEM (w2n x,w2n sz) (source_memory_read_ranges i s) /\
    ptr_lookup_transport births positions (op_prov TG addr) {} (SOME x) (SOME y)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?addr lenop. i.inst_operands = [addr;lenop]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `?off width. eval_operand addr t = SOME off /\ eval_operand lenop t = SOME width` by
    (qpat_x_assum `step_inst fuelt Ct i t = Halt th` mp_tac >>
     simp[Once step_inst_non_invoke, step_inst_base_def,
          eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM (w2n off,w2n width) (source_memory_read_ranges i t)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `ptr_nonopaque_operand f addr /\ ptr_nonopaque_operand f lenop` by fs[] >>
  Q.SUBGOAL_THEN `i.inst_opcode = RETURN \/ i.inst_opcode = REVERT`
    assume_tac >- simp[] >>
  drule_all ptr_terminal_read_range_transport >> simp[] >> metis_tac[]
QED

Theorem focus_cut_paired_halt_observation:
  dead_wf D /\ ptr_observation_reachable vs C a /\
  active_inst a.po_fn a.po_inst a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_paired_sample positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  ptr_ledger_erases dyn births TG a.po_prov /\
  ptr_use_ok P pv a.po_inst /\ FDOM a.po_prov SUBSET pv /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands /\
  inst_wf a.po_inst /\ ~in_revert_forward a.po_fn a.po_state /\
  at.po_taint.t_stor SUBSET a.po_taint.t_stor /\
  at.po_taint.t_trans SUBSET a.po_taint.t_trans /\
  at.po_taint.t_imm SUBSET a.po_taint.t_imm /\
  (!k. (k < lo \/ dyn <= k) /\ k IN at.po_taint.t_mem ==> k IN a.po_taint.t_mem) /\
  (!v token aid obase osize pos j.
    inst_read_op a.po_inst = SOME (Var v) /\
    FLOOKUP TG v = SOME (token,aid) /\ FLOOKUP a.po_prov v = SOME (obase,osize) /\
    FLOOKUP births (token,aid) = SOME (obase,osize) /\
    FLOOKUP positions (Allocation aid) = SOME (pos,osize) /\ j < osize /\
    pos + j IN at.po_taint.t_mem ==> obase + j IN a.po_taint.t_mem) /\
  (!addr x y len.
    a.po_inst.inst_opcode = RETURN /\ inst_read_op a.po_inst = SOME addr /\
    eval_operand addr a.po_state = SOME x /\ eval_operand addr at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG addr) {} (SOME x) (SOME y) ==>
    (0 < len ==>
      (x = y /\ (w2n x + len <= lo \/ dyn <= w2n x)) \/
      (?v token aid obase osize pos.
        addr = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
        FLOOKUP a.po_prov v = SOME (obase,osize) /\
        FLOOKUP births (token,aid) = SOME (obase,osize) /\
        FLOOKUP positions (Allocation aid) = SOME (pos,osize) /\
        obase <= w2n x /\ w2n x + len <= obase + osize /\ w2n y = pos + (w2n x - obase))) /\
    (!k. k < len /\ w2n x + k NOTIN a.po_taint.t_mem ==>
      read_byte (w2n x + k) a.po_state.vs_memory = read_byte (w2n y + k) at.po_state.vs_memory)) /\
  (!sh. step_inst 0 C a.po_inst a.po_state = Halt sh ==>
    (step_taint a.po_inst a.po_state sh a.po_taint).t_stor SUBSET
      D.d_stor sh.vs_call_ctx.cc_address (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
    (step_taint a.po_inst a.po_state sh a.po_taint).t_trans SUBSET
      D.d_trans sh.vs_call_ctx.cc_address (sh.vs_transient sh.vs_call_ctx.cc_address) /\
    (step_taint a.po_inst a.po_state sh a.po_taint).t_imm SUBSET D.d_imm sh.vs_immutables /\
    ret_taint a.po_taint a.po_inst a.po_state SUBSET D.d_ret sh.vs_returndata) /\
  at.po_inst.inst_opcode <> INVOKE /\ step_inst fuelt Ct at.po_inst at.po_state = Halt th ==>
  (step_taint at.po_inst at.po_state th at.po_taint).t_stor SUBSET
    D.d_stor th.vs_call_ctx.cc_address (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
  (step_taint at.po_inst at.po_state th at.po_taint).t_trans SUBSET
    D.d_trans th.vs_call_ctx.cc_address (th.vs_transient th.vs_call_ctx.cc_address) /\
  (step_taint at.po_inst at.po_state th at.po_taint).t_imm SUBSET D.d_imm th.vs_immutables /\
  ret_taint at.po_taint at.po_inst at.po_state SUBSET D.d_ret th.vs_returndata
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM at.po_inst.inst_opcode [ASSIGN;NOP]` by
    (drule step_inst_halt_opcodes >> strip_tac >> simp[]) >>
  `at.po_inst = a.po_inst` by metis_tac[concretize_positions_other_opcode] >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  gvs[ptr_paired_sample_def, ptr_observation_reachable_def] >>
  drule ptr_history_content_labels >> strip_tac >>
  drule ptr_history_content_call_ctx >> strip_tac >>
  drule ptr_history_content_returndata >> strip_tac >>
  `(a.po_inst.inst_opcode = SELFDESTRUCT ==>
    eval_operands a.po_inst.inst_operands a.po_state =
    eval_operands a.po_inst.inst_operands at.po_state)` by
    (strip_tac >> drule_all focus_cut_selfdestruct_eval >> simp[]) >>
  Q.SUBGOAL_THEN
    `a.po_inst.inst_opcode = RETURN ==>
      ?addr lenop x y sz.
        a.po_inst.inst_operands = [addr;lenop] /\
        eval_operand addr a.po_state = SOME x /\ eval_operand addr at.po_state = SOME y /\
        eval_operand lenop a.po_state = SOME sz /\ eval_operand lenop at.po_state = SOME sz /\
        (!k. k < w2n sz /\ w2n y + k IN at.po_taint.t_mem ==>
          w2n x + k IN a.po_taint.t_mem) /\
        (!k. k < w2n sz /\ w2n x + k NOTIN a.po_taint.t_mem ==>
          read_byte (w2n x + k) a.po_state.vs_memory = read_byte (w2n y + k) at.po_state.vs_memory)`
    assume_tac >- suspend "return_slice" >>
  suspend "halt_post"
QED

Resume focus_cut_paired_halt_observation[return_slice]:
  strip_tac >> drule_all focus_cut_return_operands >> strip_tac >>
  `inst_read_op a.po_inst = SOME addr` by simp[inst_read_op_def, mem_read_ops_def] >>
  qpat_assum `!addr x y len. _ ==> _ /\ _`
    (qspecl_then [`addr`,`x`,`y`,`w2n sz`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`addr`,`lenop`,`x`,`y`,`sz`] >> asm_rewrite_tac[] >>
  reverse conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> irule focus_cut_halt_range_reflect >>
  qexistsl [`dyn`,`w2n sz`,`lo`,`at.po_taint.t_mem`,`w2n y`] >> simp[] >>
  conj_tac >- gvs[] >>
  `0 < w2n sz` by decide_tac >> qpat_assum `0 < w2n sz ==> _` drule >>
  disch_then (DISJ_CASES_THEN2 (CONJUNCTS_THEN assume_tac) strip_assume_tac)
  >- (disj1_tac >> simp[arithmeticTheory.ADD_COMM]) >>
  disj2_tac >> rename1 `w2n sz + w2n x <= obase + osize` >>
  qexistsl [`obase`,`osize`,`pos`] >> simp[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Resume focus_cut_paired_halt_observation[halt_post]:
  `?sh. step_inst 0 C a.po_inst a.po_state = Halt sh /\
    final_taint vs C sh (step_taint a.po_inst a.po_state sh a.po_taint)
      (ret_taint a.po_taint a.po_inst a.po_state) /\
    ret_taint at.po_taint a.po_inst at.po_state SUBSET ret_taint a.po_taint a.po_inst a.po_state /\
    LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
    (!k. k < LENGTH sh.vs_returndata /\ k NOTIN ret_taint a.po_taint a.po_inst a.po_state ==>
      EL k sh.vs_returndata = EL k th.vs_returndata)` by
    (irule ptr_dalloca_halt_step >> asm_rewrite_tac[] >>
     conj_tac >- (qexistsl [`Ct`,`fuelt`] >> asm_rewrite_tac[]) >>
     reverse conj_tac >-
       (qexistsl [`a.po_prov`,`a.po_params`,`a.po_fn`,`a.po_stack`] >> asm_rewrite_tac[]) >>
     strip_tac >> qpat_assum `a.po_inst.inst_opcode = RETURN ==> _` drule >>
     disch_then (qx_choose_then `addr` (qx_choose_then `lenop` strip_assume_tac)) >>
     metis_tac[]) >>
  qpat_assum `!sh. step_inst 0 C _ _ = Halt sh ==> _` drule >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_cut_halt_final_bounds >> simp[]
QED

Finalise focus_cut_paired_halt_observation
