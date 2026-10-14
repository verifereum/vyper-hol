(* TASK038: additive projections of ACTUALLY proved legacy simulations.
 * TOP-LEVEL: DSE dead-store/clear-nops, m2v abort/block/function, memzero block.
 * No corollary of copy-forward/ICF/DSE admitted function simulators is claimed.
 * ALL original hypotheses, witnesses and full result relations are retained. *)
Theory remainingOracleSim
Ancestors
  remainingOracleCoverage remainingOracleLift
  deadStoreElimDefs deadStoreElimProofs
  mem2varDefs mem2varProofs mem2varBlockSimHelpers mem2varBlockSim mem2varCorrectness
  mmCorrectnessProofs mmTransform
  venomState venomInst venomWf venomExecSemantics venomMemDefs
  passSimulationDefs passSharedDefs pointerConfinedDefs
  stateEquiv pred_set list words

Theorem dse_dead_store_step_oracle:
  !dead_ids space fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_memory_def_opcode space inst.inst_opcode /\
    inst.inst_outputs = [] /\ effects_in_space space inst ==>
    dse_equiv space s' s /\
    s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  rpt strip_tac >>
  drule_all_then (qspec_then `dead_ids` assume_tac) dse_dead_store_step_sim_ok >>
  drule dse_equiv_oracle >> simp[]
QED

Theorem clear_nops_function_dse_oracle:
  !space fuel ctx fn s.
    wf_function fn /\ s.vs_inst_idx = 0 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx (clear_nops_function fn) s) /\
    lift_result
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx (clear_nops_function fn) s)
Proof
  rpt strip_tac >>
  drule_all_then (qspecl_then [`space`, `fuel`, `ctx`] assume_tac)
    clear_nops_function_dse_equiv >>
  drule dse_equiv_lift_result_oracle >> simp[]
QED

Theorem m2v_nonterminal_abort_oracle:
  !fn inst s1 s2 a s1' fuel ctx.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s1 = Abort a s1' /\
    m2v_inv_noix fn s1 s2 /\ MEM inst (fn_insts fn) /\
    m2v_fresh_names_disjoint fn ==>
    ?s2'. step_inst fuel ctx (HD (m2v_rewrite_inst fn inst)) s2 = Abort a s2' /\
          m2v_inv_noix fn s1' s2' /\
          s1'.vs_outcomes = s2'.vs_outcomes /\ s1'.vs_requests = s2'.vs_requests
Proof
  rpt strip_tac >> drule_all m2v_nonterminal_abort_sim >> strip_tac >>
  qexists_tac `s2'` >> drule m2v_inv_noix_oracle >> simp[]
QED

Theorem m2v_per_block_oracle:
  !fn.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\ m2v_return_size_bounded fn /\
    alloca_pointer_confined fn /\ all_mem_via_pointer fn (alloca_roots fn) /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> RETFMP) bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions) fn.fn_blocks ==>
    !bb. MEM bb fn.fn_blocks ==>
    !fuel ctx s1 s2.
      m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\ m2v_ao_undef_sync fn s1 s2 /\
      m2v_fresh_undef fn s1 /\ alloca_inv s1 /\ alloca_bridge fn s1 /\
      s1.vs_alloca_next < dimword (:256) /\ m2v_nonpromoted_access_safe fn s1 /\
      s1.vs_alloca_next = s2.vs_alloca_next /\ m2v_pvars_set fn bb 0 s2 /\
      (!i fuel' ctx' s s'. i < LENGTH bb.bb_instructions /\
        m2v_nonpromoted_access_safe fn s /\
        step_inst fuel' ctx' (EL i bb.bb_instructions) s = OK s' ==>
        m2v_nonpromoted_access_safe fn s') /\
      (!inst fuel' ctx' s s'. MEM inst (fn_insts fn) /\
        s.vs_alloca_next < dimword (:256) /\
        step_inst fuel' ctx' inst s = OK s' ==>
        s'.vs_alloca_next < dimword (:256)) /\ s1.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s1 = Error e) \/
      (lift_result (\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                           m2v_ao_undef_sync fn s1 s2 /\
                           s1.vs_alloca_next = s2.vs_alloca_next)
                  (m2v_equiv (m2v_fresh_vars fn)) (m2v_equiv (m2v_fresh_vars fn))
        (exec_block fuel ctx bb s1) (exec_block fuel ctx (m2v_bt fn bb) s2) /\
       lift_result
         (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
         (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
         (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
         (exec_block fuel ctx bb s1) (exec_block fuel ctx (m2v_bt fn bb) s2))
Proof
  rpt strip_tac >>
  drule_all_then (qspecl_then [`fuel`, `ctx`] mp_tac) m2v_per_block_sim >> strip_tac
  >- simp[] >> disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (Q.INST [`P` |-> `\s1 s2. m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\ s1.vs_alloca_next = s2.vs_alloca_next`]
    m2v_inv_lift_result_oracle) >> qexists_tac `fn` >> simp[]
QED

Theorem m2v_transform_function_oracle:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\ m2v_promotable_wf fn /\
    m2v_fresh_names_disjoint fn /\ m2v_fresh_undef fn s /\ alloca_inv s /\
    s.vs_allocas = FEMPTY /\ m2v_nonpromoted_access_safe fn s /\
    (!inst fuel' ctx' s' s''.
      MEM inst (fn_insts fn) /\ m2v_nonpromoted_access_safe fn s' /\
      step_inst fuel' ctx' inst s' = OK s'' ==> m2v_nonpromoted_access_safe fn s'') /\
    (!bb fuel' ctx' s' s''.
      MEM bb fn.fn_blocks /\ m2v_nonpromoted_access_safe fn s' /\
      run_block fuel' ctx' bb s' = OK s'' ==> m2v_nonpromoted_access_safe fn s'') /\
    (!inst fuel' ctx' s' s''.
      MEM inst (fn_insts fn) /\ s'.vs_alloca_next < dimword (:256) /\
      step_inst fuel' ctx' inst s' = OK s'' ==> s''.vs_alloca_next < dimword (:256)) /\
    (!bb fuel' ctx' s' s''.
      MEM bb fn.fn_blocks /\ s'.vs_alloca_next < dimword (:256) /\
      exec_block fuel' ctx' bb s' = OK s'' ==> s''.vs_alloca_next < dimword (:256)) /\
    alloca_pointer_confined fn /\ all_mem_via_pointer fn (alloca_roots fn) /\
    m2v_promo_sizes_bounded fn /\ m2v_return_size_bounded fn /\
    s.vs_alloca_next < dimword (:256) /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> MSIZE) bb.bb_instructions) fn.fn_blocks /\
    alloca_bridge fn s /\
    (!bb fuel' ctx' s' s''.
      MEM bb fn.fn_blocks /\ alloca_bridge fn s' /\
      run_block fuel' ctx' bb s' = OK s'' ==> alloca_bridge fn s'') /\
    fn_reachable fn s.vs_current_bb /\ m2v_pvars_at_current fn s /\
    (!bb fuel' ctx' s1 s2 s1' s2'.
      wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
      alloca_pointer_confined fn /\ MEM bb fn.fn_blocks /\
      bb.bb_label = s2.vs_current_bb /\ s1.vs_current_bb = s2.vs_current_bb /\
      fn_reachable fn s1.vs_current_bb /\
      run_block fuel' ctx' bb s1 = OK s1' /\
      run_block fuel' ctx' (m2v_bt fn bb) s2 = OK s2' /\
      ~s1'.vs_halted /\ s1'.vs_current_bb = s2'.vs_current_bb /\
      m2v_pvars_at_current fn s2 ==> m2v_pvars_at_current fn s2') /\
    (!bb fuel' ctx' s1 s2.
      wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
      m2v_promotable_wf fn /\ m2v_fresh_names_disjoint fn /\
      m2v_promo_sizes_bounded fn /\ m2v_return_size_bounded fn /\
      alloca_pointer_confined fn /\ all_mem_via_pointer fn (alloca_roots fn) /\
      EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions) fn.fn_blocks /\
      EVERY (\bb. EVERY (\i. i.inst_opcode <> MSIZE) bb.bb_instructions) fn.fn_blocks /\
      MEM bb fn.fn_blocks /\ m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
      m2v_ao_undef_sync fn s1 s2 /\ m2v_fresh_undef fn s1 /\
      alloca_inv s1 /\ alloca_bridge fn s1 /\ s1.vs_alloca_next < dimword (:256) /\
      m2v_nonpromoted_access_safe fn s1 /\ s1.vs_alloca_next = s2.vs_alloca_next /\
      m2v_pvars_at_current fn s2 ==>
      (?e. run_block fuel' ctx' bb s1 = Error e) \/
      lift_result (\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                           m2v_ao_undef_sync fn s1 s2 /\
                           s1.vs_alloca_next = s2.vs_alloca_next)
                  (m2v_equiv (m2v_fresh_vars fn)) (m2v_equiv (m2v_fresh_vars fn))
        (run_block fuel' ctx' bb s1) (run_block fuel' ctx' (m2v_bt fn bb) s2)) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    (lift_result (m2v_equiv (m2v_fresh_vars fn)) (m2v_equiv (m2v_fresh_vars fn))
       (m2v_equiv (m2v_fresh_vars fn))
       (run_blocks fuel ctx fn s) (run_blocks fuel ctx (m2v_transform_function fn) s) /\
     lift_result
       (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
       (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
       (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
       (run_blocks fuel ctx fn s) (run_blocks fuel ctx (m2v_transform_function fn) s))
Proof
  rpt strip_tac >>
  drule_all_then (qspecl_then [`fuel`, `ctx`] mp_tac)
    m2v_transform_function_correct >> strip_tac
  >- simp[] >> disj2_tac >>
  drule m2v_equiv_lift_result_oracle >> simp[]
QED

Theorem mm_block_memzero_oracle:
  !dfg bb fresh.
    mm_block_fresh_memzero dfg bb SUBSET fresh /\ EVERY inst_wf bb.bb_instructions /\
    memzero_block_wf dfg bb /\
    (!x. MEM (Var x) (LAST bb.bb_instructions).inst_operands ==> x NOTIN fresh) ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s) (exec_block fuel ctx (transform_block_memzero dfg bb) s) /\
      lift_result
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (exec_block fuel ctx bb s) (exec_block fuel ctx (transform_block_memzero dfg bb) s)
Proof
  rpt strip_tac >>
  drule_all_then (qspecl_then [`fuel`, `ctx`] assume_tac) mm_block_simulates_memzero >>
  drule remaining_state_lift_result_oracle >> simp[]
QED
