(* Execution-derived registered footprints, before broad interval enlargement. *)
Theory ctorAbiActualNarrow
Ancestors
  ctorAbiActualSites ctorAbiActualAlloc ctorAbiActualMemory ctorAbiActualFrame
  abiEncoderRegisteredEffect venomExecSemantics venomState venomInst
  finite_map pred_set list arithmetic words

Theorem ctor_actual_empty_effect:
  s.vs_allocas = t.vs_allocas /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_pending_deletions = s.vs_pending_deletions ==>
  abi_encoder_registered_effect {} outs s t
Proof
  simp[abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_sites_child_effect:
  abi_encoder_registered_effect (ctor_actual_sites fn child) [(c,k)] s t /\
  child SUBSET ids /\ d <= c /\ c+k <= d+n ==>
  abi_encoder_registered_effect (ctor_actual_sites fn ids) [(d,n)] s t
Proof
  strip_tac >> irule ctor_actual_child_effect >>
  qexistsl [`c`, `ctor_actual_sites fn child`, `k`] >> simp[] >>
  irule ctor_actual_sites_mono >> simp[]
QED

Theorem ctor_actual_word_alloca_narrow:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t p.
    step_inst_base inst s = OK t /\
    eval_operand (Var out) t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    regions_disjoint (d,n) (p,32) /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_encoder_registered_effect {inst.inst_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `ctor_actual_scratch fn {inst.inst_id} d n s` by
    (irule ctor_actual_scratch_restrict >> qexists `ids` >> simp[]) >>
  mp_tac (Q.INST [`ids` |-> `{inst.inst_id}`, `outs` |-> `[]`]
    ctor_actual_word_alloca_run) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all ctor_actual_word_alloca_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem ctor_actual_index_narrow:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `ctor_actual_scratch fn {st.cs_next_id} d n s` by
    (irule ctor_actual_scratch_restrict >> qexists `ids` >> simp[]) >>
  mp_tac (Q.INST [`ids` |-> `{st.cs_next_id}`, `outs` |-> `[]`]
    ctor_actual_index_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all ctor_actual_index_sequence >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED
