Theory ctorDeployMemoryRunMemEntryImmutableFrame
Ancestors
  abiEncoderRegisteredEffect abiDecodeStaticProps valueEncoding venomState
  finite_map pred_set list arithmetic venomExecSemantics venomMemProofs
  fragGasPathMem

Theorem ctor_registered_immutable_byte_frame:
  abi_encoder_registered_effect ids [] s t /\
  (!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> cap <= b) ==>
  !a. a < cap ==>
    mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> disj1_tac >>
  `cap <= b` by metis_tac[] >> decide_tac
QED

Theorem ctor_registered_immutable_prefix_frame:
  abi_encoder_registered_effect ids [] s t /\
  (!i b sz. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> cap <= b) ==>
  mem_bytes_at 0 cap t.vs_memory = mem_bytes_at 0 cap s.vs_memory
Proof
  strip_tac >> irule mem_bytes_at_bytewise >> simp[] >>
  rpt strip_tac >> irule ctor_registered_immutable_byte_frame >>
  qexistsl [`cap`, `ids`] >> simp[] >> metis_tac[]
QED

Theorem ctor_eval_phis_alloca_fields:
  !insts s t. eval_phis s insts = OK t ==>
    t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def] >> metis_tac[]
QED

Theorem ctor_exec_alloca_lower_bound:
  exec_alloca inst s sz = OK t /\ cap <= s.vs_alloca_next /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==> cap <= b) ==>
  cap <= t.vs_alloca_next /\
  (!i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==> cap <= b)
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_ADD]
QED

Theorem ctor_bind_outputs_alloca_fields:
  !outs vals s t. bind_outputs outs vals s = SOME t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[bind_outputs_def, AllCaseEqs()] >>
  `!xs s. (FOLDL (\s (out,v). update_var out v s) s xs).vs_allocas = s.vs_allocas /\
           (FOLDL (\s (out,v). update_var out v s) s xs).vs_alloca_next = s.vs_alloca_next`
    by (Induct >> simp[] >> Cases_on `h` >> simp[update_var_def]) >>
  metis_tac[]
QED

Theorem ctor_step_inst_lower_bound:
  step_inst fuel ctx inst s = OK t /\ cap <= s.vs_alloca_next /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==> cap <= b) ==>
  cap <= t.vs_alloca_next /\
  (!i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==> cap <= b)
Proof
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once step_inst_def, AllCaseEqs()] >> rpt strip_tac >>
      drule ctor_bind_outputs_alloca_fields >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >>
      metis_tac[]) >>
  simp[Once step_inst_def] >> strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      drule ctor_exec_alloca_lower_bound >>
      disch_then (qspec_then `cap` mp_tac) >> simp[] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next`
    by (irule step_inst_base_preserves_alloca_fields >> simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem ctor_gas_path_mem_edge_lower_bound:
  gas_path_mem_edge ctx fn s g (OK t) /\ cap <= s.vs_alloca_next /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==> cap <= b) ==>
  cap <= t.vs_alloca_next /\
  (!i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==> cap <= b)
Proof
  simp[gas_path_mem_edge_def, fragExecTheory.exit_result_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac ctor_eval_phis_alloca_fields >>
  gvs[] >> metis_tac[ctor_step_inst_lower_bound]
QED

Theorem ctor_gas_path_mem_lower_bound:
  !ctx fn s g r. gas_path_mem ctx fn s g r ==>
  !t cap. r = OK t /\ cap <= s.vs_alloca_next /\
  (!i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==> cap <= b) ==>
  cap <= t.vs_alloca_next /\
  (!i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==> cap <= b)
Proof
  ho_match_mp_tac gas_path_mem_ind >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      rename1 `gas_path_mem_edge ctx fn s n (OK mid)` >>
      `cap <= mid.vs_alloca_next /\
       (!i b n. FLOOKUP mid.vs_allocas i = SOME (b,n) ==> cap <= b)`
        by (irule ctor_gas_path_mem_edge_lower_bound >>
            goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem ctor_registered_path_immutable_prefix:
  gas_path_mem ctx fn s g (OK t) /\
  s.vs_allocas = FEMPTY /\ cap <= s.vs_alloca_next /\
  abi_encoder_registered_effect ids [] s t ==>
  mem_bytes_at 0 cap t.vs_memory = mem_bytes_at 0 cap s.vs_memory
Proof
  strip_tac >> irule ctor_registered_immutable_prefix_frame >>
  qexists `ids` >> simp[] >>
  `cap <= t.vs_alloca_next /\
   (!i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==> cap <= b)`
    by (drule ctor_gas_path_mem_lower_bound >>
        disch_then (qspecl_then [`t`, `cap`] mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED
