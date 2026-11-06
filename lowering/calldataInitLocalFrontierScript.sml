Theory calldataInitLocalFrontier
Ancestors
  calldataDynOwned allocaBudgetMonotone calldataDynInit actualAllocExec
  allocaFrontierBound allocaBudgetProps abiDecoderIndexInit abiDecoderContract
  emitHelper venomState venomInst venomExecSemantics venomMemProps venomMemDefs
  finite_map words arithmetic list fragExecMem

Theorem calldata_index_init_local_frontier_after_alloca[local]:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s ==>
  alloca_inv (mstore p 0w allocated) /\
  alloca_frontier_inv ctx fn site (mstore p 0w allocated) /\
  s.vs_alloca_next <= (mstore p 0w allocated).vs_alloca_next /\
  (!id b cap. FLOOKUP s.vs_allocas id = SOME (b,cap) ==>
    FLOOKUP (mstore p 0w allocated).vs_allocas id = SOME (b,cap))
Proof
  strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA` by simp[Abbr `inst`, mk_inst_def] >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> drule calldata_index_init_instructions >>
     simp[Abbr `inst`]) >>
  `alloca_inv allocated` by metis_tac[actual_alloca_slots_preserved] >>
  `alloca_frontier_inv ctx fn site allocated` by
    metis_tac[actual_alloca_frontier_member_preserved] >>
  conj_tac
  >- (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
          mstore_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[alloca_frontier_inv_def, remaining_alloca_budget_def,
         mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, mstore_def,
      write_memory_with_expansion_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `id = inst.inst_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem calldata_index_init_local_frontier_fields:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
   (FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= s.vs_alloca_next)) /\
  (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
  (if FLOOKUP s.vs_allocas st.cs_next_id = NONE then
     t.vs_alloca_next = s.vs_alloca_next+32
   else t.vs_alloca_next = s.vs_alloca_next) ==>
  alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!id b cap. FLOOKUP s.vs_allocas id = SOME (b,cap) ==>
    FLOOKUP t.vs_allocas id = SOME (b,cap))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> drule calldata_index_init_instructions >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `?a. step_inst_base inst s = OK a /\
    a.vs_allocas = t.vs_allocas /\ a.vs_alloca_next = t.vs_alloca_next` by
    suspend "transition" >>
  `alloca_inv a` by metis_tac[actual_alloca_slots_preserved] >>
  `alloca_frontier_inv ctx fn site a` by metis_tac[actual_alloca_frontier_member_preserved] >>
  conj_tac
  >- (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac >>
  gvs[] >> rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[]
QED

Resume calldata_index_init_local_frontier_fields[transition]:
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac
  >- (`FLOOKUP s.vs_allocas inst.inst_id = NONE` by simp[] >>
      drule_all actual_word_alloca_fresh_run >> strip_tac >>
      qexists_tac `t'` >> gvs[] >>
      simp_tac bool_ss [fmap_eq_flookup] >> gen_tac >> Cases_on `x = st.cs_next_id` >>
      gvs[FLOOKUP_UPDATE]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)` by simp[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  qexists_tac `t'` >> gvs[] >>
  simp_tac bool_ss [fmap_eq_flookup] >> gen_tac >> Cases_on `x = st.cs_next_id` >> gvs[]
QED

Finalise calldata_index_init_local_frontier_fields

Theorem calldata_array_loop_init_local_frontier_owned:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\ fresh_vars_wrt st initial /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
    p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\ alloca_inv initial ==>
  frag_exec_mem ctx st loop_st (\s. s = initial)
    (\t. (?q. q = p /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand ip t = SOME (n2w q) /\ mload q t = 0w /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
      fresh_vars_wrt loop_st t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= q \/ q+32 <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
      (!id. id <> header_st.cs_next_id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (q,32) /\
      (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
         t.vs_alloca_next = initial.vs_alloca_next+32
       else t.vs_alloca_next = initial.vs_alloca_next)) /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
      initial.vs_alloca_next <= t.vs_alloca_next /\
      (!id b cap. FLOOKUP initial.vs_allocas id = SOME (b,cap) ==>
        FLOOKUP t.vs_allocas id = SOME (b,cap)))
    (\r. ?u. r = Abort Revert_abort u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_array_loop_init_safe >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  drule_all calldata_index_init_local_frontier_fields >> strip_tac >> asm_rewrite_tac[]
QED
