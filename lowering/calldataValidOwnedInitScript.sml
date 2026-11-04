(* Successful array initialization with actual-site allocation resources. *)
Theory calldataValidOwnedInit
Ancestors
  calldataDynOwned calldataDynInit actualAllocExec allocaFrontierBound
  abiDecoderArrayLoopInit abiDecoderDynarrayBound abiDecoderReservation
  abiDecoderFrameCompose
  allocaBudgetProps abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderGuards abiDecoderIndexInit abiDecoderFrame abiDecoderContract
  abiDecoderExecution emitHelperProps exprLoweringProps compileEnv emitHelper
  venomState venomInst venomExecSemantics valueEncodingProps finite_map words
  arithmetic list rich_list

Theorem calldata_array_loop_init_valid_sequence:
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
  (d+sz <= p \/ p+32 <= d) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `?cop. abi_decode_count_guard CALLDATALOAD src maxn st = (cop,guard_st)` by
    (qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
          comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `abi_decode_load CALLDATALOAD srcword initial =
     n2w (w2n (abi_decode_load CALLDATALOAD srcword initial))` by simp[] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  qpat_x_assum `abi_decode_load CALLDATALOAD srcword initial = n2w _` kall_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) initial = OK g` >>
  `g.vs_allocas = initial.vs_allocas /\ g.vs_alloca_next = initial.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     goal_assum (drule_at Any) >> fs[EVERY_MEM]) >>
  `eval_operand src g = SOME srcword /\ eval_operand dst g = SOME (n2w d)` by
    metis_tac[] >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) g = OK h` >>
  `h.vs_allocas = initial.vs_allocas /\ h.vs_alloca_next = initial.vs_alloca_next` by
    (`h.vs_allocas = g.vs_allocas /\ h.vs_alloca_next = g.vs_alloca_next` by
       (irule abi_decode_sequence_allocation_frame >>
        goal_assum (drule_at Any) >> fs[EVERY_MEM]) >> simp[]) >>
  `?allocated. step_inst_base (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString header_st.cs_next_var)]) h = OK allocated /\
     eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
     p+32 <= allocated.vs_alloca_next /\
     FLOOKUP allocated.vs_allocas header_st.cs_next_id = SOME (p,32)` by
    suspend "allocation" >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  drule_all calldata_index_init_frame >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  suspend "compose"
QED

Resume calldata_array_loop_init_valid_sequence[allocation]:
  qabbrev_tac `inst = mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString header_st.cs_next_var)] /\
   inst.inst_id = header_st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> drule calldata_index_init_instructions >> simp[Abbr `inst`]) >>
  `alloca_frontier_inv ctx fn site h` by
    (fs[alloca_frontier_inv_def, remaining_alloca_budget_def]) >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac
  >- (`FLOOKUP h.vs_allocas inst.inst_id = NONE` by metis_tac[] >>
      drule_all actual_word_alloca_fresh_run >> strip_tac >>
      qexists_tac `t` >>
      gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE] >> decide_tac) >>
  `FLOOKUP h.vs_allocas inst.inst_id = SOME (p,32)` by metis_tac[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >> qexists_tac `t` >>
  gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def,
      FLOOKUP_UPDATE]
QED

Resume calldata_array_loop_init_valid_sequence[compose]:
  qexists_tac `mstore p 0w allocated` >>
  `run_inst_seq (emitted_insts st loop_st) initial = OK (mstore p 0w allocated)` by
    (asm_rewrite_tac[] >>
     qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
     qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
     qpat_assum `run_inst_seq _ h = OK (mstore p 0w allocated)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[run_inst_seq_append]) >>
  `abi_decode_load CALLDATALOAD srcword g =
     abi_decode_load CALLDATALOAD srcword initial` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  `mem_word_at d (mstore p 0w allocated).vs_memory =
     abi_decode_load CALLDATALOAD srcword initial` by
    (`mem_word_at d (mstore p 0w allocated).vs_memory = mem_word_at d h.vs_memory` by
       (irule abi_decode_frame_mem_word >>
        goal_assum (drule_at Any) >> decide_tac) >>
     asm_rewrite_tac[]) >>
  simp[mstore_def, write_memory_with_expansion_def] >> metis_tac[]
QED

Finalise calldata_array_loop_init_valid_sequence
