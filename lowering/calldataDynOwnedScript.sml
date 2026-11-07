(* Allocator ownership for the actual dynamic calldata shell. *)
Theory calldataDynOwned
Ancestors
  calldataDynInit calldataDynStep calldataChildFrame actualAllocExec fragExecMem
  allocaFrontierBound allocaBudgetProps abiDecoderIndexInit abiDecoderContract
  compileEnv emitHelper venomState venomInst venomExecSemantics venomMemProps venomMemDefs
  valueEncodingProps finite_map words arithmetic list rich_list
  abiDecoderIndexedAddress abiDecoderReentryAddress abiDecoderReentry
  abiDecoderGuards abiDecoderFrame emitHelperProps exprLoweringProps abiEncoder
  abiDecoderExecution valueEncoding safeSequence instIdxIndep
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs
  abiDecoderLoopEmit abiDecoderCounters abiDecoderDynarrayPrefix
  abiDecoderDynarrayBound abiDecoderArrayHeader abiDecoderReservation
  abiDecoderArrayLoopInit abiDecoderFrameCompose calldataWordLeaf calldataBytesLeaf

Theorem calldata_index_init_owned_after_alloca:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s
  ==>
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
    metis_tac[actual_alloca_frontier_preserved] >>
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

(* The value postcondition records the exact allocator fields.  Validate
   their ownership by the actual fresh-or-reused ALLOCA transition. *)
Theorem calldata_index_init_owned_fields:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
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
  `alloca_frontier_inv ctx fn site a` by metis_tac[actual_alloca_frontier_preserved] >>
  conj_tac
  >- (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[alloca_frontier_inv_def, remaining_alloca_budget_def] >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac >>
  gvs[] >> rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[]
QED

Resume calldata_index_init_owned_fields[transition]:
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

Finalise calldata_index_init_owned_fields

Theorem calldata_array_loop_init_owned:
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
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) ==>
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
  drule_all calldata_index_init_owned_fields >> strip_tac >> asm_rewrite_tac[]
QED

(* Syntactic protection, unlike fresh_vars_wrt, is repeatable. *)
Theorem calldata_operand_live_not_fresh:
  abi_decoder_operand_live st.cs_next_var (Var x) <=> not_fresh_at st x
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]
QED

Theorem calldata_update_protected:
  abi_decoder_operand_live next op ==>
  eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> first_x_assum (qspec_then `next` mp_tac) >> simp[]
QED

(* Full old-operand frame, including absent old variables, for the actual
   counter allocation and zero store.  No freshness premise is needed. *)
Theorem calldata_index_init_live_frame:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op (mstore p 0w allocated) = eval_operand op s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  simp[calldata_update_protected] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem calldata_array_header_live_frame:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op t = eval_operand op s
Proof
  simp[abiDecoderArrayHeaderTheory.abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND] >>
  `LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 1) = 0` by decide_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ s = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def, eval_operands_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_write2_def, eval_operands_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[eval_operand_mstore, calldata_update_protected]
QED

Theorem calldata_count_guard_live_frame:
  abi_decode_count_guard CALLDATALOAD src limit st = (cnt,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op t = eval_operand op s
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[emitted_insts_def, DROP_APPEND] >> strip_tac >>
  `LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 1) = 0 /\
   LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 2) = 0 /\
   LENGTH st.cs_current_insts - (LENGTH st.cs_current_insts + 3) = 0` by decide_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  `abi_decoder_operand_live (st.cs_next_var + 1) op /\
   abi_decoder_operand_live (st.cs_next_var + 2) op` by
    (Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `step_inst_base _ s = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_read1_def, eval_operands_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ (update_var _ _ s) = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_update_var] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ (update_var _ _ _) = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_pure1_def, eval_operands_def,
       eval_operand_def, lookup_var_update_var] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operands_def,
       eval_operand_def, lookup_var_update_var] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[calldata_update_protected]
QED

(* Use the very same successful phase executions for values, safety, and
   the full old-variable frame.  In particular, NONE is preserved too. *)
Theorem calldata_array_loop_init_safe_live:
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
  (d+sz <= p \/ p+32 <= d) ==>
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
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial))
    (\r. ?u. r = Abort Revert_abort u)
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
  `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `isPREFIX st.cs_current_insts loop_st.cs_current_insts` by
    (qpat_x_assum `inst_extends st loop_st` mp_tac >>
     simp_tac bool_ss [inst_extends_def] >> strip_tac >>
     simp_tac bool_ss [IS_PREFIX_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st loop_st)` by
    (asm_rewrite_tac[EVERY_APPEND] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
     (emitted_insts st loop_st)` by
    (imp_res_tac calldata_dynarray_prefix_opcodes >>
     imp_res_tac calldata_array_header_opcodes >>
     imp_res_tac abi_decode_index_init_opcodes >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  reverse (Cases_on `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn`)
  >- suspend "reject" >>
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
     FLOOKUP allocated.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP allocated.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
        allocated.vs_alloca_next = initial.vs_alloca_next+32
      else allocated.vs_alloca_next = initial.vs_alloca_next)` by
    suspend "allocation" >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  drule_all calldata_index_init_frame >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op (mstore p 0w allocated) = eval_operand op initial` by
    suspend "live" >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >>
  reverse conj_tac >- suspend "execution" >>
  suspend "safety"
QED

Resume calldata_array_loop_init_safe_live[live]:
  rpt strip_tac >>
  `abi_decoder_operand_live guard_st.cs_next_var op /\
   abi_decoder_operand_live header_st.cs_next_var op` by
    (Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `eval_operand op g = eval_operand op initial` by
    (qpat_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
     qpat_assum `abi_decoder_operand_live st.cs_next_var op` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[calldata_count_guard_live_frame]) >>
  `eval_operand op h = eval_operand op g` by
    (qpat_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
     qpat_assum `abi_decoder_operand_live guard_st.cs_next_var op` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[calldata_array_header_live_frame]) >>
  qpat_assum `step_inst_base _ h = OK allocated` mp_tac >>
  qpat_assum `abi_decoder_operand_live header_st.cs_next_var op` mp_tac >>
  qpat_assum `eval_operand op h = _` mp_tac >>
  qpat_assum `eval_operand op g = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  drule_all calldata_index_init_live_frame >> simp[]
QED

Resume calldata_array_loop_init_safe_live[execution]:
  disj1_tac >> qexists_tac `mstore p 0w allocated` >>
  `run_inst_seq (emitted_insts st guard_st ++
     emitted_insts guard_st header_st ++ emitted_insts header_st loop_st)
     initial = OK (mstore p 0w allocated)` by
    (qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
     qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
     qpat_assum `run_inst_seq _ h = OK (mstore p 0w allocated)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[run_inst_seq_append]) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac
  >- (irule calldata_init_index_transport >>
      SUBGOAL_THEN ``d+32 <= p \/ p+32 <= d`` assume_tac >- decide_tac >>
      `abi_decode_load CALLDATALOAD srcword g =
         abi_decode_load CALLDATALOAD srcword initial` by
        simp[abi_decode_load_def, abi_decode_source_def] >>
      drule_all calldata_init_frame_assemble >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `eval_operand cnt (mstore p 0w allocated) =
         SOME (abi_decode_load CALLDATALOAD srcword initial)` by metis_tac[] >>
      `(mstore p 0w allocated).vs_allocas = allocated.vs_allocas /\
       (mstore p 0w allocated).vs_alloca_next = allocated.vs_alloca_next` by
        simp[mstore_def, write_memory_with_expansion_def] >>
      qpat_x_assum `header_st.cs_next_var = _`
        (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_x_assum `header_st.cs_next_id = _`
        (fn th => pure_rewrite_tac[GSYM th]) >>
      qpat_x_assum `ip = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      asm_rewrite_tac[]) >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Resume calldata_array_loop_init_safe_live[safety]:
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `g` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `h` >> asm_rewrite_tac[] >> conj_tac
  >- (`d+32 <= g.vs_alloca_next` by (asm_rewrite_tac[] >> decide_tac) >>
      ho_match_mp_tac (GEN_ALL calldata_array_header_prefix_safe) >>
      goal_assum (drule_at (Pos hd)) >>
      qexistsl_tac [`srcword`, `d`] >> asm_rewrite_tac[]) >>
  ho_match_mp_tac (GEN_ALL calldata_index_init_prefix_safe) >>
  goal_assum (drule_at (Pos hd)) >> goal_assum (drule_at (Pos hd)) >>
  qexists_tac `p` >> asm_rewrite_tac[]
QED

Resume calldata_array_loop_init_safe_live[allocation]:
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

Resume calldata_array_loop_init_safe_live[reject]:
  `cs_extends st guard_st /\ cs_extends guard_st loop_st` by
    (conj_tac >> irule cs_extends_same_block >>
     simp[] >> metis_tac[inst_extends_def, IS_PREFIX_APPEND,
                        inst_extends_trans]) >>
  irule frag_exec_mem_exit_prefix >> qexists_tac `guard_st` >>
  asm_rewrite_tac[] >>
  drule_all calldata_count_guard_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp[] >> metis_tac[]
QED

Finalise calldata_array_loop_init_safe_live

Theorem calldata_array_loop_init_owned_live:
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
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) ==>
  frag_exec_mem ctx st loop_st (\s. s = initial)
    (\t. ((?q. q = p /\
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
        FLOOKUP t.vs_allocas id = SOME (b,cap))) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial))
    (\r. ?u. r = Abort Revert_abort u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_array_loop_init_safe_live >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp_tac bool_ss [] >> gen_tac >> strip_tac >>
  drule_all calldata_index_init_owned_fields >> strip_tac >> asm_rewrite_tac[]
QED

Theorem calldata_binary_repeat:
  emit_op opc [lhs;rhs] st = (out,st') /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (if opc = ADD then a+b else a*b) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t = update_var (STRING #"%" (toString st.cs_next_var))
      (if opc = ADD then a+b else a*b) s /\ inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (if opc = ADD then a+b else a*b) s` >>
  `step_inst_base (mk_inst st.cs_next_id opc [lhs;rhs]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (gvs[Abbr `t`] >> FIRST [irule step_ADD, irule step_MUL] >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_read_repeat:
  emit_op CALLDATALOAD [src] st = (out,st') /\ eval_operand src s = SOME p ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t = update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load CALLDATALOAD p s) s /\ inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (abi_decode_load CALLDATALOAD p s) s` >>
  `step_inst_base (mk_inst st.cs_next_id CALLDATALOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_decode_read_step >>
     simp[abi_decode_source_opcode_def]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_indexed_address_repeat:
  abi_decode_indexed_address base_op idx stride st = (address,st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand address t = SOME (n2w (sb+32+j*stride)) /\
    abi_decoder_operand_live st'.cs_next_var address /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset,c2)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j)` by metis_tac[] >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand data s2 = SOME ((n2w sb : bytes32)+32w)` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, word_mul_n2w, update_var_def]
QED

Theorem calldata_element_pointer_repeat:
  !head data stride st ptr st' s hp dp.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD head data (Lit 0w) stride st =
    (ptr,st') /\ eval_operand head s = SOME hp /\ eval_operand data s = SOME dp /\
  abi_decoder_operand_live st.cs_next_var head /\
  abi_decoder_operand_live st.cs_next_var data ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ptr t = SOME (dp + abi_decode_load CALLDATALOAD hp s) /\
    abi_decoder_operand_live st'.cs_next_var ptr /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  rpt gen_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [head] st = (off,c1)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand data s1 = SOME dp` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[update_var_def]
QED

Theorem calldata_alloca_invariants_fields:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

Theorem calldata_index_init_literal_site:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) ==>
  ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = st.cs_next_id /\
    ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w] /\
    ins.inst_outputs = [STRING #"%" (toString st.cs_next_var)]
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  qexists_tac `mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  simp[mk_inst_def] >> first_x_assum irule >> simp[]
QED

Theorem calldata_live_excludes_generated:
  abi_decoder_operand_live next op /\ next <= n ==>
  op <> Var (STRING #"%" (toString n))
Proof
  Cases_on `op` >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  metis_tac[]
QED

Theorem calldata_index_init_result_live:
  abi_decode_index_init st = (ip,st') ==>
  abi_decoder_operand_live st'.cs_next_var ip
Proof
  strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  rpt strip_tac >> irule fresh_var_distinct >> decide_tac
QED

Theorem calldata_shell_operand_protection:
  first <= loop_st.cs_next_var /\
  abi_decoder_operand_live loop_st.cs_next_var src /\
  abi_decoder_operand_live loop_st.cs_next_var dst /\
  abi_decoder_operand_live loop_st.cs_next_var ip /\
  abi_decode_loop_prefix ip src opc loop_st = (labels,st0) /\
  st0.cs_next_var <= st1.cs_next_var /\
  hiv = STRING #"%" (toString loop_st.cs_next_var) /\
  hcv = STRING #"%" (toString (loop_st.cs_next_var+1)) /\
  hcmp = STRING #"%" (toString (loop_st.cs_next_var+2)) /\
  hdone = STRING #"%" (toString (loop_st.cs_next_var+3)) /\
  nv = STRING #"%" (toString st1.cs_next_var) ==>
  !op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live first op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op
Proof
  strip_tac >>
  `st0.cs_next_var = loop_st.cs_next_var + 4` by
    (qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
     simp[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def] >>
     strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!n. loop_st.cs_next_var <= n ==>
      op <> Var (STRING #"%" (toString n))` by
    (gen_tac >> disch_tac >> irule calldata_live_excludes_generated >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_operand_live st0.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `loop_st.cs_next_var <= st1.cs_next_var` by decide_tac >> simp[]
QED

Theorem calldata_element_setup_static_live:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,middle) ==>
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op)
Proof
  strip_tac >> drule abi_decode_array_element_setup_operands >> strip_tac >>
  simp[] >> rpt strip_tac >> irule abi_decoder_operand_live_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_shell_static_producer:
  first <= loop_st.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first dst /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src opc loop_st = (labels,st0) /\
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi di middle = ((),st1) ==>
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  (!op. op = src \/ op = dst \/ op = ip \/ abi_decoder_operand_live first op ==>
    op <> Var (STRING #"%" (toString loop_st.cs_next_var)) /\
    op <> Var (STRING #"%" (toString (loop_st.cs_next_var+1))) /\
    op <> Var (STRING #"%" (toString (loop_st.cs_next_var+2))) /\
    op <> Var (STRING #"%" (toString (loop_st.cs_next_var+3))) /\
    op <> Var (STRING #"%" (toString st1.cs_next_var)) /\
    abi_decoder_operand_live st0.cs_next_var op)
Proof
  strip_tac >> drule calldata_element_setup_static_live >> strip_tac >>
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  drule abi_decoder_variable_counter >> strip_tac >>
  `st0.cs_next_var <= st1.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule calldata_index_init_result_live >> strip_tac >>
  simp[] >> ho_match_mp_tac (GEN_ALL calldata_shell_operand_protection) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `st1` >> simp[] >> qexistsl_tac [`opc`,`labels`] >> simp[]
QED

(* Reentry probe: neither allocator branch needs register freshness.
   Direct execution and every-prefix safety are obtained from
   calldata_index_init_frag_mem; this is not prune-state run transport.

   Remaining reentrant initializer boundary (not asserted here): keep
   calldata_array_loop_init_owned's compiler equations, output allocation,
   separation, budget and ownership premises; replace fresh_vars_wrt st
   initial by abi_decoder_operand_live st.cs_next_var src and dst.  Drop
   fresh_vars_wrt loop_st t and restrict operand preservation to operands
   live at st.cs_next_var.  All count, memory, allocation, safe fragment,
   and revert conclusions must remain.

   Exact freshness consumers in calldataDynInit's old initializer:
   - count_guard_sequence: read/GT/ISZERO success and old-operand frame;
   - array_header_sequence and array_header_prefix_safe: preservation of
     dst across the count load, then MSTORE execution and safety;
   - index_init_frame and init_index_transport: overstrong all-operands
     preservation and freshness postconditions (index execution itself is
     already freshness-free, as the theorem below checks);
   - count_guard_frag_mem: rejected guard execution and safe rejection.
   Consequently the new index boundary alone cannot implement recursive
   nonbulk initialization.  Direct live-operand guard success/rejection
   and header companions are still required; no raw-run equivalence with
   a pruned state has been established. *)
Theorem calldata_index_init_owned_frag_mem:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) initial = OK allocated /\
  eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
  p+32 <= allocated.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. t = (mstore p 0w allocated with
        vs_inst_idx := LENGTH st'.cs_current_insts) /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
      initial.vs_alloca_next <= t.vs_alloca_next /\
      (!id b cap. FLOOKUP initial.vs_allocas id = SOME (b,cap) ==>
        FLOOKUP t.vs_allocas id = SOME (b,cap))) (K F)
Proof
  strip_tac >>
  drule_all calldata_index_init_owned_after_alloca >> strip_tac >>
  drule_all calldata_index_init_frag_mem >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp_tac bool_ss [] >>
  qpat_x_assum `!p. alloca_inv _ /\ _` (qspec_then `p` strip_assume_tac) >>
  `((mstore p 0w allocated) with vs_inst_idx := LENGTH st'.cs_current_insts).vs_allocas =
      (mstore p 0w allocated).vs_allocas /\
   ((mstore p 0w allocated) with vs_inst_idx := LENGTH st'.cs_current_insts).vs_alloca_next =
      (mstore p 0w allocated).vs_alloca_next` by simp[] >>
  drule_all calldata_alloca_invariants_fields >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >> gvs[]
QED

Theorem calldata_header_owned_state:
  t = jump_to lbl (abi_decode_header_state iv cv cmp done j n s) ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. op <> Var iv /\ op <> Var cv /\ op <> Var cmp /\ op <> Var done ==>
    eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  drule_all calldata_alloca_invariants_fields >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem calldata_backedge_owned_state:
  t = jump_to hdr (mstore counter w (update_var nv w s)) ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. op <> Var nv ==> eval_operand op t = eval_operand op s) /\
  (!a len. a+len <= counter \/ counter+32 <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  drule_all calldata_alloca_invariants_fields >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  conj_tac >- simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  conj_tac >- simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  conj_tac
  >- (Cases_on `op` >>
      simp[jump_to_def, mstore_def, write_memory_with_expansion_def,
           update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rpt strip_tac >> simp_tac (srw_ss()) [jump_to_def] >>
  `mem_bytes_at a len (mstore counter w (update_var nv w s)).vs_memory =
    mem_bytes_at a len (update_var nv w s).vs_memory` suffices_by
    simp[update_var_def] >>
  irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem calldata_indexed_address_code_shape:
  abi_decode_indexed_address base_op idx stride st = (address,st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  simp[abi_decode_indexed_address_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem calldata_element_pointer_code_shape:
  !head data stride st ptr st'.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD head data (Lit 0w) stride st =
    (ptr,st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  rpt gen_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem calldata_indexed_address_repeat_frag_mem:
  abi_decode_indexed_address base_op idx stride st = (address,st') /\
  eval_operand base_op initial = SOME (n2w sb) /\
  eval_operand idx initial = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. eval_operand address t = SOME (n2w (sb+32+j*stride)) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (K F)
Proof
  strip_tac >> drule calldata_indexed_address_code_shape >> strip_tac >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL calldata_indexed_address_prefix_safe) >>
      goal_assum (drule_at Any)) >>
  disj1_tac >> qexists_tac `t` >> simp[eval_op_inst_idx]
QED

Theorem calldata_element_pointer_repeat_frag_mem:
  !head data stride st ptr st' initial hp dp ctx.
  compile_abi_decode_dyn_elem_ptr CALLDATALOAD head data (Lit 0w) stride st =
    (ptr,st') /\ eval_operand head initial = SOME hp /\
  eval_operand data initial = SOME dp /\
  abi_decoder_operand_live st.cs_next_var head /\
  abi_decoder_operand_live st.cs_next_var data ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. eval_operand ptr t = SOME (dp + abi_decode_load CALLDATALOAD hp initial) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (K F)
Proof
  rpt gen_tac >> strip_tac >>
  drule calldata_element_pointer_code_shape >> strip_tac >>
  drule_all calldata_element_pointer_repeat >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL calldata_element_pointer_prefix_safe) >>
      goal_assum (drule_at Any)) >>
  disj1_tac >> qexists_tac `t` >> simp[eval_op_inst_idx]
QED

Theorem calldata_header_owned_safe_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w j /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w n /\
  j <= n /\ n < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block (if j<n then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to (if j<n then body_lbl else exit_lbl)
        (abi_decode_header_state iv cv cmp done j n s) ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. op <> Var iv /\ op <> Var cv /\ op <> Var cmp /\ op <> Var done ==>
    eval_operand op t = eval_operand op s) /\
  (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> drule calldata_header_owned_state >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  drule calldata_header_safe_transfer >> disch_then assume_tac >> metis_tac[]
QED

Theorem calldata_backedge_owned_safe_transfer:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ j < n /\ n < dimword (:256) /\
  w2n p+32 <= s.vs_alloca_next /\
  lookup_block hdr fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to hdr
        (mstore (w2n p) (n2w (SUC j)) (update_var nv (n2w (SUC j)) s)) ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. op <> Var nv ==> eval_operand op t = eval_operand op s) /\
  (!a len. a+len <= w2n p \/ w2n p+32 <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
  (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> drule calldata_backedge_owned_state >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  drule calldata_backedge_safe_transfer >> disch_then assume_tac >> metis_tac[]
QED

(* The setup's counter read is repeatable even after its temporary was bound. *)
Theorem calldata_mload_repeat:
  emit_op MLOAD [src] st = (out,st') /\ eval_operand src s = SOME p ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (mload (w2n p) s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (mload (w2n p) s) s` >>
  `step_inst_base (mk_inst st.cs_next_id MLOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_MLOAD >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var, update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_static_setup_repeat:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz st = (ops,st') /\
  ~dec_info_needs_offset di /\ eval_operand ip s = SOME p /\
  mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb+32+j*abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decode_static_element_setup_operands >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_element_setup_phases, comp_bind_def,
    comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_address src idx abi_sz c1 = (child_src,c2)` >>
  rename1 `abi_decode_indexed_address dst idx mem_sz c2 = (child_dst,end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_address_counters >>
  drule_all calldata_mload_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j)` by metis_tac[] >>
  `eval_operand src s1 = SOME (n2w sb) /\ eval_operand dst s1 = SOME (n2w d)`
    by metis_tac[] >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c2.cs_next_var idx /\
   abi_decoder_operand_live c2.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\ eval_operand idx s2 = SOME (n2w j)`
    by metis_tac[] >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 end_st) s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem calldata_coordinates_repeat:
  abi_decode_indexed_coordinates base_op idx stride st = ((data,address),st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand data t = SOME (n2w (sb+32)) /\
    eval_operand address t = SOME (n2w (sb+32+j*stride)) /\
    abi_decoder_operand_live st'.cs_next_var data /\
    abi_decoder_operand_live st'.cs_next_var address /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_indexed_coordinates_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset,c2)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j)` by metis_tac[] >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand data s2 = SOME ((n2w sb : bytes32)+32w)` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] calldata_binary_repeat)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  `abi_decoder_operand_live c2.cs_next_var data /\
   abi_decoder_operand_live st'.cs_next_var data` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand data t = SOME ((n2w sb : bytes32)+32w)` by metis_tac[] >>
  qexists_tac `t` >> gvs[word_add_n2w, word_mul_n2w, update_var_def]
QED

Theorem calldata_head_setup_repeat:
  abi_decode_array_head_setup ip src abi_sz st = ((idx,data,head),st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand data t = SOME (n2w (sb+32)) /\
    eval_operand head t = SOME (n2w (sb+32+j*abi_sz)) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    abi_decoder_operand_live st'.cs_next_var data /\
    abi_decoder_operand_live st'.cs_next_var head /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_array_head_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_coordinates src idx abi_sz c1 = ((data,head),end_st)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  imp_res_tac abi_decode_indexed_coordinates_counters >>
  drule_all calldata_mload_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w j) /\ eval_operand src s1 = SOME (n2w sb)`
    by metis_tac[] >>
  `abi_decoder_operand_live c1.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_coordinates_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 end_st) s1 = OK t` >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `abi_decoder_operand_live end_st.cs_next_var idx` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     metis_tac[]) >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem calldata_dynamic_setup_repeat:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\ dec_info_needs_offset di /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME
      (n2w (sb+32) + abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_decode_dynamic_element_setup_counters >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynamic_element_setup_phases,
    abi_decode_array_source_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  PairCases_on `src_ops` >> PairCases_on `head_ops` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_array_head_setup ip src abi_sz st = ((idx,data,head),c1)` >>
  rename1 `compile_abi_decode_dyn_elem_ptr CALLDATALOAD head data (Lit 0w) abi_sz c1 =
    (child_src,c2)` >>
  rename1 `abi_decode_indexed_address dst idx mem_sz c2 = (child_dst,end_st)` >>
  imp_res_tac abi_decode_array_head_setup_counters >>
  imp_res_tac abi_decoder_array_pointer_counters >>
  imp_res_tac abi_decode_indexed_address_counters >>
  drule_all calldata_head_setup_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all calldata_element_pointer_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c1.cs_next_var dst /\
   abi_decoder_operand_live c2.cs_next_var dst /\
   abi_decoder_operand_live c2.cs_next_var idx` by
    (conj_tac
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     conj_tac
     >- (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\ eval_operand idx s2 = SOME (n2w j)`
    by metis_tac[] >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 end_st) s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK t /\ inst_extends st end_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[abi_decode_load_def, abi_decode_source_def] >> metis_tac[]
QED

Theorem calldata_element_setup_repeat:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME
      (if dec_info_needs_offset di then
        n2w (sb+32) + abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) s
       else n2w (sb+32+j*abi_sz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decoder_address_frame st.cs_next_var s t /\ inst_extends st st'
Proof
  strip_tac >> Cases_on `dec_info_needs_offset di`
  >- (drule_all calldata_dynamic_setup_repeat >> strip_tac >>
      qexists_tac `t` >> simp[abi_decoder_address_frame_def]) >>
  drule_all calldata_static_setup_repeat >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_address_frame_def]
QED

Theorem calldata_element_setup_repeat_frag_mem:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz mem_sz st = (ops,st') /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  w2n p+32 <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (FST (SND ops)) t = SOME
        (if dec_info_needs_offset di then n2w (sb+32) +
          abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_sz) : bytes32) initial
         else n2w (sb+32+j*abi_sz)) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*mem_sz)) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      abi_decoder_address_frame st.cs_next_var initial t)
    (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all calldata_element_setup_repeat >> strip_tac >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  disj1_tac >> qexists_tac `t` >>
  gvs[eval_op_inst_idx, abi_decoder_address_frame_def]
QED

(* A nested array's output may be a subrange of a containing allocation. *)
Theorem calldata_child_preserves_contained_prefix:
  abi_decode_footprint_frame
    ((dst+32+j*stride,stride)::scratch) s t /\ alloca_inv t /\
  (!id. id < lo \/ hi <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (output_id < lo \/ hi <= output_id) /\
  FLOOKUP s.vs_allocas output_id = SOME (base_addr,cap) /\
  base_addr <= dst /\ dst+32+j*stride <= base_addr+cap /\
  (!q len. MEM (q,len) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,len)) ==>
  mem_bytes_at dst (32+j*stride) t.vs_memory =
    mem_bytes_at dst (32+j*stride) s.vs_memory
Proof
  strip_tac >>
  irule (cj 2 calldata_child_preserves_allocated_region) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >>
  qexistsl_tac [`base_addr`,`cap`,`dst+32+j*stride`,`output_id`,`stride`] >>
  simp[] >> metis_tac[]
QED

(* Convert the iterator's indexed prefix to the recursive memory layout. *)
Theorem calldata_elems_memory_from_index:
  !vs off. (!k. k < LENGTH vs ==>
    val_in_memory tv (EL k vs) (off+k*type_memory_size tv) mem) ==>
    elems_in_memory vs off tv mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt strip_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `SUC k` mp_tac) >>
  simp_tac bool_ss [EL, TL, LESS_MONO_EQ, MULT_CLAUSES] >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> simp[]
QED

Theorem calldata_elems_wf_from_every:
  !vs. EVERY (val_wf tv) vs ==> elems_val_wf vs tv
Proof
  Induct >> simp[val_wf_def]
QED

Theorem calldata_terminal_array_memory:
  LENGTH vs = n /\ n <= maxn /\ EVERY (val_wf tv) vs /\
  mem_word_at d s.vs_memory = n2w n /\
  (!k. k < n ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) s.vs_memory) ==>
  val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  strip_tac >> simp[val_wf_def, val_in_memory_def] >> conj_tac
  >- metis_tac[calldata_elems_wf_from_every] >>
  irule calldata_elems_memory_from_index >> gvs[]
QED

(* The terminal callback uses the very same emitted header as an iteration,
   but at the accepted count it transfers to the exit block. *)
Theorem calldata_terminal_header_array:
  lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts id ip src CALLDATALOAD iv cv cmp done body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\ src <> Var iv /\ iv <> cv /\
  eval_operand ip s = SOME p /\ eval_operand src s = SOME srcaddr /\
  mload (w2n p) s = n2w n /\
  abi_decode_load CALLDATALOAD srcaddr s = n2w n /\
  n < dimword (:256) /\ w2n p+32 <= s.vs_alloca_next /\
  lookup_block exit_lbl fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 /\
  t = jump_to exit_lbl (abi_decode_header_state iv cv cmp done n n s) /\
  LENGTH vs = n /\ n <= maxn /\ EVERY (val_wf tv) vs /\
  mem_word_at d s.vs_memory = n2w n /\
  (!k. k < n ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) s.vs_memory) ==>
  val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s) /\
  (!op. op <> Var iv /\ op <> Var cv /\ op <> Var cmp /\ op <> Var done ==>
    eval_operand op t = eval_operand op s) /\
  (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`j` |-> `n`] calldata_header_owned_safe_transfer)) >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  drule_all calldata_terminal_array_memory >> strip_tac >> simp[]
QED

Theorem calldata_owned_interval_restrict:
  (!id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  lo <= a /\ a <= b /\ b <= hi ==>
  !id q k. a <= id /\ id < b /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[] >> decide_tac
QED

Theorem calldata_owned_interval_replace:
  (!id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (!id q k. a <= id /\ id < b /\ FLOOKUP t.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  lo <= a /\ a <= b /\ b <= hi /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!id. id < a \/ b <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
  !id q k. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
Proof
  simp_tac (pure_ss ++ boolSimps.BOOL_ss) [LET_THM] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `a <= id /\ id < b`
  >- metis_tac[] >>
  `FLOOKUP s.vs_allocas id = SOME (q,k)` by
    (qpat_x_assum `!id. _` (qspec_then `id` mp_tac) >>
     (impl_tac >- decide_tac) >> metis_tac[]) >>
  qpat_x_assum `!id q k. lo <= id /\ _ ==> _` drule >>
  disch_then (qspecl_then [`q`,`k`] mp_tac) >>
  qpat_x_assum `!id q k. _` kall_tac >>
  qpat_x_assum `!id. _` kall_tac >>
  (impl_tac >- asm_rewrite_tac []) >> strip_tac >>
  asm_rewrite_tac [] >> conj_tac >- decide_tac >>
  qexists_tac `ins` >> asm_rewrite_tac []
QED

Theorem calldata_owned_counter_update:
  (!id q k. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  lo <= c /\ c < hi /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  FLOOKUP t.vs_allocas c = SOME (p,32) /\
  p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
  MEM ins (fn_insts fn) /\ ins.inst_id = c /\
  ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w] /\
  (!id. id <> c ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
  !id q k. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]
Proof
  simp_tac (pure_ss ++ boolSimps.BOOL_ss) [LET_THM] >> strip_tac >>
  ho_match_mp_tac (GEN_ALL (SIMP_RULE (pure_ss ++ boolSimps.BOOL_ss) [LET_THM]
    calldata_owned_interval_replace)) >>
  qexistsl_tac [`s`,`SUC c`,`c`] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `id = c` by decide_tac >>
      qpat_x_assum `!id q k. _` kall_tac >> gvs[] >>
      qexists_tac `ins` >> simp[]) >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac >- decide_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem calldata_scratch_witness_transport:
  (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  (!q k. MEM (q,k) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k)) ==>
  !q k. MEM (q,k) scratch ==>
    ?id. lo <= id /\ id < hi /\ FLOOKUP t.vs_allocas id = SOME (q,k)
Proof
  metis_tac[]
QED

Theorem calldata_footprint_accumulate:
  abi_decode_footprint_frame ((d,sz)::old) s u /\
  abi_decode_footprint_frame ((e,stride)::new) u v /\
  d <= e /\ e+stride <= d+sz ==>
  abi_decode_footprint_frame ((d,sz)::(old++new)) s v
Proof
  strip_tac >> irule abi_decode_footprint_frame_trans >> qexists_tac `u` >> conj_tac
  >- (irule abi_decode_footprint_frame_weaken >> goal_assum (drule_at Any) >>
      rpt gen_tac >> strip_tac >>
      qexistsl_tac [`d'`,`sz'`] >> gvs[MEM_APPEND]) >>
  irule abi_decode_footprint_frame_weaken >> goal_assum (drule_at Any) >>
  simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`d`,`sz`] >> simp[]) >>
  qexistsl_tac [`d'`,`sz'`] >> simp[]
QED

(* Exact concrete initial header boundary; H deliberately includes equality
   of absent as well as present old operands. *)
Theorem calldata_owned_header_initial:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\ fresh_vars_wrt st initial /\
  maxn < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?u.
    (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    0 <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w 0 /\
    mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame
      ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    !fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn initial)
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 <= bufsize` by simp[Abbr `bufsize`] >>
  `d < dimword (:256)` by decide_tac >>
  drule_all calldata_array_loop_init_owned_live >> disch_tac >>
  qmatch_asmsub_abbrev_tac `frag_exec_mem ctx st loop_st _ InitPost _` >>
  drule calldata_init_to_header_safe >>
  disch_then drule >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `initial` mp_tac) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [] >>
  reverse (disch_then DISJ_CASES_TAC)
  >- (disj1_tac >> simp_tac bool_ss [Abbr `X`] >>
      pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
      strip_tac >> metis_tac[]) >>
  pop_assum (qx_choose_then `t` strip_assume_tac) >>
  disj2_tac >> qexists_tac `jump_to hdr t` >>
  reverse conj_tac >- simp[Abbr `Rel`] >>
  qpat_x_assum `InitPost t` mp_tac >>
  simp_tac bool_ss [Abbr `InitPost`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p < dimword (:256) /\ p+32 <= t.vs_alloca_next` by
    (qpat_x_assum `FLOOKUP t.vs_allocas _ = SOME (p,32)` mp_tac >>
     qpat_x_assum `alloca_inv t` mp_tac >>
     qpat_x_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     qpat_x_assum `unit_alloca_budget ctx < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def, alloca_frontier_inv_def] >>
     rpt strip_tac >>
     `p+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `Own st.cs_next_id end_st.cs_next_id t` by suspend "ownership" >>
  `abi_decode_footprint_frame [(d,bufsize);(p,32)] initial t` by
    suspend "footprint" >>
  `!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
     FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `FLOOKUP t.vs_allocas oid = SOME (base_addr,cap)` by metis_tac[] >>
  `alloca_inv (jump_to hdr t) /\
   alloca_frontier_inv ctx fn site (jump_to hdr t)` by
    (mp_tac (Q.INST [`s` |-> `t`, `t` |-> `jump_to hdr t`]
       calldata_alloca_invariants_fields) >> simp[jump_to_def]) >>
  `Own st.cs_next_id end_st.cs_next_id (jump_to hdr t)` by
    (qpat_assum `Own _ _ t` mp_tac >>
     simp_tac pure_ss [Abbr `Own`] >> POP_ASSUM_LIST (K all_tac) >>
     BETA_TAC >>
     `((jump_to hdr t).vs_allocas = t.vs_allocas) /\
      ((jump_to hdr t).vs_alloca_next = t.vs_alloca_next)` by
       simp[jump_to_def] >>
     asm_rewrite_tac[]) >>
  `mload p (jump_to hdr t) = 0w` by
    (qpat_assum `mload p t = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[mload_def, jump_to_def]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
  simp_tac bool_ss [Abbr `H`] >>
  simp[Abbr `nelts`] >>
  simp[jump_to_def] >>
  qexists_tac `[(p,32)]` >>
  simp[jump_to_def, abi_decode_footprint_frame_def] >>
  qexists_tac `header_st.cs_next_id` >> simp[]
QED

Resume calldata_owned_header_initial[ownership]:
  drule_all calldata_index_init_literal_site >> strip_tac >>
  qpat_x_assum `Own _ _ initial` mp_tac >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> disch_tac >>
  ho_match_mp_tac (GEN_ALL (SIMP_RULE (pure_ss ++ boolSimps.BOOL_ss)
    [LET_THM] calldata_owned_counter_update)) >>
  qexistsl_tac [`initial`,`p`,`ins`,`header_st.cs_next_id`] >>
  asm_rewrite_tac[]
QED

Resume calldata_owned_header_initial[footprint]:
  qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` mp_tac >>
  qpat_assum `t.vs_call_ctx = _` mp_tac >>
  qpat_assum `t.vs_data_section = _` mp_tac >>
  qpat_assum `32 <= bufsize` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >>
  qpat_assum `!d' sz. _` (qspecl_then [`d`,`bufsize`]
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!d' sz. _` (qspecl_then [`p`,`32`]
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  first_x_assum irule >> decide_tac
QED

Finalise calldata_owned_header_initial

(* Conditional composition for the actual nonbulk shell.  Own permits both
   absent sites and previously allocated 32-byte scratch slots. *)
(* Owned nonbulk interface audit (C1.8.6.5.4).

   Concrete header invariant, using precisely the local Own and bufsize of
   calldata_nonbulk_owned; n = nelts, L = st.cs_next_id,
   U = end_st.cs_next_id, c = header_st.cs_next_id:

   H = \j u.
     ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
     j <= nelts /\ nelts <= maxn /\
     eval_operand src u = SOME srcword /\
     eval_operand dst u = SOME (n2w d) /\
     eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
     mem_word_at d u.vs_memory = n2w nelts /\
     u.vs_call_ctx = initial.vs_call_ctx /\
     u.vs_data_section = initial.vs_data_section /\
     FLOOKUP u.vs_allocas c = SOME (p,32) /\
     FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
     alloca_inv u /\ alloca_frontier_inv ctx fn site u /\ Own L U u /\
     initial.vs_alloca_next <= u.vs_alloca_next /\
     (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
       FLOOKUP u.vs_allocas id = SOME (q,k)) /\
     (!id. id < L \/ U <= id ==>
       FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (!op. abi_decoder_operand_live st.cs_next_var op ==>
       eval_operand op u = eval_operand op initial) /\
     ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
       !q k. MEM (q,k) scratch ==>
         ?id. L <= id /\ id < U /\ FLOOKUP u.vs_allocas id = SOME (q,k).

   This is proof-local notation for the expanded theorem statements, NOT a new
   definition. The typed prefix list belongs to the iterator, not H.
   Initialization produces count/length/counter and allocator fields via
   calldata_array_loop_init_owned; calldata_init_to_header_safe supplies
   control and Rel. Scratch starts as [(p,32)]. Step producers are the
   owned header transfer, repeatable setup, smaller-child contract, and
   owned backedge transfer. Interval replacement and footprint append are
   still required to assemble H after a child. Terminal consumes the
   typed prefix and length via calldata_terminal_header_array.

   Static-premise provenance:
   - The four loop phase equations are abi_decode_dyn_loop_trace.
   - Header IDs/registers/labels and empty body instruction prefix are
     abi_decode_loop_prefix_shape / abi_decoder_loop_prefix_facts.
   - Header/backedge lookups are abi_decoder_loop_phase_lookups;
     zero-phi body/child/exit obligations are covered by
     abi_decoder_array_body_entry_phi / abi_decoder_loop_phase_cfg,
     with the enclosing continuation's zero-phi premise still required.
   - Phase fn_has_code facts come from fn_has_code_split and
     abi_decoder_loop_phase_containment, not from runtime execution.
   - FST ops = Var biv is abi_decoder_array_setup_head; middle liveness
     is exported by calldata_element_setup_repeat and obtained statically
     from emit counters plus abi_decoder_operand_live_emit/mono.
   - The counter ID lies before child IDs by index-init/prefix shapes;
     child/end monotonicity comes from cs_extends_abi_decode and suffix
     shape. Protected old names exclude header/suffix output names by
     abi_decoder_older_vars_def and fresh_var_distinct. The combined
     implication and middle liveness are now calldata_shell_static_producer;
     header/suffix names are its explicit generated names, matched to the
     phase shapes. calldata_shell_operand_protection also accepts named
     outputs with their syntactic equalities.
   - Counter ALLOCA literal membership is calldata_index_init_literal_site,
     derived directly from the index-init instructions and containment.
     actual_index_init_function_site exports only alloca_size=32.
     General decoder scratch sizes
     use abi_decoder_code_alloca, not abi_decoder_budget.
   - ALL_DISTINCT fn IDs and instruction membership are packaged-function
     properties; output allocation/exclusion and counter availability are
     entry ownership facts, not consequences of shell syntax alone.

   Remaining interface issue: this theorem still requires initial
   fresh_vars_wrt, while its smaller-child callback deliberately does not.
   Consequently it is a conditional single-entry companion, NOT yet a
   recursive implementation of that callback for nested dynamic arrays.
   Prune-fresh/eval lemmas alone do not transport raw run_from or
   mem_safe_run back to the unpruned state. A reentrant initialization or
   full safe execution transport boundary remains necessary downstream.
   The conditional theorem itself has not been proved by this audit.
*)
Theorem calldata_owned_header_terminal:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone) /\
  p < dimword (:256) /\ maxn < dimword (:256) /\
  (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <=
      w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\
    mload p u = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame
      ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  EVERY P vs /\ EVERY (val_wf tv) vs /\
  (!k. k < w2n (abi_decode_load CALLDATALOAD srcword initial) ==>
    val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) u.vs_memory) ==>
  (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn u) \/
  ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn u)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `H nelts u` mp_tac >>
  simp_tac bool_ss [Abbr `H`] >> strip_tac >>
  `p+32 <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (p,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `nelts < dimword (:256)` by decide_tac >>
  `abi_decode_load CALLDATALOAD srcword u = n2w nelts` by
    simp[Abbr `nelts`, abi_decode_load_def, abi_decode_source_def] >>
  `mload (w2n (n2w p:bytes32)) u = n2w nelts` by simp[] >>
  `w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  qabbrev_tac `v = jump_to exit_lbl
    (abi_decode_header_state hiv hcv hcmp hdone nelts nelts u)` >>
  `v = jump_to exit_lbl
    (abi_decode_header_state hiv hcv hcmp hdone nelts nelts u)` by simp[Abbr `v`] >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|>`
    by simp[] >>
  drule_all calldata_terminal_header_array >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  disj2_tac >> qexistsl_tac [`v`,`scratch`] >>
  `Own st.cs_next_id end_st.cs_next_id v` by
    (qpat_assum `Own _ _ u` mp_tac >>
     qpat_assum `v.vs_allocas = _` mp_tac >>
     qpat_assum `v.vs_alloca_next = _` mp_tac >>
     qpat_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >> BETA_TAC >>
     ntac 2 disch_tac >> asm_rewrite_tac[]) >>
  `Rel u v` by
    (qpat_assum `!fuel r. _` mp_tac >> simp_tac bool_ss [Abbr `Rel`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op initial` by
    (qpat_assum `!op. _ ==> eval_operand op v = eval_operand op u` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live _ op ==> eval_operand op u = _` mp_tac >>
     qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `v = jump_to _ _` kall_tac >>
  qpat_x_assum `!fuel r. _` kall_tac >>
  `~v.vs_halted /\ v.vs_current_bb = exit_lbl /\ v.vs_inst_idx = 0` by
    (qpat_assum `Abbrev (v = _)` mp_tac >>
     qpat_assum `~u.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]) >>
  `abi_decode_footprint_frame ((d,bufsize)::scratch) initial v` by
    (qpat_assum `abi_decode_footprint_frame _ initial u` mp_tac >>
     qpat_assum `v.vs_memory = _` mp_tac >>
     qpat_assum `v.vs_call_ctx = _` mp_tac >>
     qpat_assum `v.vs_data_section = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_footprint_frame_def]) >>
  asm_rewrite_tac[listTheory.LENGTH]
QED

Theorem calldata_owned_header_step:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  fn_has_code st0 middle fn /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  p < dimword (:256) /\ maxn < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!a w e.
    ~a.vs_halted /\ a.vs_current_bb = middle.cs_current_bb /\
    a.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) a = SOME w /\
    eval_operand (SND (SND ops)) a = SOME (n2w e) /\
    alloca_inv a /\ alloca_frontier_inv ctx fn site a /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP a.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= a.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP a.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn a = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn a) \/ ?b x scratch.
      ~b.vs_halted /\ b.vs_current_bb = st1.cs_current_bb /\
      b.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e b.vs_memory /\
      (!fuel r. run_from fuel ctx fn b = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn a = r /\
          (mem_safe_run fuel ctx fn b ==> mem_safe_run fuel' ctx fn a)) /\
      b.vs_call_ctx = a.vs_call_ctx /\ b.vs_data_section = a.vs_data_section /\
      alloca_inv b /\ alloca_frontier_inv ctx fn site b /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP b.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= b.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      a.vs_alloca_next <= b.vs_alloca_next /\
      (!id q k. FLOOKUP a.vs_allocas id = SOME (q,k) ==>
        FLOOKUP b.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP b.vs_allocas id = FLOOKUP a.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op b = eval_operand op a) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) a b /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP b.vs_allocas id = SOME (q,k))) /\
  j < w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) ==>
  (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn u) \/ ?v x.
    (~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\
      SUC j <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src v = SOME srcword /\
      eval_operand dst v = SOME (n2w d) /\
      eval_operand ip v = SOME (n2w p) /\ mload p v = n2w (SUC j) /\
      mem_word_at d v.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
      v.vs_call_ctx = initial.vs_call_ctx /\
      v.vs_data_section = initial.vs_data_section /\
      FLOOKUP v.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP v.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op v = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial v /\
        !q k. MEM (q,k) scratch ==>
          ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
            FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    P x /\ val_wf tv x /\
    val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
    mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
      mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\ eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    alloca_inv u /\ FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32)` by
    (qpat_assum `H j u` mp_tac >>
     simp_tac bool_ss [Abbr `H`] >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `Abbrev (H = _)` (mk_asm "Hdef") >>
  `p+32 <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (p,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `nelts < dimword (:256)` by decide_tac >>
  `abi_decode_load CALLDATALOAD srcword u = n2w nelts` by
    simp[Abbr `nelts`, abi_decode_load_def, abi_decode_source_def] >>
  `mload (w2n (n2w p:bytes32)) u = n2w j` by simp[] >>
  `w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  qabbrev_tac `head = jump_to body_lbl
    (abi_decode_header_state hiv hcv hcmp hdone j nelts u)` >>
  `head = jump_to (if j<nelts then body_lbl else exit_lbl)
    (abi_decode_header_state hiv hcv hcmp hdone j nelts u)` by simp[Abbr `head`] >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|>`
    by simp[] >>
  `lookup_block (if j<nelts then body_lbl else exit_lbl) fn.fn_blocks = SOME body_bb`
    by simp[] >>
  drule_all calldata_header_owned_safe_transfer >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  qpat_x_assum `head = jump_to _ _` kall_tac >>
  `~head.vs_halted /\ head.vs_current_bb = st0.cs_current_bb /\
    head.vs_inst_idx = LENGTH st0.cs_current_insts` by
    (qpat_assum `Abbrev (head = _)` mp_tac >>
     qpat_assum `~u.vs_halted` mp_tac >>
     qpat_assum `st0.cs_current_bb = _` mp_tac >>
     qpat_assum `st0.cs_current_insts = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]) >>
  `!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op head = eval_operand op u` by
    (qpat_assum `!op. _ ==> eval_operand op head = _` mp_tac >>
     qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `eval_operand ip head = SOME (n2w p) /\
    eval_operand src head = SOME (n2w (w2n srcword)) /\
    eval_operand dst head = SOME (n2w d)` by
    (qpat_assum `!op. _ ==> eval_operand op head = eval_operand op u` mp_tac >>
     qpat_assum `eval_operand ip u = _` mp_tac >>
     qpat_assum `eval_operand src u = _` mp_tac >>
     qpat_assum `eval_operand dst u = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  `mload (w2n (n2w p:bytes32)) head = n2w j` by
    (qpat_assum `head.vs_memory = _` mp_tac >>
     qpat_assum `mload (w2n (n2w p)) u = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[mload_def]) >>
  `abi_decoder_operand_live st0.cs_next_var src /\
    abi_decoder_operand_live st0.cs_next_var dst` by
    (qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `w2n (n2w p:bytes32)+32 <= head.vs_alloca_next` by simp[] >>
  drule_all calldata_element_setup_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  rewrite_tac[frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `head` mp_tac) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [combinTheory.K_THM] >>
  disch_then (qx_choose_then `entry` strip_assume_tac) >>
  `entry.vs_memory = u.vs_memory /\
    entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\
    entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `abi_decoder_address_frame _ head entry` mp_tac >>
     qpat_assum `head.vs_memory = _` mp_tac >>
     qpat_assum `head.vs_call_ctx = _` mp_tac >>
     qpat_assum `head.vs_data_section = _` mp_tac >>
     qpat_assum `head.vs_allocas = _` mp_tac >>
     qpat_assum `head.vs_alloca_next = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_address_frame_def] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  `alloca_inv entry /\ alloca_frontier_inv ctx fn site entry /\
    Own st.cs_next_id end_st.cs_next_id entry /\
    FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap)` by
    suspend "entry_resources" >>
  `Own middle.cs_next_id st1.cs_next_id entry` by
    (qpat_assum `Own st.cs_next_id end_st.cs_next_id entry` mp_tac >>
     qpat_assum `st.cs_next_id <= header_st.cs_next_id` mp_tac >>
     qpat_assum `header_st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >> BETA_TAC >> ntac 4 disch_tac >>
     rpt gen_tac >> strip_tac >> first_x_assum irule >>
     asm_rewrite_tac[] >> decide_tac) >>
  `base_addr <= d+32+j*type_memory_size tv /\
    d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+cap /\
    d+32+j*type_memory_size tv+type_memory_size tv < dimword (:256)` by
    (qpat_assum `j < nelts` mp_tac >>
     qpat_assum `nelts <= maxn` mp_tac >>
     qpat_assum `base_addr <= d` mp_tac >>
     qpat_assum `d+bufsize <= base_addr+cap` mp_tac >>
     qpat_assum `d+bufsize < dimword (:256)` mp_tac >>
     qpat_assum `Abbrev (bufsize = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [markerTheory.Abbrev_def] >> ntac 6 disch_tac >>
     `j+1 <= maxn` by decide_tac >>
     `(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by
       simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(j+1)*_ <= maxn*_` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `eval_operand (FST (SND ops)) entry = SOME childword` >>
  qpat_x_assum `!a w e. _` (qspecl_then
    [`entry`,`childword`,`d+32+j*type_memory_size tv`] mp_tac) >>
  asm_rewrite_tac[] >>
  suspend "child_result"
QED

Resume calldata_owned_header_step[entry_resources]:
  qpat_assum `entry.vs_allocas = u.vs_allocas` mp_tac >>
  qpat_assum `entry.vs_alloca_next = u.vs_alloca_next` mp_tac >>
  qpat_assum `H j u` mp_tac >>
  asm "Hdef" mp_tac >>
  qpat_assum `Abbrev (Own = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac[markerTheory.Abbrev_def] >>
  disch_tac >> disch_then SUBST1_TAC >> BETA_TAC >>
  strip_tac >> ntac 2 disch_tac >>
  `(alloca_inv entry <=> alloca_inv u) /\
    (alloca_frontier_inv ctx fn site entry <=> alloca_frontier_inv ctx fn site u)` by
    (irule calldata_alloca_invariants_fields >> asm_rewrite_tac[]) >>
  `Own st.cs_next_id end_st.cs_next_id entry` by
    (qpat_assum `Own st.cs_next_id end_st.cs_next_id u` mp_tac >>
     qpat_assum `Own = _` mp_tac >>
     qpat_assum `entry.vs_allocas = _` mp_tac >>
     qpat_assum `entry.vs_alloca_next = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     ntac 2 disch_tac >> disch_then SUBST1_TAC >>
     BETA_TAC >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED
Resume calldata_owned_header_step[child_result]:
  disch_then DISJ_CASES_TAC
  >- (disj1_tac >>
      qpat_assum `X entry` mp_tac >>
      qpat_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx fn u = _ /\ _` mp_tac >>
      qpat_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn head = _ /\ _` mp_tac >>
      simp_tac bool_ss [Abbr `X`] >>
      POP_ASSUM_LIST (K all_tac) >>
      rpt strip_tac >> metis_tac[exec_result_distinct]) >>
  pop_assum (qx_choose_then `child` (qx_choose_then `x`
    (qx_choose_then `new_scratch` assume_tac))) >>
  `eval_operand (Var biv) child = SOME (n2w j) /\
    eval_operand ip child = SOME (n2w p) /\
    w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` by
    suspend "backedge_inputs" >>
  suspend "success_continuation"
QED
Resume calldata_owned_header_step[backedge_inputs]:
  qpat_assum `~child.vs_halted /\ _` mp_tac >>
  qpat_assum `eval_operand (Var biv) entry = _` mp_tac >>
  qpat_assum `eval_operand ip head = _` mp_tac >>
  qpat_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> eval_operand op entry = _` mp_tac >>
  qpat_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> abi_decoder_operand_live middle.cs_next_var op` mp_tac >>
  qpat_assum `abi_decoder_operand_live middle.cs_next_var (FST ops)` mp_tac >>
  qpat_assum `FST ops = Var biv` mp_tac >>
  qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
  qpat_assum `w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  ntac 9 strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> decide_tac
QED
Resume calldata_owned_header_step[success_continuation]:
  qpat_assum `~child.vs_halted /\ _` (mk_asm "childpost") >>
  `~child.vs_halted /\ child.vs_current_bb = st1.cs_current_bb /\
    child.vs_inst_idx = LENGTH st1.cs_current_insts` by
    (asm "childpost" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [] >> rpt strip_tac >> asm_rewrite_tac[]) >>
  `lookup_block child.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|>`
    by simp[] >>
  `phi_prefix_length (abi_decode_header_insts hid ip src CALLDATALOAD
    hiv hcv hcmp hdone body_lbl exit_lbl) = 0` by
    simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
  qabbrev_tac `v = jump_to hdr
    (mstore (w2n (n2w p:bytes32)) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) child))` >>
  `v = jump_to hdr
    (mstore (w2n (n2w p:bytes32)) (n2w (SUC j))
      (update_var nv (n2w (SUC j)) child))` by simp[Abbr `v`] >>
  qpat_x_assum `Abbrev (v = _)` (mk_asm "vdef") >>
  `p MOD dimword (:256)+32 <= child.vs_alloca_next` by
    (qpat_assum `w2n (n2w p:bytes32)+32 <= child.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qpat_x_assum `v = jump_to _ _`
    (mp_then Any mp_tac calldata_backedge_owned_safe_transfer) >>
  disch_then drule >>
  simp_tac (srw_ss()) [] >>
  `st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr =
    st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr` by
    REFL_TAC >>
  disch_then drule >>
  disch_then (drule_at (Pat `lookup_block hdr fn.fn_blocks = SOME _`)) >>
  simp_tac (srw_ss()) [] >>
  disch_then (qspecl_then [`site`,`nelts`,`ctx`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `d+32+j*type_memory_size tv+type_memory_size tv <= d+bufsize` by
    (qpat_assum `j < nelts` mp_tac >> qpat_assum `nelts <= maxn` mp_tac >>
     qpat_assum `Abbrev (bufsize = _)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [markerTheory.Abbrev_def] >> ntac 3 disch_tac >>
     `j+1 <= maxn` by decide_tac >>
     `(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(j+1)*_ <= maxn*_` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `!a len. d <= a /\ a+len <= d+bufsize ==>
    mem_bytes_at a len v.vs_memory = mem_bytes_at a len child.vs_memory` by
    (qpat_assum `!a len. _ ==> mem_bytes_at a len v.vs_memory = _` mp_tac >>
     qpat_assum `d+bufsize <= p \/ p+32 <= d` mp_tac >>
     qpat_assum `p < dimword (:256)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  `mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory` by suspend "prefix_memory" >>
  disj2_tac >> qexistsl_tac [`v`,`x`] >>
  conj_tac >- suspend "next_invariant" >>
  `P x /\ val_wf tv x` by
    (asm "childpost" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  conj_tac >- suspend "element_memory" >>
  `Rel entry child` by
    (asm "childpost" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  qpat_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx fn u = _ /\ _` mp_tac >>
  qpat_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn head = _ /\ _` mp_tac >>
  qpat_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn child = _ /\ _` mp_tac >>
  qpat_assum `Rel entry child` mp_tac >>
  simp_tac bool_ss [Abbr `Rel`] >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn child = _ /\ _`
    (qspec_then `fuel` mp_tac) >> asm_rewrite_tac[] >>
  disch_then (qx_choose_then `fc` strip_assume_tac) >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn entry = _ /\ _`
    (qspec_then `fc` mp_tac) >> asm_rewrite_tac[] >>
  disch_then (qx_choose_then `fe` strip_assume_tac) >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn head = _ /\ _`
    (qspec_then `fe` mp_tac) >> asm_rewrite_tac[] >>
  disch_then (qx_choose_then `fh` strip_assume_tac) >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn u = _ /\ _`
    (qspec_then `fh` mp_tac) >> asm_rewrite_tac[] >> metis_tac[]
QED
Resume calldata_owned_header_step[element_memory]:
  `val_wf tv x /\ val_in_memory tv x (d+32+j*type_memory_size tv) child.vs_memory` by
    (asm "childpost" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  qpat_assum `val_wf tv x` mp_tac >>
  qpat_assum `val_in_memory tv x _ child.vs_memory` mp_tac >>
  qpat_assum `!a len. d <= a /\ _ ==> _` mp_tac >>
  qpat_assum `d+32+j*type_memory_size tv+type_memory_size tv <= d+bufsize` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  irule val_in_memory_mem_agree >> conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`type_memory_size tv`,`child.vs_memory`] >>
  asm_simp_tac bool_ss [LESS_EQ_REFL] >> sym_tac >> first_x_assum irule >> decide_tac
QED
Resume calldata_owned_header_step[prefix_memory]:
  `mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) entry.vs_memory` by
    (asm "childpost" mp_tac >>
     qpat_assum `FLOOKUP entry.vs_allocas oid = SOME (base_addr,cap)` mp_tac >>
     qpat_assum `base_addr <= d` mp_tac >>
     qpat_assum `d+bufsize <= base_addr+cap` mp_tac >>
     qpat_assum `d+32+j*type_memory_size tv+type_memory_size tv <= d+bufsize` mp_tac >>
     qpat_assum `oid < st.cs_next_id \/ end_st.cs_next_id <= oid` mp_tac >>
     qpat_assum `st.cs_next_id <= header_st.cs_next_id` mp_tac >>
     qpat_assum `header_st.cs_next_id < middle.cs_next_id` mp_tac >>
     qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
     qpat_assum `entry.vs_allocas = u.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     `oid < middle.cs_next_id \/ st1.cs_next_id <= oid` by decide_tac >>
     `d+32+j*type_memory_size tv <= base_addr+cap` by decide_tac >>
     `!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
       FLOOKUP child.vs_allocas id = FLOOKUP entry.vs_allocas id` by metis_tac[] >>
     irule calldata_child_preserves_contained_prefix >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`base_addr`,`cap`,`oid`,`new_scratch`] >> gvs[]) >>
  qpat_assum `mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory = _` mp_tac >>
  qpat_assum `entry.vs_memory = u.vs_memory` mp_tac >>
  qpat_assum `!a len. d <= a /\ _ ==> _` mp_tac >>
  qpat_assum `d+32+j*type_memory_size tv+type_memory_size tv <= d+bufsize` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
    mem_bytes_at d (32+j*type_memory_size tv) child.vs_memory` by
    (first_x_assum irule >> decide_tac) >> metis_tac[]
QED
Resume calldata_owned_header_step[next_invariant]:
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op child = eval_operand op entry` by
    (asm "childpost" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op u` by
    (qpat_assum `!op. abi_decoder_operand_live middle.cs_next_var op ==> eval_operand op child = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> eval_operand op entry = _` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> abi_decoder_operand_live middle.cs_next_var op` mp_tac >>
     qpat_assum `!op. _ ==> eval_operand op head = eval_operand op u` mp_tac >>
     qpat_assum `!op. op <> Var nv ==> eval_operand op v = _` mp_tac >>
     qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[]) >>
  `~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\
    mload p v = n2w (SUC j)` by
    (asm "vdef" mp_tac >> qpat_assum `~child.vs_halted` mp_tac >>
     qpat_assum `p < dimword (:256)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     `v.vs_memory = (mstore p (n2w (SUC j)) child).vs_memory` by
       gvs[markerTheory.Abbrev_def, jump_to_def, mstore_def, update_var_def] >>
     `mload p v = mload p (mstore p (n2w (SUC j)) child)` by simp[mload_def] >>
     gvs[mload_mstore_same, markerTheory.Abbrev_def, jump_to_def,
       mstore_def, update_var_def]) >>
  `u.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id)` by
    (asm "childpost" mp_tac >>
     qpat_assum `v.vs_allocas = child.vs_allocas` mp_tac >>
     qpat_assum `v.vs_alloca_next = child.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `Own st.cs_next_id end_st.cs_next_id v` by suspend "ownership_frame" >>
  suspend "invariant_assembly"
QED
Resume calldata_owned_header_step[ownership_frame]:
  `Own st.cs_next_id end_st.cs_next_id u` by
    (qpat_assum `H j u` mp_tac >> asm "Hdef" mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac[markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >> BETA_TAC >> strip_tac >> asm_rewrite_tac[]) >>
  `Own middle.cs_next_id st1.cs_next_id child` by
    (asm "childpost" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `Own middle.cs_next_id st1.cs_next_id v` by
    (qpat_assum `Own middle.cs_next_id st1.cs_next_id child` mp_tac >>
     qpat_assum `v.vs_allocas = child.vs_allocas` mp_tac >>
     qpat_assum `v.vs_alloca_next = child.vs_alloca_next` mp_tac >>
     qpat_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >> BETA_TAC >>
     ntac 2 disch_tac >> asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  qpat_assum `Own st.cs_next_id end_st.cs_next_id u` mp_tac >>
  qpat_assum `Own middle.cs_next_id st1.cs_next_id v` mp_tac >>
  qpat_assum `u.vs_alloca_next <= v.vs_alloca_next` mp_tac >>
  qpat_assum `!id. _ ==> FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id` mp_tac >>
  qpat_assum `st.cs_next_id <= header_st.cs_next_id` mp_tac >>
  qpat_assum `header_st.cs_next_id < middle.cs_next_id` mp_tac >>
  qpat_assum `middle.cs_next_id <= st1.cs_next_id` mp_tac >>
  qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
  qpat_assum `Abbrev (Own = _)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >> BETA_TAC >>
  ntac 8 disch_tac >>
  match_mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
                        `s` |-> `u`, `t` |-> `v`, `a` |-> `middle.cs_next_id`,
                        `b` |-> `st1.cs_next_id`]
                  calldata_owned_interval_replace) >>
  asm_rewrite_tac[] >> decide_tac
QED
Resume calldata_owned_header_step[invariant_assembly]:
  `?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial v /\
    !q k. MEM (q,k) scratch ==> ?id.
      st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)` by suspend "scratch_assembly" >>
  suspend "invariant_fields"
QED
Resume calldata_owned_header_step[scratch_assembly]:
  `?old. abi_decode_footprint_frame ((d,bufsize)::old) initial u /\
    !q k. MEM (q,k) old ==> ?id.
      st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k)` by
    (qpat_assum `H j u` mp_tac >> asm "Hdef" mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac[markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >> BETA_TAC >> strip_tac >> metis_tac[]) >>
  qexists_tac `old ++ new_scratch ++ [(p,32)]` >> conj_tac
  >- suspend "scratch_footprint" >>
  qpat_assum `!q k. MEM (q,k) old ==> _` mp_tac >>
  qpat_assum `!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==> FLOOKUP v.vs_allocas id = _` mp_tac >>
  asm "childpost" mp_tac >>
  qpat_assum `FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32)` mp_tac >>
  qpat_assum `v.vs_allocas = child.vs_allocas` mp_tac >>
  qpat_assum `st.cs_next_id <= header_st.cs_next_id` mp_tac >>
  qpat_assum `header_st.cs_next_id < middle.cs_next_id` mp_tac >>
  qpat_assum `middle.cs_next_id <= st1.cs_next_id` mp_tac >>
  qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  qpat_x_assum `~child.vs_halted /\ _` strip_assume_tac >>
  pure_rewrite_tac [MEM_APPEND, MEM, pairTheory.PAIR_EQ] >> rpt gen_tac >> strip_tac
  >- metis_tac[]
  >- (first_x_assum drule >> strip_tac >> qexists_tac `id` >>
      asm_rewrite_tac[] >> decide_tac) >>
  gvs[] >> qexists_tac `header_st.cs_next_id` >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >> metis_tac[]
QED
Resume calldata_owned_header_step[scratch_footprint]:
  `abi_decode_footprint_frame
    ((d+32+j*type_memory_size tv,type_memory_size tv)::new_scratch) u child` by
    (asm "childpost" mp_tac >>
     qpat_assum `entry.vs_memory = u.vs_memory` mp_tac >>
     qpat_assum `entry.vs_call_ctx = u.vs_call_ctx` mp_tac >>
     qpat_assum `entry.vs_data_section = u.vs_data_section` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[abi_decode_footprint_frame_def]) >>
  `abi_decode_footprint_frame ((d,bufsize)::(old++new_scratch)) initial child` by
    (qpat_assum `abi_decode_footprint_frame ((d,bufsize)::old) initial u` mp_tac >>
     qpat_assum `abi_decode_footprint_frame _ u child` mp_tac >>
     qpat_assum `d+32+j*type_memory_size tv+type_memory_size tv <= d+bufsize` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule calldata_footprint_accumulate >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `abi_decode_footprint_frame ((d,bufsize)::(old++new_scratch++[(p,32)])) initial child` by
    (qpat_assum `abi_decode_footprint_frame _ initial child` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     irule abi_decode_footprint_frame_weaken >> goal_assum (drule_at Any) >>
     rpt gen_tac >> strip_tac >> qexistsl_tac [`d'`,`sz`] >> gvs[MEM_APPEND]) >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `child` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm "vdef" mp_tac >> qpat_assum `p < dimword (:256)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `abi_decode_footprint_frame ((d,bufsize)::(old++new_scratch++[(p,32)]))
    child (mstore p (n2w (SUC j)) child)` by
    (simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
         qpat_x_assum `abi_footprint_disjoint _ _ _` mp_tac >>
         simp[abi_footprint_disjoint_def, MEM_APPEND] >> metis_tac[]) >>
     simp[mstore_def]) >>
  gvs[markerTheory.Abbrev_def, abi_decode_footprint_frame_def,
    jump_to_def, update_var_def, mstore_def]
QED
Resume calldata_owned_header_step[invariant_fields]:
  `mem_word_at d v.vs_memory = mem_word_at d u.vs_memory` by
    (qpat_assum `mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> strip_tac >>
     sym_tac >> first_x_assum irule >> decide_tac) >>
  suspend "invariant_final"
QED
Resume calldata_owned_header_step[invariant_final]:
  qpat_assum `H j u` mp_tac >>
  qpat_assum `j < nelts` mp_tac >>
  qpat_assum `~v.vs_halted` mp_tac >>
  qpat_assum `v.vs_current_bb = hdr` mp_tac >>
  qpat_assum `v.vs_inst_idx = 0` mp_tac >>
  qpat_assum `mload p v = n2w (SUC j)` mp_tac >>
  qpat_assum `mem_word_at d v.vs_memory = mem_word_at d u.vs_memory` mp_tac >>
  qpat_assum `v.vs_call_ctx = initial.vs_call_ctx` mp_tac >>
  qpat_assum `v.vs_data_section = u.vs_data_section` mp_tac >>
  qpat_assum `alloca_inv v` mp_tac >>
  qpat_assum `alloca_frontier_inv ctx fn site v` mp_tac >>
  qpat_assum `Own st.cs_next_id end_st.cs_next_id v` mp_tac >>
  qpat_assum `u.vs_alloca_next <= v.vs_alloca_next` mp_tac >>
  qpat_assum `!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==> FLOOKUP v.vs_allocas id = _` mp_tac >>
  qpat_assum `!id. _ ==> FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id` mp_tac >>
  qpat_assum `!op. op = src \/ op = dst \/ op = ip \/ _ ==> eval_operand op v = _` mp_tac >>
  qpat_assum `st.cs_next_id <= header_st.cs_next_id` mp_tac >>
  qpat_assum `header_st.cs_next_id < middle.cs_next_id` mp_tac >>
  qpat_assum `st1.cs_next_id <= end_st.cs_next_id` mp_tac >>
  qpat_assum `abi_decode_footprint_frame ((d,bufsize)::scratch) initial v` mp_tac >>
  qpat_assum `!q k. MEM (q,k) scratch ==> _` mp_tac >>
  asm "Hdef" mp_tac >> POP_ASSUM_LIST (K all_tac) >>
  pure_rewrite_tac[markerTheory.Abbrev_def] >> disch_then SUBST1_TAC >>
  BETA_TAC >> rpt disch_tac >>
  qpat_x_assum `~u.vs_halted /\ _` strip_assume_tac >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `id < middle.cs_next_id \/ st1.cs_next_id <= id` by decide_tac >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `scratch` >> asm_rewrite_tac[]
QED
Finalise calldata_owned_header_step

(* Equality-premise application interface; no new specification constant. *)
Theorem calldata_owned_header_initial_apply[local]:
  Own = (\lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  Rel = (\s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  X = (\s. ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn s) /\
  (bufsize:num) = 32+maxn*type_memory_size tv /\
  n = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  H = (\j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= n /\ n <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w n /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st = ((hdr,body_lbl,exit_lbl),st0) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\ fresh_vars_wrt st initial /\
  maxn < dimword (:256) /\ d+bufsize < dimword (:256) /\
  d+bufsize <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+bufsize <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+bufsize <= base_addr+cap /\
  Own st.cs_next_id end_st.cs_next_id initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  X initial \/ ?u. H 0 u /\ Rel initial u
Proof
  ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  asm_rewrite_tac[] >> BETA_TAC >>
  MATCH_ACCEPT_TAC (BETA_RULE (SIMP_RULE pure_ss [LET_THM]
    calldata_owned_header_initial))
QED

Theorem calldata_owned_header_step_apply[local]:
  Own = (\lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  Rel = (\s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  X = (\s. ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn s) /\
  (bufsize:num) = 32+maxn*type_memory_size tv /\
  n = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  H = (\j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= n /\ n <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w n /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  fn_has_code st0 middle fn /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  p < dimword (:256) /\ maxn < dimword (:256) /\ d+bufsize < dimword (:256) /\
  (d+bufsize <= p \/ p+32 <= d) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+bufsize <= base_addr+cap /\
  (!a w e.
    ~a.vs_halted /\ a.vs_current_bb = middle.cs_current_bb /\
    a.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) a = SOME w /\
    eval_operand (SND (SND ops)) a = SOME (n2w e) /\
    alloca_inv a /\ alloca_frontier_inv ctx fn site a /\
    Own middle.cs_next_id st1.cs_next_id a /\
    FLOOKUP a.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    X a \/ ?b x scratch.
      ~b.vs_halted /\ b.vs_current_bb = st1.cs_current_bb /\
      b.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e b.vs_memory /\ Rel a b /\
      b.vs_call_ctx = a.vs_call_ctx /\ b.vs_data_section = a.vs_data_section /\
      alloca_inv b /\ alloca_frontier_inv ctx fn site b /\
      Own middle.cs_next_id st1.cs_next_id b /\
      a.vs_alloca_next <= b.vs_alloca_next /\
      (!id q k. FLOOKUP a.vs_allocas id = SOME (q,k) ==>
        FLOOKUP b.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP b.vs_allocas id = FLOOKUP a.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op b = eval_operand op a) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) a b /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP b.vs_allocas id = SOME (q,k))) /\
  j < n /\ H j u ==>
  X u \/ ?v x.
    H (SUC j) v /\ P x /\ val_wf tv x /\
    val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
    mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
      mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel u v
Proof
  ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  asm_rewrite_tac[] >> BETA_TAC >>
  MATCH_ACCEPT_TAC (BETA_RULE (SIMP_RULE pure_ss [LET_THM]
    calldata_owned_header_step))
QED

Theorem calldata_owned_header_terminal_apply[local]:
  Own = (\lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  Rel = (\s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  X = (\s. ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn s) /\
  (bufsize:num) = 32+maxn*type_memory_size tv /\
  n = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  H = (\j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= n /\ n <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w n /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone) /\
  p < dimword (:256) /\ maxn < dimword (:256) /\
  H n u /\ LENGTH vs = n /\ EVERY P vs /\ EVERY (val_wf tv) vs /\
  (!k. k < n ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  X u \/ ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = n /\ n <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    Rel u t /\ t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  asm_rewrite_tac[] >> BETA_TAC >>
  MATCH_ACCEPT_TAC (BETA_RULE (SIMP_RULE pure_ss [LET_THM]
    calldata_owned_header_terminal))
QED

Theorem calldata_owned_iteration_apply[local]:
  Rel = (\s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  X = (\s. ?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\ R r /\
    mem_safe_run fuel ctx fn s) /\
  H 0 s /\
  (!j u. j < bound /\ H j u ==>
    X u \/ ?v x. H (SUC j) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel u v) /\
  (!u vs. H bound u /\ LENGTH vs = bound /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < bound ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    X u \/ ?t. Q t /\ Rel u t) ==>
  X s \/ ?t. Q t /\ Rel s t
Proof
  ntac 2 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  asm_rewrite_tac[] >> BETA_TAC >> strip_tac >>
  irule (BETA_RULE (SIMP_RULE pure_ss [LET_THM]
    calldata_typed_prefix_finite_iteration_terminal)) >>
  qexistsl_tac [`H`,`P`,`bound`,`d`,`0`,`tv`] >>
  rpt conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!j u. _` drule_all >> simp[])
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `[]` >> simp[])
  >- first_assum ACCEPT_TAC
  >> simp[]
QED

Theorem calldata_nonbulk_owned:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD
    (Lit 0w) di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),end_st) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\
  fn_has_code st1 end_st fn /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\ fresh_vars_wrt st initial /\
  maxn < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn u) \/ ?v x scratch.
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?t vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 <= bufsize` by (simp[Abbr `bufsize`]) >>
  `d < dimword (:256)` by decide_tac >>
  `header_st.cs_next_id < end_st.cs_next_id` by decide_tac >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  `X initial \/ ?u. H 0 u /\ Rel initial u` by
    (irule calldata_owned_header_initial_apply >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `Abbrev (H = _)`
       (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`
       (irule_at (Pat `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`)) >>
     qpat_assum `abi_decode_loop_prefix _ _ _ _ = _`
       (irule_at (Pat `abi_decode_loop_prefix _ _ _ _ = _`)) >>
     qpat_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`
       (irule_at (Pat `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`)) >>
     qexists_tac `tv` >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
         Abbr `bufsize`, Abbr `nelts`]])
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  rename1 `H 0 start` >>
  `initial.vs_alloca_next < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> disch_then ACCEPT_TAC) >>
  `p < dimword (:256)` by
    (qpat_assum `(_ = NONE /\ p = _) \/ _` mp_tac >>
     qpat_assum `initial.vs_alloca_next < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  `!j u. j < nelts /\ H j u ==>
    X u \/ ?v x. H (SUC j) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel u v` by
    (rpt gen_tac >> strip_tac >>
     irule calldata_owned_header_step_apply >>
     conj_tac >- simp[] >>
     qpat_assum `Abbrev (H = _)`
       (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`
       (irule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`)) >>
     qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ _|>`)) >>
     qpat_assum `lookup_block body_lbl _ = _`
       (irule_at (Pat `lookup_block body_lbl _ = _`)) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
         Abbr `bufsize`, Abbr `nelts`]]) >>
  qabbrev_tac `Q = \t. ?vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = nelts /\ nelts <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))` >>
  `!u vs. H nelts u /\ LENGTH vs = nelts /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < nelts ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    X u \/ ?t. Q t /\ Rel u t` by
    (rpt gen_tac >> strip_tac >>
     `!op. abi_decoder_operand_live st.cs_next_var op ==>
       op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone` by
       (qpat_assum `!op. (op = src \/ op = dst \/ _) ==> _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     `X u \/ ?t scratch.
       ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
       t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
       LENGTH vs = nelts /\ nelts <= maxn /\ EVERY P vs /\
       val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
       val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
       Rel u t /\ t.vs_call_ctx = initial.vs_call_ctx /\
       t.vs_data_section = initial.vs_data_section /\
       alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
       Own st.cs_next_id end_st.cs_next_id t /\
       initial.vs_alloca_next <= t.vs_alloca_next /\
       (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
         FLOOKUP t.vs_allocas id = SOME (q,k)) /\
       (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
         FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
       (!op. abi_decoder_operand_live st.cs_next_var op ==>
         eval_operand op t = eval_operand op initial) /\
       abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
       (!q k. MEM (q,k) scratch ==>
         ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
           FLOOKUP t.vs_allocas id = SOME (q,k))` by
       (irule calldata_owned_header_terminal_apply >>
        qpat_assum `Abbrev (H = _)`
          (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
          (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
        qpat_assum `lookup_block exit_lbl _ = _`
          (irule_at (Pat `lookup_block exit_lbl _ = _`)) >>
        rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
          (rpt gen_tac >> strip_tac >>
           qpat_assum `!op. op = src \/ _`
             (qspec_then `op` mp_tac) >> simp[]),
          simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
            Abbr `bufsize`, Abbr `nelts`]])
     >- (disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> qexists_tac `t` >>
     conj_tac >- (simp_tac bool_ss [Abbr `Q`] >>
       qexistsl_tac [`vs`,`scratch`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `X start \/ ?t. Q t /\ Rel start t` by
    (irule calldata_owned_iteration_apply >>
     reverse conj_tac
     >- (qexistsl_tac [`\r. ?z. r = Abort Revert_abort z`,`ctx`,`fn`] >>
         simp_tac bool_ss [Abbr `Rel`, Abbr `X`, FUN_EQ_THM] >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[fragExecTheory.exit_result_def]) >>
     qexistsl_tac [`H`,`P`,`nelts`,`d`,`tv`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (disj1_tac >>
      qpat_assum `Rel initial start` mp_tac >>
      qpat_assum `X start` mp_tac >>
      simp_tac bool_ss [Abbr `Rel`, Abbr `X`] >>
      POP_ASSUM_LIST (K all_tac) >> strip_tac >>
      disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >> metis_tac[]) >>
  `Rel initial t` by
    (qpat_assum `Rel initial start` mp_tac >>
     qpat_assum `Rel start t` mp_tac >>
     simp_tac bool_ss [Abbr `Rel`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[calldataSafeIterationTheory.calldata_safe_transfer_trans]) >>
  disj2_tac >>
  qpat_x_assum `Q t` mp_tac >> simp_tac bool_ss [Abbr `Q`] >>
  disch_then (qx_choose_then `vs` (qx_choose_then `scratch` strip_assume_tac)) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >> asm_rewrite_tac[]
QED

(* Finite guard arithmetic is independent of stale temporary bindings. *)
Theorem calldata_gt_repeat:
  emit_op GT [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (bool_to_word (w2n a > w2n b)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (w2n a > w2n b)) s` >>
  `step_inst_base (mk_inst st.cs_next_id GT [lhs;rhs]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_GT >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_iszero_repeat:
  emit_op ISZERO [arg] st = (out,st') /\ eval_operand arg s = SOME a ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (bool_to_word (a = 0w)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (a = 0w)) s` >>
  `step_inst_base (mk_inst st.cs_next_id ISZERO [arg]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_ISZERO >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_count_guard_repeat_sequence:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= limit ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all calldata_gt_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all calldata_iszero_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last_st)` >>
  `run_inst_seq (emitted_insts c3 last_st) s3 = OK s3` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def, assert_ok]) >>
  imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >>
  conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`,`c2`] >>
      conj_tac >- (irule run_inst_seq_compose_ok >>
        goal_assum (drule_at Any) >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      metis_tac[inst_extends_trans]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  conj_tac
  >- (`abi_decoder_operand_live c1.cs_next_var count_op` by
        metis_tac[abi_decoder_operand_live_emit] >>
      `abi_decoder_operand_live c2.cs_next_var count_op` by
        metis_tac[abi_decoder_operand_live_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live c1.cs_next_var op /\
   abi_decoder_operand_live c2.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  metis_tac[]
QED

Theorem calldata_count_guard_repeat_rejected:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  limit < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last_st)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all calldata_gt_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all calldata_iszero_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  qabbrev_tac `rstate = revert_state (set_returndata [] s3)` >>
  `run_inst_seq (emitted_insts c3 last_st) s3 = Abort Revert_abort rstate` by
    (`step_inst_base (mk_inst c3.cs_next_id ASSERT [ok] []) s3 =
       Abort Revert_abort rstate` by
       (irule assert_revert >> simp[Abbr `rstate`]) >>
     drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def]) >>
  imp_res_tac inst_extends_emit_void >>
  `emitted_insts st last_st = emitted_insts st c1 ++
    emitted_insts c1 c2 ++ emitted_insts c2 c3 ++ emitted_insts c3 last_st` by
    metis_tac[emitted_insts_append, inst_extends_trans, inst_extends_def,
              APPEND_ASSOC] >>
  qexists_tac `rstate` >> asm_rewrite_tac[] >>
  qpat_assum `run_inst_seq _ s = OK _` mp_tac >>
  qpat_assum `run_inst_seq _ _ = OK s2` mp_tac >>
  qpat_assum `run_inst_seq _ s2 = OK s3` mp_tac >>
  qpat_assum `run_inst_seq _ s3 = Abort Revert_abort rstate` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[run_inst_seq_append]
QED

Theorem calldata_array_header_repeat_sequence:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ d < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD p s) /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    abi_decode_frame d 32 s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),last_st)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK loaded` >>
  `eval_operand dst loaded = SOME (n2w d)` by metis_tac[] >>
  `run_inst_seq (emitted_insts c1 last_st) loaded =
     OK (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
    (`step_inst_base (mk_inst c1.cs_next_id MSTORE [dst;cnt] []) loaded =
       OK (mstore (w2n (n2w d : bytes32)) (abi_decode_load CALLDATALOAD p s) loaded)` by
       (irule step_MSTORE >> simp[]) >>
     `w2n (n2w d : bytes32) = d` by simp[] >>
     drule emitted_insts_emit_void >> strip_tac >>
     qpat_x_assum `loaded = _` kall_tac >> fs[run_inst_seq_def]) >>
  drule inst_extends_emit_void >> strip_tac >>
  qexists_tac `mstore d (abi_decode_load CALLDATALOAD p s) loaded` >>
  conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`loaded`,`c1`] >> simp[]) >>
  qpat_x_assum `loaded = _` kall_tac >>
  simp[eval_operand_mstore, mstore_mem_word_at_same] >>
  conj_tac
  >- (`abi_decode_frame d 32 loaded
         (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
        irule abi_decode_mstore_frame >>
      qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
      simp[abi_decode_frame_def]) >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  metis_tac[inst_extends_trans]
QED

Theorem calldata_array_header_repeat_prefix_safe:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ d+32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),st')` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c1)` by
    (drule emitted_insts_emit_op >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> simp[]) >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_mstore_prefix_safe) >>
  qexists_tac `d` >> simp[] >> metis_tac[]
QED

Theorem calldata_count_guard_repeat_frag_mem:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src initial = SOME p /\ limit < dimword (:256) ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= limit /\
      eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p initial) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next /\ t.vs_halted = initial.vs_halted)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >> drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_count_guard_code_shape >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >>
  fs[inst_extends_def] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= limit`
  >- (drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      simp[instIdxIndepTheory.eval_op_inst_idx]) >>
  `limit < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_count_guard_repeat_rejected >> strip_tac >>
  disj2_tac >> qexists_tac `t` >> simp[]
QED

Theorem calldata_array_header_repeat_frag_mem:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  d+32 <= initial.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD p initial) /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      abi_decode_frame d 32 initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next /\
      t.vs_halted = initial.vs_halted)
    (K F)
Proof
  strip_tac >> drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  `st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  drule calldata_array_header_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> fs[inst_extends_def] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_array_header_repeat_prefix_safe) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  fs[instIdxIndepTheory.eval_op_inst_idx, abi_decode_frame_def] >>
  first_assum ACCEPT_TAC
QED

Theorem calldata_index_init_repeat_memory_frame:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated ==>
  abi_decode_frame p 32 s (mstore p 0w allocated)
Proof
  strip_tac >>
  `abi_decode_frame p 32 allocated (mstore p 0w allocated)` by
    irule abi_decode_mstore_frame >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[abi_decode_frame_def, update_var_def] >> first_assum ACCEPT_TAC
QED

Theorem calldata_array_loop_init_repeat_safe:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
    p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) ==>
  frag_exec_mem ctx st loop_st (\s. s = initial)
    (\t. eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
      (!id. id <> header_st.cs_next_id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
         t.vs_alloca_next = initial.vs_alloca_next+32
       else t.vs_alloca_next = initial.vs_alloca_next) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial))
    (\r. ?u. r = Abort Revert_abort u)
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
  `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `isPREFIX st.cs_current_insts loop_st.cs_current_insts` by
    (qpat_x_assum `inst_extends st loop_st` mp_tac >>
     simp_tac bool_ss [inst_extends_def] >> strip_tac >>
     simp_tac bool_ss [IS_PREFIX_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st loop_st)` by
    (asm_rewrite_tac[EVERY_APPEND] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
     (emitted_insts st loop_st)` by
    (imp_res_tac calldata_dynarray_prefix_opcodes >>
     imp_res_tac calldata_array_header_opcodes >>
     imp_res_tac abi_decode_index_init_opcodes >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  reverse (Cases_on `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn`)
  >- suspend "reject" >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) initial = OK g` >>
  `eval_operand src g = SOME srcword /\ eval_operand dst g = SOME (n2w d)` by
    metis_tac[] >>
  `abi_decoder_operand_live guard_st.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) g = OK h` >>
  `h.vs_allocas = initial.vs_allocas /\ h.vs_alloca_next = initial.vs_alloca_next` by
    metis_tac[] >>
  `?allocated. step_inst_base (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString header_st.cs_next_var)]) h = OK allocated /\
     eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
     p+32 <= allocated.vs_alloca_next /\
     FLOOKUP allocated.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP allocated.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
        allocated.vs_alloca_next = initial.vs_alloca_next+32
      else allocated.vs_alloca_next = initial.vs_alloca_next)` by
    suspend "allocation" >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op (mstore p 0w allocated) = eval_operand op initial` by
    suspend "live" >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >>
  reverse conj_tac >- suspend "execution" >>
  suspend "safety"
QED

Resume calldata_array_loop_init_repeat_safe[allocation]:
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

Resume calldata_array_loop_init_repeat_safe[live]:
  rpt strip_tac >>
  `abi_decoder_operand_live guard_st.cs_next_var op /\
   abi_decoder_operand_live header_st.cs_next_var op` by
    (conj_tac >>
     irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_rewrite_tac[] >> decide_tac) >>
  `eval_operand op h = eval_operand op initial` by metis_tac[] >>
  drule_all calldata_index_init_live_frame >> simp[]
QED

Resume calldata_array_loop_init_repeat_safe[reject]:
  `cs_extends st guard_st /\ cs_extends guard_st loop_st` by
    (conj_tac >> irule cs_extends_same_block >>
     simp[] >> metis_tac[inst_extends_def, IS_PREFIX_APPEND,
                        inst_extends_trans]) >>
  irule frag_exec_mem_exit_prefix >> qexists_tac `guard_st` >>
  asm_rewrite_tac[] >>
  drule_all calldata_count_guard_repeat_frag_mem >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp[] >> metis_tac[]
QED

Resume calldata_array_loop_init_repeat_safe[safety]:
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `g` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `h` >> asm_rewrite_tac[] >> conj_tac
  >- (`d+32 <= g.vs_alloca_next` by (asm_rewrite_tac[] >> decide_tac) >>
      ho_match_mp_tac (GEN_ALL calldata_array_header_repeat_prefix_safe) >>
      goal_assum (drule_at (Pos hd)) >>
      qexistsl_tac [`srcword`, `d`] >> asm_rewrite_tac[]) >>
  ho_match_mp_tac (GEN_ALL calldata_index_init_prefix_safe) >>
  goal_assum (drule_at (Pos hd)) >> goal_assum (drule_at (Pos hd)) >>
  qexists_tac `p` >> asm_rewrite_tac[]
QED

Resume calldata_array_loop_init_repeat_safe[execution]:
  disj1_tac >> qexists_tac `mstore p 0w allocated` >>
  conj_tac
  >- (qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
      qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
      qpat_assum `run_inst_seq _ h = OK (mstore p 0w allocated)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[run_inst_seq_append]) >>
  `abi_decode_load CALLDATALOAD srcword g =
     abi_decode_load CALLDATALOAD srcword initial` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  `abi_decode_frame p 32 h (mstore p 0w allocated)` by
    (irule calldata_index_init_repeat_memory_frame >> goal_assum (drule_at Any)) >>
  `abi_decoder_operand_live header_st.cs_next_var cnt` by
    (qpat_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     drule abi_decoder_operand_live_emit >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `eval_operand cnt (mstore p 0w allocated) = eval_operand cnt h` by
    (irule calldata_index_init_live_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `mem_word_at d (mstore p 0w allocated).vs_memory = mem_word_at d h.vs_memory` by
    (irule abi_decode_frame_mem_word >> goal_assum (drule_at Any) >> decide_tac) >>
  `(!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
     mem_bytes_at a n (mstore p 0w allocated).vs_memory = mem_bytes_at a n initial.vs_memory) /\
   (mstore p 0w allocated).vs_call_ctx = initial.vs_call_ctx /\
   (mstore p 0w allocated).vs_data_section = initial.vs_data_section` by
    (qpat_assum `abi_decode_frame p 32 h _` mp_tac >>
     qpat_assum `abi_decode_frame d 32 g h` mp_tac >>
     qpat_assum `g.vs_memory = _` mp_tac >>
     qpat_assum `g.vs_call_ctx = _` mp_tac >>
     qpat_assum `g.vs_data_section = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [abi_decode_frame_def] >> rpt strip_tac >>
     metis_tac[]) >>
  `(mstore p 0w allocated).vs_allocas = allocated.vs_allocas /\
   (mstore p 0w allocated).vs_alloca_next = allocated.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `header_st.cs_next_var = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `header_st.cs_next_id = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `ip = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `!s k. mload p (s with vs_inst_idx := k) = mload p s` by simp[mload_def] >>
  simp[instIdxIndepTheory.eval_op_inst_idx, eval_operand_mstore] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise calldata_array_loop_init_repeat_safe

Theorem calldata_owned_header_initial_repeat:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?u.
    (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      0 <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src u = SOME srcword /\
      eval_operand dst u = SOME (n2w d) /\
      eval_operand ip u = SOME (n2w p) /\ mload p u = n2w 0 /\
      mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
      u.vs_call_ctx = initial.vs_call_ctx /\
      u.vs_data_section = initial.vs_data_section /\
      FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= u.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op u = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
        !q k. MEM (q,k) scratch ==>
          ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
            FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn initial))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 <= bufsize` by simp[Abbr `bufsize`] >>
  `d < dimword (:256)` by decide_tac >>
  drule_all calldata_array_loop_init_repeat_safe >> disch_tac >>
  qmatch_asmsub_abbrev_tac `frag_exec_mem ctx st loop_st _ InitPost _` >>
  drule calldata_init_to_header_safe >>
  disch_then drule >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `initial` mp_tac) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [] >>
  reverse (disch_then DISJ_CASES_TAC)
  >- (disj1_tac >> simp_tac bool_ss [Abbr `X`] >>
      pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
      strip_tac >> metis_tac[]) >>
  pop_assum (qx_choose_then `t` strip_assume_tac) >>
  disj2_tac >> qexists_tac `jump_to hdr t` >>
  reverse conj_tac >- simp[Abbr `Rel`] >>
  qpat_x_assum `InitPost t` mp_tac >>
  simp_tac bool_ss [Abbr `InitPost`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_index_init_owned_fields >> strip_tac >>
  `p < dimword (:256) /\ p+32 <= t.vs_alloca_next` by
    (qpat_x_assum `FLOOKUP t.vs_allocas _ = SOME (p,32)` mp_tac >>
     qpat_x_assum `alloca_inv t` mp_tac >>
     qpat_x_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     qpat_x_assum `unit_alloca_budget ctx < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def, alloca_frontier_inv_def] >>
     rpt strip_tac >>
     `p+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `Own st.cs_next_id end_st.cs_next_id t` by suspend "ownership" >>
  `abi_decode_footprint_frame [(d,bufsize);(p,32)] initial t` by
    suspend "footprint" >>
  `!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
     FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `FLOOKUP t.vs_allocas oid = SOME (base_addr,cap)` by metis_tac[] >>
  `alloca_inv (jump_to hdr t) /\
   alloca_frontier_inv ctx fn site (jump_to hdr t)` by
    (mp_tac (Q.INST [`s` |-> `t`, `t` |-> `jump_to hdr t`]
       calldata_alloca_invariants_fields) >> simp[jump_to_def]) >>
  `Own st.cs_next_id end_st.cs_next_id (jump_to hdr t)` by
    (qpat_assum `Own _ _ t` mp_tac >>
     simp_tac pure_ss [Abbr `Own`] >> POP_ASSUM_LIST (K all_tac) >>
     BETA_TAC >>
     `((jump_to hdr t).vs_allocas = t.vs_allocas) /\
      ((jump_to hdr t).vs_alloca_next = t.vs_alloca_next)` by
       simp[jump_to_def] >>
     asm_rewrite_tac[]) >>
  `mload p (jump_to hdr t) = 0w` by
    (qpat_assum `mload p t = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[mload_def, jump_to_def]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
  simp_tac bool_ss [Abbr `H`] >>
  simp[Abbr `nelts`] >>
  simp[jump_to_def] >>
  qexists_tac `[(p,32)]` >>
  simp[jump_to_def, abi_decode_footprint_frame_def] >>
  qexists_tac `header_st.cs_next_id` >> simp[]
QED

Resume calldata_owned_header_initial_repeat[ownership]:
  drule_all calldata_index_init_literal_site >> strip_tac >>
  qpat_x_assum `Own _ _ initial` mp_tac >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  BETA_TAC >> disch_tac >>
  ho_match_mp_tac (GEN_ALL (SIMP_RULE (pure_ss ++ boolSimps.BOOL_ss)
    [LET_THM] calldata_owned_counter_update)) >>
  qexistsl_tac [`initial`,`p`,`ins`,`header_st.cs_next_id`] >>
  asm_rewrite_tac[]
QED

Resume calldata_owned_header_initial_repeat[footprint]:
  qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` mp_tac >>
  qpat_assum `t.vs_call_ctx = _` mp_tac >>
  qpat_assum `t.vs_data_section = _` mp_tac >>
  qpat_assum `32 <= bufsize` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >>
  qpat_assum `!d' sz. _` (qspecl_then [`d`,`bufsize`]
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!d' sz. _` (qspecl_then [`p`,`32`]
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  first_x_assum irule >> decide_tac
QED

Finalise calldata_owned_header_initial_repeat


(* Composition from the owned header boundary, independently of register freshness. *)
Theorem calldata_owned_after_initial_repeat[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  fn_has_code st0 middle fn /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  maxn < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn u) \/ ?v x scratch.
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ((?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn initial) \/ ?u.
    (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      0 <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src u = SOME srcword /\
      eval_operand dst u = SOME (n2w d) /\
      eval_operand ip u = SOME (n2w p) /\ mload p u = n2w 0 /\
      mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
      u.vs_call_ctx = initial.vs_call_ctx /\
      u.vs_data_section = initial.vs_data_section /\
      FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= u.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op u = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
        !q k. MEM (q,k) scratch ==> ?id.
          st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn initial))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?t vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `X initial \/ _` strip_assume_tac
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  rename1 `H 0 start` >>
  `p < dimword (:256)` by
    (qpat_assum `H 0 start` mp_tac >> simp_tac bool_ss [Abbr `H`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all alloca_frontier_inv_bound >> disch_tac >>
     qpat_x_assum `alloca_inv start` mp_tac >>
     qpat_x_assum `FLOOKUP start.vs_allocas _ = SOME (p,32)` mp_tac >>
     qpat_x_assum `start.vs_alloca_next < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> rpt strip_tac >>
     `p+32 <= start.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `!j u. j < nelts /\ H j u ==>
    X u \/ ?v x. H (SUC j) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel u v` by
    (rpt gen_tac >> strip_tac >>
     irule calldata_owned_header_step_apply >>
     conj_tac >- simp[] >>
     qpat_assum `Abbrev (H = _)`
       (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`
       (irule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`)) >>
     qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ _|>`)) >>
     qpat_assum `lookup_block body_lbl _ = _`
       (irule_at (Pat `lookup_block body_lbl _ = _`)) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
         Abbr `bufsize`, Abbr `nelts`]]) >>
  qabbrev_tac `Q = \t. ?vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = nelts /\ nelts <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))` >>
  `!u vs. H nelts u /\ LENGTH vs = nelts /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < nelts ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    X u \/ ?t. Q t /\ Rel u t` by suspend "terminal" >>
  `X start \/ ?t. Q t /\ Rel start t` by
    (irule calldata_owned_iteration_apply >>
     reverse conj_tac
     >- (qexistsl_tac [`\r. ?z. r = Abort Revert_abort z`,`ctx`,`fn`] >>
         simp_tac bool_ss [Abbr `Rel`, Abbr `X`, FUN_EQ_THM] >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[fragExecTheory.exit_result_def]) >>
     qexistsl_tac [`H`,`P`,`nelts`,`d`,`tv`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (disj1_tac >>
      qpat_assum `Rel initial start` mp_tac >>
      qpat_assum `X start` mp_tac >>
      simp_tac bool_ss [Abbr `Rel`, Abbr `X`] >>
      POP_ASSUM_LIST (K all_tac) >> strip_tac >>
      disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >> metis_tac[]) >>
  `Rel initial t` by
    (qpat_assum `Rel initial start` mp_tac >>
     qpat_assum `Rel start t` mp_tac >>
     simp_tac bool_ss [Abbr `Rel`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[calldataSafeIterationTheory.calldata_safe_transfer_trans]) >>
  disj2_tac >>
  qpat_x_assum `Q t` mp_tac >> simp_tac bool_ss [Abbr `Q`] >>
  disch_then (qx_choose_then `vs` (qx_choose_then `scratch` strip_assume_tac)) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >> asm_rewrite_tac[]
QED

Resume calldata_owned_after_initial_repeat[terminal]:
  rpt gen_tac >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone` by
    (qpat_assum `!op. (op = src \/ op = dst \/ _) ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `X u \/ ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = nelts /\ nelts <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    Rel u t /\ t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))` by
    (irule calldata_owned_header_terminal_apply >>
     qpat_assum `Abbrev (H = _)`
       (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
     qpat_assum `lookup_block exit_lbl _ = _`
       (irule_at (Pat `lookup_block exit_lbl _ = _`)) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!op. op = src \/ _`
          (qspec_then `op` mp_tac) >> simp[]),
       simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
         Abbr `bufsize`, Abbr `nelts`]])
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists_tac `t` >>
  conj_tac >- (simp_tac bool_ss [Abbr `Q`] >>
    qexistsl_tac [`vs`,`scratch`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise calldata_owned_after_initial_repeat

Theorem calldata_nonbulk_owned_repeat:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD
    (Lit 0w) di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),end_st) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\
  fn_has_code st1 end_st fn /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn u) \/ ?v x scratch.
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?t vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `header_st.cs_next_id < end_st.cs_next_id` by decide_tac >>
  simp_tac pure_ss [NoAsms, Abbr `Own`, Abbr `Rel`, Abbr `X`,
    Abbr `bufsize`, Abbr `nelts`] >>
  BETA_TAC >>
  irule calldata_owned_after_initial_repeat >>
  qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`
    (irule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`)) >>
  qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
    (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
  qpat_assum `lookup_block st1.cs_current_bb _ = _`
    (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ _|>`)) >>
  qpat_assum `lookup_block exit_lbl _ = _`
    (irule_at (Pat `lookup_block exit_lbl _ = _`)) >>
  qexistsl_tac [`p`,`oid`,`header_st`,`cap`,`body_bb`,`base_addr`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp_tac bool_ss []]
  >- (first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [] o BETA_RULE)) >>
  irule (SIMP_RULE bool_ss [] calldata_owned_header_initial_repeat) >>
  qpat_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`
    (irule_at (Pat `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`)) >>
  qpat_assum `abi_decode_loop_prefix _ _ _ _ = _`
    (irule_at (Pat `abi_decode_loop_prefix _ _ _ _ = _`)) >>
  qpat_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`
    (irule_at (Pat `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp_tac bool_ss []] >>
  first_assum (ACCEPT_TAC o BETA_RULE)
QED

(* The generated guard observes the encoded word threshold, even when the
   source capacity itself does not fit in a word. *)
Theorem calldata_count_guard_mod_limit:
  abi_decode_count_guard CALLDATALOAD src (limit MOD dimword (:256)) st =
  abi_decode_count_guard CALLDATALOAD src limit st
Proof
  simp[abi_decode_count_guard_def, n2w_mod]
QED

Theorem calldata_count_guard_repeat_sequence_mod:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\
  w2n (abi_decode_load CALLDATALOAD p s) <= limit MOD dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `abi_decode_count_guard CALLDATALOAD src (limit MOD dimword (:256)) st =
    (count_op,st')` by simp[calldata_count_guard_mod_limit] >>
  drule calldata_count_guard_repeat_sequence >> simp[]
QED

Theorem calldata_count_guard_repeat_rejected_mod:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\
  limit MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  `abi_decode_count_guard CALLDATALOAD src (limit MOD dimword (:256)) st =
    (count_op,st')` by simp[calldata_count_guard_mod_limit] >>
  drule calldata_count_guard_repeat_rejected >> simp[]
QED

Theorem calldata_count_guard_accepted_bounds:
  w2n (w:bytes32) <= limit MOD dimword (:256) ==>
  w2n w < dimword (:256) /\ w2n w <= limit
Proof
  strip_tac >> simp[w2n_lt] >>
  `limit MOD dimword (:256) <= limit` by simp[MOD_LESS_EQ] >>
  decide_tac
QED

Theorem calldata_count_guard_repeat_frag_mem_mod:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src initial = SOME p ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= limit MOD dimword (:256) /\
      eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p initial) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next /\ t.vs_halted = initial.vs_halted)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >>
  `abi_decode_count_guard CALLDATALOAD src (limit MOD dimword (:256)) st =
    (count_op,st')` by simp[calldata_count_guard_mod_limit] >>
  drule calldata_count_guard_repeat_frag_mem >> simp[]
QED

Theorem calldata_array_loop_init_repeat_safe_mod:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
    p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) ==>
  frag_exec_mem ctx st loop_st (\s. s = initial)
    (\t. eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) < dimword (:256) /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
      (!id. id <> header_st.cs_next_id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
         t.vs_alloca_next = initial.vs_alloca_next+32
       else t.vs_alloca_next = initial.vs_alloca_next) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial))
    (\r. ?u. r = Abort Revert_abort u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w)
     (maxn MOD dimword (:256)) abi_sz st = ((),guard_st)` by
    (qpat_assum `abi_decode_dynarray_prefix _ _ _ maxn _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_dynarray_prefix_def, comp_bind_def,
        calldata_count_guard_mod_limit]) >>
  `abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w)
     (maxn MOD dimword (:256)) abi_sz st = ((ip,cnt),loop_st)` by
    (qpat_assum `abi_decode_array_loop_init _ _ _ _ maxn _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
        comp_bind_def, comp_ignore_bind_def, calldata_count_guard_mod_limit]) >>
  `maxn MOD dimword (:256) < dimword (:256)` by simp[] >>
  drule_all calldata_array_loop_init_repeat_safe >>
  disch_then (fn th => irule frag_exec_mem_conseq >> irule_at Any th) >>
  simp[w2n_lt] >> rpt strip_tac >>
  drule calldata_count_guard_accepted_bounds >> simp[]
QED

Theorem calldata_owned_header_terminal_observed:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone) /\
  p < dimword (:256) /\
  (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <=
      w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\
    mload p u = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame
      ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  EVERY P vs /\ EVERY (val_wf tv) vs /\
  (!k. k < w2n (abi_decode_load CALLDATALOAD srcword initial) ==>
    val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) u.vs_memory) ==>
  (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn u) \/
  ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn u)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `H nelts u` mp_tac >>
  simp_tac bool_ss [Abbr `H`] >> strip_tac >>
  `p+32 <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (p,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `nelts < dimword (:256)` by simp[Abbr `nelts`, w2n_lt] >>
  `abi_decode_load CALLDATALOAD srcword u = n2w nelts` by
    simp[Abbr `nelts`, abi_decode_load_def, abi_decode_source_def] >>
  `mload (w2n (n2w p:bytes32)) u = n2w nelts` by simp[] >>
  `w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  qabbrev_tac `v = jump_to exit_lbl
    (abi_decode_header_state hiv hcv hcmp hdone nelts nelts u)` >>
  `v = jump_to exit_lbl
    (abi_decode_header_state hiv hcv hcmp hdone nelts nelts u)` by simp[Abbr `v`] >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|>`
    by simp[] >>
  drule_all calldata_terminal_header_array >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  disj2_tac >> qexistsl_tac [`v`,`scratch`] >>
  `Own st.cs_next_id end_st.cs_next_id v` by
    (qpat_assum `Own _ _ u` mp_tac >>
     qpat_assum `v.vs_allocas = _` mp_tac >>
     qpat_assum `v.vs_alloca_next = _` mp_tac >>
     qpat_assum `Abbrev (Own = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rewrite_tac[markerTheory.Abbrev_def] >>
     disch_then SUBST1_TAC >> BETA_TAC >>
     ntac 2 disch_tac >> asm_rewrite_tac[]) >>
  `Rel u v` by
    (qpat_assum `!fuel r. _` mp_tac >> simp_tac bool_ss [Abbr `Rel`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op initial` by
    (qpat_assum `!op. _ ==> eval_operand op v = eval_operand op u` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live _ op ==> eval_operand op u = _` mp_tac >>
     qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `v = jump_to _ _` kall_tac >>
  qpat_x_assum `!fuel r. _` kall_tac >>
  `~v.vs_halted /\ v.vs_current_bb = exit_lbl /\ v.vs_inst_idx = 0` by
    (qpat_assum `Abbrev (v = _)` mp_tac >>
     qpat_assum `~u.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]) >>
  `abi_decode_footprint_frame ((d,bufsize)::scratch) initial v` by
    (qpat_assum `abi_decode_footprint_frame _ initial u` mp_tac >>
     qpat_assum `v.vs_memory = _` mp_tac >>
     qpat_assum `v.vs_call_ctx = _` mp_tac >>
     qpat_assum `v.vs_data_section = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_footprint_frame_def]) >>
  asm_rewrite_tac[listTheory.LENGTH]
QED

(* The only unbounded-capacity case has zero element stride.  In that
   case the old step can use the observed count as its capacity without
   changing any footprint, destination extent, or child obligation. *)
Theorem calldata_owned_header_step_observed:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  fn_has_code st0 middle fn /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  p < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!a w e.
    ~a.vs_halted /\ a.vs_current_bb = middle.cs_current_bb /\
    a.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) a = SOME w /\
    eval_operand (SND (SND ops)) a = SOME (n2w e) /\
    alloca_inv a /\ alloca_frontier_inv ctx fn site a /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP a.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= a.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP a.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn a = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn a) \/ ?b x scratch.
      ~b.vs_halted /\ b.vs_current_bb = st1.cs_current_bb /\
      b.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e b.vs_memory /\
      (!fuel r. run_from fuel ctx fn b = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn a = r /\
          (mem_safe_run fuel ctx fn b ==> mem_safe_run fuel' ctx fn a)) /\
      b.vs_call_ctx = a.vs_call_ctx /\ b.vs_data_section = a.vs_data_section /\
      alloca_inv b /\ alloca_frontier_inv ctx fn site b /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP b.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= b.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      a.vs_alloca_next <= b.vs_alloca_next /\
      (!id q k. FLOOKUP a.vs_allocas id = SOME (q,k) ==>
        FLOOKUP b.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP b.vs_allocas id = FLOOKUP a.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op b = eval_operand op a) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) a b /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP b.vs_allocas id = SOME (q,k))) /\
  j < w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==>
        ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) ==>
  (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn u) \/ ?v x.
    (~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\
      SUC j <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src v = SOME srcword /\
      eval_operand dst v = SOME (n2w d) /\
      eval_operand ip v = SOME (n2w p) /\ mload p v = n2w (SUC j) /\
      mem_word_at d v.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
      v.vs_call_ctx = initial.vs_call_ctx /\
      v.vs_data_section = initial.vs_data_section /\
      FLOOKUP v.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP v.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op v = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial v /\
        !q k. MEM (q,k) scratch ==>
          ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
            FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    P x /\ val_wf tv x /\
    val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
    mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
      mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `maxn < dimword (:256)`
  >- (mp_tac (SPEC_ALL calldata_owned_header_step) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  `type_memory_size tv = 0` by
    (Cases_on `type_memory_size tv` >> simp[] >>
     `maxn <= maxn * SUC n` by simp[MULT_CLAUSES] >>
     qpat_x_assum `d+(32+maxn*_) < dimword (:256)` mp_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  mp_tac (Q.INST [`maxn` |-> `w2n (abi_decode_load CALLDATALOAD srcword initial)`]
    (SPEC_ALL calldata_owned_header_step)) >>
  qpat_assum `type_memory_size tv = 0` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, MULT_0, ADD_0]) >>
    pure_rewrite_tac [th, MULT_0, ADD_0]) >>
  qpat_assum `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn`
    (fn th => pure_rewrite_tac [th, LESS_EQ_REFL, w2n_lt, AND_CLAUSES]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem calldata_owned_header_initial_repeat_observed:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?u.
    (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      0 <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src u = SOME srcword /\
      eval_operand dst u = SOME (n2w d) /\
      eval_operand ip u = SOME (n2w p) /\ mload p u = n2w 0 /\
      mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
      u.vs_call_ctx = initial.vs_call_ctx /\
      u.vs_data_section = initial.vs_data_section /\
      FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= u.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op u = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
        !q k. MEM (q,k) scratch ==>
          ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
            FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `maxn < dimword (:256)`
  >- (mp_tac (SPEC_ALL calldata_owned_header_initial_repeat) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  `type_memory_size tv = 0` by
    (Cases_on `type_memory_size tv` >> simp[] >>
     `maxn <= maxn * SUC n` by simp[MULT_CLAUSES] >>
     qpat_x_assum `d+(32+maxn*_) < dimword (:256)` mp_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  `abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w)
     (maxn MOD dimword (:256)) abi_sz st = ((),guard_st)` by
    (qpat_assum `abi_decode_dynarray_prefix _ _ _ maxn _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_dynarray_prefix_def, comp_bind_def,
        calldata_count_guard_mod_limit]) >>
  `abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w)
     (maxn MOD dimword (:256)) abi_sz st = ((ip,cnt),loop_st)` by
    (qpat_assum `abi_decode_array_loop_init _ _ _ _ maxn _ _ = _` mp_tac >>
     simp_tac bool_ss [abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
        comp_bind_def, comp_ignore_bind_def, calldata_count_guard_mod_limit]) >>
  `maxn MOD dimword (:256) < dimword (:256)` by simp[] >>
  mp_tac (Q.INST [`maxn` |-> `maxn MOD dimword (:256)`]
    (SPEC_ALL calldata_owned_header_initial_repeat)) >>
  qpat_assum `type_memory_size tv = 0` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, MULT_0, ADD_0]) >>
    pure_rewrite_tac [th, MULT_0, ADD_0]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then DISJ_CASES_TAC >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn` by
    (drule calldata_count_guard_accepted_bounds >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  disj2_tac >> qexists_tac `u` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem calldata_owned_header_step_apply_observed[local]:
  Own = (\lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  Rel = (\s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  X = (\s. ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn s) /\
  (bufsize:num) = 32+maxn*type_memory_size tv /\
  n = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  H = (\j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= n /\ n <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w n /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  fn_has_code st0 middle fn /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  p < dimword (:256) /\ d+bufsize < dimword (:256) /\
  (d+bufsize <= p \/ p+32 <= d) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+bufsize <= base_addr+cap /\
  (!a w e.
    ~a.vs_halted /\ a.vs_current_bb = middle.cs_current_bb /\
    a.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) a = SOME w /\
    eval_operand (SND (SND ops)) a = SOME (n2w e) /\
    alloca_inv a /\ alloca_frontier_inv ctx fn site a /\
    Own middle.cs_next_id st1.cs_next_id a /\
    FLOOKUP a.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    X a \/ ?b x scratch.
      ~b.vs_halted /\ b.vs_current_bb = st1.cs_current_bb /\
      b.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e b.vs_memory /\ Rel a b /\
      b.vs_call_ctx = a.vs_call_ctx /\ b.vs_data_section = a.vs_data_section /\
      alloca_inv b /\ alloca_frontier_inv ctx fn site b /\
      Own middle.cs_next_id st1.cs_next_id b /\
      a.vs_alloca_next <= b.vs_alloca_next /\
      (!id q k. FLOOKUP a.vs_allocas id = SOME (q,k) ==>
        FLOOKUP b.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP b.vs_allocas id = FLOOKUP a.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op b = eval_operand op a) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) a b /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP b.vs_allocas id = SOME (q,k))) /\
  j < n /\ H j u ==>
  X u \/ ?v x.
    H (SUC j) v /\ P x /\ val_wf tv x /\
    val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
    mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
      mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel u v
Proof
  ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  asm_rewrite_tac[] >> BETA_TAC >>
  MATCH_ACCEPT_TAC (BETA_RULE (SIMP_RULE pure_ss [LET_THM]
    calldata_owned_header_step_observed))
QED

Theorem calldata_owned_header_terminal_apply_observed[local]:
  Own = (\lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  Rel = (\s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)) /\
  X = (\s. ?fuel z. run_from fuel ctx fn s = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn s) /\
  (bufsize:num) = 32+maxn*type_memory_size tv /\
  n = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
  H = (\j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= n /\ n <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w n /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone) /\
  p < dimword (:256) /\
  H n u /\ LENGTH vs = n /\ EVERY P vs /\ EVERY (val_wf tv) vs /\
  (!k. k < n ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  X u \/ ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = n /\ n <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    Rel u t /\ t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  ntac 6 (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  asm_rewrite_tac[] >> BETA_TAC >>
  MATCH_ACCEPT_TAC (BETA_RULE (SIMP_RULE pure_ss [LET_THM]
    calldata_owned_header_terminal_observed))
QED

Theorem calldata_owned_after_initial_repeat_observed[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  fn_has_code st0 middle fn /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn u) \/ ?v x scratch.
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ((?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn initial) \/ ?u.
    (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      0 <= w2n (abi_decode_load CALLDATALOAD srcword initial) /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src u = SOME srcword /\
      eval_operand dst u = SOME (n2w d) /\
      eval_operand ip u = SOME (n2w p) /\ mload p u = n2w 0 /\
      mem_word_at d u.vs_memory = n2w (w2n (abi_decode_load CALLDATALOAD srcword initial)) /\
      u.vs_call_ctx = initial.vs_call_ctx /\
      u.vs_data_section = initial.vs_data_section /\
      FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= u.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op u = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial u /\
        !q k. MEM (q,k) scratch ==> ?id.
          st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn initial))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?t vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  qabbrev_tac `H = \j u.
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    j <= nelts /\ nelts <= maxn /\
    eval_operand src u = SOME srcword /\
    eval_operand dst u = SOME (n2w d) /\
    eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
    mem_word_at d u.vs_memory = n2w nelts /\
    u.vs_call_ctx = initial.vs_call_ctx /\
    u.vs_data_section = initial.vs_data_section /\
    FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    Own st.cs_next_id end_st.cs_next_id u /\
    initial.vs_alloca_next <= u.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op u = eval_operand op initial) /\
    ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
      !q k. MEM (q,k) scratch ==> ?id.
        st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k)` >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `X initial \/ _` strip_assume_tac
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  rename1 `H 0 start` >>
  `p < dimword (:256)` by
    (qpat_assum `H 0 start` mp_tac >> simp_tac bool_ss [Abbr `H`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all alloca_frontier_inv_bound >> disch_tac >>
     qpat_x_assum `alloca_inv start` mp_tac >>
     qpat_x_assum `FLOOKUP start.vs_allocas _ = SOME (p,32)` mp_tac >>
     qpat_x_assum `start.vs_alloca_next < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> rpt strip_tac >>
     `p+32 <= start.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `!j u. j < nelts /\ H j u ==>
    X u \/ ?v x. H (SUC j) v /\ P x /\ val_wf tv x /\
      val_in_memory tv x (d+32+j*type_memory_size tv) v.vs_memory /\
      mem_bytes_at d (32+j*type_memory_size tv) v.vs_memory =
        mem_bytes_at d (32+j*type_memory_size tv) u.vs_memory /\ Rel u v` by
    (rpt gen_tac >> strip_tac >>
     irule calldata_owned_header_step_apply_observed >>
     conj_tac >- simp[] >>
     qpat_assum `Abbrev (H = _)`
       (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`
       (irule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`)) >>
     qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
     qpat_assum `lookup_block st1.cs_current_bb _ = _`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ _|>`)) >>
     qpat_assum `lookup_block body_lbl _ = _`
       (irule_at (Pat `lookup_block body_lbl _ = _`)) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
         Abbr `bufsize`, Abbr `nelts`]]) >>
  qabbrev_tac `Q = \t. ?vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = nelts /\ nelts <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))` >>
  `!u vs. H nelts u /\ LENGTH vs = nelts /\ EVERY P vs /\
    EVERY (val_wf tv) vs /\
    (!k. k < nelts ==> val_in_memory tv (EL k vs)
      (d+32+k*type_memory_size tv) u.vs_memory) ==>
    X u \/ ?t. Q t /\ Rel u t` by suspend "terminal" >>
  `X start \/ ?t. Q t /\ Rel start t` by
    (irule calldata_owned_iteration_apply >>
     reverse conj_tac
     >- (qexistsl_tac [`\r. ?z. r = Abort Revert_abort z`,`ctx`,`fn`] >>
         simp_tac bool_ss [Abbr `Rel`, Abbr `X`, FUN_EQ_THM] >>
         POP_ASSUM_LIST (K all_tac) >>
         metis_tac[fragExecTheory.exit_result_def]) >>
     qexistsl_tac [`H`,`P`,`nelts`,`d`,`tv`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (disj1_tac >>
      qpat_assum `Rel initial start` mp_tac >>
      qpat_assum `X start` mp_tac >>
      simp_tac bool_ss [Abbr `Rel`, Abbr `X`] >>
      POP_ASSUM_LIST (K all_tac) >> strip_tac >>
      disch_then (qspec_then `fuel` mp_tac) >>
      simp[] >> metis_tac[]) >>
  `Rel initial t` by
    (qpat_assum `Rel initial start` mp_tac >>
     qpat_assum `Rel start t` mp_tac >>
     simp_tac bool_ss [Abbr `Rel`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[calldataSafeIterationTheory.calldata_safe_transfer_trans]) >>
  disj2_tac >>
  qpat_x_assum `Q t` mp_tac >> simp_tac bool_ss [Abbr `Q`] >>
  disch_then (qx_choose_then `vs` (qx_choose_then `scratch` strip_assume_tac)) >>
  qexistsl_tac [`t`,`vs`,`scratch`] >> asm_rewrite_tac[]
QED

Resume calldata_owned_after_initial_repeat_observed[terminal]:
  rpt gen_tac >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone` by
    (qpat_assum `!op. (op = src \/ op = dst \/ _) ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `X u \/ ?t scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = nelts /\ nelts <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    Rel u t /\ t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    Own st.cs_next_id end_st.cs_next_id t /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))` by
    (irule calldata_owned_header_terminal_apply_observed >>
     qpat_assum `Abbrev (H = _)`
       (irule_at (Pat `H = _`) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
       (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
     qpat_assum `lookup_block exit_lbl _ = _`
       (irule_at (Pat `lookup_block exit_lbl _ = _`)) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!op. op = src \/ _`
          (qspec_then `op` mp_tac) >> simp[]),
       simp_tac bool_ss [Abbr `Own`, Abbr `Rel`, Abbr `X`,
         Abbr `bufsize`, Abbr `nelts`]])
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexists_tac `t` >>
  conj_tac >- (simp_tac bool_ss [Abbr `Q`] >>
    qexistsl_tac [`vs`,`scratch`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise calldata_owned_after_initial_repeat_observed

Theorem calldata_nonbulk_owned_repeat_observed:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di
    abi_sz (type_memory_size tv) st0 = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD
    (Lit 0w) di middle = ((),st1) /\
  abi_decode_loop_suffix ip (FST ops) hdr exit_lbl st1 = ((),end_st) /\
  st.cs_next_id <= header_st.cs_next_id /\
  header_st.cs_next_id < middle.cs_next_id /\
  middle.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  fn_has_code st0 middle fn /\ fn_has_code middle st1 fn /\
  fn_has_code st1 end_st fn /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ st0.cs_current_bb = body_lbl /\
  st0.cs_current_insts = [] /\
  lookup_block st1.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := st1.cs_current_bb; bb_instructions :=
      st1.cs_current_insts ++ abi_decode_backedge_insts st1.cs_next_id biv nv ip hdr|> /\
  FST ops = Var biv /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\ ip <> Var nv /\
  (!op. op = src \/ op = dst \/ op = ip \/
      abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone /\
    op <> Var nv /\ abi_decoder_operand_live st0.cs_next_var op) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  (!op. abi_decoder_operand_live st0.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
      p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  (!u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST (SND ops)) u = SOME w /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn u) \/ ?v x scratch.
      ~v.vs_halted /\ v.vs_current_bb = st1.cs_current_bb /\
      v.vs_inst_idx = LENGTH st1.cs_current_insts /\
      P x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ st1.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==>
        ?id. middle.cs_next_id <= id /\ id < st1.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,k))) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/ ?t vs scratch.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    LENGTH vs = w2n (abi_decode_load CALLDATALOAD srcword initial) /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\ EVERY P vs /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\
    t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==>
      ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  qabbrev_tac `Own = \lo hi s. !id q k.
    lo <= id /\ id < hi /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `Rel = \s t. !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)` >>
  qpat_assum `Abbrev (Rel = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `X = \s. ?fuel z.
    run_from fuel ctx fn s = Abort Revert_abort z /\ mem_safe_run fuel ctx fn s` >>
  qpat_assum `Abbrev (X = _)`
    (fn th => pure_rewrite_tac [GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  qabbrev_tac `bufsize = 32+maxn*type_memory_size tv` >>
  qabbrev_tac `nelts = w2n (abi_decode_load CALLDATALOAD srcword initial)` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `header_st.cs_next_id < end_st.cs_next_id` by decide_tac >>
  simp_tac pure_ss [NoAsms, Abbr `Own`, Abbr `Rel`, Abbr `X`,
    Abbr `bufsize`, Abbr `nelts`] >>
  BETA_TAC >>
  irule calldata_owned_after_initial_repeat_observed >>
  qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`
    (irule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`)) >>
  qpat_assum `lookup_block hdr _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`
    (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
  qpat_assum `lookup_block st1.cs_current_bb _ = _`
    (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ _|>`)) >>
  qpat_assum `lookup_block exit_lbl _ = _`
    (irule_at (Pat `lookup_block exit_lbl _ = _`)) >>
  qexistsl_tac [`p`,`oid`,`header_st`,`cap`,`body_bb`,`base_addr`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp_tac bool_ss []]
  >- (first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [] o BETA_RULE)) >>
  irule (SIMP_RULE bool_ss [] calldata_owned_header_initial_repeat_observed) >>
  qpat_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`
    (irule_at (Pat `abi_decode_array_loop_init _ _ _ _ _ _ _ = _`)) >>
  qpat_assum `abi_decode_loop_prefix _ _ _ _ = _`
    (irule_at (Pat `abi_decode_loop_prefix _ _ _ _ = _`)) >>
  qpat_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`
    (irule_at (Pat `abi_decode_dynarray_prefix _ _ _ _ _ _ = _`)) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp_tac bool_ss []] >>
  first_assum (ACCEPT_TAC o BETA_RULE)
QED
