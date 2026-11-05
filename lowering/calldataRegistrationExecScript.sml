(* Liveness-only execution boundaries for positional calldata registration. *)
Theory calldataRegistrationExec
Ancestors
  calldataRegistration abiDecoderReentryAddress fragExecMem actualAllocExec
  venomExecProofs emitHelperProps exprLoweringProps finite_map words
  abiDecoderReentry venomState venomExecSemantics abiDecoderContract
  compileEnv emitHelper venomInst arithmetic moduleLowering abiEncoder
  abiCallerAllocation abiDecoderFrame valueEncodingProps valueEncoding venomMemDefs
  fragExec abiDecoderAppend calldataDynOwned allocLimitsProps

Theorem registration_emit_step_mem:
  emit_op opc args st = (out,last) /\
  (opc = ADD \/ opc = CALLDATALOAD) /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) initial = OK t ==>
  frag_exec_mem ctx st last (\s. s = initial)
    (\s. s = t with vs_inst_idx := LENGTH last.cs_current_insts) R
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  gvs[inst_extends_def, same_blocks_def] >>
  irule frag_exec_mem_step >> simp[] >>
  simp[mk_inst_def, is_terminator_def] >>
  gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]
QED

(* A pure emitted result, including its safe continuation boundary. *)
Theorem registration_pure_emit_live_mem:
  emit_op opc args st = (out,last) /\
  (opc = ADD \/ opc = CALLDATALOAD) /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME w /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> (
  `frag_exec_mem ctx st last (\u. u = s)
    (\u. u = (update_var (STRING #"%" (toString st.cs_next_var)) w s)
      with vs_inst_idx := LENGTH last.cs_current_insts) (\r. F)` by
    (irule registration_emit_step_mem >> goal_assum $ drule_at Any >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString st.cs_next_var)) w s)
    with vs_inst_idx := LENGTH last.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       ASCIInumbersTheory.toString_inj]) >>
  gen_tac >> strip_tac >>
  drule calldata_update_protected >>
  disch_then (qspecl_then [`w`,`s`] mp_tac) >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, update_var_def])
QED

Theorem registration_add_live_mem:
  emit_op ADD [lhs;rhs] st = (out,last) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME (a+b) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> irule registration_pure_emit_live_mem >>
  goal_assum $ drule_at Any >> simp[] >> irule step_ADD >> simp[]
QED

Theorem registration_read_live_mem:
  emit_op CALLDATALOAD [src] st = (out,last) /\
  eval_operand src s = SOME p ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> irule registration_pure_emit_live_mem >>
  goal_assum $ drule_at Any >> simp[] >> irule abi_decode_read_step >>
  simp[abi_decode_source_opcode_def]
QED

Theorem registration_address_prelude_live_mem:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) ==>
  ?t. frag_exec_mem ctx st first (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `eval_operand (Lit (n2w 4)) s = SOME (n2w 4) /\
   eval_operand (Lit (n2w (off-4))) s = SOME (n2w (off-4))` by
    simp[eval_operand_def] >>
  drule_all registration_add_live_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  reverse (Cases_on `dyn`) >- (gvs[] >> goal_assum $ drule_at Any >> simp[]) >>
  gvs[] >> drule_all registration_read_live_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) t =
   abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  `eval_operand (Lit (n2w 4)) t' = SOME (n2w 4)` by simp[eval_operand_def] >>
  drule_all registration_add_live_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `cs_extends st after_head /\ cs_extends after_head after_load /\
   cs_extends after_load first` by
    (imp_res_tac emit_op_extends >> rpt conj_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `frag_exec_mem ctx st after_load (\u. u = s) (\u. u = t') (\r. F)` by
    (irule frag_exec_mem_seq >> goal_assum $ drule_at Any >> simp[] >>
     goal_assum $ drule_at Any >> simp[]) >>
  `frag_exec_mem ctx st first (\u. u = s) (\u. u = t'') (\r. F)` by
    (irule frag_exec_mem_seq >> qexistsl_tac [`\u. u = t'`, `after_load`] >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  qexists_tac `t''` >> simp[] >>
  gen_tac >> strip_tac >>
  `st.cs_next_var <= after_head.cs_next_var /\
   after_head.cs_next_var <= after_load.cs_next_var` by
    metis_tac[emitted_insts_emit_op, LESS_EQ_ADD] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

(* Primitive registration is the same word decoder after its literal head ADD.
   Thus its clamps use the existing arbitrary-input decoder theorem too. *)
Theorem registration_primitive_decoder_prelude:
  compile_decode_args ce [(name,T,dyn,sz,DecPrimWord c)] off
    CALLDATALOAD (Lit 0w) 4 st = ((),last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  ?src first.
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (src,first) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DecPrimWord c) first = ((),last)
Proof
  strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    abiDecoderRangeTheory.compile_abi_dec_addr_zero,
    compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

Theorem registration_decoder_prelude:
  compile_decode_args ce [(name,prim,dyn,sz,info)] off
    CALLDATALOAD (Lit 0w) 4 st = ((),last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst /\
  (prim ==> ?c. info = DecPrimWord c) ==>
  ?head after_head src first.
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
    (if dyn /\ ~prim then
       ?offset after_load.
         emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
         emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
     else src = head /\ first = after_head) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info first = ((),last)
Proof
  Cases_on `prim` >> simp[] >> strip_tac
  >- (gvs[] >> drule_all registration_primitive_decoder_prelude >>
      strip_tac >> rpt (goal_assum $ drule_at Any) >> simp[]) >>
  drule_all decode_singleton_aggregate_prelude >> simp[]
QED

Theorem registration_previous_owned_value:
  alloca_inv after /\
  FLOOKUP after.vs_allocas old_id = SOME (old_base,old_cap) /\
  FLOOKUP after.vs_allocas output_id = SOME (output_base,output_cap) /\
  old_id <> output_id /\ (old_id < lo \/ hi <= old_id) /\
  old_base <= p /\ p + type_memory_size tv <= old_base + old_cap /\
  output_base <= d /\ d+n <= output_base+output_cap /\
  (!q k. MEM (q,k) scratch ==> ?id. lo <= id /\ id < hi /\
    FLOOKUP after.vs_allocas id = SOME (q,k)) /\
  abi_decode_footprint_frame ((d,n)::scratch) before after /\
  val_in_memory tv x p before.vs_memory /\ val_wf tv x ==>
  val_in_memory tv x p after.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint p (type_memory_size tv) ((d,n)::scratch)` by
    (simp[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
     conj_tac
     >- (drule_all abi_caller_allocation_separate >> strip_tac >> decide_tac) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!q k. MEM _ scratch ==> _` drule >> strip_tac >>
     `old_id <> id` by decide_tac >>
     drule_all abi_caller_allocation_separate >> strip_tac >> decide_tac) >>
  drule_all abi_decode_footprint_frame_slice >> strip_tac >>
  irule val_in_memory_mem_agree >>
  goal_assum $ drule_at Any >> simp[] >>
  qexists_tac `type_memory_size tv` >> simp[] >>
  qexists_tac `before.vs_memory` >> simp[]
QED

(* The address prelude is pure, but its consumer also needs alignment and
   safe continuation lifting, not merely a fragment judgment. *)
Theorem registration_address_owned_run:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  fn_has_code st first fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all registration_address_prelude_live_mem >>
  disch_then (qspecl_then [`s`,`ctx`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >> disch_then (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    allocaFrontierBoundTheory.alloca_frontier_inv_def,
    allocaBudgetPropsTheory.remaining_alloca_budget_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem registration_address_prelude_bounds:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) ==>
  cs_extends st first /\ st.cs_next_id < first.cs_next_id /\
  st.cs_next_var <= first.cs_next_var
Proof
  strip_tac >> Cases_on `dyn` >> gvs[] >>
  imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
  `cs_extends st after_head` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  FIRST [
    (gvs[] >> decide_tac),
    (`cs_extends after_head after_load /\ cs_extends after_load first` by
      (conj_tac >> irule cs_extends_same_block >>
       gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
     conj_tac >- metis_tac[cs_extends_trans] >> decide_tac)]
QED

(* Allocation and literal address calculation, stopping exactly at the
   universal decoder boundary. No source values are assumed. *)
Theorem registration_singleton_owned_prefix:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st =
    (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n /\
  (prim ==> ?c. info = DecPrimWord c) /\
  fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?dst src first ready p.
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst n) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) info first =
      ((),final) /\ fn_has_code first final fn /\
    st.cs_next_id < first.cs_next_id /\
    st.cs_next_var <= first.cs_next_var /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts /\
    (?w. eval_operand src ready = SOME w) /\
    eval_operand dst ready = SOME (n2w p) /\
    abi_decoder_operand_live first.cs_next_var src /\
    abi_decoder_operand_live first.cs_next_var dst /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv ctx fn site ready /\
    initial.vs_alloca_next <= ready.vs_alloca_next /\
    ready.vs_memory = initial.vs_memory /\
    ready.vs_call_ctx = initial.vs_call_ctx /\
    ready.vs_data_section = initial.vs_data_section /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP ready.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn ready = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn ready ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all register_singleton_allocated_boundary >> strip_tac >>
  `FLOOKUP cef.ce_vars name = SOME (PtrVar buf.buf_operand n)` by
    simp[FLOOKUP_UPDATE] >>
  `var_location_decode_operand (PtrVar buf.buf_operand n) =
    SOME buf.buf_operand` by simp[var_location_decode_operand_def] >>
  drule_all registration_decoder_prelude >> strip_tac >>
  `cs_extends st allocated /\ cs_extends allocated final` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends,
      actualRegistrationCodeTheory.decode_args_suffix_extends] >>
  `fn_has_code st allocated fn /\ fn_has_code allocated final fn` by
    metis_tac[fn_has_code_split] >>
  `cs_extends allocated first /\ allocated.cs_next_id < first.cs_next_id /\
    allocated.cs_next_var <= first.cs_next_var` by
    (drule_all registration_address_prelude_bounds >> simp[]) >>
  `cs_extends first final` by
    metis_tac[abiDecoderAppendTheory.cs_appends_abi_decode_mutual,
      cs_appends_def] >>
  `fn_has_code allocated first fn /\ fn_has_code first final fn` by
    metis_tac[fn_has_code_split] >>
  drule_all actual_alloc_buffer_owned_run >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!entry. FLOOKUP initial.vs_allocas _ = SOME entry ==> _` kall_tac >>
  qpat_x_assum `alloca_inv initial` kall_tac >>
  qpat_x_assum `alloca_frontier_inv _ _ _ initial` kall_tac >>
  drule_all registration_address_owned_run >> strip_tac >>
  qexistsl_tac [`buf.buf_operand`,`src`,`first`,`t`,`p`] >> simp[] >>
  conj_tac >- suspend "pointer_live" >>
  conj_tac >- suspend "old_live" >>
  suspend "continuation"
QED

Resume registration_singleton_owned_prefix[pointer_live]:
  qpat_x_assum `abi_decoder_operand_live allocated.cs_next_var _` mp_tac >>
  qpat_x_assum `allocated.cs_next_var <= first.cs_next_var` mp_tac >>
  qpat_x_assum `buf.buf_operand = _` SUBST_ALL_TAC >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]
QED

Resume registration_singleton_owned_prefix[old_live]:
  qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` mp_tac >>
  qpat_x_assum `!op. abi_decoder_operand_live allocated.cs_next_var op ==> _` mp_tac >>
  qpat_x_assum `allocated.cs_next_var = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[abi_decoder_operand_live_mono, LESS_EQ_ADD]
QED

Resume registration_singleton_owned_prefix[continuation]:
  qpat_x_assum `!fuel r. run_from fuel ctx fn t = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn v = r /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Finalise registration_singleton_owned_prefix

Theorem registration_singleton_owned_run:
  abi_decoder_coherent ce env sf ty tv /\
  compile_register_positional_args ce
    [(name,prim,dyn,sz,type_to_abi_dec_info sf ce ty)] off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  (prim ==> ?c. type_to_abi_dec_info sf ce ty = DecPrimWord c) /\
  fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  type_memory_size tv < dimword (:256) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,type_memory_size tv) /\
      p+type_memory_size tv < dimword (:256)) /\
  (!id q k. st.cs_next_id < id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x dst p lo sc.
    ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    eval_operand dst v = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var dst /\
    FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv) /\
    p+type_memory_size tv < dimword (:256) /\
    st.cs_next_id < lo /\ lo <= final.cs_next_id /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((p,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. lo <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all registration_singleton_owned_prefix >> strip_tac >>
  `first.cs_next_id <= final.cs_next_id /\
   first.cs_next_var <= final.cs_next_var` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[cj 1 ci_mono_compile_abi_decode, ci_mono_def, pairTheory.SND]) >>
  `!id q k. first.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP ready.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= ready.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    suspend "scratch_input" >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
    calldataRecursiveExecutionTheory.calldata_coherent_owned_run >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  impl_tac >- (asm_rewrite_tac[] >> decide_tac) >>
  strip_tac >- suspend "revert" >>
  suspend "success"
QED

Resume registration_singleton_owned_run[revert]:
  disj1_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn ready = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `run_from _ _ _ ready = Abort _ _` mp_tac >>
  qpat_x_assum `mem_safe_run _ _ _ ready` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  first_x_assum (qspec_then `fuel` mp_tac) >>
  asm_rewrite_tac[] >> simp[] >> metis_tac[]
QED

Resume registration_singleton_owned_run[success]:
  disj2_tac >> qexistsl_tac [`v`,`x`,`dst`,`p`,`first.cs_next_id`,`sc`] >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!entry. FLOOKUP initial.vs_allocas _ = SOME entry ==> _` kall_tac >>
  qpat_x_assum `!id q k. st.cs_next_id < id /\ _ ==> _` kall_tac >>
  qpat_x_assum `!id q k. first.cs_next_id <= id /\ _ /\ FLOOKUP ready.vs_allocas _ = _ ==> _` kall_tac >>
  qpat_x_assum `!id q k. first.cs_next_id <= id /\ _ /\ FLOOKUP v.vs_allocas _ = _ ==> _` kall_tac >>
  `eval_operand dst v = SOME (n2w p)` by metis_tac[] >>
  `abi_decoder_operand_live final.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,type_memory_size tv)` by
    metis_tac[] >>
  asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac >- suspend "old_slots" >>
  conj_tac >- suspend "outside" >>
  conj_tac >- suspend "old_live" >>
  conj_tac >- suspend "footprint" >>
  suspend "continuation"
QED

Resume registration_singleton_owned_run[scratch_input]:
  rpt gen_tac >> strip_tac >>
  `id <> st.cs_next_id /\ st.cs_next_id < id` by decide_tac >>
  `FLOOKUP initial.vs_allocas id = SOME (q,k)` by metis_tac[] >>
  qpat_x_assum `!id q k. st.cs_next_id < id /\ _ ==> _` drule >>
  simp[]
QED

Resume registration_singleton_owned_run[old_slots]:
  qpat_x_assum `!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==> _` mp_tac >>
  qpat_x_assum `!id q k. FLOOKUP ready.vs_allocas id = SOME (q,k) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume registration_singleton_owned_run[outside]:
  qpat_x_assum `!id. id <> st.cs_next_id ==> _` mp_tac >>
  qpat_x_assum `!id. id < first.cs_next_id \/ _ ==> _` mp_tac >>
  qpat_x_assum `st.cs_next_id < first.cs_next_id` mp_tac >>
  qpat_x_assum `first.cs_next_id <= final.cs_next_id` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  `id <> st.cs_next_id /\ (id < first.cs_next_id \/ final.cs_next_id <= id)` by
    decide_tac >> metis_tac[]
QED

Resume registration_singleton_owned_run[old_live]:
  qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _` mp_tac >>
  qpat_x_assum `!op. abi_decoder_operand_live first.cs_next_var op ==> _` mp_tac >>
  qpat_x_assum `st.cs_next_var <= first.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[abi_decoder_operand_live_mono]
QED

Resume registration_singleton_owned_run[footprint]:
  qpat_x_assum `abi_decode_footprint_frame _ ready v` mp_tac >>
  qpat_x_assum `ready.vs_memory = initial.vs_memory` mp_tac >>
  qpat_x_assum `ready.vs_call_ctx = initial.vs_call_ctx` mp_tac >>
  qpat_x_assum `ready.vs_data_section = initial.vs_data_section` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[abi_decode_footprint_frame_def]
QED

Resume registration_singleton_owned_run[continuation]:
  qpat_x_assum `!fuel r. run_from fuel ctx fn v = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx fn ready = r /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Finalise registration_singleton_owned_run

(* Sequential registration writes only the union of the owned footprints. *)
Theorem registration_footprint_append:
  abi_decode_footprint_frame left s t /\
  abi_decode_footprint_frame right t u ==>
  abi_decode_footprint_frame (left ++ right) s u
Proof
  strip_tac >> irule abi_decode_footprint_frame_trans >>
  qexists_tac `t` >> conj_tac >>
  irule abi_decode_footprint_frame_weaken >>
  goal_assum $ drule_at Any >> simp[] >> rpt strip_tac >>
  qexistsl_tac [`d`,`sz`] >> simp[]
QED

Theorem registration_owned_footprint_value:
  alloca_inv after /\
  FLOOKUP after.vs_allocas old_id = SOME (old_base,cap) /\
  (old_id < lo \/ hi <= old_id) /\
  old_base <= p /\ p + type_memory_size tv <= old_base + cap /\
  (!q k. MEM (q,k) fp ==> ?id. lo <= id /\ id < hi /\
    FLOOKUP after.vs_allocas id = SOME (q,k)) /\
  abi_decode_footprint_frame fp before after /\
  val_in_memory tv x p before.vs_memory /\ val_wf tv x ==>
  val_in_memory tv x p after.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint p (type_memory_size tv) fp` by
    (simp[abi_footprint_disjoint_def] >> rpt strip_tac >>
     qpat_x_assum `!q k. MEM _ fp ==> _` drule >> strip_tac >>
     `old_id <> id` by decide_tac >>
     drule_all abi_caller_allocation_separate >> strip_tac >> decide_tac) >>
  drule_all abi_decode_footprint_frame_slice >> strip_tac >>
  irule val_in_memory_mem_agree >>
  goal_assum $ drule_at Any >> simp[] >>
  qexists_tac `type_memory_size tv` >> simp[] >>
  qexists_tac `before.vs_memory` >> simp[]
QED

Theorem registration_unmentioned_binding:
  !args ce off st cef final name.
    compile_register_positional_args ce args off st = (cef,final) /\
    ~MEM name (MAP (\(n,prim,dyn,sz,info). n) args) ==>
    FLOOKUP cef.ce_vars name = FLOOKUP ce.ce_vars name
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >> simp[]
  >- metis_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  first_x_assum drule >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem registration_dec_info_env_cong:
  !sf ce ty. !ce'.
    ce'.ce_struct_fields = ce.ce_struct_fields /\
    ce'.ce_flag_n_members = ce.ce_flag_n_members ==>
    type_to_abi_dec_info sf ce' ty = type_to_abi_dec_info sf ce ty
Proof
  recInduct exprLoweringTheory.type_to_abi_dec_info_ind >> rpt strip_tac >>
  `type_memory_bytes ce' = type_memory_bytes cenv` by
    (simp[FUN_EQ_THM] >> metis_tac[type_memory_bytes_struct_fields]) >>
  simp[Once exprLoweringTheory.type_to_abi_dec_info_def] >>
  simp[Once exprLoweringTheory.type_to_abi_dec_info_def] >>
  gvs[]
  >- (irule listTheory.GENLIST_CONG >> rpt strip_tac >>
      simp[] >> metis_tac[])
  >- (irule listTheory.MAP_CONG >> simp[])
  >> Cases_on `FLOOKUP sfields (nsid_to_string nsid)` >> simp[] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  PairCases_on `x'` >> simp[] >> metis_tac[]
QED

Theorem registration_env_fields:
  !args ce off st cef final.
    compile_register_positional_args ce args off st = (cef,final) ==>
    cef.ce_struct_fields = ce.ce_struct_fields /\
    cef.ce_flag_n_members = ce.ce_flag_n_members
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >> simp[]
  >- metis_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* Compile-only counter interfaces; execution uses these without unfolding decoders. *)
Theorem registration_decode_ci_mono:
  !args ce off opc hi adj s.
    ci_mono s (SND (compile_decode_args ce args off opc hi adj s))
Proof
  Induct >> simp[compile_decode_args_def, ci_mono_comp_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[Once compile_decode_args_def, LET_THM] >>
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind,
              IF_CASES_TAC] >> rpt conj_tac >> rpt gen_tac >>
    PURE_REWRITE_TAC[LET_THM] >> BETA_TAC) >>
  simp[ci_mono_compile_abi_clamp_basetype, ci_mono_emit_op, ci_mono_emit_void,
    ci_mono_comp_return, ci_mono_compile_abi_decode] >>
  Cases_on `var_location_decode_operand x` >> simp[] >>
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
    rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_comp_return, ci_mono_emit_void, ci_mono_emit_op,
    ci_mono_compile_abi_decode]
QED

Theorem registration_compile_ci_mono:
  !args ce off s.
    ci_mono s (SND (compile_register_positional_args ce args off s))
Proof
  Induct >> simp[compile_register_positional_args_def, ci_mono_comp_return] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `FLOOKUP ce.ce_vars h0` >>
  simp[Once compile_register_positional_args_def] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >>
    rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[ci_mono_compile_alloc_buffer, ci_mono_comp_return,
    registration_decode_ci_mono]
QED

Theorem registration_compile_counters:
  compile_register_positional_args ce args off st = (cef,final) ==>
  st.cs_next_id <= final.cs_next_id /\ st.cs_next_var <= final.cs_next_var
Proof
  strip_tac >>
  qspecl_then [`args`, `ce`, `off`, `st`] mp_tac registration_compile_ci_mono >>
  simp[ci_mono_def]
QED

Theorem registration_singleton_id_strict[local]:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n ==>
  st.cs_next_id < final.cs_next_id
Proof
  strip_tac >> drule_all register_singleton_allocated_boundary >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  qspecl_then [`[(name,prim,dyn,sz,info)]`, `cef`, `off`,
    `CALLDATALOAD`, `Lit 0w`, `4`, `allocated`] mp_tac registration_decode_ci_mono >>
  simp[ci_mono_def]
QED

Theorem registration_list_owned_provenance:
  !specs ce env sf off st cef final ctx fn site initial.
    compile_register_positional_args ce
      (MAP (\(name,prim,dyn,sz,ty,tv).
        (name,prim,dyn,sz,type_to_abi_dec_info sf ce ty)) specs) off st = (cef,final) /\
    ALL_DISTINCT (MAP (\(name,prim,dyn,sz,ty,tv). name) specs) /\
    EVERY (\(name,prim,dyn,sz,ty,tv).
      abi_decoder_coherent ce env sf ty tv /\
      (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      (prim ==> ?c. type_to_abi_dec_info sf ce ty = DecPrimWord c) /\
      type_memory_size tv < dimword (:256)) specs /\
    fn_has_code st final fn /\
    alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    unit_alloca_budget ctx < dimword (:256) /\
    (!id. st.cs_next_id <= id /\ id < final.cs_next_id ==>
      FLOOKUP initial.vs_allocas id = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    (final.cs_current_insts = [] ==>
      !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
    (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn initial) \/
    ?v outputs fp.
      ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
      v.vs_inst_idx = LENGTH final.cs_current_insts /\
      LIST_REL (\(name,prim,dyn,sz,ty,tv) (x,dst,p,id).
        value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
        FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
        eval_operand dst v = SOME (n2w p) /\
        abi_decoder_operand_live final.cs_next_var dst /\
        st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
        p+type_memory_size tv < dimword (:256) /\
        (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
          ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
          ins.inst_id = id)) specs outputs /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      initial.vs_alloca_next <= v.vs_alloca_next /\
      v.vs_call_ctx = initial.vs_call_ctx /\
      v.vs_data_section = initial.vs_data_section /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op v = eval_operand op initial) /\
      abi_decode_footprint_frame fp initial v /\
      (!q k. MEM (q,k) fp ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn initial = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  qabbrev_tac `Meta = \ce env sf specs.
    EVERY (\(name,prim,dyn:bool,sz:num,ty,tv).
      abi_decoder_coherent ce env sf ty tv /\
      (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      (prim ==> ?c. type_to_abi_dec_info sf ce ty = DecPrimWord c) /\
      type_memory_size tv < dimword (:256)) specs` >>
  qabbrev_tac `Owned = \fn cef final st v.
    LIST_REL (\(name,prim:bool,dyn:bool,sz:num,ty:type,tv) (x,dst,p,id).
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
      FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      eval_operand dst v = SOME (n2w p) /\
      abi_decoder_operand_live final.cs_next_var dst /\
      st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
      p+type_memory_size tv < dimword (:256) /\
      (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
        ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
        ins.inst_id = id))` >>
  qabbrev_tac `Entry = \ctx fn site st final initial.
    fn_has_code st final fn /\
    alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    unit_alloca_budget ctx < dimword (:256) /\
    (!id. st.cs_next_id <= id /\ id < final.cs_next_id ==>
      FLOOKUP initial.vs_allocas id = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    (final.cs_current_insts = [] ==>
      !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)` >>
  qabbrev_tac `Frame = \ctx fn site st final initial v fp.
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame fp initial v /\
    (!q k. MEM (q,k) fp ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))` >>
  map_every (fn q => qpat_assum q (fn th =>
    rewrite_tac[GSYM (BETA_RULE (REWRITE_RULE[markerTheory.Abbrev_def, FUN_EQ_THM] th))]))
    [`Abbrev (Meta = _)`, `Abbrev (Owned = _)`,
     `Abbrev (Entry = _)`, `Abbrev (Frame = _)`] >>
  ho_match_mp_tac listTheory.list_induction >> conj_tac
  >- (simp[compile_register_positional_args_def, comp_return_def] >>
      rpt gen_tac >> strip_tac >> disj2_tac >>
      qexistsl_tac [`initial`,`[]`,`[]`] >>
      gvs[Abbr `Entry`, Abbr `Owned`, Abbr `Frame`,
        abi_decode_footprint_frame_def] >> metis_tac[]) >>
  gen_tac >> disch_tac >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [listTheory.MAP] >>
  once_rewrite_tac[SIMP_RULE (srw_ss()) []
    (Q.SPEC `[(h0,h1,h2,h3,type_to_abi_dec_info sf ce h4)]`
      actualRegistrationCodeTheory.register_positional_args_append)] >>
  strip_tac >>
  qpat_x_assum `Meta ce env sf _` mp_tac >>
  qpat_assum `Abbrev (Meta = _)` (fn th =>
    simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th,
      listTheory.EVERY_DEF]) >>
  strip_tac >>
  qpat_x_assum `Entry ctx fn site st final initial` mp_tac >>
  qpat_assum `Abbrev (Entry = _)` (fn th =>
    simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >> strip_tac >>
  `st.cs_next_id <= stm.cs_next_id /\ st.cs_next_var <= stm.cs_next_var` by
    (irule registration_compile_counters >> goal_assum (drule_at Any)) >>
  `stm.cs_next_id <= final.cs_next_id /\ stm.cs_next_var <= final.cs_next_var` by
    (irule registration_compile_counters >> goal_assum (drule_at Any)) >>
  `cs_extends st stm /\ cs_extends stm final` by
    metis_tac[actualRegistrationCodeTheory.register_positional_args_suffix_extends] >>
  `fn_has_code st stm fn /\ fn_has_code stm final fn` by
    metis_tac[fn_has_code_split] >>
  `stm.cs_current_insts = [] ==>
    !bb. lookup_block stm.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >>
     qpat_assum `compile_register_positional_args _ (MAP _ _) _ _ = _`
       (mp_then Any mp_tac registration_suffix_empty_phi) >>
     simp[] >> disch_then (qspecl_then [`fn`,`bb`] mp_tac) >> simp[]) >>
  `st.cs_next_id < stm.cs_next_id` by
    (drule_all registration_singleton_id_strict >> simp[]) >>
  `!id. st.cs_next_id <= id /\ id < stm.cs_next_id ==>
    FLOOKUP initial.vs_allocas id = NONE` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    registration_singleton_owned_run >>
  disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
    `FLOOKUP initial.vs_allocas id = NONE` by
      (qpat_assum `!id. st.cs_next_id <= id /\ id < final.cs_next_id ==> _`
        (qspec_then `id` mp_tac) >> impl_tac >- decide_tac >> simp[]) >>
    gvs[]) >>
  disch_then DISJ_CASES_TAC
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (qx_choose_then `mid` strip_assume_tac) >>
  `?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
    ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
    ins.inst_id = st.cs_next_id` by
    (drule_all register_singleton_alloca_output >> strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `Frame ctx fn site st stm initial mid ((p,type_memory_size h5)::sc)` by
    (qpat_assum `Abbrev (Frame = _)` (fn th =>
      simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >> first_assum irule >> simp[]) >>
     rpt gen_tac >> strip_tac
     >- (qexists `st.cs_next_id` >> simp[]) >>
     qpat_assum `!q k. MEM (q,k) sc ==> _` drule >> strip_tac >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `cenvm.ce_struct_fields = ce.ce_struct_fields /\
   cenvm.ce_flag_n_members = ce.ce_flag_n_members` by
    (qpat_assum `compile_register_positional_args ce [_] _ _ = _`
      (mp_then Any mp_tac registration_env_fields) >> simp[]) >>
  `!ty. type_to_abi_dec_info sf cenvm ty = type_to_abi_dec_info sf ce ty` by
    (gen_tac >> irule registration_dec_info_env_cong >> simp[]) >>
  `!name. MEM name (MAP (\(n,prim,dyn,sz,ty,tv). n) specs) ==>
    FLOOKUP cenvm.ce_vars name = FLOOKUP ce.ce_vars name` by
    (rpt strip_tac >> irule registration_unmentioned_binding >>
     goal_assum (drule_at Any) >> gvs[] >> metis_tac[]) >>
  `Meta cenvm env sf specs` by
    (qpat_assum `Abbrev (Meta = _)` (fn th =>
      simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     rewrite_tac[listTheory.EVERY_MEM] >>
     qx_gen_tac `spec` >> PairCases_on `spec` >> strip_tac >>
     qpat_assum `EVERY _ specs` (mp_tac o REWRITE_RULE[listTheory.EVERY_MEM]) >>
     disch_then (qspec_then `(spec0,spec1,spec2,spec3,spec4,spec5)` mp_tac) >>
     simp[] >> strip_tac >>
     `MEM spec0 (MAP (\(n,prim,dyn,sz,ty,tv). n) specs)` by
       (simp[listTheory.MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
     simp[] >> irule registration_coherent_env_cong >>
     goal_assum (drule_at Any) >> simp[]) >>
  `Entry ctx fn site stm final mid` by
    (qpat_assum `Abbrev (Entry = _)` (fn th =>
      simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     qpat_x_assum `Abbrev (Entry = _)` kall_tac >>
     asm_simp_tac std_ss [] >> rpt strip_tac >>
     qpat_assum `!id. id < st.cs_next_id \/ stm.cs_next_id <= id ==> _`
       (qspec_then `id` mp_tac) >> asm_simp_tac std_ss [] >>
     qpat_assum `!id. st.cs_next_id <= id /\ id < final.cs_next_id ==> _` irule >>
     decide_tac) >>
  `MAP (\(name,prim,dyn,sz,ty,tv).
      (name,prim,dyn,sz,type_to_abi_dec_info sf cenvm ty)) specs =
   MAP (\(name,prim,dyn,sz,ty,tv).
      (name,prim,dyn,sz,type_to_abi_dec_info sf ce ty)) specs` by
    (irule listTheory.MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  qpat_assum `MAP _ specs = MAP _ specs`
    (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE[GSYM th])) >>
  `ALL_DISTINCT (MAP (\(name,prim,dyn,sz,ty,tv). name) specs)` by gvs[] >>
  qpat_x_assum `!ce env sf off st cef final ctx fn site initial. _`
    (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `Meta _ _ _ _`)) >>
  disch_then (drule_at (Pat `Entry _ _ _ _ _ _`)) >>
  simp[] >> disch_then DISJ_CASES_TAC
  >- (disj1_tac >> pop_assum strip_assume_tac >>
      qpat_assum `!fuel r. run_from fuel ctx fn mid = r /\ _ ==> _` drule >>
      impl_tac >- simp[] >> strip_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  pop_assum (qx_choose_then `v` strip_assume_tac) >>
  qpat_assum `Frame ctx fn site stm final mid v fp` mp_tac >>
  qpat_assum `Abbrev (Frame = _)` (fn th =>
    simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >> strip_tac >>
  `FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,type_memory_size h5)` by
    (qpat_assum `!id q k. FLOOKUP mid.vs_allocas id = SOME (q,k) ==> _` irule >>
     simp[]) >>
  `val_in_memory h5 x p v.vs_memory` by
    (drule_at (Pat `FLOOKUP _ _ = SOME _`) registration_owned_footprint_value >>
     disch_then (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >>
     disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
     disch_then (qspecl_then [`stm.cs_next_id`,`final.cs_next_id`] mp_tac) >>
     simp[]) >>
  `FLOOKUP cef.ce_vars h0 = SOME (PtrVar dst (type_memory_size h5))` by
    (qpat_assum `compile_register_positional_args cenvm _ _ _ = _`
      (mp_then Any mp_tac registration_unmentioned_binding) >>
     disch_then (qspec_then `h0` mp_tac) >>
     simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
     gvs[]) >>
  `eval_operand dst v = SOME (n2w p)` by
    (qpat_assum `!op. abi_decoder_operand_live stm.cs_next_var op ==> _`
      (qspec_then `dst` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live final.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  disj2_tac >> qexistsl_tac [`v`,`(x,dst,p,st.cs_next_id)::outputs`,
    `((p,type_memory_size h5)::sc) ++ fp`] >> simp[] >> conj_tac
  >- (qpat_assum `Abbrev (Owned = _)` (fn th =>
        simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
      simp[] >> conj_tac
      >- (gvs[] >> goal_assum (drule_at Any) >> simp[]) >>
      qpat_assum `Owned fn cef final stm v specs outputs` mp_tac >>
      qpat_x_assum `Abbrev (Owned = _)` (fn th =>
        simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
      strip_tac >> irule listTheory.LIST_REL_mono >>
      goal_assum (drule_at Any) >>
      simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> simp[] >> decide_tac) >>
  qpat_x_assum `Abbrev (Frame = _)` (fn th =>
    simp_tac std_ss [REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
  asm_simp_tac std_ss [] >> rpt conj_tac
  >- suspend "list_outside"
  >- suspend "list_live"
  >- suspend "list_footprint"
  >- suspend "list_fp_owned"
  >> suspend "list_continuation"
QED

Resume registration_list_owned_provenance[list_outside]:
  rpt strip_tac >>
  `id < stm.cs_next_id \/ final.cs_next_id <= id` by decide_tac >>
  `id < st.cs_next_id \/ stm.cs_next_id <= id` by decide_tac >>
  simp[]
QED

Resume registration_list_owned_provenance[list_live]:
  rpt strip_tac >>
  `abi_decoder_operand_live stm.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists `st.cs_next_var` >> simp[]) >>
  simp[]
QED

Resume registration_list_owned_provenance[list_footprint]:
  once_rewrite_tac[GSYM (CONJUNCT2 listTheory.APPEND)] >>
  irule registration_footprint_append >> qexists `mid` >> simp[]
QED

Resume registration_list_owned_provenance[list_fp_owned]:
  rpt gen_tac >> strip_tac
  >- (gvs[] >> qexists `st.cs_next_id` >> simp[] >> decide_tac)
  >- (first_x_assum (drule_at (Pat `MEM _ sc`)) >>
      strip_tac >> qexists `id` >> simp[] >> decide_tac) >>
  first_x_assum (drule_at (Pat `MEM _ fp`)) >>
  strip_tac >> qexists `id` >> simp[] >> decide_tac
QED

Resume registration_list_owned_provenance[list_continuation]:
  qpat_x_assum `!fuel r. run_from fuel ctx fn mid = r /\ _ ==> _` mp_tac >>
  qpat_x_assum `!fuel. (!err. run_from fuel ctx fn v <> Error err) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[] >>
  strip_tac >> qexists `fuel''` >> simp[]
QED

Finalise registration_list_owned_provenance

Theorem registration_positional_owned_provenance:
  compile_register_positional_args ce (build_positional_args ce args) off st = (cef,final) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) (ty',tv).
    ty = ty' /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tys /\
  fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!id. st.cs_next_id <= id /\ id < final.cs_next_id ==>
    FLOOKUP initial.vs_allocas id = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v outputs fp.
    ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\
    LIST_REL (\((name,ty),tv) (x,dst,p,id).
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
      FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      eval_operand dst v = SOME (n2w p) /\
      abi_decoder_operand_live final.cs_next_var dst /\
      st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
      p+type_memory_size tv < dimword (:256) /\
      (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
        ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
        ins.inst_id = id)) (ZIP (args,MAP SND tys)) outputs /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame fp initial v /\
    (!q k. MEM (q,k) fp ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  strip_tac >> drule positional_registration_specs >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  qpat_assum `MAP _ specs = build_positional_args ce args` (fn th =>
    rewrite_tac[GSYM th]) >> strip_tac >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    registration_list_owned_provenance >>
  disch_then (qspecl_then [`env`,`ctx`,`fn`,`site`,`initial`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >- metis_tac[] >>
  disj2_tac >> qexistsl [`v`,`outputs`,`fp`] >> simp[] >>
  qpat_assum `MAP _ specs = ZIP (args,MAP SND tys)` (fn th =>
    rewrite_tac[GSYM th]) >>
  simp[listTheory.LIST_REL_MAP1,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
  rpt strip_tac >> simp[]
QED

Theorem registration_singleton_owned_backing:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st =
    (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n /\
  fn_has_code st final fn /\
  FLOOKUP cef.ce_vars name = SOME (PtrVar dst n) /\
  FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,n) /\
  alloca_inv v ==>
  ?vname. dst = Var vname /\ local_backed fn vname v p n /\
    p+n <= v.vs_alloca_next
Proof
  strip_tac >> drule_all register_singleton_alloca_output >> strip_tac >>
  gvs[] >> conj_tac
  >- (simp[local_backed_def] >> disj1_tac >>
      goal_assum $ drule_at Any >> simp[]) >>
  gvs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> simp[]
QED

(* Compatibility projection: the public contract deliberately forgets provenance. *)
Theorem registration_list_owned_run:
  !specs ce env sf off st cef final ctx fn site initial.
    compile_register_positional_args ce
      (MAP (\(name,prim,dyn,sz,ty,tv).
        (name,prim,dyn,sz,type_to_abi_dec_info sf ce ty)) specs) off st = (cef,final) /\
    ALL_DISTINCT (MAP (\(name,prim,dyn,sz,ty,tv). name) specs) /\
    EVERY (\(name,prim,dyn,sz,ty,tv).
      abi_decoder_coherent ce env sf ty tv /\
      (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      (prim ==> ?c. type_to_abi_dec_info sf ce ty = DecPrimWord c) /\
      type_memory_size tv < dimword (:256)) specs /\
    fn_has_code st final fn /\
    alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    unit_alloca_budget ctx < dimword (:256) /\
    (!id. st.cs_next_id <= id /\ id < final.cs_next_id ==>
      FLOOKUP initial.vs_allocas id = NONE) /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    (final.cs_current_insts = [] ==>
      !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
    (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn initial) \/
    ?v outputs fp.
      ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
      v.vs_inst_idx = LENGTH final.cs_current_insts /\
      LIST_REL (\(name,prim,dyn,sz,ty,tv) (x,dst,p,id).
        value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
        FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
        eval_operand dst v = SOME (n2w p) /\
        abi_decoder_operand_live final.cs_next_var dst /\
        st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
        p+type_memory_size tv < dimword (:256)) specs outputs /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      initial.vs_alloca_next <= v.vs_alloca_next /\
      v.vs_call_ctx = initial.vs_call_ctx /\
      v.vs_data_section = initial.vs_data_section /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op v = eval_operand op initial) /\
      abi_decode_footprint_frame fp initial v /\
      (!q k. MEM (q,k) fp ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn initial = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  rpt gen_tac >> strip_tac >> drule_all registration_list_owned_provenance >>
  strip_tac >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`v`,`outputs`,`fp`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem registration_positional_owned_run:
  compile_register_positional_args ce (build_positional_args ce args) off st = (cef,final) /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\(name,ty) (ty',tv).
    ty = ty' /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
      var_location_memory_size loc = SOME (type_memory_size tv)) /\
    type_memory_size tv < dimword (:256)) args tys /\
  fn_has_code st final fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!id. st.cs_next_id <= id /\ id < final.cs_next_id ==>
    FLOOKUP initial.vs_allocas id = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v outputs fp.
    ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\
    LIST_REL (\((name,ty),tv) (x,dst,p,id).
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
      FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
      eval_operand dst v = SOME (n2w p) /\
      abi_decoder_operand_live final.cs_next_var dst /\
      st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
      p+type_memory_size tv < dimword (:256)) (ZIP (args,MAP SND tys)) outputs /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame fp initial v /\
    (!q k. MEM (q,k) fp ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  strip_tac >> drule_all registration_positional_owned_provenance >>
  strip_tac >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`v`,`outputs`,`fp`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem registration_positional_backing:
  alloca_inv v /\
  LIST_REL (\((name,ty),tv) (x,dst,p,id).
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    eval_operand dst v = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var dst /\
    st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
    p+type_memory_size tv < dimword (:256) /\
    (?vname ins. dst = Var vname /\ MEM ins (fn_insts fn) /\
      ins.inst_opcode = ALLOCA /\ ins.inst_outputs = [vname] /\
      ins.inst_id = id)) (ZIP (args,MAP SND tys)) outputs ==>
  LIST_REL (\((name,ty),tv) (x,dst,p,id).
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x p v.vs_memory /\
    FLOOKUP cef.ce_vars name = SOME (PtrVar dst (type_memory_size tv)) /\
    eval_operand dst v = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var dst /\
    st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP v.vs_allocas id = SOME (p,type_memory_size tv) /\
    p+type_memory_size tv < dimword (:256) /\
    (?vname. dst = Var vname /\ local_backed fn vname v p (type_memory_size tv)) /\
    p+type_memory_size tv <= v.vs_alloca_next)
    (ZIP (args,MAP SND tys)) outputs
Proof
  strip_tac >> irule listTheory.LIST_REL_mono >>
  goal_assum (drule_at Any) >> simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (simp[local_backed_def] >> disj1_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]
QED
