Theory entryReachBodyRegistrationAllocation
Ancestors
  loweringStateRelDefs actualAllocExec abiAllocationHistory entryReachBodyPreludeFrame
  entryReachBodyExactArrayLoop fragExecMem fragExec emitHelperProps
  compileEnv emitHelper venomInst venomExecSemantics venomState
  abiDecoderReentry exprLoweringProps finite_map words arithmetic list loweringHalt
  venomMemDefs

Theorem registration_alloca_step_frame[local]:
  inst.inst_outputs = [STRING #"%" (toString k)] /\
  exec_alloca inst s (amount:bytes32) = OK t /\
  fresh_vars_wrt limit s /\ k < limit.cs_next_var ==>
  fresh_vars_wrt limit t /\ entry_loop_fields s t
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, entry_loop_fields_def,
      fresh_vars_wrt_def, FLOOKUP_DEF, FDOM_FUPDATE] >>
  rpt strip_tac >> simp[ASCIInumbersTheory.toString_inj] >>
  metis_tac[LESS_LESS_EQ_TRANS, prim_recTheory.LESS_REFL]
QED

Theorem registration_alloc_buffer_framed:
  compile_alloc_buffer n st = (buf,last) /\ fn_has_code st last fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_alloca_history (fn_insts fn) initial /\ fresh_vars_wrt limit initial /\
  last.cs_next_var <= limit.cs_next_var ==>
  ?v p. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    eval_operand buf.buf_operand v = SOME (n2w p) /\
    abi_decoder_operand_live last.cs_next_var buf.buf_operand /\
    FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    v.vs_memory = initial.vs_memory /\ v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    abi_alloca_history (fn_insts fn) v /\ fresh_vars_wrt limit v /\
    entry_loop_fields initial v /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP v.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ins (fn_insts fn)` >>
  `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit (n2w n)] /\
    ins.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
    ins.inst_id = st.cs_next_id` by simp[Abbr `ins`, mk_inst_def] >>
  `!entry. FLOOKUP initial.vs_allocas ins.inst_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)` by metis_tac[] >>
  drule_all actual_literal_alloca_owned_step >> strip_tac >>
  `abi_alloca_history (fn_insts fn) t` by
    (irule abi_alloca_history_step >> goal_assum $ drule_at Any >> simp[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `st.cs_next_var < limit.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit t /\ entry_loop_fields initial t` by
    (irule registration_alloca_step_frame >> simp[] >>
     qexistsl_tac [`(n2w n:bytes32)`, `ins`, `st.cs_next_var`] >> simp[]) >>
  `frag_exec_mem ctx st last (\s. s = initial)
    (\s. s = t with vs_inst_idx := LENGTH last.cs_current_insts) (\r. F)` by
    (irule actual_alloc_buffer_step_mem >>
     goal_assum $ drule_at Any >> fs[Abbr `ins`]) >>
  drule actual_alloc_buffer_live >> strip_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >> disch_then (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n)` by metis_tac[] >>
  `!id. id <> st.cs_next_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by metis_tac[] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH last.cs_current_insts`, `p`] >>
  fs[eval_operand_def, lookup_var_def, abi_alloca_history_def,
     fresh_vars_wrt_def, entry_loop_fields_def] >> rpt strip_tac >>
  qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` drule >>
  strip_tac >> qpat_x_assum `!op. op <> Var _ ==> _` drule >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

(* A bounded write interface adds the fixed-limit freshness missing from the
   existing prelude frame.  Every observation refers to its explicit update. *)
Theorem registration_pure_limit_step[local]:
  emit_op opc args st = (out,last) /\ (opc = ADD \/ opc = CALLDATALOAD) /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  fresh_vars_wrt limit s /\ last.cs_next_var <= limit.cs_next_var ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME w /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t /\ fresh_vars_wrt limit t
Proof
  strip_tac >> (
  `frag_exec_mem ctx st last (\u. u = s)
    (\u. u = (update_var (STRING #"%" (toString st.cs_next_var)) w s)
      with vs_inst_idx := LENGTH last.cs_current_insts) (\r. F)` by
    (irule calldataRegistrationExecTheory.registration_emit_step_mem >>
     goal_assum $ drule_at Any >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `fresh_vars_wrt limit (update_var (STRING #"%" (toString st.cs_next_var)) w s)` by
    (irule fresh_vars_wrt_update_var >> simp[]) >>
  qexists_tac `(update_var (STRING #"%" (toString st.cs_next_var)) w s)
    with vs_inst_idx := LENGTH last.cs_current_insts` >>
  `fresh_vars_wrt limit ((update_var (STRING #"%" (toString st.cs_next_var)) w s)
     with vs_inst_idx := LENGTH last.cs_current_insts)` by
    fs[fresh_vars_wrt_def] >>
  simp[entry_prelude_frame_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          ASCIInumbersTheory.toString_inj] >>
  gen_tac >> strip_tac >> drule calldataDynOwnedTheory.calldata_update_protected >>
  disch_then (qspecl_then [`w`,`s`] mp_tac) >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, update_var_def])
QED

Theorem registration_add_limit[local]:
  emit_op ADD [lhs;rhs] st = (out,last) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fresh_vars_wrt limit s /\ last.cs_next_var <= limit.cs_next_var ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME (a+b) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t /\ fresh_vars_wrt limit t
Proof
  strip_tac >> irule registration_pure_limit_step >>
  simp[] >> qexistsl_tac [`[lhs;rhs]`, `ADD`] >> simp[] >>
  irule step_ADD >> simp[]
QED

Theorem registration_read_limit[local]:
  emit_op CALLDATALOAD [src] st = (out,last) /\
  eval_operand src s = SOME p /\
  fresh_vars_wrt limit s /\ last.cs_next_var <= limit.cs_next_var ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t /\ fresh_vars_wrt limit t
Proof
  strip_tac >> irule registration_pure_limit_step >>
  simp[] >> qexistsl_tac [`[src]`, `CALLDATALOAD`] >> simp[] >>
  irule abiDecoderContractTheory.abi_decode_read_step >>
  simp[abiDecoderContractTheory.abi_decode_source_opcode_def]
QED

Theorem registration_address_limit_framed:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  fresh_vars_wrt limit s /\ first.cs_next_var <= limit.cs_next_var ==>
  ?t. frag_exec_mem ctx st first (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t /\ fresh_vars_wrt limit t
Proof
  strip_tac >> reverse (Cases_on `dyn`) >> gvs[]
  >- (irule registration_add_limit >> simp[eval_operand_def] >>
      qexistsl_tac [`Lit 4w`, `Lit (n2w (off-4))`] >> simp[eval_operand_def]) >>
  `after_head.cs_next_var <= limit.cs_next_var /\
   after_load.cs_next_var <= limit.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  `eval_operand (Lit (n2w 4)) s = SOME (n2w 4) /\
   eval_operand (Lit (n2w (off-4))) s = SOME (n2w (off-4))` by simp[eval_operand_def] >>
  drule_all registration_add_limit >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all registration_read_limit >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) t =
   abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) s` by
    fs[entry_prelude_frame_def, abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def] >>
  `eval_operand (Lit (n2w 4)) t' = SOME (n2w 4)` by simp[eval_operand_def] >>
  drule_all registration_add_limit >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `cs_extends st after_head /\ cs_extends after_head after_load /\
   cs_extends after_load first` by
    (imp_res_tac emit_op_extends >> rpt conj_tac >> irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `frag_exec_mem ctx st after_load (\u. u = s) (\u. u = t') (\r. F)` by
    (irule frag_exec_mem_seq >> goal_assum $ drule_at Any >> simp[] >>
     goal_assum $ drule_at Any >> simp[]) >>
  `frag_exec_mem ctx st first (\u. u = s) (\u. u = t'') (\r. F)` by
    (irule frag_exec_mem_seq >> qexistsl_tac [`\u. u = t'`, `after_load`] >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  `entry_prelude_frame s t''` by fs[entry_prelude_frame_def] >>
  qexists_tac `t''` >> simp[] >> gen_tac >> strip_tac >>
  `st.cs_next_var <= after_head.cs_next_var /\
   after_head.cs_next_var <= after_load.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem registration_address_framed_run:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  fn_has_code st first fn /\ fresh_vars_wrt limit s /\
  first.cs_next_var <= limit.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  abi_alloca_history (fn_insts fn) s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = first.cs_current_bb /\
    t.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t /\ fresh_vars_wrt limit t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_alloca_history (fn_insts fn) t /\ entry_loop_fields s t /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all registration_address_limit_framed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >> disch_then (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >>
  gvs[entry_prelude_frame_def, entry_loop_fields_def,
      alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      abi_alloca_history_def, allocaFrontierBoundTheory.alloca_frontier_inv_def,
      allocaBudgetPropsTheory.remaining_alloca_budget_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem registration_allocation_address_run:
  compile_alloc_buffer n st = (buf,allocated) /\
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  fn_has_code st allocated fn /\ fn_has_code allocated first fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_alloca_history (fn_insts fn) initial /\ fresh_vars_wrt limit initial /\
  first.cs_next_var <= limit.cs_next_var ==>
  ?v p. ~v.vs_halted /\ v.vs_current_bb = first.cs_current_bb /\
    v.vs_inst_idx = LENGTH first.cs_current_insts /\
    eval_operand buf.buf_operand v = SOME (n2w p) /\
    abi_decoder_operand_live first.cs_next_var buf.buf_operand /\
    eval_operand src v = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) initial else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    FLOOKUP v.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    initial.vs_alloca_next <= v.vs_alloca_next /\ v.vs_memory = initial.vs_memory /\
    abi_alloca_history (fn_insts fn) v /\ fresh_vars_wrt limit v /\
    entry_loop_fields initial v /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP v.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `allocated.cs_next_var <= first.cs_next_var` by
    (drule_all calldataRegistrationExecTheory.registration_address_prelude_bounds >> simp[]) >>
  `allocated.cs_next_var <= limit.cs_next_var` by decide_tac >>
  drule_all registration_alloc_buffer_framed >> strip_tac >>
  drule_all registration_address_framed_run >> strip_tac >>
  `abi_decoder_operand_live first.cs_next_var buf.buf_operand` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand buf.buf_operand t = SOME (n2w p)` by metis_tac[] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial` by
    (rpt strip_tac >>
     drule actual_alloc_buffer_live >> strip_tac >> metis_tac[]) >>
  qexistsl_tac [`t`, `p`] >>
  gvs[entry_prelude_frame_def, entry_loop_fields_def,
      abiDecoderContractTheory.abi_decode_load_def,
      abiDecoderContractTheory.abi_decode_source_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED
