(* Execution and allocation-map frames from actual allocation-site credit. *)
Theory actualAllocExec
Ancestors
  actualAllocCredit actualDecoderSites abiDecoderIndexInit emitHelper context compileEnv
  loweringHalt fragExecMem fragExec abiDecoderReentry venomInstProofs
  venomExecSemantics venomState
  allocaFrontierBound allocaBudgetProps vyperCompiler venomInst
  venomMemProps venomMemDefs emitHelperProps exprLoweringProps finite_map words arithmetic list rich_list

Theorem physical_word_alloca_fresh_run:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  s.vs_alloca_next + 32 < dimword (:256) ==>
  step_inst_base inst s = OK
    (update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,32));
        vs_alloca_next := s.vs_alloca_next + 32|>))
Proof
  strip_tac >> simp[step_inst_base_def, exec_alloca_def] >>
  simp[update_var_def, FLOOKUP_UPDATE,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem actual_word_alloca_fresh_run:
  alloca_frontier_inv ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  unit_alloca_budget ctx < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    t = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,32));
        vs_alloca_next := s.vs_alloca_next + 32|>) /\
    s.vs_alloca_next + 32 < dimword (:256) /\
    t.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,32)) /\
    t.vs_alloca_next = s.vs_alloca_next + 32 /\
    (!j. j <> inst.inst_id ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j)
Proof
  strip_tac >>
  `alloca_size inst = 32` by
    simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
  drule_all actual_word_alloca_no_wrap >> strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  simp[update_var_def, FLOOKUP_UPDATE,
       dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem actual_word_alloca_reuse_run:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (32w:bytes32) = OK t /\
    t = update_var out (n2w p) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    remaining_alloca_budget insts t = remaining_alloca_budget insts s
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  simp[update_var_def, remaining_alloca_budget_def]
QED

Theorem actual_alloca_frontier_preserved:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  step_inst_base inst s = OK t /\ alloca_frontier_inv ctx fn site s ==>
  alloca_frontier_inv ctx fn site' t
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all step_inst_base_alloca_budget >>
  simp[alloca_frontier_inv_def] >> strip_tac >>
  fs[alloca_frontier_inv_def] >> decide_tac
QED

Theorem actual_alloca_slots_preserved:
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK t /\ alloca_inv s ==>
  alloca_inv t
Proof
  strip_tac >> irule alloca_inv_step_inst >>
  qexistsl_tac [`ctx`, `0`, `inst`, `s`] >>
  simp[Once step_inst_def]
QED

Theorem actual_index_init_literal_site:
  abi_decode_index_init first = (ip,last) ==>
  ?inst out. MEM inst (emitted_insts first last) /\
    inst.inst_id = first.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\ ip = Var out
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND] >>
  qexists `mk_inst first.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString first.cs_next_var)]` >> simp[mk_inst_def]
QED

Theorem actual_index_init_site_twice:
  abi_decode_index_init first = (ip,last) /\
  (!i. MEM i (emitted_insts first last) ==> MEM i (fn_insts fn)) /\
  alloca_frontier_inv ctx fn site s /\ unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas first.cs_next_id = NONE ==>
  ?inst out t u.
    MEM inst (emitted_insts first last) /\ inst.inst_id = first.cs_next_id /\
    ip = Var out /\ step_inst_base inst s = OK t /\ step_inst_base inst t = OK u /\
    t.vs_alloca_next = s.vs_alloca_next + 32 /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_allocas = t.vs_allocas /\
    u = update_var out (n2w s.vs_alloca_next) t /\
    (!j. j <> first.cs_next_id ==> FLOOKUP u.vs_allocas j = FLOOKUP s.vs_allocas j)
Proof
  strip_tac >> drule actual_index_init_literal_site >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  `FLOOKUP s.vs_allocas inst.inst_id = NONE` by simp[] >>
  drule_all actual_word_alloca_fresh_run >> strip_tac >>
  `FLOOKUP t.vs_allocas inst.inst_id = SOME (s.vs_alloca_next,32)` by
    simp[FLOOKUP_UPDATE] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  goal_assum $ drule_at Any >> goal_assum $ drule_at Any >>
  goal_assum $ drule_at Any >> goal_assum $ drule_at Any >> simp[FLOOKUP_UPDATE]
QED

(* Literal-capacity companions do not require the output variable to be absent. *)
Theorem actual_literal_alloca_fresh_run:
  alloca_frontier_inv ctx fn site s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (n2w n:bytes32) = OK t /\
    t = update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (inst.inst_id,(s.vs_alloca_next,n));
        vs_alloca_next := s.vs_alloca_next + n|>) /\
    s.vs_alloca_next + n < dimword (:256) /\
    t.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,n)) /\
    t.vs_alloca_next = s.vs_alloca_next + n /\
    (!j. j <> inst.inst_id ==> FLOOKUP t.vs_allocas j = FLOOKUP s.vs_allocas j)
Proof
  strip_tac >>
  `alloca_size inst = n` by simp[alloca_size_def] >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
  drule_all actual_alloca_frontier_credit >> strip_tac >>
  `s.vs_alloca_next + n < dimword (:256)` by decide_tac >>
  simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

Theorem actual_literal_alloca_reuse_run:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,n) /\
  n < dimword (:256) ==>
  ?t. step_inst_base inst s = OK t /\
    exec_alloca inst s (n2w n:bytes32) = OK t /\
    t = update_var out (n2w p) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    remaining_alloca_budget insts t = remaining_alloca_budget insts s
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_alloca_def] >>
  simp[update_var_def, remaining_alloca_budget_def]
QED

Theorem actual_literal_alloca_frame:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  exec_alloca inst s amount = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
  (!op. op <> Var out ==> eval_operand op t = eval_operand op s) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
    FLOOKUP t.vs_allocas id = SOME entry)
Proof
  simp[exec_alloca_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def] >>
  TRY (Cases_on `op` >>
    simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  gvs[FLOOKUP_UPDATE] >> Cases_on `inst.inst_id = id` >> gvs[]
QED

Theorem actual_alloc_buffer_step_mem:
  compile_alloc_buffer n st = (buf,last) /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial = OK t ==>
  frag_exec_mem ctx st last (\s. s = initial)
    (\s. s = t with vs_inst_idx := LENGTH last.cs_current_insts) R
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  irule frag_exec_mem_step >> simp[] >>
  simp[mk_inst_def, is_terminator_def] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]
QED

Theorem actual_literal_alloca_owned_step:
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ inst.inst_outputs = [out] /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas inst.inst_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) ==>
  ?t p. step_inst_base inst s = OK t /\
    exec_alloca inst s (n2w n:bytes32) = OK t /\
    lookup_var out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n) /\
    p+n < dimword (:256) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    (!op. op <> Var out ==> eval_operand op t = eval_operand op s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> inst.inst_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id)
Proof
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all actual_literal_alloca_fresh_run >> strip_tac >>
      `alloca_inv t` by metis_tac[actual_alloca_slots_preserved] >>
      `alloca_frontier_inv ctx fn site t` by
        metis_tac[actual_alloca_frontier_preserved] >>
      drule_all actual_literal_alloca_frame >> strip_tac >>
      qexistsl_tac [`t`, `s.vs_alloca_next`] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  gvs[] >>
  `n < dimword (:256)` by decide_tac >>
  drule_all actual_literal_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `alloca_inv t` by metis_tac[actual_alloca_slots_preserved] >>
  `alloca_frontier_inv ctx fn site t` by
    metis_tac[actual_alloca_frontier_preserved] >>
  drule_all actual_literal_alloca_frame >> strip_tac >>
  qexistsl_tac [`t`, `p`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem actual_alloc_buffer_site:
  compile_alloc_buffer n st = (buf,last) /\ fn_has_code st last fn ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts fn)
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  fs[fn_has_code_def] >> irule lookup_block_fn_insts >>
  goal_assum $ drule_at Any >> fs[IS_PREFIX_APPEND] >> simp[]
QED

Theorem actual_alloc_buffer_live:
  compile_alloc_buffer n st = (buf,last) ==>
  abi_decoder_operand_live last.cs_next_var buf.buf_operand /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var (STRING #"%" (toString st.cs_next_var)) /\
    abi_decoder_operand_live last.cs_next_var op)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem actual_alloca_inv_inst_idx[simp]:
  alloca_inv (s with vs_inst_idx := idx) = alloca_inv s
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem actual_alloca_frontier_inst_idx[simp]:
  alloca_frontier_inv ctx fn site (s with vs_inst_idx := idx) =
    alloca_frontier_inv ctx fn site s
Proof
  simp[alloca_frontier_inv_def, remaining_alloca_budget_def]
QED

Theorem actual_alloc_buffer_owned_run:
  compile_alloc_buffer n st = (buf,last) /\ fn_has_code st last fn /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
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
  `frag_exec_mem ctx st last (\s. s = initial)
    (\s. s = t with vs_inst_idx := LENGTH last.cs_current_insts) (\r. F)` by
    (irule actual_alloc_buffer_step_mem >>
     goal_assum $ drule_at Any >> fs[Abbr `ins`]) >>
  drule actual_alloc_buffer_live >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_mem_def] >> disch_then (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n)` by metis_tac[] >>
  `!id. id <> st.cs_next_id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by metis_tac[] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH last.cs_current_insts`, `p`] >>
  fs[eval_operand_def, lookup_var_def] >> rpt strip_tac >>
  qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` drule >>
  strip_tac >> qpat_x_assum `!op. op <> Var _ ==> _` drule >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED
