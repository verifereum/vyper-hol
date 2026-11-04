(* Execution and allocation-map frames from actual allocation-site credit. *)
Theory actualAllocExec
Ancestors
  actualAllocCredit actualDecoderSites abiDecoderIndexInit emitHelper context compileEnv
  venomExecSemantics venomState
  allocaFrontierBound allocaBudgetProps vyperCompiler venomInst
  venomMemProps venomMemDefs emitHelperProps exprLoweringProps finite_map words arithmetic list rich_list

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
  simp[step_inst_base_def, exec_alloca_def] >>
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
  strip_tac >> simp[step_inst_base_def, exec_alloca_def] >>
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
