Theory stmtSimCustomErrorTrap
Ancestors
  exprLoweringProps fragExec abiEncoderProps memSafeRun fcgDefs venomWf
  contextCodegenRel
  venomExecSemantics venomInst venomState compileEnv list rich_list relation

Definition ce_trap_inst_def:
  ce_trap_inst i =
    if i.inst_opcode = GAS \/ i.inst_opcode = INVOKE then
      i with <|inst_opcode := GAS; inst_outputs := i.inst_outputs ++ i.inst_outputs|>
    else i
End

Definition ce_trap_block_def:
  ce_trap_block b = b with bb_instructions := MAP ce_trap_inst b.bb_instructions
End

Definition ce_trap_fn_def:
  ce_trap_fn f = f with fn_blocks := MAP ce_trap_block f.fn_blocks
End

Definition ce_trap_ctx_def:
  ce_trap_ctx ctx = ctx with ctx_functions := MAP ce_trap_fn ctx.ctx_functions
End

Definition ce_trap_cs_def:
  ce_trap_cs cs = cs with
    <|cs_blocks := MAP ce_trap_block cs.cs_blocks;
      cs_current_insts := MAP ce_trap_inst cs.cs_current_insts|>
End

Theorem ce_trap_lookup_function:
  lookup_function name (ce_trap_ctx ctx).ctx_functions =
  OPTION_MAP ce_trap_fn (lookup_function name ctx.ctx_functions)
Proof
  simp[ce_trap_ctx_def] >> irule lookup_function_map >> simp[ce_trap_fn_def]
QED

Theorem ce_trap_lookup_block:
  !bbs. lookup_block lbl (MAP ce_trap_block bbs) =
    OPTION_MAP ce_trap_block (lookup_block lbl bbs)
Proof
  Induct >> simp[lookup_block_def, FIND_thm, ce_trap_block_def] >>
  rw[] >> gvs[lookup_block_def, ce_trap_block_def]
QED

Theorem ce_trap_get_instruction:
  get_instruction (ce_trap_block bb) idx =
    OPTION_MAP ce_trap_inst (get_instruction bb idx)
Proof
  simp[ce_trap_block_def, get_instruction_def, EL_MAP] >> rw[]
QED

Theorem ce_trap_inst_fields:
  (ce_trap_inst i).inst_id = i.inst_id /\
  (ce_trap_inst i).inst_operands = i.inst_operands /\
  ((ce_trap_inst i).inst_opcode = ALLOCA <=> i.inst_opcode = ALLOCA) /\
  ((ce_trap_inst i).inst_opcode = PHI <=> i.inst_opcode = PHI) /\
  (ce_trap_inst i).inst_opcode <> INVOKE
Proof
  rw[ce_trap_inst_def] >> gvs[]
QED

Theorem ce_trap_phi_prefix_length:
  !is. phi_prefix_length (MAP ce_trap_inst is) = phi_prefix_length is
Proof
  Induct >> simp[phi_prefix_length_def, ce_trap_inst_fields]
QED

Theorem ce_trap_fn_insts_blocks:
  !bs. fn_insts_blocks (MAP ce_trap_block bs) = MAP ce_trap_inst (fn_insts_blocks bs)
Proof
  Induct >> simp[fn_insts_blocks_def, ce_trap_block_def, MAP_APPEND]
QED

Theorem ce_trap_fn_insts:
  fn_insts (ce_trap_fn fn) = MAP ce_trap_inst (fn_insts fn)
Proof
  simp[fn_insts_def, ce_trap_fn_def, ce_trap_fn_insts_blocks]
QED

Theorem ce_trap_step_context:
  inst.inst_opcode <> INVOKE ==>
  step_inst fuel (ce_trap_ctx ctx) inst s = step_inst fuel ctx inst s
Proof
  simp[step_inst_non_invoke]
QED

Theorem ce_trap_mem_safe_context:
  inst.inst_opcode <> INVOKE ==>
  (mem_safe_step fuel (ce_trap_ctx ctx) inst s <=> mem_safe_step fuel ctx inst s)
Proof
  simp[mem_safe_step_non_invoke]
QED

Theorem ce_trap_pending_alloca_size:
  pending_alloca_size (ce_trap_fn fn) s = pending_alloca_size fn s
Proof
  simp[pending_alloca_size_def, ce_trap_fn_insts, FILTER_MAP, MAP_MAP_o,
       ce_trap_inst_fields, combinTheory.o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[alloca_lit_size_def, ce_trap_inst_fields]
QED

Theorem ce_trap_no_direct_calls:
  ~fn_directly_calls (ce_trap_ctx ctx) a b
Proof
  simp[fn_directly_calls_def, ce_trap_lookup_function] >>
  strip_tac >> Cases_on `lookup_function a ctx.ctx_functions` >>
  gvs[ce_trap_fn_insts, MEM_MAP] >>
  rpt strip_tac >> gvs[ce_trap_inst_fields]
QED

Theorem ce_trap_no_call_paths:
  ~TC (fn_directly_calls (ce_trap_ctx ctx)) a b
Proof
  strip_tac >> pop_assum mp_tac >>
  simp[Once TC_CASES1, ce_trap_no_direct_calls]
QED

Theorem ce_trap_alloca_room:
  alloca_room ctx fn s ==> alloca_room (ce_trap_ctx ctx) (ce_trap_fn fn) s
Proof
  simp[alloca_room_def, ce_trap_fn_def, ce_trap_lookup_function,
       ce_trap_no_call_paths] >>
  strip_tac >>
  `pending_alloca_size (ce_trap_fn fn) s = pending_alloca_size fn s` by
    simp[ce_trap_pending_alloca_size] >>
  gvs[ce_trap_fn_def] >> decide_tac
QED

Theorem ce_trap_frag_ids:
  frag_ids (ce_trap_cs a) (ce_trap_cs b) = frag_ids a b
Proof
  simp[frag_ids_def, ce_trap_cs_def]
QED

Theorem ce_trap_emitted_blocks:
  emitted_blocks (ce_trap_cs a) (ce_trap_cs b) =
    MAP ce_trap_block (emitted_blocks a b)
Proof
  simp[emitted_blocks_def, ce_trap_cs_def, MAP_TAKE]
QED

Theorem ce_trap_fn_has_code:
  fn_has_code a b fn ==>
  fn_has_code (ce_trap_cs a) (ce_trap_cs b) (ce_trap_fn fn)
Proof
  simp[fn_has_code_def, ce_trap_emitted_blocks, MEM_MAP] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[ce_trap_fn_def, ce_trap_lookup_block,
                           ce_trap_block_def] >> metis_tac[]) >>
  qexists_tac `ce_trap_block bb` >>
  simp[ce_trap_cs_def, ce_trap_fn_def, ce_trap_lookup_block,
       ce_trap_block_def] >>
  gvs[IS_PREFIX_APPEND] >> simp[MAP_APPEND, IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem ce_trap_fn_inst_ids_distinct:
  fn_inst_ids_distinct (ce_trap_fn fn) <=> fn_inst_ids_distinct fn
Proof
  simp[fn_inst_ids_distinct_def, ce_trap_fn_def, MAP_MAP_o,
       combinTheory.o_DEF, ce_trap_block_def, ce_trap_inst_fields]
QED

Theorem ce_trap_recorded_alloca_size:
  (!inst w base sz.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n w) ==>
  (!inst w base sz.
    MEM inst (fn_insts (ce_trap_fn fn)) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n w)
Proof
  simp[ce_trap_fn_insts, MEM_MAP] >> rpt strip_tac >>
  gvs[ce_trap_inst_fields] >> metis_tac[]
QED

Theorem ce_trap_error:
  i.inst_opcode = GAS \/ i.inst_opcode = INVOKE ==>
  step_inst fuel ctx (ce_trap_inst i) s = Error "read0 requires single output"
Proof
  strip_tac >>
  simp[ce_trap_inst_def, step_inst_non_invoke, step_inst_base_def, exec_gas_def] >>
  Cases_on `i.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem ce_trap_step_back_assign:
  step_back_assign (ce_trap_inst i) op = step_back_assign i op
Proof
  Cases_on `i.inst_opcode = GAS \/ i.inst_opcode = INVOKE` >>
  Cases_on `op` >> gvs[ce_trap_inst_def, step_back_assign_def, MEM_APPEND]
QED

Theorem ce_trap_resolve_block_assigns:
  !is op. resolve_block_assigns (MAP ce_trap_inst is) op = resolve_block_assigns is op
Proof
  Induct >> simp[resolve_block_assigns_def] >> gen_tac >>
  Cases_on `h.inst_opcode = GAS \/ h.inst_opcode = INVOKE` >>
  Cases_on `op` >> gvs[ce_trap_inst_def, resolve_block_assigns_def, MEM_APPEND]
QED

Theorem ce_trap_same_after_assigns:
  !is p q. same_after_assigns (MAP ce_trap_inst is) p q = same_after_assigns is p q
Proof
  Induct >> simp[same_after_assigns_def, ce_trap_step_back_assign]
QED

Theorem ce_trap_observed_opcodes:
  ((ce_trap_inst i).inst_opcode = ASSIGN <=> i.inst_opcode = ASSIGN) /\
  ((ce_trap_inst i).inst_opcode = RETURNDATACOPY <=> i.inst_opcode = RETURNDATACOPY) /\
  ((ce_trap_inst i).inst_opcode = REVERT <=> i.inst_opcode = REVERT)
Proof
  rw[ce_trap_inst_def] >> gvs[]
QED

Theorem ce_trap_revert_forward_pair:
  revert_forward_pair (ce_trap_block bb) i j <=> revert_forward_pair bb i j
Proof
  simp[revert_forward_pair_def, ce_trap_get_instruction,
       ce_trap_block_def, GSYM MAP_TAKE, GSYM MAP_DROP, GSYM MAP_REVERSE,
       ce_trap_same_after_assigns, ce_trap_resolve_block_assigns] >>
  Cases_on `get_instruction bb i` >> Cases_on `get_instruction bb j` >>
  simp[ce_trap_inst_fields, ce_trap_observed_opcodes] >>
  eq_tac >> rpt strip_tac >>
  gvs[ce_trap_inst_fields, ce_trap_observed_opcodes] >>
  metis_tac[ce_trap_observed_opcodes, optionTheory.option_CLAUSES]
QED

Theorem ce_trap_revert_forward_at:
  revert_forward_at (ce_trap_block bb) k <=> revert_forward_at bb k
Proof
  simp[revert_forward_at_def, ce_trap_revert_forward_pair]
QED
