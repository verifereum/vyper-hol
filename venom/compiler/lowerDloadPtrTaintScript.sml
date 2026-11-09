Theory lowerDloadPtrTaint
Ancestors
  lowerDloadPtrBoundary ptrDiscipline codegenRel stepWriteFootprintBase
  venomExecSemantics venomState finite_map pred_set list words

Theorem fresh_alloca_bytes_tainted:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK t /\
  s.vs_alloca_next <= i /\ i < s.vs_alloca_next + w2n amount ==>
  i IN mem_taint tn inst s t
Proof
  strip_tac >> drule_all exec_alloca_fresh_site >>
  simp[update_var_def] >> strip_tac >> gvs[] >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       range_bytes_def, new_site_bytes_def, FLOOKUP_UPDATE] >>
  disj1_tac >> disj2_tac >> qexists_tac `inst.inst_id` >>
  simp[] >> fs[FLOOKUP_DEF]
QED

Theorem codecopy_mem_taint:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand size_op s = SOME n /\ new_site_bytes s t = {} ==>
  mem_taint tn inst s t = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}
Proof
  simp[mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def]
QED

Theorem mem_word_taint_cleared_range:
  mem_word_taint (M DIFF {i | b <= i /\ i < b+32}) b = {}
Proof
  simp[mem_word_taint_def, EXTENSION] >> decide_tac
QED

Theorem codecopy_byte_outside:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand size_op s = SOME n /\ step_inst_base inst s = OK t /\
  ~(w2n b <= i /\ i < w2n b + w2n n) ==>
  read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >> irule copy_byte_frame >>
  qexistsl [`dst`,`inst`,`size_op`,`src`] >>
  simp[source_memory_write_ranges_def, sized_source_write_range_def]
QED

Theorem codecopy_scratch_untainted:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand size_op s = SOME n /\ w2n n = 32 /\
  new_site_bytes s t = {} ==>
  mem_word_taint (mem_taint tn inst s t) (w2n b) = {}
Proof
  strip_tac >> drule_all codecopy_mem_taint >>
  simp[mem_word_taint_cleared_range]
QED

Theorem codecopy_no_new_site_bytes:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand size_op s = SOME n /\ step_inst_base inst s = OK t ==>
  new_site_bytes s t = {}
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  simp[step_inst_base_def, write_memory_with_expansion_def] >>
  strip_tac >> gvs[] >>
  simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem codecopy_scratch_step_untainted:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand size_op s = SOME n /\ w2n n = 32 /\
  step_inst_base inst s = OK t ==>
  mem_word_taint (mem_taint tn inst s t) (w2n b) = {}
Proof
  strip_tac >> drule_all codecopy_no_new_site_bytes >> strip_tac >>
  irule codecopy_scratch_untainted >> metis_tac[]
QED

Theorem codecopy_disjoint_region:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
  eval_operand size_op s = SOME n /\ step_inst_base inst s = OK t /\
  (c+m <= w2n b \/ w2n b+w2n n <= c) ==>
  !i. c <= i /\ i < c+m ==>
      read_byte i t.vs_memory = read_byte i s.vs_memory
Proof
  strip_tac >> rpt strip_tac >> irule codecopy_byte_outside >>
  qexistsl [`a`,`b`,`dst`,`inst`,`n`,`size_op`,`src`] >> simp[] >>
  decide_tac
QED
