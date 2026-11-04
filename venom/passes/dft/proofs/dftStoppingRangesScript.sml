Theory dftStoppingRanges
Ancestors
  dftRunRel unitMemInv venomEffects contextCodegenRel codegenRel
  dftScheduleOrder opcodeClass pred_set venomInst

(* Opcode-only boundary: absence of memory effects excludes direct ranges.
   This does not exclude ranges observed in an INVOKE's callee. *)
Theorem dft_no_memory_effect_ranges:
  ~(Eff_MEMORY IN read_effects i.inst_opcode) /\
  ~(Eff_MEMORY IN write_effects i.inst_opcode) ==>
  inst_mem_ranges i s = []
Proof
  simp[] >> Cases_on `i.inst_opcode` >>
  simp[read_effects_def, write_effects_def, all_effects_def, empty_effects_def] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

(* An instruction writing MEMORY cannot cross a direct nonempty range. *)
Theorem dft_memory_writer_crossing_ranges:
  Eff_MEMORY IN write_effects x.inst_opcode /\
  ~dft_must_order x y ==> inst_mem_ranges y s = []
Proof
  strip_tac >> irule dft_no_memory_effect_ranges >>
  gvs[dft_must_order_def] >>
  fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem dft_nonroot_abort_crossing_ranges:
  inst_wf x /\ ~is_terminator x.inst_opcode /\
  ~dft_must_order x y /\ step_inst fuel C x s = Abort a t ==>
  inst_mem_ranges y u = []
Proof
  strip_tac >>
  `~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
     write_effects x.inst_opcode = empty_effects)` by
    fs[dft_must_order_def] >>
  drule_all dft_swap_nonroot_abort_class >> strip_tac >>
  irule dft_memory_writer_crossing_ranges >>
  qexists `x` >> simp[write_effects_def, all_effects_def]
QED

Theorem dft_nonterminator_halt_crossing_ranges:
  ~is_terminator x.inst_opcode /\ ~dft_must_order x y /\
  step_inst fuel C x s = Halt t ==> inst_mem_ranges y u = []
Proof
  strip_tac >> drule step_inst_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def] >>
  irule dft_memory_writer_crossing_ranges >>
  qexists `x` >> simp[write_effects_def, all_effects_def]
QED

(* Direct ranges alone would miss observations inside a skipped callee. *)
Theorem dft_memory_writer_crossing_not_invoke:
  Eff_MEMORY IN write_effects x.inst_opcode /\
  ~dft_must_order x y ==> y.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >>
  fs[dft_must_order_def, read_effects_def, write_effects_def,
     all_effects_def, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem dft_abort_crossing_not_invoke:
  inst_wf x /\ ~is_terminator x.inst_opcode /\
  ~dft_must_order x y /\ step_inst fuel C x s = Abort a t ==>
  y.inst_opcode <> INVOKE
Proof
  strip_tac >>
  `~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
     write_effects x.inst_opcode = empty_effects)` by
    fs[dft_must_order_def] >>
  drule_all dft_swap_nonroot_abort_class >> strip_tac >>
  irule dft_memory_writer_crossing_not_invoke >>
  qexists `x` >> simp[write_effects_def, all_effects_def]
QED

Theorem dft_halt_crossing_not_invoke:
  ~is_terminator x.inst_opcode /\ ~dft_must_order x y /\
  step_inst fuel C x s = Halt t ==> y.inst_opcode <> INVOKE
Proof
  strip_tac >> drule step_inst_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def] >>
  irule dft_memory_writer_crossing_not_invoke >>
  qexists `x` >> simp[write_effects_def, all_effects_def]
QED

(* In particular this covers an open or divergent INVOKE, without a return
   assumption. It excludes only observations in the crossed instruction. *)
Theorem dft_invoke_crossing_ranges:
  x.inst_opcode = INVOKE /\ ~dft_must_order x y ==>
  inst_mem_ranges y u = [] /\ y.inst_opcode <> INVOKE
Proof
  strip_tac >>
  `Eff_MEMORY IN write_effects x.inst_opcode` by
    simp[write_effects_def, all_effects_def] >>
  conj_tac
  >- (irule dft_memory_writer_crossing_ranges >> metis_tac[]) >>
  irule dft_memory_writer_crossing_not_invoke >> metis_tac[]
QED
