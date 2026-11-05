Theory bodyPtrIntCallLowRegion
Ancestors bodyPtrIntCallWriteFrame bodyPtrIntCallConfinement
  memSafeRun ptrDiscipline contextCodegenRel list pred_set

Theorem intcall_revert_forward_written_taint:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  revert_forward_at bb s.vs_inst_idx ==>
  written_taint tn inst s = {}
Proof
  strip_tac >> drule_all revert_forward_at_opcode >> strip_tac >>
  simp[written_taint_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem intcall_in_revert_forward_written_taint:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  in_revert_forward fn s ==>
  written_taint tn inst s = {}
Proof
  strip_tac >> gvs[in_revert_forward_def] >>
  irule intcall_revert_forward_written_taint >>
  qexistsl [`bb`, `fn`] >> simp[]
QED

(* gas_outcome_ptr uses gas_summary_ptr_at, whose path threshold is 0.
   ptr_safe_step retains that same lo when entering nested callees; it
   does not replace lo by the caller frontier. Thus no region lower-bound
   assumption is needed for the actual counted-path consumer. *)
Theorem intcall_written_taint_outside_lookup:
  step_inst fuel ctx inst s = OK t /\
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  access_ok lo G fn inst s /\
  intcall_prov_outside P PG G /\ (!i. i < lo ==> i NOTIN P) ==>
  written_taint tn inst s SUBSET COMPL P
Proof
  strip_tac >> Cases_on `in_revert_forward fn s`
  >- (drule_all intcall_in_revert_forward_written_taint >> simp[]) >>
  irule intcall_written_taint_outside_ok >> metis_tac[]
QED

Theorem intcall_written_taint_outside_zero:
  step_inst fuel ctx inst s = OK t /\
  (!op k. MEM op inst.inst_operands /\ k IN op_taint tn op ==> k < 32) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  access_ok 0 G fn inst s /\ intcall_prov_outside P PG G ==>
  written_taint tn inst s SUBSET COMPL P
Proof
  strip_tac >> irule intcall_written_taint_outside_lookup >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`G`, `PG`, `bb`, `fn`, `0`] >> simp[]
QED
