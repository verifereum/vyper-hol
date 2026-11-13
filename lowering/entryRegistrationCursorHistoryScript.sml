(* Allocation-free entry checks and history at their actual cursor. *)
Theory entryRegistrationCursorHistory
Ancestors
  entryPrefixAllocationResources moduleLowering compileEnv emitHelper
  fragExec allocaHistory venomInst list rich_list

Theorem entry_checks_alloca_free_prefix[local]:
  compile_entry_checks mc pay sc = ((),sk) /\ sc.cs_current_insts = [] ==>
  sk.cs_current_bb = sc.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> ALLOCA) sk.cs_current_insts
Proof
  Cases_on `pay` >> Cases_on `mc > 4` >>
  simp[compile_entry_checks_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_checks_cursor_no_alloca:
  compile_entry_checks mc pay sc = ((),sk) /\
  sc.cs_current_insts = [] /\ fn_has_code sc sk func /\
  t.vs_current_bb = sk.cs_current_bb /\
  t.vs_inst_idx = LENGTH sk.cs_current_insts ==>
  (!bb k inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    k < t.vs_inst_idx /\ get_instruction bb k = SOME inst ==>
    inst.inst_opcode <> ALLOCA)
Proof
  strip_tac >> drule_all entry_checks_alloca_free_prefix >> strip_tac >>
  gvs[fn_has_code_def] >> rpt strip_tac >>
  gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN] >>
  gvs[EVERY_EL] >> metis_tac[]
QED

Theorem entry_checks_cursor_alloca_history:
  compile_entry_checks mc pay sc = ((),sk) /\
  sc.cs_current_insts = [] /\ fn_has_code sc sk func /\
  t.vs_current_bb = sk.cs_current_bb /\
  t.vs_inst_idx = LENGTH sk.cs_current_insts /\
  t.vs_allocas = FEMPTY ==>
  alloca_history func t
Proof
  strip_tac >> irule empty_allocas_history_prefix >> simp[] >>
  metis_tac[entry_checks_cursor_no_alloca]
QED
