Theory concretizePtrBufferCopyFamilyForwardProbe
Ancestors
  concretizePtrPairedFields ptrDiscipline contextCodegenRel
  venomInst venomState venomExecSemantics finite_map list pred_set words
  arithmetic codegenRel

(* A local obstruction, not yet a counterexample to the frozen theorem. *)
Theorem ptr_buffer_forward_empty_births_obstruction:
  ~ptr_paired_write_owner 0 positions reloc {0}
    (tokens,registry,FEMPTY,PT,TG,saved,entries)
Proof
  simp[ptr_paired_write_owner_def]
QED

Theorem ptr_buffer_forward_zero_birth_obstruction:
  ~ptr_paired_write_owner 0 positions reloc {0}
    (tokens,registry,FEMPTY |+ ((token,aid),(0,0)),PT,TG,saved,entries)
Proof
  simp[ptr_paired_write_owner_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ptr_buffer_forward_pair_concrete:
  revert_forward_at
    <|bb_label := "entry";
      bb_instructions :=
        [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
         mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|> 0
Proof
  simp[revert_forward_at_def] >> qexists_tac `1` >>
  disj1_tac >>
  simp[revert_forward_pair_def, get_instruction_def,
       mk_inst_def, same_after_assigns_def, resolve_block_assigns_def]
QED

Theorem ptr_buffer_forward_access_exempt:
  access_ok 0 FEMPTY
    (fn with fn_blocks :=
      [<|bb_label := "entry";
         bb_instructions :=
          [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
           mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>])
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [])
    (s with <|vs_current_bb := "entry"; vs_inst_idx := 0|>)
Proof
  simp[access_ok_def, in_revert_forward_def,
       lookup_block_def, FIND_thm, ptr_buffer_forward_pair_concrete] >>
  simp[mk_inst_def]
QED

Theorem ptr_buffer_forward_nonempty_success:
  ?post.
    step_inst 0 C
      (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [])
      (s with vs_returndata := [7w]) = OK post /\
    0 IN range_bytes
      (step_writes (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [])
        (s with vs_returndata := [7w]) post)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
       eval_operand_def, step_writes_def, range_bytes_def,
       source_memory_write_ranges_def, sized_source_write_range_def]
QED

Theorem ptr_buffer_forward_ledger_obstruction:
  j < LENGTH done /\ EL j done = n /\
  ~is_terminator (EL n h).po_inst.inst_opcode /\
  (EL n h).po_inst.inst_opcode <> INVOKE /\
  x IN range_bytes (step_writes (EL n h).po_inst
    (EL n h).po_state (EL (SUC n) h).po_state) /\
  EL (SUC n) H = (tokens,registry,FEMPTY,PT,TG,saved,entries) ==>
  ~ptr_paired_writes 0 positions C Ct h ht done H writes
Proof
  strip_tac >> strip_tac >>
  `range_bytes (step_writes (EL n h).po_inst
     (EL n h).po_state (EL (SUC n) h).po_state) <> {}` by
    (strip_tac >> gvs[]) >>
  fs[ptr_paired_writes_def, EVERY_MEM] >>
  `?reloc. MEM (n,j,reloc) writes` by metis_tac[] >>
  `ptr_paired_write 0 positions C Ct h ht done H (n,j,reloc)` by
    metis_tac[] >>
  qpat_x_assum `!e. MEM e writes ==> _` kall_tac >>
  gvs[ptr_paired_write_def] >>
  fs[ptr_paired_write_owner_def] >> metis_tac[]
QED
