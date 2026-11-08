(* Counted pointer boundaries for PHI-free For control flow and element stores.
   These construct edges directly, rather than converting fixed-run safety. *)
Theory forPtrBoundary
Ancestors
  wordLoadStorePtr bodyPtrDefs typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr gasCount
  emitHelperProps exprLoweringProps fragExec ptrSafeRun ptrDiscipline
  codegenRel contextCodegenRel venomInst venomState venomExecSemantics
  venomExecProofs venomInstProofs list

Theorem for_emit_jump_zero_path_ptr:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem straight_line_single_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\ step_inst_base i s = OK u ==>
  gas_path_ptr D lo ctx fn PG G tn s
    (if i.inst_opcode = GAS then 1 else 0)
    (step_prov PG G i u) (step_taint i s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all straight_line_ptr_edge >> strip_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  qpat_x_assum `!PG. gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `PG` mp_tac) >>
  strip_tac >>
  `gas_path_ptr D lo ctx fn PG (step_prov PG G i u) (step_taint i s u tn)
     (u with vs_inst_idx := SUC s.vs_inst_idx) 0
     (step_prov PG G i u) (step_taint i s u tn)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED

Theorem mstore_zero_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MSTORE [Var dst; value] []) /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn)
    (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  qspecl_then [`mk_inst id MSTORE [Var dst; value] []`, `mstore (w2n a) w s`, `0`]
    mp_tac (Q.GENL [`i`, `u`, `lo`] straight_line_single_path_ptr) >>
  simp[GSYM mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[] >> reverse conj_tac >- (irule ptr_inst_ok_mstore >> simp[]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_write2_def, eval_operand_def]
QED

(* Interface audit for the remaining For port (C1.1).

   Supported shapes: supported/supportedStmtsScript.sml:116-125 admits
   fixed-array Names only, but does not restrict the element type to words.
   supportedTypesScript.sml:83-109 admits nested fixed/dynamic arrays,
   tuples, structs and scalar leaves. S1 bodySimDeclCasesScript:1025-1053
   (unadmitted source in alan-ref/s1) derives a local PtrVar binding and
   iterator_unmodified; mutation of the source snapshot is not a supported
   counterexample. Dynamic OUTER array iteration is excluded, not nested
   dynamic-array element copying.

   Counted copy implementation map (contextScript.sml:671-747):
   - Word element: MLOAD followed by MSTORE. compile_store_word_code
     gives the two instructions; ptr_inst_ok_mload, mload_ghost_clean,
     mload_preserves_ptr_covers and mload_then_mstore_ok supply checks.
     run_inst_seq_gas_path_ptr consumes run_inst_seq plus inst_seq_ptr;
     mstore_ghost_frame gives the concrete final ghost. The counted store
     above is one checked component, not the complete word-copy wrapper.
   - Bytestring: compile_store_bytestring reads length and copies payload;
     needs a concrete run plus inst_seq_ptr (including length cleanliness).
   - All other equal-type elements (including nested arrays, tuples and
     structs) use compile_copy_memory: empty code for size zero, otherwise
     one MCOPY. for_memory_element_copy_dispatch in forPtrCopyInterface
     checks this actual consumer dispatch. The recursive typed-store branches
     are NOT selected; no recursive-copy or INVALID exclusion proof is needed.
   Existing typedCopy*Ptr/wordCopyRobustPtr wrappers expose frag_exec_ptr,
   not counted runs. Required interface for each reachable finite branch:
     compiled equal-type store + robust source representation + coverage
       ==> counted pointer path with zero source gas,
           robust destination representation, exterior memory frame,
           and old-variable value/provenance/taint frame.
   Supply it by constructive straight-line witnesses and inst_seq_ptr for
   the same run, never by erasure inversion. The checked dispatch alone does
   not derive LocMemory, element coverage, robust representation, nonwrapping
   extents or fresh destination separation; these remain consumer obligations.

   Callback audit: bodyPtrPredsScript:87-90 grants body_stmts_ptr_ok only
   for nonempty vs. bodyPtrDefsScript:249-278 supplies ghost_inv for cenv'',
   cenv_top_ext, stmt_state_rel, old-variable lookup preservation and
   provenance/taint equalities. It does NOT supply ghost_kept memory clauses.
   Range counters/end and array saved-base/loop-slot pointer must all be
   not_fresh_at the BODY compiler entry, not merely fresh at outer entry.
   S1 stmtSimForScript:134 (for_reserved_index), 263-289 and 525-531 use
   next-var monotonicity to establish precisely these reservation facts.
   The callback then keeps their values, provenance and operand taints.
   Coverage also needs the allocation interval to survive: recover this
   through stmt_state_rel/alloca preservation, not just provenance equality.
   A dormant slot needs coverage, not obsolete value cleanliness, since
   each iteration overwrites it. Normal/Continue require increment/header
   paths; Break requires the exit path; Return uses stmt_exit_ptr.
   Scope pop needs a boundary deriving outer ghost_inv from extended
   ghost_inv plus scope projection and cenv_top_ext, matching S1
   stmtSimForArrayFrame's scope_projection_drop/finally_pop_scope_projection.
   Its exact quantified source/target environments belong to the loop-frame
   owner. The final stmt_frag_ptr obligation is only its old-variable ghost
   frame, not the stronger ghost_kept predicate.
*)

Theorem mload_zero_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
    (OK ((update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  qspecl_then [`mk_inst id MLOAD [Var src] [tmp]`,
    `update_var tmp (mload (w2n a) s) s`, `0`]
    mp_tac (Q.GENL [`i`, `u`, `lo`] straight_line_single_path_ptr) >>
  simp[GSYM mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[] >> reverse conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_read1_def, eval_operand_def]
QED
