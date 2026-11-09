(* Operand-parametric finite traversal of the typed-copy condition block. *)
Theory typedCopyRuntimeHeaderMemory
Ancestors
  stmtForRangeMemoryParts fragGasSeqMem fragGasPathMem fragExecMem
  exprLoweringProps venomExecSemantics venomInst venomState instMemFrontier
  words list rich_list finite_map arithmetic memSafeRun

Theorem typed_copy_runtime_loop_header_path_mem:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id LT [Var ctr; bound] [lt];
     mk_inst (id+1) ISZERO [Var lt] [done];
     mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand bound s = SOME (n2w N) /\
  lookup_var ctr s = SOME (n2w k) /\ k <= N /\ N < dimword (:256) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if k < N then body_lbl else exit)
      (update_var done (bool_to_word (~(k < N)))
        (update_var lt (bool_to_word (k < N)) s))))
Proof
  strip_tac >>
  qabbrev_tac `code = [mk_inst id LT [Var ctr; bound] [lt];
    mk_inst (id+1) ISZERO [Var lt] [done]]` >>
  qabbrev_tac `u = update_var done (bool_to_word (~(k < N)))
    (update_var lt (bool_to_word (k < N)) s)` >>
  `k < dimword (:256)` by decide_tac >>
  `run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s` by
    (simp[Abbr `code`, Abbr `u`, run_inst_seq_def, run_inst_seq_mem_ok_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       w2n_n2w, LESS_MOD, bool_to_word_def, inst_dload_in_section_def,
       below_frontier_no_ranges, mk_inst_def] >>
     Cases_on `k < N` >> simp[]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := 2))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := 2) 0
      (OK (jump_to (if bool_to_word (~(k < N)) <> 0w then exit else body_lbl)
        (u with vs_inst_idx := 2)))` by
    (irule for_range_jnz_zero_path_mem >>
     conj_tac >- simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`bb`, `id+2`, `Var done`] >>
     simp[Abbr `u`, update_var_def, get_instruction_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `jump_to (if bool_to_word (~(k < N)) <> 0w then exit else body_lbl)
       (u with vs_inst_idx := 2) = jump_to (if k < N then body_lbl else exit) u` by
    (Cases_on `k < N` >> simp[bool_to_word_def, jump_to_def]) >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
