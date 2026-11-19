(* Concrete terminal outcomes at the native block evaluator boundary. *)
Theory gasFocusTerminalRow
Ancestors
  dftIndexedExec dftRunRel venomExecSemantics venomInst venomState list rich_list
  arithmetic

Theorem focus_terminal_row_result:
  !fuel C fn entry bb sp zs inst t r.
    lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis entry bb.bb_instructions = OK sp /\
    bb.bb_instructions =
      TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ zs ++ [inst] /\
    EVERY (\i. ~is_terminator i.inst_opcode) zs /\
    FOLDR (dft_exec_cons fuel C) OK zs
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t /\
    is_terminator inst.inst_opcode /\
    step_inst fuel C inst t = r /\
    (!u. r <> OK u)
    ==> run_blocks (SUC fuel) C fn entry = r
Proof
  rpt strip_tac >>
  `phi_prefix_length bb.bb_instructions -
     (LENGTH zs + phi_prefix_length bb.bb_instructions) = 0` by decide_tac >>
  `DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions = zs ++ [inst]` by
    (qpat_x_assum `bb.bb_instructions = _` (mp_tac o AP_TERM
       ``DROP (phi_prefix_length bb.bb_instructions):instruction list -> instruction list``) >>
     simp[DROP_APPEND, LENGTH_TAKE, DROP_TAKE,
          venomExecProofsTheory.phi_prefix_length_le]) >>
  `exec_block fuel C bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r` by
    (`exec_block fuel C bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      dft_exec_suffix fuel C (zs ++ [inst])
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
       (irule dft_exec_suffix_boundary >> simp[]) >>
     simp[dft_exec_suffix_append, dft_exec_prefix_continue] >>
     Cases_on `r` >> gvs[dft_exec_suffix_def]) >>
  simp[run_blocks_unfold, run_block_def] >>
  Cases_on `r` >> gvs[]
QED
