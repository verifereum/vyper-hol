Theory sourceArrayBackedgeGasMem
Ancestors
  abiDecoderExecution abiDecoderFrame abiDecoderLoop emitHelperProps fragGasSeqMem fragGasPathMem fragExecMem
  instMemFrontier memSafeRun gasCount venomExecSemantics venomExecProofs
  venomInst venomState emitHelper exprLoweringProps list rich_list words arithmetic

Theorem source_array_backedge_gas_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) /\
  w2n p + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx fn s 0
    (OK (jump_to hdr (mstore (w2n p) (n2w (SUC i))
      (update_var nv (n2w (SUC i)) s))))
Proof
  strip_tac >>
  drule_all abi_decode_increment_prefix >> strip_tac >>
  `eval_operand ip (update_var nv (n2w (SUC i)) s) = SOME p` by
    (Cases_on `ip` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  `step_inst_base (mk_inst id ADD [Var iv; Lit 1w] [nv]) s =
    OK (update_var nv (n2w (SUC i)) s)` by
    (drule_all abi_decode_loop_increment_word >> strip_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_lit]) >>
  `run_inst_seq_mem_ok
     (TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)) s` by
    (simp[abi_decode_backedge_insts_def, run_inst_seq_mem_ok_def,
          inst_dload_in_section_def] >>
     conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     simp[below_frontier_MSTORE, update_var_def] >>
     Cases_on `step_inst_base (mk_inst (id+1) MSTORE [ip; Var nv] [])
       (update_var nv (n2w (SUC i)) s)` >> gvs[update_var_def]) >>
  qpat_x_assum `!id hdr. run_inst_seq _ _ = _`
    (qspecl_then [`id`, `hdr`] assume_tac) >>
  drule_at (Pat `run_inst_seq_mem_ok _ _`) run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then [`mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s)`,
      `ctx`, `fn`, `bb`] mp_tac) >>
  simp[abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def,
       DROP_LENGTH_APPEND] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s 0 (OK u)` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_inst_idx = LENGTH prefix + 2` by
    simp[Abbr `u`, mstore_def, update_var_def] >>
  `gas_path_mem_edge ctx fn u 0 (OK (jump_to hdr u))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     qexists_tac `mk_inst (id+2) JMP [Label hdr] []` >>
     simp[get_instruction_def, EL_APPEND_EQN, abi_decode_backedge_insts_def,
          gas_count_step_def, mem_safe_step_non_invoke, step_inst_non_invoke,
          step_inst_base_opcode_eqs, mk_inst_def, is_terminator_def,
          inst_dload_in_section_def] >>
     conj_tac
     >- (disj2_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     disj2_tac >> disj1_tac >> qexists_tac `hdr` >> simp[]) >>
  `gas_path_mem ctx fn u 0 (OK (jump_to hdr u))` by
    (`~(jump_to hdr u).vs_halted` by simp[jump_to_def] >>
     metis_tac[gas_path_mem_rules, ADD_CLAUSES]) >>
  `jump_to hdr u = jump_to hdr
     (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))` by
    simp[Abbr `u`, jump_to_def, mstore_def, update_var_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
