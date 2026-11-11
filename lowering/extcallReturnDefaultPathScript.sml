(* Counted execution of the default return branch's code-presence check. *)
Theory extcallReturnDefaultPath
Ancestors
  extCallSeamPrecheck placeMemoryPrimitiveForward storageCopyGasPath
  fragGasSeqAbort fragExec exprLowering exprLoweringProps compileEnv
  venomState venomInst emitHelper emitHelperProps list rich_list

Theorem return_default_check_no_gas:
  compile_extcodesize_check addr a = ((),b) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts a b)
Proof
  simp[compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem return_default_check_counted:
  compile_extcodesize_check addr a = ((),b) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw ==>
  ?u. (if (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) = 0w
       then gas_marked_path F ctx func s 0 (Abort Revert_abort u)
       else gas_marked_path F ctx func s 0 (OK u) /\
         u = (update_var (STRING #"%" (toString a.cs_next_var))
           (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) s)
           with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  strip_tac >> drule_all extcall_codesize_check_run >> strip_tac >>
  drule extcall_codesize_check_shape >> strip_tac >>
  drule return_default_check_no_gas >> strip_tac >>
  Cases_on `(n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code) : bytes32) = 0w`
  >- (gvs[] >>
      `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts a b) (DROP s.vs_inst_idx bb.bb_instructions)` by
        (simp[] >> irule storage_copy_code_prefix >>
         gvs[same_blocks_def, cs_extends_def]) >>
      `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                 ~is_terminator i.inst_opcode) (emitted_insts a b)` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      drule_all run_inst_seq_abort_zero_path >> metis_tac[]) >>
  gvs[] >> irule_at Any straight_line_zero_gas_path >>
  simp[] >> qexistsl_tac [`emitted_insts a b`, `a`] >>
  simp[] >>
  `isPREFIX a.cs_current_insts b.cs_current_insts` by
    gvs[same_blocks_def, cs_extends_def] >>
  gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND,
      same_blocks_def, cs_extends_def]
QED
