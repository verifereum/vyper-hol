(* Successful memory writes outside pending-abort prefixes have witnesses
   outside those prefixes, including writes performed by INVOKE callees. *)
Theory stepWriteFootprintAbort
Ancestors
  staticAbortExec staticAbortDefs stepWriteFootprintRun
  stepWriteFootprintBase stepWriteFootprintForward unitMemInv
  contextRawReachable contextCodegenRel contextCodegenRelProps codegenRel venomExecSemantics
  venomExecProofs venomInstProofs venomInst venomState calleeTransport

Definition step_write_footprint_abort_def:
  step_write_footprint_abort ctx vs <=>
    !fn inst s s' fuel i.
      raw_reachable vs ctx fn inst s /\ ~in_revert_forward fn s /\
      ~in_static_abort_prefix fn s /\
      step_inst fuel ctx inst s = OK s' /\
      read_byte i s.vs_memory <> read_byte i s'.vs_memory ==>
      ?fn2 inst2 s2 off len.
        raw_reachable vs ctx fn2 inst2 s2 /\ ~in_revert_forward fn2 s2 /\
        ~in_static_abort_prefix fn2 s2 /\
        MEM (off,len) (source_memory_write_ranges inst2 s2) /\
        off <= i /\ i < off + len
End

(* The range hypothesis deliberately excludes both kinds of abort prefix.
   Block clauses obtain the exclusions from their normal outcome. *)
Theorem run_defs_abort_byte_frame[local]:
  (!fuel ctx inst s. !vs0 i fn ret t.
    (!fn2 inst2 s2 off len.
       raw_reachable vs0 ctx fn2 inst2 s2 /\ ~in_revert_forward fn2 s2 /\
       ~in_static_abort_prefix fn2 s2 /\
       MEM (off,len) (source_memory_write_ranges inst2 s2) ==>
       ~(off <= i /\ i < off + len)) /\
    raw_reachable vs0 ctx fn inst s /\ ~in_revert_forward fn s /\
    ~in_static_abort_prefix fn s /\
    (step_inst fuel ctx inst s = OK t \/ step_inst fuel ctx inst s = IntRet ret t) ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory) /\
  (!fuel ctx bb s. !vs0 i fn inst ret t.
    (!fn2 inst2 s2 off len.
       raw_reachable vs0 ctx fn2 inst2 s2 /\ ~in_revert_forward fn2 s2 /\
       ~in_static_abort_prefix fn2 s2 /\
       MEM (off,len) (source_memory_write_ranges inst2 s2) ==>
       ~(off <= i /\ i < off + len)) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    raw_reachable vs0 ctx fn inst s /\
    (exec_block fuel ctx bb s = OK t \/ exec_block fuel ctx bb s = IntRet ret t) ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory) /\
  (!fuel ctx fn s. !vs0 i ret t.
    (!fn2 inst2 s2 off len.
       raw_reachable vs0 ctx fn2 inst2 s2 /\ ~in_revert_forward fn2 s2 /\
       ~in_static_abort_prefix fn2 s2 /\
       MEM (off,len) (source_memory_write_ranges inst2 s2) ==>
       ~(off <= i /\ i < off + len)) /\
    fn_entry_inv (raw_reachable vs0) ctx fn s /\
    run_blocks fuel ctx fn s = IntRet ret t ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_abort_byte_frame[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
      ~(off <= i /\ i < off + len)` by metis_tac[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  gvs[step_inst_non_invoke] >>
  FIRST [drule step_inst_base_OK_byte_frame,
         drule step_inst_base_IntRet_byte_frame] >> simp[]
QED
Resume run_defs_abort_byte_frame[invoke]:
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.step_inst_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all raw_reachable_callee_entry >> strip_tac >>
  drule bind_outputs_shared_fields >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  gvs[] >> first_x_assum irule >> qexists_tac `vs0` >> simp[] >> metis_tac[]
QED
Resume run_defs_abort_byte_frame[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~in_revert_forward fn s` by
    (gvs[in_revert_forward_def] >> metis_tac[revert_forward_at_no_normal]) >>
  `~in_static_abort_prefix fn s` by
    (gvs[in_static_abort_prefix_def] >> metis_tac[static_abort_at_no_normal]) >>
  qpat_x_assum `_ \/ _` mp_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[] >>
  Cases_on `?ir u. step_inst fuel ctx inst s = IntRet ir u`
  >- (pop_assum strip_assume_tac >> simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  `read_byte i u.vs_memory = read_byte i s.vs_memory` by metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[AllCaseEqs()] >>
  suspend "suffix"
QED
Resume run_defs_abort_byte_frame[suffix]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  (Cases_on `get_instruction bb (SUC s.vs_inst_idx)`
   >- (qpat_x_assum `run_block_non_phis _ _ _ _ = _` mp_tac >>
       once_rewrite_tac[GSYM venomExecSemanticsTheory.exec_block_def] >>
       once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[])) >>
  rename1 `get_instruction bb (SUC s.vs_inst_idx) = SOME next` >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule lookup_instruction_active >> simp[] >> metis_tac[]) >>
  `raw_reachable vs0 ctx fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule raw_reachable_next >> metis_tac[raw_reachable_active]) >>
  metis_tac[]
QED
Resume run_defs_abort_byte_frame[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.run_blocks_def] >>
  Cases_on `fuel` >> simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `enters_block fn s (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  drule enters_block_memory >> simp[] >> strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  (Cases_on `get_instruction bb (phi_prefix_length bb.bb_instructions)`
   >- (qpat_x_assum `run_block_non_phis _ _ _ _ = _` mp_tac >>
       once_rewrite_tac[GSYM venomExecSemanticsTheory.exec_block_def] >>
       once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[])) >>
  rename1 `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME head` >>
  `active_inst fn head (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule lookup_instruction_active >> simp[]) >>
  `raw_reachable vs0 ctx fn head
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[fn_entry_inv_def] >>
  (Cases_on `?u. run_block_non_phis n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u`
   >- (pop_assum strip_assume_tac >>
       rename1 `run_block_non_phis _ _ _ _ = OK u` >>
       `fn_entry_inv (raw_reachable vs0) ctx fn u` by
         (irule raw_reachable_exec_block_entry >>
          qexistsl_tac [`bb`, `n`, `head`,
            `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
          simp[] >> metis_tac[]) >>
       gvs[] >> metis_tac[])) >>
  gvs[] >> metis_tac[]
QED
Finalise run_defs_abort_byte_frame

Theorem step_write_footprint_abort_holds:
  !ctx vs. step_write_footprint_abort ctx vs
Proof
  rw[step_write_footprint_abort_def] >>
  spose_not_then assume_tac >>
  `read_byte i s'.vs_memory = read_byte i s.vs_memory` suffices_by metis_tac[] >>
  irule (cj 1 run_defs_abort_byte_frame) >>
  qexistsl_tac [`ctx`, `fn`, `fuel`, `inst`, `ARB`, `vs`] >>
  simp[] >> metis_tac[]
QED
