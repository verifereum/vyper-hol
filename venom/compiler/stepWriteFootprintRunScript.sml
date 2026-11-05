(* Reachability interfaces for bytewise execution framing. *)
Theory stepWriteFootprintRun
Ancestors
  stepWriteFootprintBase stepWriteFootprintForward contextCodegenRelProps codegenRel
  contextRawReachable contextCodegenRel venomExecProofs venomExecSemantics venomInstProofs venomInst calleeTransport

Theorem raw_reachable_callee_entry:
  raw_reachable vs0 ctx caller invoke s /\
  invoke.inst_opcode = INVOKE /\ decode_invoke invoke = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  fn_entry_inv (raw_reachable vs0) ctx callee cs
Proof
  strip_tac >> irule reachability_closed_callee >>
  metis_tac[raw_reachable_closed, raw_reachable_active]
QED

Theorem raw_reachable_exec_block_entry:
  !s inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    raw_reachable vs0 ctx fn inst s /\ exec_block fuel ctx bb s = OK t ==>
    fn_entry_inv (raw_reachable vs0) ctx fn t
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
      simp[fn_entry_inv_def] >> rpt strip_tac >>
      irule raw_reachable_block >>
      metis_tac[raw_reachable_active]) >>
  simp[] >> strip_tac >>
  Cases_on `get_instruction bb (SUC s.vs_inst_idx)`
  >- (qpat_x_assum `exec_block _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
      once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >> simp[]) >>
  rename1 `get_instruction bb (SUC s.vs_inst_idx) = SOME next` >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule lookup_instruction_active >> simp[] >> metis_tac[]) >>
  `raw_reachable vs0 ctx fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule raw_reachable_next >> metis_tac[raw_reachable_active]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (gvs[get_instruction_def, AllCaseEqs()] >> decide_tac)) >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> qexists_tac `next` >> simp[]
QED

Definition footprint_covers_def:
  footprint_covers vs0 ctx i <=>
    ?fn inst s off len.
      raw_reachable vs0 ctx fn inst s /\ ~in_revert_forward fn s /\
      MEM (off,len) (source_memory_write_ranges inst s) /\
      off <= i /\ i < off + len
End

Theorem outside_footprint_ranges:
  ~footprint_covers vs0 ctx i /\ raw_reachable vs0 ctx fn inst s /\
  ~in_revert_forward fn s ==>
  !off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
            ~(off <= i /\ i < off + len)
Proof
  simp[footprint_covers_def] >> metis_tac[]
QED

Theorem run_defs_byte_frame:
  (!fuel ctx inst s. !vs0 i fn ret t.
    ~footprint_covers vs0 ctx i /\ raw_reachable vs0 ctx fn inst s /\
    ~in_revert_forward fn s /\
    (step_inst fuel ctx inst s = OK t \/ step_inst fuel ctx inst s = IntRet ret t) ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory) /\
  (!fuel ctx bb s. !vs0 i fn inst ret t.
    ~footprint_covers vs0 ctx i /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    raw_reachable vs0 ctx fn inst s /\
    (exec_block fuel ctx bb s = OK t \/ exec_block fuel ctx bb s = IntRet ret t) ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory) /\
  (!fuel ctx fn s. !vs0 i ret t.
    ~footprint_covers vs0 ctx i /\ fn_entry_inv (raw_reachable vs0) ctx fn s /\
    run_blocks fuel ctx fn s = IntRet ret t ==>
    read_byte i t.vs_memory = read_byte i s.vs_memory)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_byte_frame[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
      ~(off <= i /\ i < off + len)` by
    metis_tac[outside_footprint_ranges] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  gvs[step_inst_non_invoke] >>
  FIRST [drule step_inst_base_OK_byte_frame,
         drule step_inst_base_IntRet_byte_frame] >> simp[]
QED
Resume run_defs_byte_frame[invoke]:
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[venomExecSemanticsTheory.step_inst_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all raw_reachable_callee_entry >> strip_tac >>
  drule bind_outputs_shared_fields >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  gvs[] >> first_x_assum irule >> qexists_tac `vs0` >> simp[]
QED
Resume run_defs_byte_frame[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~in_revert_forward fn s` by
    (gvs[in_revert_forward_def] >> metis_tac[revert_forward_at_no_normal]) >>
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
Resume run_defs_byte_frame[suffix]:
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
Resume run_defs_byte_frame[run]:
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
Finalise run_defs_byte_frame
