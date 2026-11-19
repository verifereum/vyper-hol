Theory dftFinitePacketReachability
Ancestors
  dftGasFromListTraceDefs stepWriteFootprintRun contextCodegenRelProps
  contextRawReachable contextCodegenRel venomExecProofs venomExecSemantics
  venomInstProofs venomInst venomState list

Theorem trace_raw_reachable[local]:
  (!p d fuel ctx fn inst s. !vs0.
    raw_reachable vs0 ctx fn inst s ==>
    !key f i t. MEM (key,f,i,t) (trace_step p d fuel ctx fn inst s) ==>
      raw_reachable vs0 ctx f i t) /\
  (!p d fuel ctx fn bb s. !vs0.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (!i. active_inst fn i s ==> raw_reachable vs0 ctx fn i s) ==>
    !key f i t. MEM (key,f,i,t) (trace_block p d fuel ctx fn bb s) ==>
      raw_reachable vs0 ctx f i t) /\
  (!p d fuel ctx fn s. !vs0.
    fn_entry_inv (raw_reachable vs0) ctx fn s ==>
    !key f i t. MEM (key,f,i,t) (trace_blocks p d fuel ctx fn s) ==>
      raw_reachable vs0 ctx f i t)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_raw_reachable[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[Once trace_defs] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  Cases_on `lookup_function decoded0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands decoded1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  rename1 `setup_callee _ _ _ = SOME cs` >> rpt strip_tac >>
  drule_all raw_reachable_callee_entry >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Resume trace_raw_reachable[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_defs] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `active_inst fn inst s` by (irule lookup_instruction_active >> simp[]) >>
  `raw_reachable vs0 ctx fn inst s` by metis_tac[] >>
  simp[Once trace_defs, MEM_APPEND] >> rpt strip_tac
  >- gvs[]
  >- metis_tac[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK out` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  qpat_x_assum `!vs0'. lookup_block _ _ = _ /\ _ ==> _` irule >>
  conj_tac
  >- (rpt strip_tac >> irule raw_reachable_next >> metis_tac[]) >>
  simp[] >> goal_assum drule
QED

Resume trace_raw_reachable[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- simp[] >>
  rename1 `trace_blocks p d (SUC k) ctx fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_defs] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once trace_defs] >> gvs[] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `enters_block fn s (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  rpt strip_tac
  >- (first_x_assum irule >> simp[] >>
      metis_tac[fn_entry_inv_def]) >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK out` >>
  Cases_on `out.vs_halted` >> gvs[] >>
  Cases_on `get_instruction bb (phi_prefix_length bb.bb_instructions)`
  >- (qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `active_inst fn inst (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule lookup_instruction_active >> simp[]) >>
  `raw_reachable vs0 ctx fn inst
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[fn_entry_inv_def] >>
  `lookup_block (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
    fn.fn_blocks = SOME bb` by simp[] >>
  `get_instruction bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_inst_idx =
    SOME inst` by simp[] >>
  drule_all raw_reachable_exec_block_entry >> strip_tac >>
  qpat_x_assum `!vs0. fn_entry_inv _ _ _ out ==> _` irule >> metis_tac[]
QED

Finalise trace_raw_reachable

Theorem dft_packet_trace_raw_reachable:
  !C nm root lbl entry key fn inst s F.
  C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME root /\
  fn_entry_label root = SOME lbl /\ entry.vs_prev_bb = NONE /\
  entry.vs_current_bb = lbl /\ entry.vs_inst_idx = 0 /\
  MEM (key,fn,inst,s) (trace_blocks [] 0 F C root entry) ==>
  raw_reachable entry C fn inst s
Proof
  rpt gen_tac >> strip_tac >> irule (cj 3 trace_raw_reachable) >>
  goal_assum drule >> simp[fn_entry_inv_def] >> rpt strip_tac >>
  irule raw_reachable_entry >>
  conj_tac >- metis_tac[] >> simp[] >>
  `entry with <|vs_prev_bb := NONE; vs_current_bb := lbl|> = entry` by
    gvs[venom_state_component_equality] >> simp[]
QED
