Theory dftPacketBlockAppendNative
Ancestors
  dftGasFromListTraceDefs dftGasFromListOpenTrace dftPacketSameLevelCompose venomInstProofs
  venomExecProofs rich_list arithmetic

Theorem native_open_continuations[local]:
  (!P D fuel C f inst s. !h p d id fn i t.
    h < LENGTH (trace_step P D fuel C f inst s) /\
    EL h (trace_step P D fuel C f inst s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_step P D fuel C f inst s) =
        open_trace p d (D + fuel - d) C fn bt t ++ rest) /\
  (!P D fuel C f bb s. !h p d id fn i t.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (open_trace P D fuel C f bb s) =
        open_trace p d (D + fuel - d) C fn bt t ++ rest) /\
  (!P D fuel C f s. !h p d id fn i t.
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        open_trace p d (D + fuel - d) C fn bt t ++ rest)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_open_continuations[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Resume native_open_continuations[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> qexistsl_tac [`bb`,`[]`] >> simp[]) >>
  rename1 `SUC k` >> gvs[] >>
  Cases_on `k < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      simp[Once open_trace_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      qmatch_goalsub_abbrev_tac `DROP k (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  drule_all open_trace_next >> disch_then assume_tac >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume native_open_continuations[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexistsl_tac [`bt`,`rest`] >>
      gvs[open_trace_def, ADD_CLAUSES]) >>
  Cases_on `exec_block n C bb start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2, ADD_CLAUSES] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise native_open_continuations

Theorem dft_packet_native_next_block_cut:
  !F C root_fn root_entry a d sf bb s i post bb1 sp1 s1 i1
    before after K0 gs0 Kb gsb T.
  T = trace_blocks [] 0 F C root_fn root_entry /\
  T = before ++ [((a,d,i.inst_id),sf,i,s)] ++ after /\
  lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ d < F /\
  exec_block (F-d) C bb s = OK post /\ ~post.vs_halted /\
  lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\
  eval_phis post bb1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions /\
  get_instruction bb1 s1.vs_inst_idx = SOME i1 /\
  trace_gas before = ZIP (K0,gs0) /\
  trace_gas (trace_block a d (F-d) C sf bb s) = ZIP (Kb,gsb) /\
  LENGTH K0 = LENGTH gs0 /\ LENGTH Kb = LENGTH gsb ==>
  ?rest. T = before ++ trace_block a d (F-d) C sf bb s ++
      trace_blocks a d (F-d) C sf post ++ rest /\
    ?before1 after1.
      T = before1 ++ [((a,SUC d,i1.inst_id),sf,i1,s1)] ++ after1 /\
      trace_gas before1 = ZIP (K0 ++ Kb,gs0 ++ gsb)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `T' = trace_blocks [] 0 fuel C root_fn root_entry` >>
  `LENGTH before < LENGTH (trace_blocks [] 0 fuel C root_fn root_entry) /\
   EL (LENGTH before) (trace_blocks [] 0 fuel C root_fn root_entry) =
     ((a,d,i.inst_id),sf,i,s)` by
    (qpat_x_assum `T' = trace_blocks _ _ _ _ _ _` (SUBST1_TAC o SYM) >> simp[EL_APPEND]) >>
  drule_all (cj 3 native_open_continuations) >> strip_tac >>
  `bt = bb` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `trace_blocks [] 0 fuel C root_fn root_entry =
    before ++ trace_block a d (fuel-d) C sf bb s ++
      trace_blocks a d (fuel-d) C sf post ++ rest` by
    (qpat_x_assum `DROP (LENGTH before) _ = _` mp_tac >>
     simp[open_trace_def, APPEND_ASSOC] >>
     qpat_x_assum `_ = trace_blocks [] 0 _ _ _ _` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `?tail. trace_blocks a d (fuel-d) C sf post =
    ((a,SUC d,i1.inst_id),sf,i1,
      sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions)::tail` by
    (Cases_on `fuel-d` >- gvs[] >>
     drule_all trace_blocks_enter >> disch_then assume_tac >> simp[] >>
     `get_instruction bb1
        (sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions).vs_inst_idx = SOME i1` by simp[] >>
     drule trace_block_visit >> simp[]) >>
  qexists_tac `rest` >> simp[] >>
  qexistsl_tac [`before ++ trace_block a d (fuel-d) C sf bb s`,`tail ++ rest`] >>
  simp[APPEND_ASSOC, ZIP_APPEND]
QED

Theorem dft_packet_native_next_partial_cut:
  !F C root_fn root_entry a d sf bb s i post bb1 sp1 s1 i1 k u next
    before after K0 gs0 Kb gsb K1 gs1 T.
  T = trace_blocks [] 0 F C root_fn root_entry /\
  T = before ++ [((a,d,i.inst_id),sf,i,s)] ++ after /\
  lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ d < F /\
  exec_block (F-d) C bb s = OK post /\ ~post.vs_halted /\
  lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\
  eval_phis post bb1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions /\
  get_instruction bb1 s1.vs_inst_idx = SOME i1 /\
  trace_gas before = ZIP (K0,gs0) /\
  trace_gas (trace_block a d (F-d) C sf bb s) = ZIP (Kb,gsb) /\
  LENGTH K0 = LENGTH gs0 /\ LENGTH Kb = LENGTH gsb /\
  s1.vs_inst_idx + k <= LENGTH bb1.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP s1.vs_inst_idx bb1.bb_instructions)) /\
  FOLDR (dft_exec_cons (F-SUC d) C) OK
    (TAKE k (DROP s1.vs_inst_idx bb1.bb_instructions)) s1 = OK u /\
  get_instruction bb1 u.vs_inst_idx = SOME next /\
  trace_gas (trace_block a (SUC d) (F-SUC d) C sf
    (bb1 with bb_instructions := TAKE (s1.vs_inst_idx+k) bb1.bb_instructions) s1) =
      ZIP (K1,gs1) /\ LENGTH K1 = LENGTH gs1 ==>
  ?before1 after1.
    T = before1 ++ [((a,SUC d,next.inst_id),sf,next,u)] ++ after1 /\
    trace_gas before1 = ZIP (K0 ++ Kb ++ K1,gs0 ++ gsb ++ gs1)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_native_next_block_cut >> strip_tac >>
  `lookup_block s1.vs_current_bb sf.fn_blocks = SOME bb1` by
    (gvs[] >> metis_tac[eval_phis_preserves_current_bb]) >>
  rename1 `d < fuel` >>
  irule dft_packet_native_row_cut >> simp[] >>
  qexistsl_tac [`C`,`fuel`] >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `trace_gas _ = _`)) >>
  gvs[APPEND_ASSOC, ADD_COMM] >> metis_tac[]
QED
