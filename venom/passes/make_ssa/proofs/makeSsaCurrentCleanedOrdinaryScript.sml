Theory makeSsaCurrentCleanedOrdinary
Ancestors makeSsaCurrentOriginalFinalSlots makeSsaCurrentOriginalSingletonStep makeSsaCurrentOrdinaryIds
  makeSsaCurrentReinsertionNames makeSsaCurrentSourceCuts
  makeSsaCurrentOutputNames makeSsaCurrentCertificate makeSsaCurrentTreeTrace
  makeSsaCurrentCleanupShape makeSsaCurrentRenameTrace makeSsaCurrentSimDefs
  makeSsaCurrentInstructionSingleton makeSsaCurrentValueInvariant
  makeSsaCurrentTreePaths cfgHelpers venomExecProps venomWf venomInst venomExecSemantics stateFrame list

(* The annotation prefix is recovered from the certificate, not supplied
   as an independent renaming oracle by the semantic consumer. *)
Theorem current_certificate_block_annotations:
  current_structural_certificate s fn fn' s' A H events /\
  lookup_block l fn.fn_blocks = SOME old ==>
  ?pre. A l = current_block_annotations old pre
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all current_provenance_annotation_lookup >> metis_tac[]
QED

Theorem current_annotation_prefix_length:
  A l = current_block_annotations old pre /\
  current_event_trace A H
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_edge_shape
    (old with bb_instructions := ip ++ old.bb_instructions) bb ==>
  LENGTH pre = LENGTH ip
Proof
  simp[current_event_trace_def] >> strip_tac >>
  drule current_local_trace_lengths >> strip_tac >>
  drule current_edge_shape_opcodes >> strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH ip + LENGTH old.bb_instructions` by
    (qpat_x_assum `MAP _ _ = MAP _ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  gvs[current_block_annotations_def, current_inserted_annotations_def]
QED

Theorem current_original_step_singleton_ready:
  wf_function fn /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  current_history_valid U Hfinal /\
  LENGTH inst'.inst_outputs =
    LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs /\
  (!k. k < LENGTH inst'.inst_outputs ==>
    current_token_name Hfinal (CurrentOriginal (EL b fn.fn_blocks).bb_label i k) =
      SOME (EL k inst'.inst_outputs)) /\
  current_inst_trace anns (EL i (EL b fn.fn_blocks).bb_instructions)
    s rs H E inst' s' rt H' E' /\
  inst_wf (EL i (EL b fn.fn_blocks).bb_instructions) /\
  (EL i (EL b fn.fn_blocks).bb_instructions).inst_opcode <> PHI ==>
  !st st' after.
    execution_frame st = execution_frame st' /\
    st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
    current_name_agree rs
      (venomInst$operand_vars (EL i (EL b fn.fn_blocks).bb_instructions).inst_operands) st st' /\
    current_singleton_agree (current_instruction_singleton_table fn Hfinal) st st' /\
    step_inst_base (EL i (EL b fn.fn_blocks).bb_instructions) st = OK after ==>
    ?after'. step_inst_base inst' st' = OK after' /\
      current_singleton_agree (current_instruction_singleton_table fn Hfinal) after after' /\
      execution_frame after = execution_frame after' /\
      after.vs_current_bb = after'.vs_current_bb /\ after.vs_prev_bb = after'.vs_prev_bb
Proof
  rpt strip_tac >> metis_tac[current_original_step_singleton]
QED

Theorem current_certificate_ordinary_step_singleton:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_inst_wf fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::later /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j ==>
  ?ip out rs E.
    EVERY (\inst. inst.inst_opcode = PHI) ip /\
    current_edge_shape
      (old with bb_instructions := ip ++ old.bb_instructions) bb /\
    lookup_block l fn'.fn_blocks = SOME out /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (LENGTH ip+i) rs E /\
    (!st st' post.
      current_name_agree rs (venomInst$operand_vars (EL i old.bb_instructions).inst_operands) st st' /\
      current_singleton_agree (current_instruction_singleton_table fn H) st st' /\
      execution_frame st = execution_frame st' /\
      st.vs_current_bb = st'.vs_current_bb /\ st.vs_prev_bb = st'.vs_prev_bb /\
      step_inst_base (EL i old.bb_instructions) st = OK post ==>
      ?post'. step_inst_base (EL (LENGTH ip+i) out.bb_instructions) st' = OK post' /\
        current_singleton_agree (current_instruction_singleton_table fn H) post post' /\
        execution_frame post = execution_frame post' /\
        post.vs_current_bb = post'.vs_current_bb /\ post.vs_prev_bb = post'.vs_prev_bb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_ordinary_position >> strip_tac >>
  drule_all current_certificate_ordinary_id_position >> strip_tac >>
  `LENGTH ip' = LENGTH ip` by
    (imp_res_tac current_edge_shape_opcodes >>
     qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[]) >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >>
  `MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events` by simp[] >>
  `?pre. EVERY (\inst. inst.inst_opcode = PHI) pre /\
    current_edge_shape (old with bb_instructions := pre ++ old.bb_instructions) bb /\
    current_event_trace A H
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)` by
    (drule current_certificate_source_shape >>
     disch_then (qspecl_then [`old`,
       `(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`] mp_tac) >>
     simp[current_event_label_def, current_event_input_block_def]) >>
  drule_all current_certificate_block_annotations >> strip_tac >>
  drule_all current_annotation_prefix_length >> strip_tac >>
  drule_all current_certificate_events_valid >> strip_tac >>
  `current_event_valid A V
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)` by
    metis_tac[EVERY_MEM] >>
  `MEM old fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `?b. b < LENGTH fn.fn_blocks /\ old = EL b fn.fn_blocks` by
    metis_tac[MEM_EL] >>
  `i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_opcode <> PHI` by
    simp[EL_APPEND_EQN] >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `LENGTH pre' = LENGTH ip` by metis_tac[current_annotation_prefix_length] >>
  `LENGTH (EL (LENGTH ip+i) ren).inst_outputs =
    LENGTH (EL i old.bb_instructions).inst_outputs` by
    (drule_all current_event_original_output_length >> asm_rewrite_tac[]) >>
  `!k. k < LENGTH (EL (LENGTH ip+i) ren).inst_outputs ==>
    current_token_name H (CurrentOriginal old.bb_label i k) =
      SOME (EL k (EL (LENGTH ip+i) ren).inst_outputs)` by
    (rpt strip_tac >>
     `k < LENGTH (EL i old.bb_instructions).inst_outputs` by metis_tac[] >>
     drule_all current_event_original_output_name >> asm_rewrite_tac[] >>
     metis_tac[]) >>
  `EL (LENGTH ip+i) out.bb_instructions = EL (LENGTH ip+i) ren` by metis_tac[] >>
  qexistsl_tac [`ip`, `out`, `rs`, `E`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `old = EL b fn.fn_blocks` SUBST_ALL_TAC >>
  qpat_x_assum `EL _ out.bb_instructions = _` SUBST_ALL_TAC >>
  drule_at (Pat `current_inst_trace _ _ _ _ _ _ _ _ _ _ _`)
    current_original_step_singleton_ready >>
  disch_then (qspecl_then [`V`, `H`] mp_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
