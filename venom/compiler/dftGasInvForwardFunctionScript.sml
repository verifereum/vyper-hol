Theory dftGasInvForwardFunction
Ancestors
  dftGasInvForwardPair dftGasInvForwardOrder dftDefs dftStructural dftCorrectness stackOrderDefs
  venomExecProps venomInst o1PassContract contextCodegenRel finite_map list arithmetic

Theorem inv_forward_block_label[local]:
  (dft_block order bb).bb_label = bb.bb_label
Proof
  simp[dft_block_def]
QED

Theorem inv_forward_lookup_update:
  !bbs. new.bb_label = key ==>
  lookup_block lbl (MAP (\b. if b.bb_label = key then new else b) bbs) =
    if lbl = key then OPTION_MAP (K new) (lookup_block lbl bbs)
    else lookup_block lbl bbs
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt strip_tac >>
  Cases_on `h.bb_label = key` >> Cases_on `h.bb_label = lbl` >>
  Cases_on `lbl = key` >> gvs[lookup_block_def]
QED

Theorem inv_forward_process_other[local]:
  lbl <> key /\
  dft_process_one cfg lr fn st lbl = (st',converged,out_labels) ==>
  lookup_block key st'.dls_blocks = lookup_block key st.dls_blocks /\
  FLOOKUP st'.dls_last_order key = FLOOKUP st.dls_last_order key
Proof
  strip_tac >>
  qpat_x_assum `dft_process_one _ _ _ _ _ = _` mp_tac >>
  simp[dft_process_one_def] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  rename1 `lookup_block lbl st.dls_blocks = SOME current` >>
  `current.bb_label = lbl` by metis_tac[lookup_block_label] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `FLOOKUP st.dls_last_order lbl` >> simp[] >>
  rpt IF_CASES_TAC >> rpt strip_tac >> gvs[] >>
  simp[inv_forward_lookup_update, inv_forward_block_label, FLOOKUP_UPDATE]
QED

Theorem inv_forward_process_same[local]:
  (!cur ft. so_get_stack cfg lr cur ft bb.bb_label = ([],ft)) /\
  ((lookup_block bb.bb_label st.dls_blocks = SOME bb /\
    FLOOKUP st.dls_last_order bb.bb_label = NONE) \/
   (lookup_block bb.bb_label st.dls_blocks = SOME (dft_block [] bb) /\
    FLOOKUP st.dls_last_order bb.bb_label = SOME [])) /\
  dft_process_one cfg lr fn st bb.bb_label = (st',converged,out_labels) ==>
  (lookup_block bb.bb_label st'.dls_blocks = SOME bb /\
    FLOOKUP st'.dls_last_order bb.bb_label = NONE) \/
  (lookup_block bb.bb_label st'.dls_blocks = SOME (dft_block [] bb) /\
    FLOOKUP st'.dls_last_order bb.bb_label = SOME [])
Proof
  strip_tac >>
  qpat_x_assum `dft_process_one _ _ _ _ _ = _` mp_tac >>
  simp[dft_process_one_def] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  simp[inv_forward_lookup_update, inv_forward_block_label, FLOOKUP_UPDATE]
QED

Theorem inv_forward_loop_lookup:
  (!cur ft. so_get_stack cfg lr cur ft bb.bb_label = ([],ft)) /\
  ((lookup_block bb.bb_label st.dls_blocks = SOME bb /\
    FLOOKUP st.dls_last_order bb.bb_label = NONE) \/
   (lookup_block bb.bb_label st.dls_blocks = SOME (dft_block [] bb) /\
    FLOOKUP st.dls_last_order bb.bb_label = SOME [])) ==>
  (lookup_block bb.bb_label
    (FST (FUNPOW (dft_loop_step cfg lr fn) n (st,work,done))).dls_blocks = SOME bb /\
    FLOOKUP (FST (FUNPOW (dft_loop_step cfg lr fn) n (st,work,done))).dls_last_order
      bb.bb_label = NONE) \/
  (lookup_block bb.bb_label
    (FST (FUNPOW (dft_loop_step cfg lr fn) n (st,work,done))).dls_blocks =
      SOME (dft_block [] bb) /\
    FLOOKUP (FST (FUNPOW (dft_loop_step cfg lr fn) n (st,work,done))).dls_last_order
      bb.bb_label = SOME [])
Proof
  map_every qid_spec_tac [`done`, `work`, `st`, `n`] >>
  Induct >> simp[FUNPOW] >> rpt gen_tac >> strip_tac >>
  Cases_on `done`
  >- (simp[dft_loop_step_def] >> metis_tac[]) >>
  simp[dft_loop_step_def] >> Cases_on `work`
  >- (simp[] >> metis_tac[]) >>
  simp[] >> pairarg_tac >> simp[] >>
  ` (lookup_block bb.bb_label st'.dls_blocks = SOME bb /\
      FLOOKUP st'.dls_last_order bb.bb_label = NONE) \/
    (lookup_block bb.bb_label st'.dls_blocks = SOME (dft_block [] bb) /\
      FLOOKUP st'.dls_last_order bb.bb_label = SOME [])` by
    (Cases_on `h = bb.bb_label`
     >- (gvs[] >> irule inv_forward_process_same >> metis_tac[]) >>
     drule_all inv_forward_process_other >> simp[] >> metis_tac[]) >>
  Cases_on `converged` >> simp[] >> metis_tac[]
QED

Theorem inv_forward_fn_lookup:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb i j ==>
  lookup_block lbl (dft_fn fn).fn_blocks = SOME bb \/
  lookup_block lbl (dft_fn fn).fn_blocks = SOME (dft_block [] bb)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `!lr cur ft. so_get_stack (cfg_analyze fn) lr cur ft bb.bb_label = ([],ft)` by
    (rpt gen_tac >> irule inv_order_forward_source_stack >> metis_tac[]) >>
  simp[dft_fn_def] >> pairarg_tac >> simp[] >>
  rename1 `FUNPOW _ _ _ = (final_st,tail)` >>
  ` (lookup_block bb.bb_label final_st.dls_blocks = SOME bb /\
      FLOOKUP final_st.dls_last_order bb.bb_label = NONE) \/
    (lookup_block bb.bb_label final_st.dls_blocks = SOME (dft_block [] bb) /\
      FLOOKUP final_st.dls_last_order bb.bb_label = SOME [])` by
    (qpat_x_assum `FUNPOW _ _ _ = _` (mp_tac o AP_TERM ``FST : dft_loop_state # (string list # bool) -> dft_loop_state``) >>
     simp[] >> disch_then (SUBST1_TAC o SYM) >>
     qpat_assum `bb.bb_label = lbl` (SUBST1_TAC o SYM) >>
     irule inv_forward_loop_lookup >> simp[]) >>
  metis_tac[]
QED

Theorem inv_forward_fn_endpoints:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ dft_fn_rel fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev ==>
  ?bb' k l. lookup_block lbl (dft_fn fn).fn_blocks = SOME bb' /\
    revert_forward_pair bb' k l /\ get_instruction bb' k = SOME copy /\
    get_instruction bb' l = SOME rev
Proof
  strip_tac >>
  drule_all inv_forward_fn_lookup >> strip_tac
  >- metis_tac[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all inv_forward_block_pair >> metis_tac[]
QED

Theorem inv_forward_fn_at:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ dft_fn_rel fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ revert_forward_at bb i /\
  get_instruction bb i = SOME inst ==>
  ?bb' k. lookup_block lbl (dft_fn fn).fn_blocks = SOME bb' /\
    get_instruction bb' k = SOME inst /\ revert_forward_at bb' k
Proof
  strip_tac >>
  gvs[revert_forward_at_def]
  >- (`?rev. get_instruction bb j = SOME rev` by
        metis_tac[revert_forward_pair_def] >>
      drule_all inv_forward_fn_endpoints >> metis_tac[]) >>
  `?copy. get_instruction bb j = SOME copy` by
    metis_tac[revert_forward_pair_def] >>
  drule_all inv_forward_fn_endpoints >> metis_tac[]
QED
