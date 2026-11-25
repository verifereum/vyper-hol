(* Transport a single return-fragment edge across the proof-only marker. *)
Theory entryReturnMarkerEdge
Ancestors
  entryReturnMarker createSizeCutRegion fragGasOriginPtr ptrSafeRun
  createSizePrefixReplay createSizeCutCode fragExec fragFuel fragGasOrigin
  fragGasPathPtr ptrDiscipline contextCodegenRel memSafeRun gasEvents frameGasEvents
  venomExecProofs venomExecSemantics
  venomInst venomState list rich_list arithmetic

Triviality marker_prefix_fetch:
  k <= LENGTH bb.bb_instructions /\ j <= k ==>
  get_instruction (bb with bb_instructions := TAKE k bb.bb_instructions ++
    return_marker_inst id :: DROP k bb.bb_instructions) j =
  (if j = k then SOME (return_marker_inst id) else get_instruction bb j)
Proof
  simp[get_instruction_def, EL_APPEND_EQN, LENGTH_TAKE_EQ, LENGTH_DROP] >>
  strip_tac >> Cases_on `j = k` >>
  fs[EL_TAKE, DECIDE ``j <= k /\ j <> k ==> j < k``] >> decide_tac
QED

Triviality marker_prefix_take:
  n <= k /\ k <= LENGTH xs ==>
  TAKE n (TAKE k xs ++ m :: DROP k xs) = TAKE n xs
Proof
  strip_tac >> `n <= LENGTH (TAKE k xs)` by simp[LENGTH_TAKE_EQ] >>
  simp[listTheory.TAKE_APPEND1, TAKE_TAKE_MIN, MIN_DEF] >>
  IF_CASES_TAC >> fs[LESS_OR_EQ]
QED

Triviality marker_forward_pair:
  k <= LENGTH bb.bb_instructions /\ i < k /\
  revert_forward_pair (bb with bb_instructions := TAKE k bb.bb_instructions ++
    return_marker_inst id :: DROP k bb.bb_instructions) i j ==>
  revert_forward_pair bb i j
Proof
  simp[revert_forward_pair_def] >> strip_tac >>
  `get_instruction (bb with bb_instructions := TAKE k bb.bb_instructions ++
     return_marker_inst id :: DROP k bb.bb_instructions) k =
     SOME (return_marker_inst id)` by simp[marker_prefix_fetch] >>
  `j < k` by
    (Cases_on `j = k` >- gvs[return_marker_inst_def, mk_inst_def] >>
     CCONTR_TAC >> `k < j` by decide_tac >>
     res_tac >> gvs[return_marker_inst_def, mk_inst_def]) >>
  `!u. u < k ==>
     get_instruction (bb with bb_instructions := TAKE k bb.bb_instructions ++
       return_marker_inst id :: DROP k bb.bb_instructions) u =
     get_instruction bb u` by (rpt strip_tac >> drule marker_prefix_fetch >> simp[]) >>
  `i < k /\ i <= k /\ j <= k /\ j - SUC i + SUC i = j` by decide_tac >>
  conj_tac
  >- (rpt strip_tac >> rename1 `i < u` >> `u < k` by decide_tac >> metis_tac[]) >>
  qexistsl_tac [`inst1`, `inst2`, `p`, `src`, `rds`, `p'`, `rds'`] >>
  simp[] >>
  qpat_x_assum `same_after_assigns _ rds _` mp_tac >>
  qpat_x_assum `same_after_assigns _ p _` mp_tac >>
  qpat_x_assum `same_after_assigns _ src _` mp_tac >>
  simp[listTheory.TAKE_DROP_SWAP, marker_prefix_take] >> metis_tac[]
QED

Triviality marker_revert_forward:
  k <= LENGTH bb.bb_instructions /\ j < k /\
  revert_forward_at (bb with bb_instructions := TAKE k bb.bb_instructions ++
    return_marker_inst id :: DROP k bb.bb_instructions) j ==>
  revert_forward_at bb j
Proof
  rw[revert_forward_at_def]
  >- metis_tac[marker_forward_pair] >>
  `j' < k` by (fs[revert_forward_pair_def] >> decide_tac) >>
  metis_tac[marker_forward_pair]
QED

Triviality marker_block_labels:
  !bbs. MAP (\b. b.bb_label) (return_marker_blocks l k id bbs) =
        MAP (\b. b.bb_label) bbs
Proof
  Induct >> simp[return_marker_blocks_def] >> rw[]
QED

Triviality marker_successor_revert:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (s.vs_current_bb = l ==> s.vs_inst_idx < k /\ k <= LENGTH bb.bb_instructions) /\
  about_to_revert (return_marker_fn fn l k id) inst s ==>
  about_to_revert fn inst s
Proof
  simp[about_to_revert_def] >> strip_tac >> simp[] >>
  `ALL_DISTINCT (fn_labels (return_marker_fn fn l k id))` by
    fs[fn_labels_def, return_marker_fn_def, marker_block_labels] >>
  drule return_marker_fetch >>
  disch_then (qspecl_then [`l`, `k`, `id`] strip_assume_tac) >>
  rename1 `lookup_block _ (return_marker_fn fn l k id).fn_blocks = SOME mb` >>
  `get_instruction mb (SUC s.vs_inst_idx) = SOME rinst` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >> simp[active_inst_def] >>
     strip_tac >> fs[fn_labels_def] >>
     `lookup_block s.vs_current_bb (return_marker_fn fn l k id).fn_blocks = SOME bb'`
       by (irule MEM_lookup_block >> simp[]) >>
     gvs[get_instruction_def]) >>
  `get_instruction bb (SUC s.vs_inst_idx) = SOME rinst` by
    (Cases_on `s.vs_current_bb = l` >> gvs[] >>
     Cases_on `SUC s.vs_inst_idx = k`
     >- gvs[return_marker_inst_def, mk_inst_def] >>
     `SUC s.vs_inst_idx < k` by decide_tac >> metis_tac[]) >>
  qexists_tac `rinst` >> simp[active_inst_def] >>
  qexists_tac `bb` >>
  fs[get_instruction_def, AllCaseEqs()] >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED

Triviality marker_current_fetch:
  lookup_block s.vs_current_bb (return_marker_fn fn l k id).fn_blocks = SOME mb /\
  get_instruction mb s.vs_inst_idx = SOME inst /\
  (s.vs_current_bb = l ==> s.vs_inst_idx < k) /\
  (!b. lookup_block l fn.fn_blocks = SOME b ==> k <= LENGTH b.bb_instructions) ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst /\
       (s.vs_current_bb = l ==> k <= LENGTH bb.bb_instructions) /\
       (revert_forward_at mb s.vs_inst_idx ==> revert_forward_at bb s.vs_inst_idx)
Proof
  simp[return_marker_lookup, AllCaseEqs()] >> strip_tac >> gvs[]
  >- (rename1 `lookup_block l fn.fn_blocks = SOME bb` >>
      `k <= LENGTH bb.bb_instructions /\ s.vs_inst_idx <= k /\ s.vs_inst_idx <> k` by
        (conj_tac >- metis_tac[] >> decide_tac) >>
      fs[marker_prefix_fetch] >> strip_tac >> irule marker_revert_forward >>
      qexistsl_tac [`id`, `k`] >> simp[] >> decide_tac) >>
  simp[]
QED

Triviality marker_ptr_check:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb (return_marker_fn fn l k id).fn_blocks = SOME mb /\
  (s.vs_current_bb = l ==> s.vs_inst_idx < k /\ k <= LENGTH bb.bb_instructions) /\
  (revert_forward_at mb s.vs_inst_idx ==> revert_forward_at bb s.vs_inst_idx) /\
  inst.inst_opcode <> INVOKE /\
  (ctx_has_dalloca mc <=> ctx_has_dalloca ctx) /\
  ptr_safe_step D lo fuel mc (return_marker_fn fn l k id) PG G tn inst s ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  strip_tac >>
  `in_revert_forward (return_marker_fn fn l k id) s ==> in_revert_forward fn s`
    by simp[in_revert_forward_def] >>
  `about_to_revert (return_marker_fn fn l k id) inst s ==> about_to_revert fn inst s`
    by (strip_tac >> irule marker_successor_revert >> metis_tac[]) >>
  qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once ptr_safe_step_def] >> rewrite_tac[Once ptr_safe_step_def] >>
  simp[ptr_inst_ok_def, step_inst_non_invoke] >>
  Cases_on `in_revert_forward fn s` >>
  Cases_on `about_to_revert fn inst s` >>
  fs[access_ok_def, taint_ok_def] >> strip_tac >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Triviality marker_phi_zero:
  phi_prefix_length xs = 0 ==>
  phi_prefix_length (TAKE k xs ++ return_marker_inst id :: DROP k xs) = 0
Proof
  Cases_on `k` >> Cases_on `xs` >>
  simp[phi_prefix_length_def, return_marker_inst_def, mk_inst_def, AllCaseEqs()]
QED

Triviality marker_target_phi:
  no_phi_fn fn /\
  lookup_block t.vs_current_bb (return_marker_fn fn l k id).fn_blocks = SOME mt ==>
  ?target. lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    phi_prefix_length mt.bb_instructions = 0 /\
    phi_prefix_length target.bb_instructions = 0 /\
    eval_phis t mt.bb_instructions = OK t /\
    eval_phis t target.bb_instructions = OK t /\
    entry_prov (return_marker_fn fn l k id) t G = entry_prov fn t G /\
    entry_taint_vars (return_marker_fn fn l k id) t tn = entry_taint_vars fn t tn
Proof
  strip_tac >>
  `?b. lookup_block t.vs_current_bb fn.fn_blocks = SOME b` by
    (qpat_x_assum `lookup_block _ (return_marker_fn _ _ _ _).fn_blocks = _` mp_tac >>
     simp[return_marker_lookup, AllCaseEqs()] >> metis_tac[]) >>
  `phi_prefix_length b.bb_instructions = 0` by
    (fs[no_phi_fn_def, EVERY_MEM] >> metis_tac[lookup_block_MEM]) >>
  `phi_prefix_length mt.bb_instructions = 0` by
    (qpat_x_assum `lookup_block _ (return_marker_fn _ _ _ _).fn_blocks = _` mp_tac >>
     simp[return_marker_lookup] >> rw[] >> simp[marker_phi_zero]) >>
  simp[eval_phis_no_phi] >>
  simp[entry_prov_def, entry_taint_vars_def] >>
  Cases_on `mt.bb_instructions` >> Cases_on `b.bb_instructions` >>
  gvs[phi_prefix_length_def, phis_prov_def, phis_taint_def, AllCaseEqs()]
QED

Triviality marker_region_before_cut:
  create_cut_region a b s /\
  (s.vs_current_bb <> b.cs_current_bb \/ s.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b)) ==>
  (s.vs_current_bb = b.cs_current_bb ==> s.vs_inst_idx < LENGTH b.cs_current_insts)
Proof
  simp[create_cut_region_def, MEM_MAP] >> strip_tac >> strip_tac >> gvs[]
  >- metis_tac[MEM_LAST_NOT_NIL] >>
  `emitted_blocks a b <> []` by (strip_tac >> gvs[FRONT_DEF]) >>
  metis_tac[MEM_FRONT_NOT_NIL]
QED

Triviality marker_origin_without_check:
  gas_origin_edge T explicit ctx fn s marks r ==>
  gas_origin_edge F explicit ctx fn s marks r
Proof
  rewrite_tac[gas_origin_edge_def] >> metis_tac[]
QED

Theorem return_marker_edge_transfer:
  create_cut_code {} a b /\ fn_has_code a b fn /\ no_phi_fn fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b)) /\
  EVERY (\i. i.inst_opcode <> INVOKE) (frag_code a b) /\
  (ctx_has_dalloca mc <=> ctx_has_dalloca ctx) /\
  create_cut_region a b s /\
  (s.vs_current_bb <> b.cs_current_bb \/ s.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  gas_origin_ptr_edge (D,lo,explicit,mc,
    return_marker_fn fn b.cs_current_bb (LENGTH b.cs_current_insts) id,PG)
    (s,G,tn) marks (r,G',tn') ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') /\
  !v. r = OK v ==>
    create_prefix_step a b explicit ctx fn s marks v /\ create_cut_region a b v
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `mb` (qx_choose_then `inst`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `!bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
        LENGTH b.cs_current_insts <= LENGTH bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[IS_PREFIX_LENGTH]) >>
  `(s.vs_current_bb = b.cs_current_bb ==>
    s.vs_inst_idx < LENGTH b.cs_current_insts)` by
    (strip_tac >> drule_all_then ACCEPT_TAC marker_region_before_cut) >>
  drule_all marker_current_fetch >>
  disch_then (qx_choose_then `bb` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_all create_cut_region_rules >> strip_tac >>
  `MEM inst (frag_code a b) /\ inst.inst_id IN frag_ids a b` by metis_tac[] >>
  `inst.inst_opcode <> INVOKE` by fs[EVERY_MEM] >>
  `(s.vs_current_bb = b.cs_current_bb ==>
    s.vs_inst_idx < LENGTH b.cs_current_insts /\
    LENGTH b.cs_current_insts <= LENGTH bb.bb_instructions)` by simp[] >>
  `ptr_safe_step D lo fuel ctx fn PG G tn inst s` by
    (drule_all_then ACCEPT_TAC marker_ptr_check) >>
  `revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s` by
    (fs[mem_safe_step_non_invoke] >> metis_tac[]) >>
  `step_inst fuel ctx inst s = middle` by fs[step_inst_non_invoke] >>
  `marks = MAP (\key. key IN explicit) (gas_events_step fuel ctx fn.fn_name inst s)` by
    fs[gas_events_step_plain, return_marker_fn_def] >>
  `LENGTH marks = gas_count_step fuel ctx inst s` by
    (qpat_x_assum `marks = MAP _ (gas_events_step _ ctx _ _ _)` SUBST1_TAC >>
     simp[gas_events_length]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn')` by
    (qpat_x_assum `(?t. middle = OK t /\ ~is_terminator _ /\ _) \/ _` strip_assume_tac
     >- (`ghost_step fuel ctx PG G tn inst s = ghost_step fuel mc PG G tn inst s` by
           metis_tac[ghost_step_non_invoke] >>
         pure_rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
         conj_tac >> (conj_tac >- simp[]) >> qexistsl_tac [`fuel`, `bb`, `inst`, `middle`] >> simp[])
     >- (pure_rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
         conj_tac >> (conj_tac >- simp[]) >> qexistsl_tac [`fuel`, `bb`, `inst`, `middle`] >> simp[])
     >- (drule_all marker_target_phi >> strip_tac >> gvs[] >>
         pure_rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
         conj_tac >> (conj_tac >- simp[]) >> qexistsl_tac [`fuel`, `bb`, `inst`, `OK t`] >> simp[] >> metis_tac[])
     >- (pure_rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
         conj_tac >> (conj_tac >- simp[]) >> qexistsl_tac [`fuel`, `bb`, `inst`, `middle`] >> simp[] >> metis_tac[])
     >> pure_rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
        conj_tac >> (conj_tac >- simp[]) >> qexistsl_tac [`fuel`, `bb`, `inst`, `middle`] >> simp[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >> gen_tac >> disch_then SUBST_ALL_TAC >>
  qpat_assum `gas_origin_ptr_edge (_,_,_,ctx,fn,_) _ _ _`
    (assume_tac o CONJUNCT1 o REWRITE_RULE[gas_origin_ptr_edge_def]) >>
  drule_then assume_tac marker_origin_without_check >>
  (conj_tac
   >- (rewrite_tac[create_prefix_step_def] >> qexistsl_tac [`bb`, `inst`] >> simp[])) >>
  `(MEM b.cs_current_bb (added_labels a b) ==>
    !target. lookup_block b.cs_current_bb fn.fn_blocks = SOME target ==>
    phi_prefix_length target.bb_instructions <= LENGTH b.cs_current_insts)` by
    (rpt strip_tac >> fs[no_phi_fn_def, EVERY_MEM] >>
     `MEM target fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     res_tac >> simp[]) >>
  first_x_assum drule >> disch_then (drule_all_then ACCEPT_TAC)
QED
