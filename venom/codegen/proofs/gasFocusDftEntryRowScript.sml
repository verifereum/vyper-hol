Theory gasFocusDftEntryRow
Ancestors
  o1DftStageSsa dftContractGas dftRunRel dftScheduleOrder dftStructural dftWf
  dftDefs o1PassContract venomPassSchedule venomWf venomWfProps venomExecProofs
  unitShapeDefs venomInst list rich_list sorting option

(* Translate the ID permutation into positions in the original body. *)
Theorem indexed_body_schedule[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  PERM (MAP (\i. i.inst_id) ys) (MAP (\i. i.inst_id) xs) /\
  EVERY (from_block xs) ys ==>
  ?rho. LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
                    from_block [EL q xs] y) rho ys
Proof
  strip_tac >>
  `LENGTH xs = LENGTH ys` by metis_tac[PERM_LENGTH, LENGTH_MAP] >>
  qabbrev_tac `ids = MAP (\i. i.inst_id) xs` >>
  qabbrev_tac `idx = \id. THE (INDEX_OF id ids)` >>
  `!k. k < LENGTH xs ==> idx ((EL k xs).inst_id) = k` by
    (rpt strip_tac >>
     `INDEX_OF (EL k ids) ids = SOME k` by
       (irule ALL_DISTINCT_INDEX_OF_EL >> simp[Abbr `ids`]) >>
     simp[Abbr `idx`] >>
     pop_assum mp_tac >> simp[Abbr `ids`, EL_MAP]) >>
  `MAP idx ids = COUNT_LIST (LENGTH xs)` by
    simp[LIST_EQ_REWRITE, Abbr `ids`, EL_MAP, LENGTH_COUNT_LIST, EL_COUNT_LIST] >>
  qexists `MAP idx (MAP (\i. i.inst_id) ys)` >> simp[] >>
  conj_tac
  >- metis_tac[Q.SPEC `idx` PERM_MAP] >>
  simp[LIST_REL_EL_EQN, EL_MAP] >> qx_gen_tac `n` >> strip_tac >>
  `from_block xs (EL n ys)` by fs[EVERY_EL] >>
  qpat_x_assum `from_block xs (EL n ys)` mp_tac >>
  rewrite_tac[from_block_def] >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  `?k. k < LENGTH xs /\ j = EL k xs` by metis_tac[MEM_EL] >>
  `idx ((EL k xs).inst_id) = k` by metis_tac[] >>
  gvs[from_block_def]
QED

Theorem focus_dft_entry_row:
  ctx_pass_stage rp (CFP_Simple VP_DFT) view C7 C8 /\
  o1_pre 7 C7 C8 /\ o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  EVERY wf_ssa C7.ctx_functions /\ C7.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME sf /\ fn_entry_label sf = SOME lbl ==>
  ?bb bt ps xs ys rho.
    lookup_block lbl sf.fn_blocks = SOME bb /\
    lookup_block lbl (dft_fn sf).fn_blocks = SOME bt /\ bb.bb_label = lbl /\ bt.bb_label = lbl /\
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    EVERY inst_shape_ok bb.bb_instructions /\
    LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
                    from_block [EL q xs] y) rho ys
Proof
  simp[LET_THM] >> strip_tac >>
  drule_all dft_stage_fn_rel >> strip_tac >>
  `lookup_function nm C8.ctx_functions = SOME (dft_fn sf)` by
    (drule dft_ctx_functions_map >> simp[lookup_function_map]) >>
  `dft_fn_rel sf (dft_fn sf)` by
    (drule dft_fn_rel_lookup_function >>
     disch_then (qspec_then `nm` mp_tac) >> simp[OPTREL_def]) >>
  `?bb. lookup_block lbl sf.fn_blocks = SOME bb` by
    (Cases_on `sf.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  `MEM bb sf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `LIST_REL dftScheduleOrder$dft_block_rel sf.fn_blocks (dft_fn sf).fn_blocks /\
   wf_function sf /\ fn_pseudos_prefix sf` by fs[dft_fn_rel_def] >>
  drule dft_block_rel_lookup_block >>
  disch_then (qspec_then `lbl` mp_tac) >> simp[OPTREL_def, AllCaseEqs()] >>
  disch_then (qx_choose_then `bt` strip_assume_tac) >>
  `pseudos_prefix bb` by metis_tac[fn_pseudos_prefix_def] >>
  pop_assum mp_tac >> simp[venomWfPropsTheory.pseudos_prefix_split] >>
  disch_then (qx_choose_then `ps` (qx_choose_then `xs` strip_assume_tac)) >>
  `FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs /\
   FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
   FILTER (\i. ~is_pseudo i.inst_opcode) ps = []` by
    simp[FILTER_EQ_ID, FILTER_EQ_NIL] >>
  qpat_x_assum `dftScheduleOrder$dft_block_rel bb bt` mp_tac >>
  simp[dftScheduleOrderTheory.dft_block_rel_def, FILTER_APPEND] >> strip_tac >>
  rename1 `EVERY (from_block (ps ++ xs)) ys` >>
  `EVERY (from_block xs) ys /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys` by
    (fs[EVERY_MEM, from_block_def, MEM_APPEND] >> metis_tac[flip_operands_is_pseudo]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (drule_all wf_fn_block_inst_ids_distinct >> simp[ALL_DISTINCT_APPEND]) >>
  drule_all indexed_body_schedule >>
  disch_then (qx_choose_then `sched` strip_assume_tac) >>
  `o1_fn_shape C7 sf` by metis_tac[o1_ctx_shape_def, EVERY_MEM, lookup_function_MEM] >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (`EVERY inst_shape_ok (fn_insts_blocks sf.fn_blocks)` by
       fs[o1_fn_shape_def, fn_shape_ok_def, fn_insts_def] >>
     pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
     `MEM i (fn_insts_blocks sf.fn_blocks)` by
       (irule MEM_fn_insts_blocks >> qexists `bb` >> asm_rewrite_tac[]) >>
     qpat_x_assum `EVERY inst_shape_ok (fn_insts_blocks _)` mp_tac >> simp[EVERY_MEM]) >>
  qexistsl [`ps`, `xs`, `ys`, `sched`] >> gvs[EVERY_APPEND]
QED
