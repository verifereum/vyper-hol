Theory dftGasInvForwardEffects
Ancestors
  dftNonSsa dftScheduleOrder dftRunRel venomEffects dftDefs
  dftCorrectness finite_map list rich_list passSharedDefs venomInst
  contextCodegenRel venomExecSemantics arithmetic

Theorem inv_abort_scan_nofail_lookup[local]:
  !xs acc runs inst.
    EVERY (\a. a.inst_id = inst.inst_id ==>
      dft_abort_kind a.inst_opcode = NoFail) xs ==>
    FLOOKUP (FST (FOLDL abort_run_dep_step (acc,runs) xs)) inst.inst_id =
    FLOOKUP acc inst.inst_id
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `dft_abort_kind h.inst_opcode = NoFail` >>
  simp[abort_run_dep_step_def] >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem inv_dft_eda_nofail_lookup:
  ALL_DISTINCT (MAP (\a. a.inst_id) bi) /\ MEM inst bi /\
  dft_abort_kind inst.inst_opcode = NoFail ==>
  FLOOKUP (dft_eda bi) inst.inst_id = FLOOKUP (build_eda bi) inst.inst_id
Proof
  strip_tac >> simp[dft_eda_def, add_abort_run_deps_def] >>
  irule inv_abort_scan_nofail_lookup >> simp[EVERY_MEM, MEM_FILTER] >>
  rpt strip_tac >>
  `a = inst` by metis_tac[dftCorrectnessTheory.all_distinct_map_mem_inj] >>
  gvs[]
QED

Theorem inv_build_eda_present:
  ALL_DISTINCT (MAP (\a. a.inst_id) bi) /\ MEM inst bi /\
  ~is_pseudo inst.inst_opcode ==>
  ?ds. FLOOKUP (build_eda bi) inst.inst_id = SOME ds
Proof
  strip_tac >>
  `MEM inst (FILTER (\a. ~is_pseudo a.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `?s1 s2. FILTER (\a. ~is_pseudo a.inst_opcode) bi = s1 ++ inst::s2` by
    metis_tac[MEM_SPLIT] >>
  simp[build_eda_def, pairTheory.UNCURRY] >>
  qpat_assum `FILTER _ _ = _` (fn th => rewrite_tac[th]) >>
  simp[FOLDL_APPEND] >>
  pairarg_tac >> simp[] >>
  `~MEM inst.inst_id (MAP (\a. a.inst_id) s2)` by
    ( `ALL_DISTINCT (MAP (\a. a.inst_id)
         (FILTER (\a. ~is_pseudo a.inst_opcode) bi))` by
        metis_tac[all_distinct_map_filter] >>
      gvs[ALL_DISTINCT_APPEND]) >>
  simp[effect_scan_lookup_preserved, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem inv_assign_eda_lookup:
  ALL_DISTINCT (MAP (\a. a.inst_id) bi) /\ MEM inst bi /\
  inst.inst_opcode = ASSIGN ==>
  FLOOKUP (dft_eda bi) inst.inst_id = SOME []
Proof
  strip_tac >>
  `read_effects inst.inst_opcode = {} /\
   write_effects inst.inst_opcode = {} /\
   dft_abort_kind inst.inst_opcode = NoFail /\ ~is_pseudo inst.inst_opcode` by
    simp[read_effects_def, write_effects_def, empty_effects_def,
         dft_abort_kind_def, is_pseudo_def] >>
  drule_all inv_dft_eda_nofail_lookup >> disch_then SUBST1_TAC >>
  drule_all inv_build_eda_present >> strip_tac >>
  drule_all build_eda_pure_lookup >> simp[]
QED

Theorem inv_assign_effect_step:
  inst.inst_opcode = ASSIGN ==> compute_effect_deps et inst = ([],et)
Proof
  simp[compute_effect_deps_def, read_effects_def, write_effects_def,
       empty_effects_def, effects_to_list_def, nub_first_def, nub_def]
QED

Theorem inv_copy_memory_writer:
  copy.inst_opcode = RETURNDATACOPY ==>
  FLOOKUP (SND (compute_effect_deps et copy)).et_last_write Eff_MEMORY = SOME copy
Proof
  simp[compute_effect_deps_def, read_effects_def, write_effects_def,
       effects_to_list_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem inv_revert_effect_deps:
  rev.inst_opcode = REVERT /\ copy.inst_id <> rev.inst_id /\
  FLOOKUP et.et_last_write Eff_MEMORY = SOME copy ==>
  FST (compute_effect_deps et rev) = [copy]
Proof
  simp[compute_effect_deps_def, read_effects_def, write_effects_def,
       empty_effects_def, effects_to_list_def, nub_first_def, nub_def]
QED

Theorem inv_assign_effect_scan:
  !xs acc et. EVERY (\a. a.inst_opcode = ASSIGN) xs ==>
  SND (FOLDL (\(m,s) a.
    (m |+ (a.inst_id, FST (compute_effect_deps s a)),
     SND (compute_effect_deps s a))) (acc,et) xs) = et
Proof
  Induct >> simp[] >> rpt strip_tac >> simp[inv_assign_effect_step]
QED

Theorem inv_forward_build_eda_split:
  ALL_DISTINCT (MAP (\a. a.inst_id) (pre ++ copy::mid ++ rev::post)) /\
  copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT /\
  EVERY (\a. a.inst_opcode = ASSIGN) mid ==>
  FLOOKUP (build_eda (pre ++ copy::mid ++ rev::post)) rev.inst_id = SOME [copy]
Proof
  strip_tac >>
  `copy.inst_id <> rev.inst_id /\
   ~MEM rev.inst_id (MAP (\a. a.inst_id) post)` by
    gvs[ALL_DISTINCT_APPEND, MEM_MAP] >>
  simp[build_eda_def, FILTER_APPEND, is_pseudo_def, FOLDL_APPEND,
       pairTheory.UNCURRY] >>
  qmatch_goalsub_abbrev_tac `FOLDL scan start (FILTER _ pre)` >>
  Cases_on `FOLDL scan start (FILTER (\a. ~is_pseudo a.inst_opcode) pre)` >>
  rename1 `_ = (acc,et)` >> simp[] >>
  `FILTER (\a. ~is_pseudo a.inst_opcode) mid = mid` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >> gvs[EVERY_MEM, is_pseudo_def]) >>
  simp[] >>
  Cases_on `FOLDL scan
    (acc |+ (copy.inst_id, FST (compute_effect_deps et copy)),
     SND (compute_effect_deps et copy)) mid` >>
  rename1 `_ = (acc',et')` >> simp[] >>
  `et' = SND (compute_effect_deps et copy)` by
    (drule inv_assign_effect_scan >>
     disch_then (qspecl_then
       [`acc |+ (copy.inst_id, FST (compute_effect_deps et copy))`,
        `SND (compute_effect_deps et copy)`] mp_tac) >>
     gvs[Abbr `scan`]) >>
  `FST (compute_effect_deps et' rev) = [copy]` by
    (irule inv_revert_effect_deps >> simp[inv_copy_memory_writer]) >>
  `~MEM rev.inst_id
     (MAP (\a. a.inst_id) (FILTER (\a. ~is_pseudo a.inst_opcode) post))` by
    (gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  simp[Abbr `scan`, effect_scan_lookup_preserved, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem inv_forward_eda_lookup:
  ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions) /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev ==>
  FLOOKUP (dft_eda bb.bb_instructions) rev.inst_id = SOME [copy]
Proof
  strip_tac >>
  `i < j /\ j < LENGTH bb.bb_instructions /\ i < LENGTH bb.bb_instructions /\
   copy = EL i bb.bb_instructions /\ rev = EL j bb.bb_instructions /\
   copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `TAKE j bb.bb_instructions = TAKE i bb.bb_instructions ++ [copy] ++
     TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)` by
    (qspec_then `SUC i` (qspec_then `TAKE j bb.bb_instructions` mp_tac) TAKE_DROP >>
     pure_rewrite_tac[TAKE_TAKE, DROP_TAKE] >>
     simp[TAKE_EL_SNOC, ADD1, TAKE_TAKE, EL_TAKE, SNOC_APPEND,
          Excl "TAKE_DROP"]) >>
  `bb.bb_instructions = TAKE i bb.bb_instructions ++ copy::
     TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions) ++
     rev::DROP (SUC j) bb.bb_instructions` by
    (qspec_then `SUC j` (qspec_then `bb.bb_instructions` mp_tac) TAKE_DROP >>
     simp[TAKE_EL_SNOC, ADD1, SNOC_APPEND, Excl "TAKE_DROP"]) >>
  `EVERY (\a. a.inst_opcode = ASSIGN)
     (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions))` by
    (simp[EVERY_EL, LENGTH_TAKE, LENGTH_DROP] >>
     qx_gen_tac `k` >> strip_tac >>
     `i < k + SUC i /\ k + SUC i < j /\
      k + SUC i < LENGTH bb.bb_instructions` by decide_tac >>
     `get_instruction bb (k + SUC i) =
        SOME (EL (k + SUC i) bb.bb_instructions)` by simp[get_instruction_def] >>
     simp[EL_TAKE, EL_DROP] >> metis_tac[revert_forward_pair_def]) >>
  `MEM rev bb.bb_instructions` by metis_tac[MEM_EL] >>
  `dft_abort_kind rev.inst_opcode = NoFail` by simp[dft_abort_kind_def] >>
  drule_all inv_dft_eda_nofail_lookup >> disch_then SUBST1_TAC >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qpat_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
  disch_tac >> irule inv_forward_build_eda_split >> simp[]
QED

Theorem inv_assign_all_deps:
  ALL_DISTINCT (MAP (\a. a.inst_id) bi) /\ MEM inst bi /\
  inst.inst_opcode = ASSIGN ==>
  (MEM dep (inst_all_deps bi order (dft_eda bi) inst) <=>
   MEM dep (inst_data_deps bi order inst))
Proof
  strip_tac >> drule_all inv_assign_eda_lookup >>
  simp[inst_all_deps_def, nub_first_def, MEM_nub]
QED

Theorem inv_forward_all_deps:
  ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions) /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev ==>
  (MEM dep (inst_all_deps bb.bb_instructions order (dft_eda bb.bb_instructions) rev) <=>
   MEM dep (inst_data_deps bb.bb_instructions order rev) \/ dep = copy)
Proof
  strip_tac >> drule_all inv_forward_eda_lookup >>
  simp[inst_all_deps_def, nub_first_def, MEM_nub] >> metis_tac[]
QED
