Theory o1LowerDloadScratchCount
Ancestors
  o1LowerDloadJointRelation o1LowerDloadStackFunctions o1LowerDloadOccurrence
  lowerDloadDefs venomInst list finite_map pred_set o1PassContract contextCodegenRel

Theorem ld_scratch_instruction[local]:
  ld_joint_scratch u fn did aid ==>
  ?inst. MEM inst (fn_insts fn) /\ inst.inst_id = did /\
    inst.inst_opcode = DLOAD
Proof
  simp[ld_joint_scratch_def] >> rpt strip_tac >>
  qexists_tac `EL j (EL k fn.fn_blocks).bb_instructions` >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[MEM_EL]
QED

Theorem ld_frame_scratch_support[local]:
  ld_joint_frame sites X lo owner older u fn fn' H HP tv s t ==>
  !did. (owner,did) IN FDOM X ==>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_id = did /\
      inst.inst_opcode = DLOAD
Proof
  simp[ld_joint_frame_def] >> rpt strip_tac >>
  `?v. FLOOKUP X (owner,did) = SOME v` by
    metis_tac[FLOOKUP_DEF, optionTheory.option_CASES] >>
  PairCases_on `v` >>
  metis_tac[ld_scratch_instruction]
QED

Theorem ld_saved_scratch_support[local]:
  !U stk ts. ld_joint_saved C' sites X lo U stk ts ==>
  !i did. i < LENGTH U /\ ((EL i U).of_owner,did) IN FDOM X ==>
    ?inst. MEM inst (fn_insts (EL i stk).cf_fn) /\
      inst.inst_id = did /\ inst.inst_opcode = DLOAD
Proof
  Induct >> simp[ld_joint_saved_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> gvs[] >> metis_tac[ld_frame_scratch_support]
QED

Theorem ld_sum_distinct_set[local]:
  !xs. ALL_DISTINCT xs ==> SUM (MAP w xs) = SIGMA w (set xs)
Proof
  Induct >> simp[SUM_IMAGE_THM] >> rpt strip_tac >>
  `set xs DELETE h = set xs` by (simp[EXTENSION] >> metis_tac[]) >> simp[]
QED

Theorem ld_sum_members_bound[local]:
  ALL_DISTINCT xs /\ EVERY (\x. MEM x ys) xs ==>
  SUM (MAP w xs) <= SUM (MAP w ys)
Proof
  strip_tac >> drule ld_sum_distinct_set >> disch_then (qspec_then `w` assume_tac) >>
  `set xs SUBSET set ys` by gvs[EVERY_MEM, SUBSET_DEF] >>
  `SIGMA w (set xs) <= SIGMA w (set ys)` by
    (irule SUM_IMAGE_SUBSET_LE >> simp[]) >>
  mp_tac (SUM_IMAGE_LIST_TO_SET_upper_bound |> Q.INST [`f` |-> `w`] |> Q.SPEC `ys`) >> decide_tac
QED

Theorem ld_supported_card_bound[local]:
  !keys xs. FINITE keys /\ (!id. id IN keys ==> MEM id xs) ==>
  CARD keys <= LENGTH xs
Proof
  rpt gen_tac >> strip_tac >>
  `keys SUBSET set xs` by simp[SUBSET_DEF] >>
  `CARD keys <= CARD (set xs)` by metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET] >>
  metis_tac[CARD_LIST_TO_SET, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ld_scratch_enumeration_length[local]:
  !owners fs. LENGTH owners = LENGTH fs ==>
  LENGTH (FLAT (MAP (\p. MAP (\inst. (FST p,inst.inst_id))
    (FILTER (\inst. inst.inst_opcode = DLOAD) (fn_insts (SND p))))
    (ZIP (owners,fs)))) =
  SUM (MAP (\f. LENGTH (FILTER (\inst. inst.inst_opcode = DLOAD)
    (fn_insts f))) fs)
Proof
  Induct >> Cases_on `fs` >> simp[]
QED

Theorem ld_scratch_keys_count[local]:
  !owners fs keys. LENGTH owners = LENGTH fs /\ FINITE keys /\
  (!id. id IN keys ==> ?i inst. i < LENGTH fs /\
    FST id = EL i owners /\ MEM inst (fn_insts (EL i fs)) /\
    inst.inst_opcode = DLOAD /\ SND id = inst.inst_id) ==>
  CARD keys <= SUM (MAP (\f. LENGTH (FILTER (\inst. inst.inst_opcode = DLOAD)
    (fn_insts f))) fs)
Proof
  rpt gen_tac >> strip_tac >>
  drule ld_scratch_enumeration_length >> disch_then (SUBST1_TAC o SYM) >>
  irule ld_supported_card_bound >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  qexistsl_tac [`(EL i owners, EL i fs)`, `inst`] >>
  conj_tac
  >- (simp[MEM_EL] >> qexists_tac `i` >> simp[EL_ZIP]) >>
  simp[MEM_FILTER] >>
  Cases_on `id` >> gvs[]
QED

Theorem ld_joint_scratch_support[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  !id. id IN FDOM X ==> ?i op. i < LENGTH (fn::MAP (\f. f.cf_fn) stk) /\
    FST id = EL i (a::MAP (\f. f.of_owner) U) /\
    MEM op (fn_insts (EL i (fn::MAP (\f. f.cf_fn) stk))) /\
    op.inst_opcode = DLOAD /\ SND id = op.inst_id
Proof
  simp_tac bool_ss [ld_joint_boundary_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM (FST id) (a::MAP (\f. f.of_owner) U)` by
    gvs[ld_joint_geometry_def] >>
  Cases_on `FST id = a`
  >- (`?op. MEM op (fn_insts fn) /\ op.inst_id = SND id /\
         op.inst_opcode = DLOAD` by
        (irule ld_frame_scratch_support >> metis_tac[pairTheory.PAIR]) >>
      qexistsl_tac [`0`, `op`] >> simp[]) >>
  `?j. j < LENGTH U /\ FST id = (EL j U).of_owner` by
    (gvs[MEM_MAP, MEM_EL] >> metis_tac[]) >>
  `LENGTH U = LENGTH stk` by metis_tac[occ_frame_reachable_stack_length] >>
  `?op. MEM op (fn_insts (EL j stk).cf_fn) /\
      op.inst_id = SND id /\ op.inst_opcode = DLOAD` by
    (drule ld_saved_scratch_support >>
     disch_then (qspecl_then [`j`, `SND id`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  qexistsl_tac [`SUC j`, `op`] >> simp[EL_MAP]
QED

Theorem ld_joint_supported_scratch_count[local]:
  !keys. ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ callee_first names C.ctx_functions /\
  FINITE keys /\ (!id. id IN keys ==> id IN FDOM X \/
    (FST id = a /\ ?op. MEM op (fn_insts fn) /\
      op.inst_opcode = DLOAD /\ SND id = op.inst_id)) ==>
  CARD keys <= ctx_dload_count C
Proof
  gen_tac >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `LENGTH U = LENGTH stk` by metis_tac[occ_frame_reachable_stack_length] >>
  `CARD keys <= SUM (MAP (\f. LENGTH (FILTER (\op. op.inst_opcode = DLOAD)
    (fn_insts f))) (fn::MAP (\f. f.cf_fn) stk))` by
    (irule ld_scratch_keys_count >> simp[] >>
     qexists_tac `a::MAP (\f. f.of_owner) U` >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac
     >- (drule ld_joint_scratch_support >> simp[] >> metis_tac[]) >>
     qexistsl_tac [`0`, `op`] >> simp[]) >>
  `ALL_DISTINCT (fn::MAP (\f. f.cf_fn) stk)` by
    (drule_all ld_occ_live_distinct >> metis_tac[ALL_DISTINCT_MAP]) >>
  `EVERY (\g. MEM g C.ctx_functions) (fn::MAP (\f. f.cf_fn) stk)` by
    metis_tac[ld_occ_live_functions] >>
  drule_all ld_sum_members_bound >>
  disch_then (qspec_then `\f. LENGTH (FILTER (\op. op.inst_opcode = DLOAD)
    (fn_insts f))` mp_tac) >>
  simp[ctx_dload_count_def] >> gvs[] >> decide_tac
QED

Theorem ld_joint_scratch_domain[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)} = FDOM X
Proof
  simp[ld_joint_boundary_def, ld_joint_geometry_def, EXTENSION] >>
  metis_tac[]
QED

Theorem ld_joint_scratch_count:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ callee_first names C.ctx_functions ==>
  CARD {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)} <=
    ctx_dload_count C
Proof
  strip_tac >> drule ld_joint_scratch_domain >> disch_then SUBST1_TAC >>
  irule ld_joint_supported_scratch_count >> simp[] >> metis_tac[]
QED

Theorem ld_joint_scratch_credit:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ callee_first names C.ctx_functions /\
  active_inst fn inst s /\ inst.inst_opcode = DLOAD /\
  (a,inst.inst_id) NOTIN FDOM X ==>
  CARD {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)} + 1 <=
    ctx_dload_count C
Proof
  strip_tac >> drule ld_joint_scratch_domain >> disch_then SUBST1_TAC >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `CARD ((a,inst.inst_id) INSERT FDOM X) <= ctx_dload_count C` by
    (drule ld_joint_supported_scratch_count >>
     disch_then (qspecl_then [`names`, `(a,inst.inst_id) INSERT FDOM X`] mp_tac) >>
     simp[] >> impl_tac
     >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     simp[]) >>
  gvs[CARD_INSERT] >> decide_tac
QED
