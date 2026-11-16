(* Syntactic abort intervals, independent of execution completion. *)
Theory dftStaticAbortInterval
Ancestors
  staticAbortDefs dftGasInvExtraction dftGasInvCrossingProbe dftGasInvInversion
  dftRunRel dftScheduleOrder dftStructural dftWf dftDefs passSharedDefs
  dftLifting dftCorrectness
  venomWf venomInst venomEffects venomState list rich_list sorting pred_set

Theorem inv_abort_interval_witness:
  bb.bb_instructions = pre ++ mid ++ w::post /\
  EVERY (\x. ~is_terminator x.inst_opcode /\
    ~MEM x.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
       SSTORE; TSTORE; LOG]) mid /\
  MEM w.inst_opcode [SSTORE; TSTORE; LOG] ==>
  static_abort_at bb (LENGTH pre)
Proof
  strip_tac >> simp[static_abort_at_def] >>
  qexists_tac `LENGTH pre + LENGTH mid` >>
  simp[static_abort_pair_def, EL_APPEND_EQN] >>
  conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  `k - LENGTH pre < LENGTH mid` by decide_tac >>
  `inst = EL (k - LENGTH pre) mid` by
    gvs[get_instruction_def, EL_APPEND_EQN] >>
  gvs[EVERY_EL]
QED

Theorem inv_abort_flip_fields:
  (MEM (flip_operands x).inst_opcode [SSTORE; TSTORE; LOG] <=>
   MEM x.inst_opcode [SSTORE; TSTORE; LOG]) /\
  ((~is_terminator (flip_operands x).inst_opcode /\
    ~MEM (flip_operands x).inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
       SSTORE; TSTORE; LOG]) <=>
   (~is_terminator x.inst_opcode /\
    ~MEM x.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
       SSTORE; TSTORE; LOG]))
Proof
  simp[flip_operands_def] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `x.inst_opcode` >>
  gvs[flip_comparison_opcode_def, is_terminator_def]
QED

Theorem inv_abort_interval_cong:
  LIST_REL (\x y.
    (MEM x.inst_opcode [SSTORE; TSTORE; LOG] <=>
     MEM y.inst_opcode [SSTORE; TSTORE; LOG]) /\
    ((~is_terminator x.inst_opcode /\
      ~MEM x.inst_opcode
        [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
         SSTORE; TSTORE; LOG]) <=>
     (~is_terminator y.inst_opcode /\
      ~MEM y.inst_opcode
        [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
         SSTORE; TSTORE; LOG])))
    bb.bb_instructions bb'.bb_instructions ==>
  (static_abort_at bb n <=> static_abort_at bb' n)
Proof
  simp_tac pure_ss [LIST_REL_EL_EQN] >> strip_tac >>
  simp_tac pure_ss [static_abort_at_def, static_abort_pair_def] >>
  eq_tac >>
  (strip_tac >> qexists_tac `j` >>
   conj_tac >- simp[] >>
   conj_tac >- gvs[] >>
   conj_tac >- metis_tac[] >>
   rpt gen_tac >> strip_tac >>
   `k < LENGTH bb.bb_instructions /\ k < LENGTH bb'.bb_instructions` by decide_tac >>
   qpat_assum `!n'. n' < LENGTH _ ==> _`
     (qspec_then `k` mp_tac) >>
   gvs[get_instruction_def] >> metis_tac[arithmeticTheory.LESS_TRANS])
QED

Theorem inv_abort_from_block_fields:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM x bi /\
  from_block bi y /\ y.inst_id = x.inst_id ==>
  (MEM x.inst_opcode [SSTORE; TSTORE; LOG] <=>
   MEM y.inst_opcode [SSTORE; TSTORE; LOG]) /\
  ((~is_terminator x.inst_opcode /\
    ~MEM x.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
       SSTORE; TSTORE; LOG]) <=>
   (~is_terminator y.inst_opcode /\
    ~MEM y.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
       SSTORE; TSTORE; LOG]))
Proof
  strip_tac >> drule_all from_block_id_cases >>
  strip_tac >> gvs[inv_abort_flip_fields]
QED

Theorem inv_abort_interval_order_witness:
  bb.bb_instructions = pre ++ tail /\ MEM w tail /\
  MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
  (!x. id_before tail x w ==>
    ~is_terminator x.inst_opcode /\
    ~MEM x.inst_opcode
      [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) ==>
  static_abort_at bb (LENGTH pre)
Proof
  strip_tac >>
  Cases_on `SPLITP (\x. MEM x.inst_opcode [SSTORE; TSTORE; LOG]) tail` >>
  rename1 `_ = (front, rest)` >>
  `tail = front ++ rest` by metis_tac[SPLITP_JOIN] >>
  `EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) front /\
   (~NULL rest ==> MEM (HD rest).inst_opcode [SSTORE; TSTORE; LOG])` by
    (drule SPLITP_IMP >> simp[combinTheory.o_DEF]) >>
  `MEM w rest` by (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  Cases_on `rest` >- gvs[] >>
  irule inv_abort_interval_witness >>
  qexistsl [`front`, `t`, `h`] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  reverse conj_tac >- gvs[] >>
  simp_tac pure_ss [EVERY_MEM] >> gen_tac >> disch_tac >>
  `id_before tail x w` by
    (gvs[] >> simp[dftSsaPreserveTheory.id_before_append] >> metis_tac[]) >>
  first_x_assum drule >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem inv_abort_call_effects:
  MEM c.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  Eff_MEMORY IN write_effects c.inst_opcode /\
  (MEM w.inst_opcode [SSTORE; TSTORE; LOG] ==> dft_must_order w c)
Proof
  simp[] >> rpt strip_tac >>
  gvs[write_effects_def, read_effects_def, all_effects_def,
      dft_must_order_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

Theorem inv_abort_normalized_inversion:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ source /\
  EVERY (\i. ~is_pseudo i.inst_opcode) source /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) (pseudos ++ target) /\
  id_before source x y /\ id_before target y x ==>
  ~dft_must_order x y /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode
Proof
  strip_tac >>
  `MEM x source /\ MEM y source` by metis_tac[id_before_mem] >>
  `MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
   id_before (MAP (\i. i.inst_id) bb'.bb_instructions) y.inst_id x.inst_id` by
    (asm_rewrite_tac[MAP_APPEND] >>
     metis_tac[dftSsaPreserveTheory.id_before_map, id_before_append_right]) >>
  drule_all inv_lookup_inversion_swap >> strip_tac >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `~dft_must_order x y` by metis_tac[dft_inversion_not_must_order] >>
  gvs[dft_gas_swap_pair_def]
QED

Theorem inv_abort_order_total:
  MEM x xs /\ MEM y xs /\ x <> y ==>
  id_before xs x y \/ id_before xs y x
Proof
  simp[MEM_EL, id_before_def] >> rpt strip_tac >>
  Cases_on `n < n'`
  >- (disj1_tac >> qexistsl [`n`, `n'`] >> simp[]) >>
  `n' < n` by (Cases_on `n = n'` >> gvs[] >> decide_tac) >>
  disj2_tac >> qexistsl [`n'`, `n`] >> simp[]
QED

Theorem inv_abort_normalized_nonterminator:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ source /\
  EVERY (\i. ~is_pseudo i.inst_opcode) source /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) (pseudos ++ target) /\
  ALL_DISTINCT source /\ PERM target source /\
  id_before target x w ==>
  ~is_terminator x.inst_opcode
Proof
  strip_tac >>
  `ALL_DISTINCT target` by metis_tac[ALL_DISTINCT_PERM] >>
  `x <> w` by metis_tac[id_before_distinct_endpoints] >>
  `MEM x source /\ MEM w source` by metis_tac[id_before_mem, PERM_MEM_EQ] >>
  `id_before source x w \/ id_before source w x` by
    metis_tac[inv_abort_order_total] >-
    (`id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id w.inst_id` by
       (asm_rewrite_tac[MAP_APPEND] >>
        metis_tac[dftSsaPreserveTheory.id_before_map, id_before_append_right]) >>
     irule dft_wf_order_nonterminator >>
     goal_assum (drule_at Any) >>
     gvs[dft_fn_rel_def] >> metis_tac[MEM_APPEND]) >>
  drule_all inv_abort_normalized_inversion >> simp[]
QED

Theorem inv_abort_normalized_call_exclusion:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ source /\
  EVERY (\i. ~is_pseudo i.inst_opcode) source /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) (pseudos ++ (consumed ++ obs::later)) /\
  ALL_DISTINCT source /\ PERM (consumed ++ obs::later) source /\
  inv_memory_observation obs.inst_opcode /\
  MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
  id_before (obs::later) x w /\
  (id_before source x obs \/ id_before source w x) ==>
  ~MEM x.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]
Proof
  strip_tac >> (disch_tac >>
  drule inv_abort_call_effects >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  `id_before (consumed ++ obs::later) x w` by
    metis_tac[id_before_append_right] >>
  `ALL_DISTINCT (consumed ++ obs::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  Cases_on `id_before source w x`
  >- (drule_all inv_abort_normalized_inversion >> metis_tac[]) >>
  `id_before source x obs` by metis_tac[] >>
  `x <> obs` by metis_tac[id_before_distinct_endpoints] >>
  `MEM x later` by
    (qpat_assum `id_before (obs::later) x w`
       (mp_tac o MATCH_MP id_before_mem) >> simp[] >> metis_tac[]) >>
  `id_before (consumed ++ obs::later) obs x` by
    simp[dftSsaPreserveTheory.id_before_append,
         dftSsaPreserveTheory.id_before_cons] >>
  `~dft_must_order x obs` by
    (drule_all inv_abort_normalized_inversion >> simp[]) >>
  drule inv_crossing_candidate_necessary >>
  metis_tac[inv_memory_writer_cannot_cross])
QED

Theorem inv_missing_write_suffix_order:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  fn' = dft_fn fn /\ EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed /\
  inv_memory_observation obs.inst_opcode /\
  (?w. MEM w (FILTER (\i. ~MEM i consumed) srcpre) /\
       MEM w.inst_opcode [SSTORE; TSTORE; LOG]) ==>
  ?w. MEM w (obs::later) /\ MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
    (!x. id_before (obs::later) x w ==> ~is_terminator x.inst_opcode /\
      ~MEM x.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
Proof
  strip_tac >>
  `MEM w srcpre /\ ~MEM w consumed` by gvs[MEM_FILTER] >>
  `MEM w (obs::later)` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `w` mp_tac) >> simp[]) >>
  qexists_tac `w` >> asm_rewrite_tac[] >>
  gen_tac >> strip_tac >>
  `id_before (consumed ++ obs::later) x w` by
    metis_tac[id_before_append_right] >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
   MAP (\i. i.inst_id) (pseudos ++ (consumed ++ obs::later))` by
    simp[MAP_APPEND] >>
  conj_tac
  >- (drule_all inv_abort_normalized_nonterminator >> simp[]) >>
  `id_before (srcpre ++ obs::srcpost) x obs \/
   id_before (srcpre ++ obs::srcpost) w x` suffices_by
    (disch_tac >> drule_all inv_abort_normalized_call_exclusion >> simp[]) >>
  `MEM x (srcpre ++ obs::srcpost)` by metis_tac[id_before_mem, PERM_MEM_EQ] >>
  simp[dftSsaPreserveTheory.id_before_append,
       dftSsaPreserveTheory.id_before_cons] >>
  gvs[MEM_APPEND, MEM] >> metis_tac[]
QED

Theorem inv_abort_source_order_witness:
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  static_abort_at bb (LENGTH pseudos + LENGTH srcpre) ==>
  ?w. MEM w (srcpre ++ obs::srcpost) /\
    MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
    (!x. MEM x (srcpre ++ obs::srcpost) /\
      MEM x.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
      id_before (srcpre ++ obs::srcpost) x obs \/
      id_before (srcpre ++ obs::srcpost) w x)
Proof
  simp_tac pure_ss [static_abort_at_def, static_abort_pair_def] >>
  strip_tac >>
  `LENGTH pseudos <= j /\
   j - LENGTH pseudos < LENGTH (srcpre ++ obs::srcpost)` by gvs[] >>
  `EL j bb.bb_instructions =
   EL (j - LENGTH pseudos) (srcpre ++ obs::srcpost)` by
    (pure_asm_rewrite_tac[] >>
     CONV_TAC (LAND_CONV (REWR_CONV EL_APPEND_EQN)) >> simp[]) >>
  qexists_tac `EL (j - LENGTH pseudos) (srcpre ++ obs::srcpost)` >>
  conj_tac >- metis_tac[MEM_EL] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  `?k. k < LENGTH (srcpre ++ obs::srcpost) /\
       x = EL k (srcpre ++ obs::srcpost)` by metis_tac[MEM_EL] >>
  Cases_on `k < LENGTH srcpre`
  >- (disj1_tac >> simp_tac pure_ss [id_before_def] >>
      qexistsl [`k`, `LENGTH srcpre`] >> simp[EL_APPEND_EQN]) >>
  Cases_on `j < LENGTH pseudos + k`
  >- (disj2_tac >> simp_tac pure_ss [id_before_def] >>
      qexistsl [`j - LENGTH pseudos`, `k`] >> simp[]) >>
  `LENGTH pseudos + LENGTH srcpre <= LENGTH pseudos + k /\
   LENGTH pseudos + k < j` by
    (Cases_on `LENGTH pseudos + k = j` >> gvs[EL_APPEND_EQN] >>
     gvs[] >> decide_tac) >>
  `EL (LENGTH pseudos + k) bb.bb_instructions = x` by
    (pure_asm_rewrite_tac[] >>
     CONV_TAC (LAND_CONV (REWR_CONV EL_APPEND_EQN)) >> simp[]) >>
  `get_instruction bb (LENGTH pseudos + k) = SOME x` by
    (simp_tac pure_ss [get_instruction_def] >>
     `LENGTH pseudos + k < LENGTH bb.bb_instructions` by gvs[] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `!k inst. _` drule_all >>
  gvs[]
QED

Theorem inv_source_prefix_suffix_order:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  fn' = dft_fn fn /\ EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed /\
  inv_memory_observation obs.inst_opcode /\
  static_abort_at bb (LENGTH pseudos + LENGTH srcpre) ==>
  ?w. MEM w (obs::later) /\ MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
    (!x. id_before (obs::later) x w ==> ~is_terminator x.inst_opcode /\
      ~MEM x.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])
Proof
  strip_tac >> drule_all inv_abort_source_order_witness >> strip_tac >>
  `~MEM w consumed` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `MEM w (obs::later)` by metis_tac[PERM_MEM_EQ, MEM_APPEND] >>
  qexists_tac `w` >> asm_rewrite_tac[] >>
  gen_tac >> strip_tac >>
  `id_before (consumed ++ obs::later) x w` by
    metis_tac[id_before_append_right] >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
   MAP (\i. i.inst_id) (pseudos ++ (consumed ++ obs::later))` by
    simp[MAP_APPEND] >>
  conj_tac
  >- (drule_all inv_abort_normalized_nonterminator >> simp[]) >>
  disch_tac >>
  `MEM x (srcpre ++ obs::srcpost)` by metis_tac[id_before_mem, PERM_MEM_EQ] >>
  `id_before (srcpre ++ obs::srcpost) x obs \/
   id_before (srcpre ++ obs::srcpost) w x` by metis_tac[] >>
  metis_tac[inv_abort_normalized_call_exclusion]
QED

Theorem inv_abort_interval_id_bridge:
  dftScheduleOrder$dft_block_rel bb bb' /\
  bb.bb_instructions = pseudos ++ sourcebody /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) sourcebody /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  PERM normalized sourcebody /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) (pseudos ++ normalized) ==>
  (static_abort_at (bb with bb_instructions := pseudos ++ normalized) n <=>
   static_abort_at bb' n)
Proof
  strip_tac >> irule inv_abort_interval_cong >>
  simp_tac pure_ss [LIST_REL_EL_EQN] >>
  `LENGTH bb'.bb_instructions = LENGTH (pseudos ++ normalized)` by
    metis_tac[LENGTH_MAP] >>
  simp[] >> qx_gen_tac `k` >> strip_tac >>
  qabbrev_tac `x = EL k (pseudos ++ normalized)` >>
  qabbrev_tac `y = EL k bb'.bb_instructions` >>
  `k < LENGTH bb'.bb_instructions /\ k < LENGTH (pseudos ++ normalized)` by
    gvs[] >>
  `MEM y bb'.bb_instructions` by (simp[Abbr `y`] >> metis_tac[MEM_EL]) >>
  `MEM x (pseudos ++ normalized)` by
    (simp_tac pure_ss [Abbr `x`] >> metis_tac[MEM_EL]) >>
  `MEM x bb.bb_instructions` by
    (gvs[MEM_APPEND] >> metis_tac[PERM_MEM_EQ]) >>
  `y.inst_id = x.inst_id` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL k`) >>
     simp[EL_MAP, Abbr `x`, Abbr `y`]) >>
  `?j. MEM j bb.bb_instructions /\
    (y = j \/ (y = flip_operands j /\ is_flippable j.inst_opcode))` by
    (qpat_x_assum `dftScheduleOrder$dft_block_rel _ _` mp_tac >>
     simp_tac std_ss [dftScheduleOrderTheory.dft_block_rel_def] >>
     strip_tac >> rename1 `EVERY (from_block _) targetbody` >>
     `MEM y (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) \/
      MEM y targetbody` by metis_tac[MEM_APPEND] >>
     Cases_on `MEM y (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)`
     >- (qexists_tac `y` >> asm_simp_tac std_ss [] >>
         metis_tac[MEM_FILTER]) >>
     `from_block bb.bb_instructions y` by
       (qpat_x_assum `EVERY (from_block _) _` mp_tac >>
        simp_tac std_ss [EVERY_MEM] >> disch_then irule >> gvs[]) >>
     qpat_x_assum `from_block _ y` mp_tac >>
     simp_tac std_ss [from_block_def] >> metis_tac[]) >>
  `j = x` by
    (irule (INST_TYPE [``:'b`` |-> ``:num``] all_distinct_map_mem_inj) >>
     qexistsl [`\i. i.inst_id`, `bb.bb_instructions`] >>
     gvs[]) >>
  gvs[inv_abort_flip_fields] >>
  mp_tac (Q.INST [`x` |-> `j`] inv_abort_flip_fields) >> simp[] >> metis_tac[]
QED

Theorem inv_missing_write_target_abort:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  fn' = dft_fn fn /\ EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed /\
  inv_memory_observation obs.inst_opcode /\
  (?w. MEM w (FILTER (\i. ~MEM i consumed) srcpre) /\
       MEM w.inst_opcode [SSTORE; TSTORE; LOG]) ==>
  static_abort_at bb' (LENGTH pseudos + LENGTH consumed)
Proof
  strip_tac >>
  `?w. MEM w (obs::later) /\ MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
    (!x. id_before (obs::later) x w ==> ~is_terminator x.inst_opcode /\
      ~MEM x.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])` by
    metis_tac[inv_missing_write_suffix_order] >>
  `static_abort_at (bb with bb_instructions := pseudos ++ (consumed ++ obs::later))
    (LENGTH (pseudos ++ consumed))` by
    (irule inv_abort_interval_order_witness >>
     qexists_tac `obs::later` >>
     goal_assum (drule_at Any) >> simp[APPEND_ASSOC]) >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule wf_fn_block_inst_ids_distinct >> goal_assum (drule_at Any) >>
     gvs[dft_fn_rel_def]) >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
   MAP (\i. i.inst_id) (pseudos ++ (consumed ++ obs::later))` by simp[MAP_APPEND] >>
  `static_abort_at (bb with bb_instructions := pseudos ++ (consumed ++ obs::later))
     (LENGTH pseudos + LENGTH consumed) <=>
   static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
    (irule inv_abort_interval_id_bridge >> asm_simp_tac std_ss [] >>
     qexists_tac `srcpre ++ obs::srcpost` >> asm_simp_tac std_ss []) >>
  gvs[]
QED


Theorem inv_source_prefix_target_abort:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  fn' = dft_fn fn /\ EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed /\
  inv_memory_observation obs.inst_opcode /\
  static_abort_at bb (LENGTH pseudos + LENGTH srcpre) ==>
  static_abort_at bb' (LENGTH pseudos + LENGTH consumed)
Proof
  strip_tac >>
  `?w. MEM w (obs::later) /\ MEM w.inst_opcode [SSTORE; TSTORE; LOG] /\
    (!x. id_before (obs::later) x w ==> ~is_terminator x.inst_opcode /\
      ~MEM x.inst_opcode [INVOKE; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2])` by
    metis_tac[inv_source_prefix_suffix_order] >>
  `static_abort_at (bb with bb_instructions := pseudos ++ (consumed ++ obs::later))
    (LENGTH (pseudos ++ consumed))` by
    (irule inv_abort_interval_order_witness >>
     qexists_tac `obs::later` >>
     goal_assum (drule_at Any) >> simp[APPEND_ASSOC]) >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule wf_fn_block_inst_ids_distinct >> goal_assum (drule_at Any) >>
     gvs[dft_fn_rel_def]) >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
   MAP (\i. i.inst_id) (pseudos ++ (consumed ++ obs::later))` by simp[MAP_APPEND] >>
  `static_abort_at (bb with bb_instructions := pseudos ++ (consumed ++ obs::later))
     (LENGTH pseudos + LENGTH consumed) <=>
   static_abort_at bb' (LENGTH pseudos + LENGTH consumed)` by
    (irule inv_abort_interval_id_bridge >> asm_simp_tac std_ss [] >>
     qexists_tac `srcpre ++ obs::srcpost` >> asm_simp_tac std_ss []) >>
  gvs[]
QED
