Theory dftGasInvScheduledAliases
Ancestors
  dftGasInvAliasNormal dftGasInvAliasPaths dftShape dftCallChecks
  dftScheduleOrder dftRunRel dftWf dftTopoSort dftStructural dftCorrectness dftIdempotent dftDefs venomEffects
  venomWf venomInst contextCodegenRel passSharedDefs list rich_list

Theorem inv_scheduled_inst_wf:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  EVERY inst_wf (dft_block order bb).bb_instructions
Proof
  strip_tac >> irule dft_block_inst_wf >>
  gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem inv_block_distinct_outputs:
  wf_ssa fn /\ MEM bb fn.fn_blocks ==>
  ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >> qpat_x_assum `wf_ssa fn` mp_tac >>
  simp[wf_ssa_def, ssa_form_def, fn_insts_def] >> strip_tac >>
  qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
                ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem inv_scheduled_distinct_outputs:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs)
    (dft_block order bb).bb_instructions))
Proof
  strip_tac >> irule dft_block_outputs_distinct >>
  `wf_ssa fn /\ wf_function fn` by gvs[dft_fn_rel_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def, EVERY_MEM] >>
  `ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `non_pseudo_defs_before_uses bb.bb_instructions` by
    (simp[non_pseudo_defs_before_uses_def] >> metis_tac[wf_ssa_defs_before_uses]) >>
  simp[] >> metis_tac[inv_block_distinct_outputs]
QED

Theorem inv_assign_edge_membership:
  ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) xs)) ==>
  (inv_assign_edge xs a b <=>
   ?v inst. a = Var v /\ MEM inst xs /\ inst.inst_opcode = ASSIGN /\
     inst.inst_outputs = [v] /\ inst.inst_operands = [b])
Proof
  strip_tac >> simp[inv_assign_edge_def] >> eq_tac >> rpt strip_tac
  >- (qexistsl [`v`, `inst`] >>
      metis_tac[producing_inst_unique]) >>
  qexistsl [`v`, `inst`] >> simp[] >>
  irule dftScheduleOrderTheory.producing_inst_distinct_outputs >> simp[]
QED

Theorem inv_flip_assign:
  (flip_operands inst).inst_opcode = ASSIGN ==>
  inst.inst_opcode = ASSIGN
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"] >> simp[flip_operands_def] >>
  namedCases_on `ops` ["", "b remaining"] >> simp[flip_operands_def] >>
  Cases_on `remaining` >> simp[flip_operands_def] >>
  Cases_on `inst.inst_opcode` >>
  simp[is_comparator_def, flip_comparison_opcode_def]
QED

Theorem inv_scheduled_assign_mem:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\ inst.inst_opcode = ASSIGN ==>
  (MEM inst (dft_block order bb).bb_instructions <=> MEM inst bb.bb_instructions)
Proof
  strip_tac >>
  `wf_ssa fn /\ wf_function fn` by gvs[dft_fn_rel_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def, EVERY_MEM] >>
  `ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `non_pseudo_defs_before_uses bb.bb_instructions` by
    (simp[non_pseudo_defs_before_uses_def] >> metis_tac[wf_ssa_defs_before_uses]) >>
  `~is_pseudo inst.inst_opcode /\ ~is_flippable inst.inst_opcode` by
    simp[is_pseudo_def, is_flippable_def, venomEffectsTheory.is_commutative_def,
      is_comparator_def] >>
  eq_tac
  >- (strip_tac >>
      `from_block bb.bb_instructions inst` by
        (irule dft_block_from_orig >> simp[MEM_FILTER] >> metis_tac[]) >>
      gvs[from_block_def] >>
      drule inv_flip_assign >> strip_tac >>
      gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  strip_tac >> irule dft_block_nonflippable_mem >> simp[]
QED

Theorem inv_scheduled_assign_edge:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  (inv_assign_edge (dft_block order bb).bb_instructions a b <=>
   inv_assign_edge bb.bb_instructions a b)
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) bb.bb_instructions))` by
    metis_tac[inv_block_distinct_outputs, dft_fn_rel_def] >>
  `ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs)
    (dft_block order bb).bb_instructions))` by
    metis_tac[inv_scheduled_distinct_outputs] >>
  simp[inv_assign_edge_membership] >> metis_tac[inv_scheduled_assign_mem]
QED

Theorem inv_scheduled_output_origin:
  MEM inst (dft_block order bb).bb_instructions ==>
  ?orig. MEM orig bb.bb_instructions /\
    inst.inst_id = orig.inst_id /\ inst.inst_outputs = orig.inst_outputs /\
    (inst = orig \/ (inst = flip_operands orig /\ is_flippable orig.inst_opcode)) /\
    (is_pseudo inst.inst_opcode <=> is_pseudo orig.inst_opcode)
Proof
  strip_tac >> Cases_on `is_pseudo inst.inst_opcode`
  >- (qexists `inst` >> simp[] >>
      qpat_x_assum `MEM inst _` mp_tac >>
      once_rewrite_tac[dft_block_suffix_decomposition] >>
      simp[MEM_FILTER]) >>
  `from_block bb.bb_instructions inst` by
    (irule dft_block_from_orig >> simp[MEM_FILTER] >> metis_tac[]) >>
  gvs[from_block_def]
  >- (qexists `inst` >> simp[]) >>
  qexists `j` >> simp[flip_operands_is_pseudo]
QED

Theorem inv_scheduled_pseudo_position[local]:
  MEM prod (dft_block order bb).bb_instructions /\ is_pseudo prod.inst_opcode /\
  k < LENGTH (dft_block order bb).bb_instructions /\
  ~is_pseudo (EL k (dft_block order bb).bb_instructions).inst_opcode ==>
  ?m. m < k /\ EL m (dft_block order bb).bb_instructions = prod
Proof
  once_rewrite_tac[dft_block_suffix_decomposition] >> strip_tac >>
  `MEM prod (FILTER (\a. is_pseudo a.inst_opcode) bb.bb_instructions)` by
    gvs[MEM_FILTER] >>
  `LENGTH (FILTER (\a. is_pseudo a.inst_opcode) bb.bb_instructions) <= k` by
    (spose_not_then assume_tac >>
     `k < LENGTH (FILTER (\a. is_pseudo a.inst_opcode) bb.bb_instructions)` by decide_tac >>
     gvs[EL_APPEND1] >>
     qpat_x_assum `k < LENGTH _` (mp_tac o MATCH_MP EL_MEM) >>
     simp[MEM_FILTER]) >>
  qpat_x_assum `MEM prod (FILTER _ _)` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qexists `n` >> simp[EL_APPEND1] >> decide_tac
QED

Theorem inv_scheduled_defs_before_uses:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  np_defs_before_uses (dft_block order bb).bb_instructions
Proof
  strip_tac >>
  `wf_ssa fn /\ wf_function fn` by gvs[dft_fn_rel_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def, EVERY_MEM] >>
  `ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `non_pseudo_defs_before_uses bb.bb_instructions` by
    (simp[non_pseudo_defs_before_uses_def] >> metis_tac[wf_ssa_defs_before_uses]) >>
  `ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) bb.bb_instructions))` by
    metis_tac[inv_block_distinct_outputs] >>
  `ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs)
    (dft_block order bb).bb_instructions))` by
    metis_tac[inv_scheduled_distinct_outputs] >>
  rewrite_tac[np_defs_before_uses_def] >> rpt strip_tac >>
  `MEM prod (dft_block order bb).bb_instructions /\ MEM var prod.inst_outputs` by
    metis_tac[producing_inst_unique] >>
  Cases_on `is_pseudo prod.inst_opcode`
  >- (irule inv_scheduled_pseudo_position >> simp[] >> metis_tac[]) >>
  drule inv_scheduled_output_origin >> strip_tac >>
  `~is_pseudo orig.inst_opcode /\ MEM var orig.inst_outputs` by metis_tac[] >>
  `?m. m < j /\
    ~is_pseudo (EL m (dft_block order bb).bb_instructions).inst_opcode /\
    (EL m (dft_block order bb).bb_instructions).inst_id = orig.inst_id` by
    (irule dft_block_producer_position >> simp[] >> metis_tac[]) >>
  qexists `m` >> simp[] >>
  `from_block bb.bb_instructions (EL m (dft_block order bb).bb_instructions)` by
    (irule dft_block_from_orig >> simp[MEM_FILTER] >>
     qexists `order` >> irule EL_MEM >> decide_tac) >>
  `EL m (dft_block order bb).bb_instructions = orig \/
   EL m (dft_block order bb).bb_instructions = flip_operands orig` by
    (irule from_block_id_cases >> simp[] >>
     qexists `bb.bb_instructions` >> simp[]) >>
  `MEM var (EL m (dft_block order bb).bb_instructions).inst_outputs` by gvs[] >>
  `MEM (EL m (dft_block order bb).bb_instructions)
    (dft_block order bb).bb_instructions` by
    (irule EL_MEM >> decide_tac) >>
  `producing_inst (dft_block order bb).bb_instructions var =
    SOME (EL m (dft_block order bb).bb_instructions)` by
    (irule dftScheduleOrderTheory.producing_inst_distinct_outputs >> simp[]) >>
  gvs[]
QED

Theorem inv_scheduled_alias_prefix:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  inv_alias_prefix (REVERSE (dft_block order bb).bb_instructions)
Proof
  strip_tac >> irule inv_alias_chronological_prefix >>
  `np_defs_before_uses (dft_block order bb).bb_instructions` by
    metis_tac[inv_scheduled_defs_before_uses] >>
  conj_tac
  >- (gvs[np_defs_before_uses_def] >> rpt strip_tac >>
      first_x_assum irule >> simp[is_pseudo_def] >> metis_tac[]) >>
  metis_tac[inv_scheduled_distinct_outputs]
QED

Theorem inv_scheduled_prefix_normal:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
  (same_after_assigns
     (REVERSE (TAKE n (dft_block order bb).bb_instructions)) a b <=>
   resolve_block_assigns
     (REVERSE (TAKE n (dft_block order bb).bb_instructions)) a =
   resolve_block_assigns
     (REVERSE (TAKE n (dft_block order bb).bb_instructions)) b)
Proof
  strip_tac >> irule inv_alias_prefix_normal >>
  irule inv_alias_prefix_take >> metis_tac[inv_scheduled_alias_prefix]
QED
