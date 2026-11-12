(* Static occurrence identities for private DLOAD allocations. *)
Theory lowerDloadScratchIdentity
Ancestors
  lowerDloadSafetyRelation lowerDloadConfiguredOrigins list rich_list
  irSupply lowerDloadDefs arithmetic

Theorem ld_nested_index_unique[local]:
  !xss a b i j.
    ALL_DISTINCT (FLAT xss) /\ a < LENGTH xss /\ b < LENGTH xss /\
    i < LENGTH (EL a xss) /\ j < LENGTH (EL b xss) /\
    EL i (EL a xss) = EL j (EL b xss) ==>
    a = b /\ i = j
Proof
  Induct_on `xss` >- simp[] >>
  rpt gen_tac >> Cases_on `a` >> Cases_on `b` >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >> gvs[] >>
  metis_tac[ALL_DISTINCT_EL_IMP, MEM_EL, MEM_FLAT]
QED

Theorem ld_fn_index_unique[local]:
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  a < LENGTH fn.fn_blocks /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL a fn.fn_blocks).bb_instructions /\
  j < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  (EL i (EL a fn.fn_blocks).bb_instructions).inst_id =
    (EL j (EL b fn.fn_blocks).bb_instructions).inst_id ==>
  a = b /\ i = j
Proof
  strip_tac >> irule (INST_TYPE [alpha |-> ``:num``] ld_nested_index_unique) >>
  qexists_tac `MAP (\bb. MAP (\inst. inst.inst_id) bb.bb_instructions) fn.fn_blocks` >>
  gvs[fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def, EL_MAP]
QED

Theorem ld_private_functional:
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ALL_DISTINCT (fn_ir_inst_ids f.lf_fn) /\
  ld_private f d ai /\ ld_private f d aj ==> ai = aj
Proof
  simp[ld_private_def] >> rpt strip_tac >> gvs[] >>
  `bi = bi' /\ j = j'` by
    (irule ld_fn_index_unique >> qexists_tac `f.lf_fn` >> simp[] >> metis_tac[]) >>
  gvs[]
QED

Theorem ld_private_position[local]:
  ld_private f d ai ==>
  ?bi j p.
    bi < LENGTH f.lf_fn.fn_blocks /\
    j < LENGTH (EL bi f.lf_fn.fn_blocks).bb_instructions /\
    (EL j (EL bi f.lf_fn.fn_blocks).bb_instructions).inst_id = d /\
    p = LENGTH (FST (lower_dload_insts_supply
      (SND (lower_dload_blocks_supply f.lf_supply (TAKE bi f.lf_fn.fn_blocks)))
      (TAKE j (EL bi f.lf_fn.fn_blocks).bb_instructions))) /\
    bi < LENGTH (ld_image f).fn_blocks /\
    p < LENGTH (EL bi (ld_image f).fn_blocks).bb_instructions /\
    (EL p (EL bi (ld_image f).fn_blocks).bb_instructions).inst_id = ai
Proof
  simp[ld_private_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `lower_dload_function_supply f.lf_supply f.lf_fn` >>
  drule_all lower_dload_function_supply_block_at >> strip_tac >>
  drule_all lower_dload_insts_supply_at >> strip_tac >> gvs[] >>
  qexistsl_tac [`LENGTH pre`,`j`] >>
  simp[ld_image_def, EL_APPEND_EQN]
QED

Theorem ld_private_injective:
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ALL_DISTINCT (fn_ir_inst_ids f.lf_fn) /\
  ld_private f d ai /\ ld_private f e ai ==> d = e
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_ir_inst_ids (ld_image f))` by
    (simp[ld_image_def] >>
     Cases_on `lower_dload_function_supply f.lf_supply f.lf_fn` >>
     drule_all lower_dload_function_supply_fresh >> simp[]) >>
  qpat_x_assum `ld_private f d ai` (strip_assume_tac o MATCH_MP ld_private_position) >>
  qpat_x_assum `ld_private f e ai` (strip_assume_tac o MATCH_MP ld_private_position) >>
  `bi = bi' /\ p = p'` by
    (irule ld_fn_index_unique >> qexists_tac `ld_image f` >> metis_tac[]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `lower_dload_insts_supply u (TAKE j ins)` >>
  Cases_on `lower_dload_insts_supply u (TAKE j ins)` >>
  Cases_on `lower_dload_insts_supply u (TAKE j' ins)` >>
  `j = j'` by
    (irule lower_dload_insts_supply_boundary_unique >>
     gvs[Abbr `ins`] >> metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  gvs[]
QED

Theorem ld_private_cache:
  ir_supply_covers_fn f.lf_supply f.lf_fn /\
  ALL_DISTINCT (fn_ir_inst_ids f.lf_fn) /\
  ld_maps A f /\ ld_private f d ai /\
  FLOOKUP f.lf_src.vs_allocas ai = NONE ==>
  (FLOOKUP f.lf_tgt.vs_allocas ai = NONE <=> d NOTIN f.lf_E)
Proof
  strip_tac >> Cases_on `FLOOKUP f.lf_tgt.vs_allocas ai`
  >- (simp[] >> strip_tac >> drule_all ld_maps_private >> simp[]) >>
  PairCases_on `x` >> simp[] >>
  drule_all ld_maps_target >> strip_tac >> gvs[] >>
  metis_tac[ld_private_injective]
QED

val _ = if List.all (null o hyp)
  [ld_private_functional, ld_private_injective, ld_private_cache]
  then () else raise Fail "private identity boundary has hypotheses";
