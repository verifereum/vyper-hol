Theory algebraicOptCmpCoherenceProofs
Ancestors
  algebraicOptDefs algebraicOptCmpPairProofs algebraicOptMainShapeProofs
  algebraicOptCmpScanProofs dfgAnalysisProps dfgDefs venomInst list pred_set
  allocaRemapSSA irSupply venomFnScheduleRunner venomInstProps unitShapeDefs
  alist passSharedDefs
  venomFnInstsProofs

(* Only producers actually selected by this scan contribute complemented names. *)
Definition ao_cmp_flipped_def:
  ao_cmp_flipped dfg xs flips =
    {v | ?inst action. MEM inst xs /\ MEM action flips /\
      ao_cmp_flip_cert dfg inst action /\ MEM v inst.inst_outputs}
End

Theorem ao_cmp_flipped_source:
  v IN ao_cmp_flipped dfg xs flips ==>
  ?inst op w after. MEM inst xs /\
    ao_cmp_source dfg inst op w v after
Proof
  simp[ao_cmp_flipped_def, ao_cmp_flip_cert_def] >>
  rpt strip_tac >>
  `v = v'` by (gvs[ao_cmp_source_def]) >> gvs[] >>
  metis_tac[]
QED

Theorem ao_cmp_flipped_read:
  v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips /\
  MEM user (fn_insts fn) /\ MEM v (operand_vars user.inst_operands) ==>
  ?inst op w. MEM inst (fn_insts fn) /\
    ao_cmp_source (dfg_build_function fn) inst op w v user
Proof
  strip_tac >> drule ao_cmp_flipped_source >> strip_tac >>
  drule_all dfg_build_function_uses_complete >>
  qpat_assum `ao_cmp_source _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_source_def]) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_cmp_flipped_read_opcode:
  v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips /\
  MEM user (fn_insts fn) /\ MEM v (operand_vars user.inst_operands) ==>
  user.inst_opcode = ISZERO \/ user.inst_opcode = ASSERT
Proof
  strip_tac >> drule_all ao_cmp_flipped_read >>
  simp[ao_cmp_source_def] >> metis_tac[]
QED

Theorem ao_cmp_flipped_writer:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  v IN ao_cmp_flipped dfg xs flips /\
  MEM writer xs /\ MEM v writer.inst_outputs ==>
  ?op w after. ao_cmp_source dfg writer op w v after
Proof
  strip_tac >> drule ao_cmp_flipped_source >> strip_tac >>
  `MEM v inst.inst_outputs` by (gvs[ao_cmp_source_def]) >>
  `writer = inst` by
    (irule (INST_TYPE [beta |-> ``:string``] all_distinct_flat_map_unique) >>
     qexistsl_tac [`\i. i.inst_outputs`, `xs`, `v`] >> simp[]) >>
  metis_tac[]
QED

Theorem ao_cmp_flipped_writer_opcode:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  v IN ao_cmp_flipped dfg xs flips /\
  MEM writer xs /\ MEM v writer.inst_outputs ==>
  is_comparator writer.inst_opcode
Proof
  strip_tac >> drule_all ao_cmp_flipped_writer >>
  simp[ao_cmp_source_def] >> metis_tac[]
QED

Theorem ao_cmp_flipped_nonconsumer_reads:
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> ISZERO /\
  inst.inst_opcode <> ASSERT ==>
  DISJOINT (set (operand_vars inst.inst_operands))
    (ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips)
Proof
  simp[DISJOINT_DEF, EXTENSION] >>
  metis_tac[ao_cmp_flipped_read_opcode]
QED

Theorem ao_cmp_flipped_noncomparator_writes:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
  MEM inst xs /\ ~is_comparator inst.inst_opcode ==>
  DISJOINT (set inst.inst_outputs) (ao_cmp_flipped dfg xs flips)
Proof
  simp[DISJOINT_DEF, EXTENSION] >>
  metis_tac[ao_cmp_flipped_writer_opcode]
QED

Theorem ao_cmp_covered_inst_vars:
  ir_supply_covers_fn s fn /\ MEM inst (fn_insts fn) ==>
  set (inst_ir_vars inst) SUBSET set s.irs_used_vars
Proof
  simp[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM,
       fn_ir_vars_def, block_ir_vars_def, fn_insts_def,
       MEM_fn_insts_blocks_iff, MEM_FLAT, MEM_MAP, SUBSET_DEF] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem ao_cmp_ignored_inst_vars:
  ir_supply_covers_fn s fn /\ MEM inst (fn_insts fn) ==>
  DISJOINT (set (inst_ir_vars inst))
    (set s'.irs_used_vars DIFF set s.irs_used_vars)
Proof
  strip_tac >> drule_all ao_cmp_covered_inst_vars >>
  simp[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem ao_cmp_ignored_flipped:
  ir_supply_covers_fn s fn ==>
  DISJOINT (ao_cmp_flipped dfg (fn_insts fn) flips)
    (set s'.irs_used_vars DIFF set s.irs_used_vars)
Proof
  rw[DISJOINT_ALT, ao_cmp_flipped_def] >>
  drule_all ao_cmp_covered_inst_vars >>
  simp[SUBSET_DEF, inst_ir_vars_def] >> metis_tac[MEM_APPEND]
QED

Theorem ao_cmp_named_supply_contract:
  !inserts s named s'.
    ir_supply_inst_ok s /\
    ao_name_inserts_supply s inserts = (named,s') ==>
    ir_supply_inst_ok s' /\
    set s.irs_used_vars SUBSET set s'.irs_used_vars /\
    (!a out id v. MEM (a,out,id,v) named ==>
      v IN set s'.irs_used_vars DIFF set s.irs_used_vars)
Proof
  Induct >> simp[Once ao_name_inserts_supply_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  Cases_on `fresh_inst_id s` >> rename1 `fresh_inst_id s = (id,s1)` >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  Cases_on `fresh_ir_var s1` >> rename1 `fresh_ir_var s1 = (v,s2)` >>
  drule fresh_ir_var_contract >> strip_tac >>
  `ir_supply_inst_ok s2` by gvs[ir_supply_inst_ok_def] >>
  Cases_on `ao_name_inserts_supply s2 inserts` >>
  rename1 `ao_name_inserts_supply s2 inserts = (tail,s3)` >>
  gvs[Once ao_name_inserts_supply_def] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_cmp_flip_lookup_cert:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\ MEM inst xs /\
  ao_cmp_flip_scan dfg xs = (flips,removes,inserts) /\
  ALOOKUP flips inst.inst_id = SOME action ==>
  ao_cmp_flip_cert dfg inst (inst.inst_id,action)
Proof
  strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
  drule ao_cmp_flip_scan_origins >>
  simp[ao_cmp_origins_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!a. MEM a flips ==> _` drule >> strip_tac >>
  `i.inst_id = inst.inst_id` by
    (qpat_x_assum `ao_cmp_flip_cert _ _ _` mp_tac >>
     Cases_on `action` >> PairCases_on `r` >>
     simp[ao_cmp_flip_cert_def] >> metis_tac[]) >>
  `i = inst` by
    (`?n. n < LENGTH xs /\ i = EL n xs` by metis_tac[MEM_EL] >>
     `?m. m < LENGTH xs /\ inst = EL m xs` by metis_tac[MEM_EL] >>
     `EL n (MAP (\i. i.inst_id) xs) =
      EL m (MAP (\i. i.inst_id) xs)` by gvs[EL_MAP] >>
     `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  gvs[]
QED

Theorem ao_cmp_remove_lookup_cert:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) =
    (flips,removes,inserts) /\ MEM inst.inst_id removes ==>
  ?producer op w v iz_out.
    MEM producer (fn_insts fn) /\
    ao_cmp_source (dfg_build_function fn) producer op w v inst /\
    inst.inst_opcode = ISZERO /\ inst.inst_outputs = [iz_out] /\
    LENGTH (dfg_get_uses (dfg_build_function fn) iz_out) = 1 /\
    (HD (dfg_get_uses (dfg_build_function fn) iz_out)).inst_opcode <> ASSERT
Proof
  strip_tac >> drule ao_cmp_flip_scan_origins >>
  simp[ao_cmp_origins_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!a. MEM a removes ==> _` drule >> strip_tac >>
  qpat_x_assum `ao_cmp_remove_cert _ _ _` mp_tac >>
  simp[ao_cmp_remove_cert_def] >> strip_tac >>
  `MEM after (fn_insts fn)` by
    (irule (cj 1 dfg_build_function_uses_sound) >> qexists_tac `v` >>
     qpat_x_assum `ao_cmp_source _ _ _ _ _ _` mp_tac >>
     simp[ao_cmp_source_def]) >>
  `after = inst` by
    (`?n. n < LENGTH (fn_insts fn) /\ after = EL n (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `?m. m < LENGTH (fn_insts fn) /\ inst = EL m (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `EL n (MAP (\i. i.inst_id) (fn_insts fn)) =
      EL m (MAP (\i. i.inst_id) (fn_insts fn))` by gvs[EL_MAP] >>
     `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  metis_tac[]
QED

Theorem ao_cmp_named_origin:
  !inserts s named s'.
    ao_name_inserts_supply s inserts = (named,s') ==>
    !a out id v. MEM (a,out,id,v) named ==>
      ?c. MEM (a,out,c) inserts
Proof
  Induct >> simp[Once ao_name_inserts_supply_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  Cases_on `fresh_inst_id s` >> rename1 `fresh_inst_id s = (id,s1)` >>
  Cases_on `fresh_ir_var s1` >> rename1 `fresh_ir_var s1 = (v,s2)` >>
  Cases_on `ao_name_inserts_supply s2 inserts` >>
  gvs[Once ao_name_inserts_supply_def] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem ao_cmp_insert_lookup_cert:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) =
    (flips,removes,inserts) /\ MEM (inst.inst_id,v,c) inserts ==>
  ?producer op w.
    MEM producer (fn_insts fn) /\ producer.inst_id = c /\
    ao_cmp_source (dfg_build_function fn) producer op w v inst /\
    inst.inst_opcode = ASSERT
Proof
  strip_tac >> drule ao_cmp_flip_scan_origins >>
  simp[ao_cmp_origins_def, EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!a. MEM a inserts ==> _` drule >> strip_tac >>
  qpat_x_assum `ao_cmp_insert_cert _ _ _` mp_tac >>
  simp[ao_cmp_insert_cert_def] >> strip_tac >> gvs[] >>
  `MEM after (fn_insts fn)` by
    (irule (cj 1 dfg_build_function_uses_sound) >> qexists_tac `v` >>
     qpat_x_assum `ao_cmp_source _ _ _ _ _ _` mp_tac >>
     simp[ao_cmp_source_def]) >>
  `after = inst` by
    (`?n. n < LENGTH (fn_insts fn) /\ after = EL n (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `?m. m < LENGTH (fn_insts fn) /\ inst = EL m (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `EL n (MAP (\i. i.inst_id) (fn_insts fn)) =
      EL m (MAP (\i. i.inst_id) (fn_insts fn))` by gvs[EL_MAP] >>
     `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  metis_tac[]
QED

Theorem ao_cmp_named_lookup:
  ir_supply_inst_ok s /\
  ao_name_inserts_supply s inserts = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) ==>
  (?c. MEM (a,out,c) inserts) /\
  v IN set s'.irs_used_vars DIFF set s.irs_used_vars
Proof
  strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
  drule_all ao_cmp_named_supply_contract >> strip_tac >>
  drule ao_cmp_named_origin >> metis_tac[]
QED

Theorem ao_cmp_remove_apply:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) =
    (flips,removes,inserts) /\ MEM inst.inst_id removes ==>
  ALOOKUP flips inst.inst_id = NONE /\
  ao_cmp_flip_apply_inst flips removes named inst =
    [inst with inst_opcode := ASSIGN]
Proof
  strip_tac >> drule_all ao_cmp_remove_lookup_cert >> strip_tac >>
  `ALOOKUP flips inst.inst_id = NONE` by
    (Cases_on `ALOOKUP flips inst.inst_id` >> simp[] >>
     drule_all ao_cmp_flip_lookup_cert >>
     simp[ao_cmp_flip_cert_def, ao_cmp_source_def, is_comparator_def]) >>
  simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_insert_apply:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) =
    (flips,removes,inserts) /\
  ir_supply_inst_ok s /\ ao_name_inserts_supply s inserts = (named,s') /\
  ALOOKUP named inst.inst_id = SOME (out,id,v) ==>
  inst.inst_opcode = ASSERT /\
  ALOOKUP flips inst.inst_id = NONE /\ ~MEM inst.inst_id removes /\
  v IN set s'.irs_used_vars DIFF set s.irs_used_vars /\
  ao_cmp_flip_apply_inst flips removes named inst =
    [<|inst_id := id; inst_opcode := ISZERO;
       inst_operands := [Var out]; inst_outputs := [v]|>;
     inst with inst_operands := [Var v]]
Proof
  strip_tac >> drule_all ao_cmp_named_lookup >> strip_tac >>
  drule_all ao_cmp_insert_lookup_cert >> strip_tac >>
  `ALOOKUP flips inst.inst_id = NONE` by
    (Cases_on `ALOOKUP flips inst.inst_id` >> simp[] >>
     drule_all ao_cmp_flip_lookup_cert >>
     simp[ao_cmp_flip_cert_def, ao_cmp_source_def, is_comparator_def]) >>
  `~MEM inst.inst_id removes` by
    (strip_tac >> drule_all ao_cmp_remove_lookup_cert >> simp[]) >>
  simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_producer_apply:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\ MEM inst xs /\
  ao_cmp_flip_scan dfg xs = (flips,removes,inserts) /\
  ALOOKUP flips inst.inst_id = SOME (opc,w,op) ==>
  ao_cmp_flip_cert dfg inst (inst.inst_id,opc,w,op) /\
  ao_cmp_flip_apply_inst flips removes named inst =
    [inst with <|inst_opcode := opc; inst_operands := [op; Lit w]|>]
Proof
  strip_tac >> drule_all ao_cmp_flip_lookup_cert >>
  simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_untouched_apply:
  ALOOKUP flips inst.inst_id = NONE /\ ~MEM inst.inst_id removes /\
  ALOOKUP named inst.inst_id = NONE ==>
  ao_cmp_flip_apply_inst flips removes named inst = [inst]
Proof
  simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_flipped_pair:
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  ao_cmp_flip_scan dfg xs = (flips,removes,inserts) /\
  v IN ao_cmp_flipped dfg xs flips ==>
  ?inst action. MEM inst xs /\ MEM action flips /\
    MEM v inst.inst_outputs /\ ao_cmp_flip_cert dfg inst action /\
    ((?r. MEM r removes /\ ao_cmp_remove_cert dfg inst r) \/
     (?a. MEM a inserts /\ ao_cmp_insert_cert dfg inst a))
Proof
  strip_tac >>
  qpat_x_assum `v IN ao_cmp_flipped _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ao_cmp_flipped_def]) >>
  drule_all ao_cmp_flip_scan_flip_pair >> strip_tac >>
  `i.inst_id = inst.inst_id` by
    (fs[ao_cmp_flip_cert_def] >> gvs[]) >>
  `i = inst` by
    (`?n. n < LENGTH xs /\ i = EL n xs` by metis_tac[MEM_EL] >>
     `?m. m < LENGTH xs /\ inst = EL m xs` by metis_tac[MEM_EL] >>
     `EL n (MAP (\i. i.inst_id) xs) =
      EL m (MAP (\i. i.inst_id) xs)` by gvs[EL_MAP] >>
     `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  metis_tac[]
QED

Theorem ao_cmp_flipped_read_action:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) =
    (flips,removes,inserts) /\
  v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips /\
  MEM user (fn_insts fn) /\ MEM v (operand_vars user.inst_operands) ==>
  MEM user.inst_id removes \/ ?c. MEM (user.inst_id,v,c) inserts
Proof
  strip_tac >> drule_all ao_cmp_flipped_pair >> strip_tac >>
  drule_all dfg_build_function_uses_complete >> strip_tac
  >- (qpat_x_assum `ao_cmp_remove_cert _ _ _` mp_tac >>
      simp[ao_cmp_remove_cert_def] >> strip_tac >>
      qpat_x_assum `ao_cmp_source _ _ _ _ _ _` mp_tac >>
      simp[ao_cmp_source_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `ao_cmp_insert_cert _ _ _` mp_tac >>
  simp[ao_cmp_insert_cert_def] >> strip_tac >>
  qpat_x_assum `ao_cmp_source _ _ _ _ _ _` mp_tac >>
  simp[ao_cmp_source_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_cmp_named_keys:
  !inserts s named s'.
    ao_name_inserts_supply s inserts = (named,s') ==>
    MAP FST named = MAP FST inserts
Proof
  Induct >> simp[Once ao_name_inserts_supply_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  Cases_on `fresh_inst_id s` >> rename1 `fresh_inst_id s = (id,s1)` >>
  Cases_on `fresh_ir_var s1` >> rename1 `fresh_ir_var s1 = (v,s2)` >>
  Cases_on `ao_name_inserts_supply s2 inserts` >>
  gvs[Once ao_name_inserts_supply_def] >> metis_tac[]
QED

Theorem ao_cmp_untouched_reads:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) =
    (flips,removes,inserts) /\
  ao_name_inserts_supply s inserts = (named,s') /\
  MEM inst (fn_insts fn) /\ ~MEM inst.inst_id removes /\
  ALOOKUP named inst.inst_id = NONE ==>
  DISJOINT (set (operand_vars inst.inst_operands))
    (ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) flips)
Proof
  strip_tac >> rewrite_tac[DISJOINT_ALT] >> rpt strip_tac >>
  drule_all ao_cmp_flipped_read_action >> simp[] >> strip_tac >>
  drule ao_cmp_named_keys >>
  strip_tac >> gvs[ALOOKUP_NONE] >>
  metis_tac[MEM_MAP, pairTheory.FST]
QED

Theorem ao_cmp_unselected_writes:
  !fn fs i.
    ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) (fn_insts fn))) /\
    MEM i (fn_insts fn) /\ ALOOKUP fs i.inst_id = NONE ==>
    DISJOINT (set i.inst_outputs)
      (ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[DISJOINT_ALT] >>
  rpt strip_tac >>
  qpat_x_assum `_ IN ao_cmp_flipped _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ao_cmp_flipped_def]) >>
  `i = inst` by
    (irule (INST_TYPE [beta |-> ``:string``] all_distinct_flat_map_unique) >>
     qexistsl_tac [`\j. j.inst_outputs`, `fn_insts fn`, `x`] >> simp[]) >>
  gvs[ao_cmp_flip_cert_def] >>
  gvs[ALOOKUP_NONE, MEM_MAP] >> metis_tac[pairTheory.FST]
QED

Theorem ao_cmp_removed_shape:
  !fn fs rs ins inst.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    MEM inst (fn_insts fn) /\ MEM inst.inst_id rs /\
    LENGTH inst.inst_operands = 1 ==>
    ?v out. inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var v] /\
      inst.inst_outputs = [out] /\
      v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
      out NOTIN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs
Proof
  rpt gen_tac >> strip_tac >> drule_all ao_cmp_flip_scan_remove_pair >>
  strip_tac >>
  qpat_x_assum `ao_cmp_remove_cert _ _ _` mp_tac >>
  simp[ao_cmp_remove_cert_def] >> strip_tac >>
  `MEM after (fn_insts fn) /\ MEM v (operand_vars after.inst_operands)` by
    (irule dfg_build_function_uses_sound >>
     qpat_x_assum `ao_cmp_source _ _ _ _ _ _` mp_tac >>
     simp[ao_cmp_source_def]) >>
  `after = inst` by
    (`?n. n < LENGTH (fn_insts fn) /\ after = EL n (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `?m. m < LENGTH (fn_insts fn) /\ inst = EL m (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `EL n (MAP (\i. i.inst_id) (fn_insts fn)) =
      EL m (MAP (\i. i.inst_id) (fn_insts fn))` by gvs[EL_MAP] >>
     `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  qpat_x_assum `after = inst` SUBST_ALL_TAC >>
  `inst.inst_operands = [Var v]` by
    (Cases_on `inst.inst_operands` >> gvs[] >>
     Cases_on `h` >> gvs[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
  qexistsl_tac [`v`, `iz_out`] >> asm_rewrite_tac[] >> conj_tac
  >- (simp[ao_cmp_flipped_def] >>
      qexistsl_tac [`i`, `f`] >> simp[] >>
      gvs[ao_cmp_source_def]) >>
  `~is_comparator inst.inst_opcode` by simp[is_comparator_def] >>
  drule_all ao_cmp_flipped_noncomparator_writes >>
  simp[DISJOINT_ALT]
QED

Theorem ao_cmp_named_shape:
  !fn fs rs ins s ns s' inst v id z.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply s ins = (ns,s') /\
    MEM inst (fn_insts fn) /\ ALOOKUP ns inst.inst_id = SOME (v,id,z) /\
    LENGTH inst.inst_operands = 1 ==>
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [Var v] /\
    v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs
Proof
  rpt gen_tac >> strip_tac >> drule ALOOKUP_MEM >> strip_tac >>
  drule_all ao_cmp_named_origin >> strip_tac >>
  drule_all ao_cmp_flip_scan_insert_pair >> strip_tac >>
  qpat_x_assum `ao_cmp_insert_cert _ _ _` mp_tac >>
  simp[ao_cmp_insert_cert_def] >> strip_tac >>
  `MEM after (fn_insts fn) /\ MEM v (operand_vars after.inst_operands)` by
    (irule dfg_build_function_uses_sound >>
     qpat_x_assum `ao_cmp_source _ _ _ _ _ _` mp_tac >>
     simp[ao_cmp_source_def]) >>
  `after = inst` by
    (`?n. n < LENGTH (fn_insts fn) /\ after = EL n (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `?m. m < LENGTH (fn_insts fn) /\ inst = EL m (fn_insts fn)`
       by metis_tac[MEM_EL] >>
     `EL n (MAP (\i. i.inst_id) (fn_insts fn)) =
      EL m (MAP (\i. i.inst_id) (fn_insts fn))` by gvs[EL_MAP] >>
     `n = m` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >> gvs[]) >>
  qpat_x_assum `after = inst` SUBST_ALL_TAC >>
  `inst.inst_operands = [Var v]` by
    (Cases_on `inst.inst_operands` >> gvs[] >>
     Cases_on `h` >> gvs[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]) >>
  asm_rewrite_tac[] >> simp[ao_cmp_flipped_def] >>
  qexistsl_tac [`i`, `f`] >> simp[] >> gvs[ao_cmp_source_def]
QED

Theorem ao_cmp_untouched_vars:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
  ao_name_inserts_supply s ins = (ns,s') /\ MEM inst (fn_insts fn) /\
  ALOOKUP fs inst.inst_id = NONE /\ ~MEM inst.inst_id rs /\
  ALOOKUP ns inst.inst_id = NONE ==>
  DISJOINT (set (operand_vars inst.inst_operands))
    (ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs) /\
  DISJOINT (set inst.inst_outputs)
    (ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs)
Proof
  strip_tac >> conj_tac
  >- (irule ao_cmp_untouched_reads >> metis_tac[]) >>
  irule ao_cmp_unselected_writes >> simp[]
QED
