Theory algebraicOptCmpCoherenceProofs
Ancestors
  algebraicOptDefs algebraicOptCmpPairProofs algebraicOptMainShapeProofs
  algebraicOptCmpScanProofs dfgAnalysisProps dfgDefs venomInst list pred_set
  allocaRemapSSA irSupply venomFnScheduleRunner venomInstProps unitShapeDefs
  alist

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
  gvs[] >> metis_tac[]
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
