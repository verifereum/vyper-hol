(* Generic instruction identity, availability and block-update facts. *)
Theory venomTransformStructureProps
Ancestors
  venomFnInstsProofs venomInst venomWf venomFnScheduleRunner
  mmSupplySsaProofs mmWfProofs mmCorrectnessProofs dfgCorrectnessProof
  dfgDefs irSupply passSharedDefs unitShapeDefs
  rich_list list sorting
Libs
  wordsLib finite_mapLib stepInstBaseLib

Theorem unique_perm:
  PERM a b ==> (ALL_DISTINCT (FILTER proj (a ++ todo)) =
                 ALL_DISTINCT (FILTER proj (b ++ todo)))
Proof
  strip_tac >> irule ALL_DISTINCT_PERM >>
  irule PERM_FILTER >> simp[PERM_APPEND_IFF]
QED

Theorem build_ids_key:
  !xs dfg.
  (!id i. dfg_get_inst_by_id dfg id = SOME i ==> i.inst_id = id) ==>
  !id i. dfg_get_inst_by_id (dfg_build_insts_rev dfg xs) id = SOME i ==>
    i.inst_id = id
Proof
  Induct >> simp[dfgDefsTheory.dfg_build_insts_rev_def] >> rpt strip_tac >>
  qpat_x_assum `!dfg. _` (qspec_then `dfg_add_inst dfg h` mp_tac) >>
  impl_tac
  >- metis_tac[dfgCorrectnessProofTheory.dfg_add_inst_ids_sound] >>
  disch_then drule >> simp[]
QED

Theorem function_ids_key:
  dfg_get_inst_by_id (dfg_build_function fn0) id = SOME i ==> i.inst_id = id
Proof
  simp[dfgDefsTheory.dfg_build_function_def, dfgDefsTheory.dfg_build_insts_def] >>
  strip_tac >> irule build_ids_key >>
  qexistsl_tac [`dfg_empty`, `REVERSE (fn_insts fn0)`] >>
  simp[dfgDefsTheory.dfg_get_inst_by_id_def, dfgDefsTheory.dfg_empty_def]
QED

Theorem function_ids_exact:
  wf_function fn0 /\ MEM i (fn_insts fn0) ==>
  dfg_get_inst_by_id (dfg_build_function fn0) i.inst_id = SOME i
Proof
  rpt strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_ids_complete >>
  strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_ids_sound >>
  strip_tac >>
  drule function_ids_key >> strip_tac >>
  `inst' = i` by
    (irule venomFnInstsProofsTheory.fn_insts_id_unique >>
     conj_tac >- simp[] >>
     qexists_tac `fn0` >> gvs[venomWfTheory.wf_function_def]) >>
  gvs[]
QED

Theorem nonoriginal_def_absent:
  ~MEM v (irSupply$fn_ir_vars fn0) ==>
  dfg_get_def (dfg_build_function fn0) v = NONE
Proof
  strip_tac >> Cases_on `dfg_get_def (dfg_build_function fn0) v` >> simp[] >>
  drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >> strip_tac >>
  mp_tac (Q.SPECL [`fn0.fn_blocks`, `irSupply$fn_ir_vars fn0`]
    mmSupplySsaProofsTheory.mm_outputs_covered_blocks) >>
  gvs[irSupplyTheory.fn_ir_vars_def, list_subset_def, EVERY_MEM,
      venomInstTheory.fn_insts_def, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem store_not_definition:
  fn_inst_wf fn0 /\ wf_function fn0 /\ MEM u (fn_insts fn0) /\
  u.inst_opcode = MSTORE /\
  dfg_get_def (dfg_build_function fn0) v = SOME li ==> li.inst_id <> u.inst_id
Proof
  strip_tac >> strip_tac >>
  drule dfgCorrectnessProofTheory.dfg_build_function_correct_proof >> strip_tac >>
  `li = u` by
    (irule venomFnInstsProofsTheory.fn_insts_id_unique >> simp[] >>
     qexists_tac `fn0` >> gvs[wf_function_def]) >>
  gvs[fn_inst_wf_def, venomInstTheory.fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  `inst_wf li` by metis_tac[] >> gvs[inst_wf_def]
QED

Theorem available_endpoint_transport:
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  target'.bb_label = target.bb_label /\
  (!db q. MEM db fn.fn_blocks /\ MEM q db.bb_instructions /\
    MEM v q.inst_outputs ==>
    ?db'. MEM db' fn'.fn_blocks /\ db'.bb_label = db.bb_label /\
      MEM q db'.bb_instructions) /\
  def_available_at fn target NONE v ==>
  def_available_at fn' target' NONE v
Proof
  simp[def_available_at_def] >> metis_tac[]
QED

Theorem available_point_transport:
  fn'.fn_blocks = MAP B fn.fn_blocks /\ MEM target fn.fn_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  (!b. MEM b fn.fn_blocks ==> (B b).bb_label = b.bb_label) /\
  (!d n. fn_dominates fn d n ==> fn_dominates fn' d n) /\
  (!db q. MEM db fn.fn_blocks /\ MEM q db.bb_instructions /\
    MEM v q.inst_outputs ==> MEM q (B db).bb_instructions) /\
  (!q a b. a < b /\ b < LENGTH target.bb_instructions /\
    EL a target.bb_instructions = q /\ EL b target.bb_instructions = u /\
    MEM v q.inst_outputs ==>
    ?c d. c < d /\ d < LENGTH (B target).bb_instructions /\
      EL c (B target).bb_instructions = q /\ EL d (B target).bb_instructions = u) /\
  def_available_at fn target (SOME u) v ==>
  def_available_at fn' (B target) (SOME u) v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  qexistsl [`B def_bb`, `def_inst`] >>
  conj_tac >- metis_tac[MEM_MAP] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  `def_bb.bb_label = target.bb_label` by metis_tac[] >>
  `def_bb = target` by metis_tac[mmWfProofsTheory.all_distinct_map_inv] >>
  gvs[] >> metis_tac[]
QED

Theorem future_id_not_prefix:
  ALL_DISTINCT (MAP (\i. i.inst_id) is) /\ n <= r /\ r < LENGTH is ==>
  ~MEM (EL r is).inst_id (MAP (\i. i.inst_id) (TAKE n is))
Proof
  strip_tac >> disch_then (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
  qpat_x_assum `MEM _ (TAKE n is)`
    (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `q < LENGTH (TAKE n is)` >>
  `q < LENGTH is /\ q < n` by gvs[] >>
  `EL q (TAKE n is) = EL q is` by simp[EL_TAKE] >>
  `q = r` by metis_tac[mmCorrectnessProofsTheory.all_distinct_inst_id_idx] >>
  decide_tac
QED

Theorem lookup_block_lupdate:
  !bbs index bb' lbl.
  index < LENGTH bbs /\ ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
  bb'.bb_label = (EL index bbs).bb_label ==>
  lookup_block lbl (LUPDATE bb' index bbs) =
    if lbl = bb'.bb_label then SOME bb' else lookup_block lbl bbs
Proof
  Induct_on `bbs` >> simp[] >> Cases_on `index`
  >- (simp[venomInstTheory.lookup_block_def, FIND_thm, LUPDATE_def] >>
      rpt strip_tac >> gvs[] >> Cases_on `lbl = h.bb_label` >> simp[]) >>
  simp[venomInstTheory.lookup_block_def, FIND_thm, LUPDATE_def] >>
  rpt strip_tac >> gvs[] >>
  `h.bb_label <> (EL n bbs).bb_label` by
    (strip_tac >> qpat_x_assum `~MEM _ _` mp_tac >>
     simp[MEM_MAP] >> metis_tac[EL_MEM]) >>
  Cases_on `lbl = h.bb_label` >> gvs[] >>
  first_x_assum (qspecl_then [`n`,`bb'`,`lbl`] mp_tac) >>
  simp[venomInstTheory.lookup_block_def]
QED

Theorem supply_operand:
  ir_supply_covers_fn supply fn /\ MEM bb fn.fn_blocks /\
  MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==>
  MEM v supply.irs_used_vars
Proof
  rpt strip_tac >>
  `MEM v (irSupply$fn_ir_vars fn)` by
    (simp[irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
       irSupplyTheory.inst_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[passSharedDefsTheory.MEM_operand_vars_eq_Var,
       venomInstTheory.inst_uses_def]) >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM]
QED


