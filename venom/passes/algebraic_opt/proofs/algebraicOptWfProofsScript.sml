Theory algebraicOptWfProofs
Ancestors
  algebraicOptDefs passSharedDefs venomInst venomWf venomFnScheduleRunner unitShapeDefs
  dfgAnalysisProps algebraicOptSupplyProofs algebraicOptShapeProofs algebraicOptMainShapeProofs
  list pred_set alist

Theorem ao_transform_inst_fresh_ids:
  inst.inst_id < s.irs_next_inst /\
  ao_alloc_fresh s = (fr, s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  EVERY (\id. id < s'.irs_next_inst)
    (MAP (\i. i.inst_id) (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  (!id. MEM id (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) ==>
    id = inst.inst_id \/ s.irs_next_inst <= id)
Proof
  strip_tac >> drule ao_alloc_fresh_props >> strip_tac >>
  drule ao_transform_inst_layout >>
  disch_then (qspecl_then [`targets`,`ra`,`lbl`,`inst`,`idx`,`dfg`] mp_tac) >>
  simp[ao_rewrite_layout_def] >> strip_tac >>
  gvs[MAP_EQ_CONS]
QED

Theorem ao_transform_inst_supply_id_origin:
  ao_alloc_fresh s = (fr,s') /\
  MEM id (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) ==>
  id = inst.inst_id \/ s.irs_next_inst <= id
Proof
  strip_tac >> drule ao_alloc_fresh_props >> strip_tac >>
  drule ao_transform_inst_layout >>
  disch_then (qspecl_then [`targets`,`ra`,`lbl`,`inst`,`idx`,`dfg`] mp_tac) >>
  simp[ao_rewrite_layout_def] >> strip_tac >>
  gvs[MAP_EQ_CONS]
QED

Theorem ao_transform_insts_supply_id_origin:
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  !id. MEM id (MAP (\i. i.inst_id) outs) ==>
    MEM id (MAP (\i. i.inst_id) insts) \/ s.irs_next_inst <= id
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[] >> gen_tac >> strip_tac
  >- metis_tac[ao_transform_inst_supply_id_origin] >>
  first_x_assum drule >> disch_then (qspec_then `id` mp_tac) >>
  simp[] >> strip_tac >- simp[] >>
  drule ao_alloc_fresh_props >> strip_tac >> gvs[] >>
  disj2_tac >> decide_tac
QED

Theorem ao_transform_insts_supply_bound:
  EVERY (\i. i.inst_id < s.irs_next_inst) insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  EVERY (\i. i.inst_id < s'.irs_next_inst) outs
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[] >>
  drule ao_alloc_fresh_props >> strip_tac >>
  `EVERY (\i. i.inst_id < r.irs_next_inst) insts` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `EVERY (\i. i.inst_id < r''.irs_next_inst) q'` by metis_tac[] >>
  `EVERY (\i. i.inst_id < r.irs_next_inst)
    (ao_transform_inst dfg ra lbl idx targets q h)` by
    (mp_tac (Q.INST [`inst` |-> `h`, `fr` |-> `q`, `s'` |-> `r`]
       ao_transform_inst_fresh_ids) >> simp[EVERY_MAP]) >>
  drule ao_transform_insts_supply_used_vars >> strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i (ao_transform_inst _ _ _ _ _ _ _) ==> _`
    drule >> simp[]
QED

Theorem ao_transform_insts_supply_distinct_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs, s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) outs)
Proof
  map_every qid_spec_tac [`s'`, `outs`, `idx`, `s`] >>
  Induct_on `insts` >> simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) insts` >>
  gvs[] >> drule ao_alloc_fresh_props >> strip_tac >>
  `EVERY (\i. i.inst_id < r.irs_next_inst) insts` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) q')` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
     (ao_transform_inst dfg ra lbl idx targets q h)) /\
   EVERY (\id. id < r.irs_next_inst)
     (MAP (\i. i.inst_id) (ao_transform_inst dfg ra lbl idx targets q h))`
    by (mp_tac (Q.INST [`inst` |-> `h`, `fr` |-> `q`, `s'` |-> `r`]
      ao_transform_inst_fresh_ids) >> simp[]) >>
  simp[ALL_DISTINCT_APPEND] >>
  gen_tac >> strip_tac >> strip_tac >>
  `MEM e (MAP (\i. i.inst_id) insts) \/ r.irs_next_inst <= e`
    by metis_tac[ao_transform_insts_supply_id_origin] >>
  `e = h.inst_id \/ s.irs_next_inst <= e`
    by metis_tac[ao_transform_inst_supply_id_origin] >>
  gvs[EVERY_MEM, MEM_MAP] >>
  metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_TRANS]
QED

Theorem ao_transform_blocks_supply_id_origin:
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  !id. MEM id (MAP (\i. i.inst_id) (fn_insts_blocks bbs')) ==>
    MEM id (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) \/ s.irs_next_inst <= id
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  simp[fn_insts_blocks_def] >> rpt strip_tac
  >- metis_tac[ao_transform_insts_supply_id_origin] >>
  first_x_assum drule >> disch_then (qspec_then `id` mp_tac) >>
  simp[] >> strip_tac >- simp[] >>
  drule ao_transform_insts_supply_used_vars >> strip_tac >> gvs[] >>
  disj2_tac >> decide_tac
QED

Theorem ao_transform_blocks_supply_bound:
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts_blocks bbs) /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  EVERY (\i. i.inst_id < s'.irs_next_inst) (fn_insts_blocks bbs')
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  drule ao_transform_insts_supply_used_vars >> strip_tac >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) (fn_insts_blocks bbs)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `EVERY (\i. i.inst_id < s'.irs_next_inst) (fn_insts_blocks bbs'')`
    by metis_tac[] >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) insts`
    by metis_tac[ao_transform_insts_supply_bound] >>
  drule ao_transform_blocks_supply_used_vars >> strip_tac >>
  gvs[fn_insts_blocks_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ao_transform_blocks_supply_distinct_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts_blocks bbs) /\
  ao_transform_blocks_supply dfg ra targets s bbs = (bbs', s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs'))
Proof
  map_every qid_spec_tac [`s'`, `bbs'`, `s`] >>
  Induct_on `bbs` >> simp[ao_transform_blocks_supply_def, fn_insts_blocks_def,
    ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_block_supply_def, pairTheory.pair_case_eq] >>
  drule ao_transform_insts_supply_used_vars >> strip_tac >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) (fn_insts_blocks bbs)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs''))`
    by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) insts)`
    by metis_tac[ao_transform_insts_supply_distinct_ids] >>
  `EVERY (\i. i.inst_id < s1.irs_next_inst) insts`
    by metis_tac[ao_transform_insts_supply_bound] >>
  simp[fn_insts_blocks_def, ALL_DISTINCT_APPEND] >>
  gen_tac >> strip_tac >> strip_tac >>
  `MEM e (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) \/ s1.irs_next_inst <= e`
    by metis_tac[ao_transform_blocks_supply_id_origin] >>
  `MEM e (MAP (\i. i.inst_id) h.bb_instructions) \/ s.irs_next_inst <= e`
    by metis_tac[ao_transform_insts_supply_id_origin] >>
  gvs[EVERY_MEM, MEM_MAP] >>
  metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_TRANS]
QED

Theorem ao_bb_cons_well_formed:
  tail <> [] ==>
  (bb_well_formed (bb with bb_instructions := h::tail) <=>
   bb_well_formed (bb with bb_instructions := tail) /\
   ~is_terminator h.inst_opcode /\
   (h.inst_opcode = PHI \/ EVERY (\i. i.inst_opcode <> PHI) tail))
Proof
  strip_tac >> simp[bb_well_formed_def, LAST_DEF] >>
  eq_tac
  >- (strip_tac >> rpt conj_tac
      >- simp[]
      >- (rpt strip_tac >>
          qpat_x_assum `!i. _ ==> i = _`
            (qspec_then `SUC i` mp_tac) >> simp[])
      >- (rpt strip_tac >>
          first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
      >- (strip_tac >>
          qpat_x_assum `!i. _ ==> i = _` (qspec_then `0` mp_tac) >>
          Cases_on `tail` >> gvs[]) >>
      Cases_on `h.inst_opcode = PHI` >> simp[EVERY_EL] >>
      rpt strip_tac >>
      qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  strip_tac >>
  (simp[] >> conj_tac
   >- (gen_tac >> Cases_on `i` >> simp[] >> rpt strip_tac >> gvs[] >>
       qpat_x_assum `!i. _ ==> i = _` (qspec_then `n` mp_tac) >>
       Cases_on `tail` >> gvs[]) >>
   rpt gen_tac >> Cases_on `i` >> Cases_on `j` >> simp[] >>
   rpt strip_tac >> gvs[EVERY_EL] >> metis_tac[])
QED

Theorem ao_bb_prefix_well_formed:
  bb_well_formed (bb with bb_instructions := tail) /\
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  (EVERY (\i. i.inst_opcode = PHI) pre \/
   EVERY (\i. i.inst_opcode <> PHI) (pre ++ tail)) ==>
  bb_well_formed (bb with bb_instructions := pre ++ tail)
Proof
  Induct_on `pre` >> simp[] >> rpt strip_tac >>
  `tail <> []` by gvs[bb_well_formed_def] >>
  `bb_well_formed (bb with bb_instructions := pre ++ tail)`
    by (first_x_assum irule >> simp[]) >>
  `pre ++ tail <> []` by simp[] >>
  simp[ao_bb_cons_well_formed] >> gvs[]
QED

Theorem ao_flip_comparison_comparator:
  is_comparator opc ==> is_comparator (flip_comparison_opcode opc)
Proof
  Cases_on `opc` >> simp[is_comparator_def, flip_comparison_opcode_def]
QED

Theorem ao_cmp_flip_scan_provenance:
  EVERY (\i. MEM i (fn_insts fn)) insts /\
  ao_cmp_flip_scan (dfg_build_function fn) insts = (flips,removes,inserts) ==>
  EVERY (\(id,opc,w,op).
    is_comparator opc /\
    ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\ is_comparator i.inst_opcode) flips /\
  EVERY (\id. ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
                  i.inst_opcode = ISZERO) removes /\
  EVERY (\(id,v,c). ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
                        i.inst_opcode = ASSERT) inserts
Proof
  map_every qid_spec_tac [`inserts`, `removes`, `flips`] >>
  Induct_on `insts`
  >- simp[ao_cmp_flip_scan_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn) insts` >>
  PairCases_on `r` >>
  gvs[] >>
  gvs[Once ao_cmp_flip_scan_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `MEM (HD (dfg_get_uses (dfg_build_function fn) out_var)) (fn_insts fn)` by
    (irule (cj 1 dfg_build_function_uses_sound) >>
     qexists `out_var` >>
     Cases_on `dfg_get_uses (dfg_build_function fn) out_var` >> gvs[]) >>
  simp[ao_flip_comparison_comparator] >> metis_tac[]
QED

Theorem ao_cmp_flip_scan_lookup_safety:
  fn_inst_ids_distinct fn /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (flips,removes,inserts) ==>
  (!i opc w op. MEM i (fn_insts fn) /\
     ALOOKUP flips i.inst_id = SOME (opc,w,op) ==>
     is_comparator i.inst_opcode /\ is_comparator opc) /\
  (!i. MEM i (fn_insts fn) /\ MEM i.inst_id removes ==> i.inst_opcode = ISZERO) /\
  (!i v c. MEM i (fn_insts fn) /\
     ALOOKUP inserts i.inst_id = SOME (v,c) ==> i.inst_opcode = ASSERT)
Proof
  strip_tac >>
  `EVERY (\i. MEM i (fn_insts fn)) (fn_insts fn)` by simp[EVERY_MEM] >>
  drule_all ao_cmp_flip_scan_provenance >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD] >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  metis_tac[ao_fn_inst_id_injective]
QED

Theorem ao_cmp_flip_apply_inst_ids:
  MAP (\i. i.inst_id) (ao_cmp_flip_apply_inst flips removes named inst) =
  if IS_SOME (ALOOKUP flips inst.inst_id) \/ MEM inst.inst_id removes then [inst.inst_id]
  else case ALOOKUP named inst.inst_id of
         NONE => [inst.inst_id]
       | SOME (out,id,v) => [id; inst.inst_id]
Proof
  Cases_on `ALOOKUP flips inst.inst_id`
  >- (simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `MEM inst.inst_id removes` >> simp[] >>
      Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
      PairCases_on `x` >> simp[]) >>
  PairCases_on `x` >> simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_flip_apply_inst_structure:
  (!opc w op. ALOOKUP flips inst.inst_id = SOME (opc,w,op) ==>
    is_comparator inst.inst_opcode /\ is_comparator opc) /\
  (MEM inst.inst_id removes ==> inst.inst_opcode = ISZERO) /\
  (!out id v. ALOOKUP named inst.inst_id = SOME (out,id,v) ==> inst.inst_opcode = ASSERT) ==>
  ao_cmp_flip_apply_inst flips removes named inst <> [] /\
  EVERY (\j. (j.inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
             (is_terminator j.inst_opcode = is_terminator inst.inst_opcode) /\
             get_successors j = get_successors inst)
    (ao_cmp_flip_apply_inst flips removes named inst) /\
  (is_terminator inst.inst_opcode ==> ao_cmp_flip_apply_inst flips removes named inst = [inst])
Proof
  strip_tac >>
  Cases_on `ALOOKUP flips inst.inst_id`
  >- (simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `MEM inst.inst_id removes` >> gvs[]
      >- simp[is_terminator_def, get_successors_def] >>
      Cases_on `ALOOKUP named inst.inst_id` >> simp[] >>
      PairCases_on `x` >> gvs[] >>
      simp[is_terminator_def, get_successors_def]) >>
  PairCases_on `x` >> gvs[] >>
  simp[ao_cmp_flip_apply_inst_def] >>
  gvs[is_comparator_def] >> simp[is_terminator_def, get_successors_def]
QED

Theorem ao_expand_insts_well_formed:
  (!i. MEM i insts ==>
    f i <> [] /\
    EVERY (\j. (j.inst_opcode = PHI <=> i.inst_opcode = PHI) /\
               (is_terminator j.inst_opcode = is_terminator i.inst_opcode)) (f i) /\
    (is_terminator i.inst_opcode ==> f i = [i])) /\
  bb_well_formed (bb with bb_instructions := insts) ==>
  bb_well_formed (bb with bb_instructions := FLAT (MAP f insts))
Proof
  Induct_on `insts`
  >- simp[bb_well_formed_def] >>
  rpt strip_tac >>
  Cases_on `insts = []`
  >- (gvs[bb_well_formed_def] >> metis_tac[]) >>
  gvs[ao_bb_cons_well_formed] >>
  (`bb_well_formed (bb with bb_instructions := FLAT (MAP f insts))` by metis_tac[] >>
   simp[] >> irule ao_bb_prefix_well_formed >> simp[] >>
   conj_tac
   >- (gvs[EVERY_MEM] >> metis_tac[]) >>
   Cases_on `h.inst_opcode = PHI`
   >- (disj1_tac >> gvs[EVERY_MEM] >> metis_tac[]) >>
   disj2_tac >>
   gvs[EVERY_FLAT, EVERY_MAP, EVERY_MEM] >>
   metis_tac[])
QED

Theorem ao_cmp_flip_apply_inst_id_origin:
  MEM j (ao_cmp_flip_apply_inst flips removes named i) ==>
  j.inst_id = i.inst_id \/
  ?out v. ALOOKUP named i.inst_id = SOME (out,j.inst_id,v)
Proof
  Cases_on `ALOOKUP flips i.inst_id`
  >- (Cases_on `MEM i.inst_id removes`
      >- simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `ALOOKUP named i.inst_id`
      >- simp[ao_cmp_flip_apply_inst_def] >>
      PairCases_on `x` >>
      simp[ao_cmp_flip_apply_inst_def] >> rpt strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[ao_cmp_flip_apply_inst_def]
QED

Theorem ao_cmp_flip_apply_insts_distinct:
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. i.inst_id < n) insts /\
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  EVERY (\(a,out,id,v). n <= id) named ==>
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) insts)))
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
    (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) insts)))` by metis_tac[] >>
  simp[ao_cmp_flip_apply_inst_ids, ALL_DISTINCT_APPEND] >>
  `!i out id v. ALOOKUP named i = SOME (out,id,v) ==> n <= id` by
    (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
     gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `!a out id v b out' v'.
    ALOOKUP named a = SOME (out,id,v) /\
    ALOOKUP named b = SOME (out',id,v') ==> a = b` by
    (rpt strip_tac >> imp_res_tac ALOOKUP_MEM >>
     metis_tac[ao_named_insert_id_injective]) >>
  Cases_on `ALOOKUP named h.inst_id` >> simp[] >>
  rpt pairarg_tac >> gvs[] >>
  Cases_on `IS_SOME (ALOOKUP flips h.inst_id) \/ MEM h.inst_id removes` >> simp[] >>
  gvs[EVERY_MEM, MEM_MAP] >>
  simp[MEM_MAP, MEM_FLAT] >>
  rpt strip_tac >> gvs[] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  imp_res_tac ao_cmp_flip_apply_inst_id_origin >> gvs[] >>
  res_tac >> gvs[] >> PairCases_on `x` >> gvs[] >>
  res_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_expand_insts_last:
  insts <> [] /\ is_terminator (LAST insts).inst_opcode /\
  (!i. MEM i insts ==> f i <> [] /\ (is_terminator i.inst_opcode ==> f i = [i])) ==>
  FLAT (MAP f insts) <> [] /\ LAST (FLAT (MAP f insts)) = LAST insts
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  Cases_on `insts = []`
  >- (gvs[] >> metis_tac[]) >>
  gvs[LAST_DEF] >>
  `FLAT (MAP f insts) <> [] /\ LAST (FLAT (MAP f insts)) = LAST insts` by metis_tac[] >>
  Cases_on `FLAT (MAP f insts)` >> gvs[LAST_APPEND_CONS]
QED

Theorem ao_cmp_flip_apply_block_structure:
  bb_well_formed bb /\
  (!i. MEM i bb.bb_instructions ==>
    (!opc w op. ALOOKUP flips i.inst_id = SOME (opc,w,op) ==>
      is_comparator i.inst_opcode /\ is_comparator opc) /\
    (MEM i.inst_id removes ==> i.inst_opcode = ISZERO) /\
    (!out id v. ALOOKUP named i.inst_id = SOME (out,id,v) ==> i.inst_opcode = ASSERT)) ==>
  bb_well_formed (bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) /\
  bb_succs (bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) = bb_succs bb
Proof
  strip_tac >>
  `!i. MEM i bb.bb_instructions ==>
    ao_cmp_flip_apply_inst flips removes named i <> [] /\
    EVERY (\j. (j.inst_opcode = PHI <=> i.inst_opcode = PHI) /\
      (is_terminator j.inst_opcode = is_terminator i.inst_opcode) /\
      get_successors j = get_successors i) (ao_cmp_flip_apply_inst flips removes named i) /\
    (is_terminator i.inst_opcode ==> ao_cmp_flip_apply_inst flips removes named i = [i])`
    by (gen_tac >> disch_tac >>
        first_x_assum drule >> strip_tac >>
        irule ao_cmp_flip_apply_inst_structure >> simp[]) >>
  conj_tac
  >- (irule ao_expand_insts_well_formed >> simp[] >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode`
    by gvs[bb_well_formed_def] >>
  `FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions) <> [] /\
   LAST (FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) =
   LAST bb.bb_instructions` by
    (irule ao_expand_insts_last >> simp[] >> metis_tac[]) >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) (h::t))` >> gvs[]
QED

Theorem ao_cmp_flip_apply_fn_well_formed:
  wf_function fn /\ EVERY (\i. i.inst_id < n) (fn_insts fn) /\
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  EVERY (\(a,out,id,v). n <= id) named /\
  (!i. MEM i (fn_insts fn) ==>
    (!opc w op. ALOOKUP flips i.inst_id = SOME (opc,w,op) ==>
      is_comparator i.inst_opcode /\ is_comparator opc) /\
    (MEM i.inst_id removes ==> i.inst_opcode = ISZERO) /\
    (!out id v. ALOOKUP named i.inst_id = SOME (out,id,v) ==> i.inst_opcode = ASSERT)) ==>
  wf_function (ao_cmp_flip_apply_fn flips removes named fn)
Proof
  strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==>
    bb_well_formed (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) /\
    bb_succs (bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) = bb_succs bb` by
    (gen_tac >> disch_tac >> irule ao_cmp_flip_apply_block_structure >>
     reverse conj_tac >- metis_tac[wf_function_def] >>
     gen_tac >> disch_tac >> first_x_assum irule >>
     simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def] >>
  simp[ao_cmp_flip_apply_fn_def, wf_function_def, fn_labels_def,
       fn_has_entry_def, MAP_MAP_o, combinTheory.o_DEF, MEM_MAP] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (gvs[fn_succs_closed_def, fn_labels_def] >>
      simp[MEM_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
      rpt strip_tac >> gvs[] >>
      `MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)` by metis_tac[] >>
      gvs[MEM_MAP] >>
      qexists `bb with bb_instructions :=
        FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)` >>
      simp[] >> metis_tac[]) >>
  `!bbs. fn_insts_blocks (MAP (\bb. bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) bb.bb_instructions)) bbs) =
    FLAT (MAP (ao_cmp_flip_apply_inst flips removes named) (fn_insts_blocks bbs))` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND]) >>
  gvs[ao_fn_inst_ids_distinct_alt, fn_insts_def] >>
  irule ao_cmp_flip_apply_insts_distinct >> simp[] >> metis_tac[]
QED

Theorem ao_cmp_flip_function_supply_well_formed:
  wf_function fn /\ EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts fn) /\
  ao_cmp_flip_function_supply (dfg_build_function fn) s fn = (fn',s') ==>
  wf_function fn'
Proof
  strip_tac >>
  Cases_on `ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn)` >>
  PairCases_on `r` >>
  gvs[ao_cmp_flip_function_supply_def] >>
  Cases_on `NULL q` >> gvs[] >>
  Cases_on `ao_name_inserts_supply s r1` >> gvs[] >>
  rename1 `ao_name_inserts_supply s inserts = (named,s')` >>
  drule ao_name_inserts_supply_numeric >> strip_tac >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  drule_all ao_cmp_flip_scan_lookup_safety >> strip_tac >>
  `EVERY (\i. MEM i (fn_insts fn)) (fn_insts fn)` by simp[EVERY_MEM] >>
  drule_all ao_cmp_flip_scan_provenance >> strip_tac >>
  irule ao_cmp_flip_apply_fn_well_formed >>
  reverse conj_tac
  >- (simp[] >> qexists `s.irs_next_inst` >>
      gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> drule_all ao_name_inserts_supply_lookup_key >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> strip_tac >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[ao_fn_inst_id_injective]
QED

Theorem ao_main_function_wf_and_bound:
  !fn fn0 s bbs s1 mid.
    wf_function fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_covers_fn s fn /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) s fn0.fn_blocks = (bbs,s1) /\
    mid = fn0 with fn_blocks := bbs ==>
    wf_function mid /\
    EVERY (\i. i.inst_id < s1.irs_next_inst) (fn_insts mid)
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_initial_inst_id_bound >> strip_tac >>
  drule ao_initial_inst_ids_distinct >> strip_tac >>
  drule ao_offset_function_insts >> strip_tac >>
  `EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts_blocks fn0.fn_blocks)` by
    (qpat_x_assum `fn_insts fn0 = _` mp_tac >>
     qpat_x_assum `EVERY (\i. i.inst_id < s.irs_next_inst) _` mp_tac >>
     simp[fn_insts_def, EVERY_MAP, ao_handle_offset_inst_shape]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks fn0.fn_blocks))` by
    (qpat_x_assum `fn_insts fn0 = _` mp_tac >>
     qpat_x_assum `ALL_DISTINCT _` mp_tac >>
     simp[fn_insts_def, MAP_MAP_o, combinTheory.o_DEF, ao_handle_offset_inst_shape]) >>
  drule_all ao_transform_blocks_supply_bound >> strip_tac >>
  drule_all ao_transform_blocks_supply_distinct_ids >> strip_tac >>
  reverse conj_tac >- gvs[fn_insts_def] >>
  drule_all ao_main_function_labels >> strip_tac >>
  drule_all ao_main_function_successors >> strip_tac >>
  `EVERY bb_well_formed fn0.fn_blocks` by
    (gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
     irule ao_offset_block_well_formed >> fs[wf_function_def]) >>
  drule_all ao_transform_blocks_supply_well_formed >> strip_tac >>
  `fn_succs_closed mid` by
    (fs[fn_succs_closed_def] >> rpt strip_tac >>
     `MEM (bb.bb_label,bb_succs bb)
       (MAP (\bb. (bb.bb_label,bb_succs bb)) mid.fn_blocks)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     `MEM (bb.bb_label,bb_succs bb)
       (MAP (\bb. (bb.bb_label,bb_succs bb)) fn.fn_blocks)` by gvs[] >>
     qpat_x_assum `MEM _ (MAP _ fn.fn_blocks)` mp_tac >>
     simp[MEM_MAP] >> strip_tac >> gvs[] >>
     metis_tac[wf_function_def, fn_succs_closed_def]) >>
  gvs[wf_function_def, ao_fn_inst_ids_distinct_alt, fn_insts_def,
      EVERY_MEM, fn_has_entry_def, fn_labels_def] >>
  Cases_on `bbs` >> gvs[]
QED

Theorem ao_preserves_wf_function_proof:
  !sup fn fn' sup'.
    wf_function fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') ==>
    wf_function fn'
Proof
  map_every qx_gen_tac [`s`, `fn`, `fn'`, `sfinal`] >> strip_tac >>
  qpat_x_assum `ao_transform_function_supply _ _ = _` mp_tac >>
  simp[ao_transform_function_supply_def] >>
  qmatch_goalsub_abbrev_tac `dfg_build_function fn0` >>
  Cases_on `ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
    (ao_compute_fn_iszero_targets fn0) s fn0.fn_blocks` >>
  simp[] >> disch_tac >>
  qspecl_then [`fn`, `fn0`, `s`, `q`, `r`, `fn0 with fn_blocks := q`]
    mp_tac ao_main_function_wf_and_bound >>
  impl_tac >- simp[Abbr `fn0`] >>
  strip_tac >>
  irule ao_cmp_flip_function_supply_well_formed >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists `sfinal` >> gvs[Abbr `fn0`]
QED
