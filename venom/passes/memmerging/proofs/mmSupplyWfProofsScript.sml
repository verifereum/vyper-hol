(*
 * Memmerging — wf_function preservation for the supply-threaded transform
 * (transform_function_supply).
 *)

Theory mmSupplyWfProofs
Ancestors
  mmWfProofs mmTransform mmTransformSupply irSupply venomFnScheduleRunner venomWf venomInst
  mmScan list rich_list arithmetic

(* Every input instruction becomes a list holding exactly one instruction
   with its own id (kept, NOP'd, or rewritten in place), plus at most one
   inserted instruction (the load in front of a downsized 32-byte copy, the
   calldatasize in front of a memzero calldatacopy) whose id comes from
   fresh_inst_id. ir_supply_covers_fn bounds the input's ids below
   irs_next_inst, which fresh_inst_id hands out and increments, so ids stay
   distinct. PHIs and terminators are never in a nop set or rep map (group
   ids are scanned loads/stores/copies, plus dfg_get_def of a load's output,
   which ssa_form makes that load), and the inserted opcodes are neither, so
   bb_well_formed holds; LAST is kept, so labels and successors don't change.
   transform_block_wf in mmWfProofs proves the bb_well_formed part for the
   non-supply transform. *)

Theorem apply_groups_inst_supply_ids:
  !mode nops reps s i out t.
    apply_groups_inst_supply mode nops reps s i = (out,t) /\
    i.inst_id < s.irs_next_inst ==>
    ALL_DISTINCT (MAP (\j. j.inst_id) out) /\
    s.irs_next_inst <= t.irs_next_inst /\
    EVERY (\j. j.inst_id < t.irs_next_inst) out /\
    (!j. MEM j out ==> j.inst_id = i.inst_id \/
      (s.irs_next_inst <= j.inst_id /\ j.inst_id < t.irs_next_inst))
Proof
  rpt gen_tac >>
  simp[apply_groups_inst_supply_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem apply_memzero_inst_supply_ids:
  !nops reps s i out t.
    apply_memzero_inst_supply nops reps s i = (out,t) /\
    i.inst_id < s.irs_next_inst ==>
    ALL_DISTINCT (MAP (\j. j.inst_id) out) /\
    s.irs_next_inst <= t.irs_next_inst /\
    EVERY (\j. j.inst_id < t.irs_next_inst) out /\
    (!j. MEM j out ==> j.inst_id = i.inst_id \/
      (s.irs_next_inst <= j.inst_id /\ j.inst_id < t.irs_next_inst))
Proof
  rpt gen_tac >> simp[apply_memzero_inst_supply_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem apply_groups_inst_supply_opcodes:
  !mode nops reps s i out t.
    apply_groups_inst_supply mode nops reps s i = (out,t) ==>
    MAP (\j. j.inst_opcode) out =
    MAP (\j. j.inst_opcode) (apply_groups_inst mode nops reps i)
Proof
  rpt gen_tac >>
  simp[apply_groups_inst_supply_def, apply_groups_inst_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_load_inst_def, mk_mstore_from_load_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem apply_memzero_inst_supply_opcodes:
  !nops reps s i out t.
    apply_memzero_inst_supply nops reps s i = (out,t) ==>
    MAP (\j. j.inst_opcode) out =
    MAP (\j. j.inst_opcode) (apply_memzero_inst nops reps i)
Proof
  rpt gen_tac >>
  simp[apply_memzero_inst_supply_def, apply_memzero_inst_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_calldatasize_inst_def, mk_memzero_calldatacopy_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem apply_groups_inst_supply_identity:
  !mode nops reps s i out t.
    apply_groups_inst_supply mode nops reps s i = (out,t) /\
    apply_groups_inst mode nops reps i = [i] ==> out = [i]
Proof
  rpt gen_tac >>
  simp[apply_groups_inst_supply_def, apply_groups_inst_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

Theorem apply_memzero_inst_supply_identity:
  !nops reps s i out t.
    apply_memzero_inst_supply nops reps s i = (out,t) /\
    apply_memzero_inst nops reps i = [i] ==> out = [i]
Proof
  rpt gen_tac >>
  simp[apply_memzero_inst_supply_def, apply_memzero_inst_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >> rpt strip_tac >> gvs[]
QED

Theorem apply_memzero_inst_supply_load_origin:
  !nops reps s i out t j mode.
    apply_memzero_inst_supply nops reps s i = (out,t) /\
    MEM j out /\ j.inst_opcode = mode_load_opcode mode ==> j = i
Proof
  rpt gen_tac >> simp[apply_memzero_inst_supply_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def] >>
  Cases_on `mode` >> simp[mode_load_opcode_def] >> rpt strip_tac >> gvs[]
QED

Theorem apply_groups_inst_supply_other_load_origin:
  !mode nops reps s i out t j other.
    apply_groups_inst_supply mode nops reps s i = (out,t) /\
    MEM j out /\ j.inst_opcode = mode_load_opcode other /\ other <> mode ==>
    j = i
Proof
  rpt gen_tac >> simp[apply_groups_inst_supply_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def] >>
  Cases_on `other` >>
  simp[mode_load_opcode_def, mode_copy_opcode_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `mode` >> gvs[mode_load_opcode_def, mode_copy_opcode_def]
QED

Theorem apply_groups_inst_supply_phi_origin:
  !mode nops reps s i out t j.
    apply_groups_inst_supply mode nops reps s i = (out,t) /\
    MEM j out /\ j.inst_opcode = PHI ==> j = i
Proof
  rpt gen_tac >> simp[apply_groups_inst_supply_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def] >> rpt strip_tac >>
  gvs[mode_load_opcode_def, mode_copy_opcode_def] >>
  Cases_on `mode` >> gvs[mode_load_opcode_def, mode_copy_opcode_def]
QED

Theorem apply_memzero_inst_supply_phi_origin:
  !nops reps s i out t j.
    apply_memzero_inst_supply nops reps s i = (out,t) /\
    MEM j out /\ j.inst_opcode = PHI ==> j = i
Proof
  rpt gen_tac >> simp[apply_memzero_inst_supply_def] >>
  Cases_on `MEM i.inst_id nops` >> simp[] >>
  Cases_on `ALOOKUP reps i.inst_id` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[fresh_inst_id_def, fresh_ir_var_def, AllCaseEqs(),
      mk_nop_from_def, mk_zero_store_inst_def, mk_memzero_calldatacopy_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem mm_flat_map_supply_opcodes:
  !f g xs s ys t.
    (!u i out v. f u i = (out,v) ==>
       MAP (\j. j.inst_opcode) out = MAP (\j. j.inst_opcode) (g i)) /\
    mm_flat_map_supply f s xs = (ys,t) ==>
    MAP (\j. j.inst_opcode) ys =
      MAP (\j. j.inst_opcode) (FLAT (MAP g xs))
Proof
  gen_tac >> gen_tac >> Induct >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> simp[] >> metis_tac[]
QED

Theorem mm_flat_map_supply_origin:
  !f P xs s ys t.
    (!u i out v j. f u i = (out,v) /\ MEM j out /\ P j ==> j = i) /\
    mm_flat_map_supply f s xs = (ys,t) ==>
    !j. MEM j ys /\ P j ==> MEM j xs
Proof
  gen_tac >> gen_tac >> Induct >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[MEM_APPEND]
QED

Theorem mm_flat_map_supply_last:
  !f xs s ys t.
    (!u i out v. f u i = (out,v) ==> out <> []) /\
    (!u out v. f u (LAST xs) = (out,v) ==> out = [LAST xs]) /\
    xs <> [] /\ mm_flat_map_supply f s xs = (ys,t) ==>
    ys <> [] /\ LAST ys = LAST xs
Proof
  gen_tac >> Induct >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `xs = []`
  >- (gvs[mm_flat_map_supply_def] >> metis_tac[LAST_DEF, NOT_NIL_CONS]) >>
  gvs[LAST_DEF] >>
  qpat_x_assum `!s ys t. _ ==> ys <> [] /\ LAST ys = LAST xs`
    (qspecl_then [`s1`, `outs`, `t`] mp_tac) >>
  simp[] >> metis_tac[LAST_APPEND_NOT_NIL]
QED

Theorem mm_flat_map_supply_ids:
  !f (key:'a -> num) (next:'b -> num) xs s ys t.
    (!u i out v. f u i = (out,v) /\ key i < next u ==>
       ALL_DISTINCT (MAP key out) /\ next u <= next v /\
       EVERY (\j. key j < next v) out /\
       (!j. MEM j out ==> key j = key i \/
         (next u <= key j /\ key j < next v))) /\
    ALL_DISTINCT (MAP key xs) /\ EVERY (\i. key i < next s) xs /\
    mm_flat_map_supply f s xs = (ys,t) ==>
    ALL_DISTINCT (MAP key ys) /\ next s <= next t /\
    EVERY (\j. key j < next t) ys /\
    (!j. MEM j ys ==> MEM (key j) (MAP key xs) \/
      (next s <= key j /\ key j < next t))
Proof
  gen_tac >> gen_tac >> gen_tac >> Induct
  >- (simp_tac std_ss [mm_flat_map_supply_def, MAP, EVERY_DEF, ALL_DISTINCT,
                      MEM, pairTheory.PAIR_EQ, LE_REFL] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `mm_flat_map_supply _ _ _ = _` mp_tac >>
  simp[Once mm_flat_map_supply_def, AllCaseEqs()] >> strip_tac >>
  fs[ALL_DISTINCT, EVERY_DEF] >>
  qpat_assum `!u i out v. _`
    (qspecl_then [`s`, `h`, `out`, `s1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `EVERY (\i. key i < next s1) xs` by
    (fs[EVERY_MEM] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `!s ys t. _`
    (qspecl_then [`s1`, `outs`, `t`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `!u i out v. _` kall_tac >>
  qpat_x_assum `f s h = _` kall_tac >>
  qpat_x_assum `mm_flat_map_supply _ _ _ = _` kall_tac >>
  `!k. MEM k (MAP key xs) ==> k < next s` by
    (fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `!a b. MEM a out /\ MEM b outs ==> key a <> key b` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!j. MEM j out ==> _` (qspec_then `a` mp_tac) >>
     qpat_x_assum `!j. MEM j outs ==> _` (qspec_then `b` mp_tac) >>
     simp[] >> rpt strip_tac >> gvs[] >>
     metis_tac[LESS_LESS_EQ_TRANS, NOT_LESS_EQUAL]) >>
  gvs[] >> conj_tac
  >- (simp[ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]) >>
  conj_tac
  >- (fs[EVERY_MEM] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  simp[] >> metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem bb_well_formed_opcodes:
  !bb cc.
    MAP (\i. i.inst_opcode) bb.bb_instructions =
    MAP (\i. i.inst_opcode) cc.bb_instructions ==>
    (bb_well_formed bb <=> bb_well_formed cc)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH cc.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  Cases_on `bb.bb_instructions = []`
  >- (gvs[bb_well_formed_def] >> Cases_on `cc.bb_instructions` >> gvs[]) >>
  `cc.bb_instructions <> []` by
    (Cases_on `cc.bb_instructions` >> gvs[]) >>
  `!n. n < LENGTH bb.bb_instructions ==>
    (EL n bb.bb_instructions).inst_opcode =
    (EL n cc.bb_instructions).inst_opcode` by
    (rpt strip_tac >>
     qpat_x_assum `MAP _ _ = MAP _ _`
       (mp_tac o ONCE_REWRITE_RULE [LIST_EQ_REWRITE]) >>
     simp[EL_MAP]) >>
  `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  `LAST cc.bb_instructions = EL (PRE (LENGTH cc.bb_instructions)) cc.bb_instructions` by
    metis_tac[LAST_EL] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  simp[bb_well_formed_def] >> metis_tac[]
QED

Theorem transform_block_memzero_supply_opcodes:
  !dfg s bb cc t.
    transform_block_memzero_supply dfg s bb = (cc,t) ==>
    MAP (\i. i.inst_opcode) cc.bb_instructions =
    MAP (\i. i.inst_opcode) (transform_block_memzero dfg bb).bb_instructions
Proof
  rpt gen_tac >>
  simp[transform_block_memzero_supply_def, transform_block_memzero_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[mm_flat_map_supply_opcodes, apply_memzero_inst_supply_opcodes]
QED

Theorem transform_block_mode_supply_opcodes:
  !dfg mode s bb cc t.
    transform_block_mode_supply dfg mode s bb = (cc,t) ==>
    MAP (\i. i.inst_opcode) cc.bb_instructions =
    MAP (\i. i.inst_opcode) (transform_block_mode dfg mode bb).bb_instructions
Proof
  rpt gen_tac >>
  simp[transform_block_mode_supply_def, transform_block_mode_def,
       AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[mm_flat_map_supply_opcodes, apply_groups_inst_supply_opcodes]
QED

Theorem transform_block_memzero_supply_wf:
  !dfg s bb cc t.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    bb_well_formed bb /\
    transform_block_memzero_supply dfg s bb = (cc,t) ==>
    bb_well_formed cc
Proof
  rpt strip_tac >> drule transform_block_memzero_supply_opcodes >>
  disch_then (mp_tac o MATCH_MP bb_well_formed_opcodes) >>
  metis_tac[transform_block_memzero_wf]
QED

Theorem transform_block_mode_supply_wf:
  !fn dfg mode s bb cc t.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\ ssa_form fn /\
    bb_well_formed bb /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) /\
    (!p i. MEM p bb.bb_instructions /\ p.inst_opcode = PHI /\
           MEM i bb.bb_instructions /\ i.inst_id = p.inst_id ==> i = p) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
         MEM i (fn_insts fn)) /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_opcode = mode_load_opcode mode /\ i.inst_outputs <> [] ==>
         MEM i (fn_insts fn)) /\
    MEM (LAST bb.bb_instructions) (fn_insts fn) /\
    transform_block_mode_supply dfg mode s bb = (cc,t) ==>
    bb_well_formed cc
Proof
  rpt strip_tac >> drule transform_block_mode_supply_opcodes >>
  disch_then (mp_tac o MATCH_MP bb_well_formed_opcodes) >>
  `bb_well_formed (transform_block_mode (dfg_build_function fn) mode bb)` by
        (irule transform_block_mode_wf >> simp[] >> qexists_tac `fn` >> simp[]) >>
  simp[]
QED

Theorem apply_memzero_inst_supply_nonempty:
  !nops reps s i out t.
    apply_memzero_inst_supply nops reps s i = (out,t) ==> out <> []
Proof
  rpt strip_tac >> drule apply_memzero_inst_supply_opcodes >>
  metis_tac[MAP_EQ_NIL, apply_memzero_inst_nonempty]
QED

Theorem apply_groups_inst_supply_nonempty:
  !mode nops reps s i out t.
    apply_groups_inst_supply mode nops reps s i = (out,t) ==> out <> []
Proof
  rpt strip_tac >> drule apply_groups_inst_supply_opcodes >>
  metis_tac[MAP_EQ_NIL, apply_groups_inst_nonempty]
QED

Theorem transform_block_memzero_supply_last:
  !dfg s bb cc t.
    bb_well_formed bb /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) /\
    transform_block_memzero_supply dfg s bb = (cc,t) ==>
    cc.bb_instructions <> [] /\
    LAST cc.bb_instructions = LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  drule_all term_id_not_in_memzero_scan_weak >> simp[] >> strip_tac >>
  qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `mm_flat_map_supply f s _ = _` >>
  irule (INST_TYPE [``:'a`` |-> ``:ir_supply``] mm_flat_map_supply_last) >> simp[] >>
  qexistsl_tac [`f`, `s`, `t`] >>
  simp[Abbr `f`] >> conj_tac
  >- metis_tac[apply_memzero_inst_supply_nonempty] >>
  simp[apply_memzero_inst_supply_def]
QED

Theorem transform_block_mode_supply_last:
  !fn dfg mode s bb cc t.
    dfg = dfg_build_function fn /\
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\
    bb_well_formed bb /\
    (!i. MEM i bb.bb_instructions /\
         i.inst_id = (LAST bb.bb_instructions).inst_id ==>
         i = LAST bb.bb_instructions) /\
    MEM (LAST bb.bb_instructions) (fn_insts fn) /\
    transform_block_mode_supply dfg mode s bb = (cc,t) ==>
    cc.bb_instructions <> [] /\
    LAST cc.bb_instructions = LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  drule_all term_id_not_in_mode_scan_weak >> simp[] >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `mm_flat_map_supply f s _ = _` >>
  irule (INST_TYPE [``:'a`` |-> ``:ir_supply``] mm_flat_map_supply_last) >> simp[] >>
  qexistsl_tac [`f`, `s`, `t`] >>
  simp[Abbr `f`] >> conj_tac
  >- metis_tac[apply_groups_inst_supply_nonempty] >>
  simp[apply_groups_inst_supply_def]
QED

Theorem transform_block_memzero_supply_label:
  !dfg s bb cc t.
    transform_block_memzero_supply dfg s bb = (cc,t) ==> cc.bb_label = bb.bb_label
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem transform_block_mode_supply_label:
  !dfg mode s bb cc t.
    transform_block_mode_supply dfg mode s bb = (cc,t) ==> cc.bb_label = bb.bb_label
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem transform_block_memzero_supply_phi_origin:
  !dfg s bb cc t i.
    transform_block_memzero_supply dfg s bb = (cc,t) /\
    MEM i cc.bb_instructions /\ i.inst_opcode = PHI ==> MEM i bb.bb_instructions
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_origin >>
  disch_then (qspec_then `\j. j.inst_opcode = PHI` mp_tac) >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[apply_memzero_inst_supply_phi_origin]) >> simp[]
QED

Theorem transform_block_mode_supply_phi_origin:
  !dfg mode s bb cc t i.
    transform_block_mode_supply dfg mode s bb = (cc,t) /\
    MEM i cc.bb_instructions /\ i.inst_opcode = PHI ==> MEM i bb.bb_instructions
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_origin >>
  disch_then (qspec_then `\j. j.inst_opcode = PHI` mp_tac) >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[apply_groups_inst_supply_phi_origin]) >> simp[]
QED

Theorem transform_block_memzero_supply_load_origin:
  !dfg s bb cc t i mode.
    transform_block_memzero_supply dfg s bb = (cc,t) /\
    MEM i cc.bb_instructions /\ i.inst_opcode = mode_load_opcode mode ==>
    MEM i bb.bb_instructions
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_origin >>
  disch_then (qspec_then `\j. j.inst_opcode = mode_load_opcode mode` mp_tac) >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[apply_memzero_inst_supply_load_origin]) >> simp[]
QED

Theorem transform_block_mode_supply_other_load_origin:
  !dfg mode s bb cc t i other.
    transform_block_mode_supply dfg mode s bb = (cc,t) /\
    MEM i cc.bb_instructions /\ i.inst_opcode = mode_load_opcode other /\
    other <> mode ==> MEM i bb.bb_instructions
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_origin >>
  disch_then (qspec_then `\j. j.inst_opcode = mode_load_opcode other` mp_tac) >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[apply_groups_inst_supply_other_load_origin]) >> simp[]
QED

Theorem transform_block_memzero_supply_ids:
  !dfg s bb cc t.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    transform_block_memzero_supply dfg s bb = (cc,t) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) cc.bb_instructions) /\
    s.irs_next_inst <= t.irs_next_inst /\
    EVERY (\i. i.inst_id < t.irs_next_inst) cc.bb_instructions /\
    (!i. MEM i cc.bb_instructions ==>
      MEM i.inst_id (MAP (\j. j.inst_id) bb.bb_instructions) \/
      (s.irs_next_inst <= i.inst_id /\ i.inst_id < t.irs_next_inst))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `transform_block_memzero_supply _ _ _ = _` mp_tac >>
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_ids >>
  disch_then (qspecl_then [`\i. i.inst_id`, `\u. u.irs_next_inst`] mp_tac) >>
  simp[] >>
  (impl_tac >- metis_tac[apply_memzero_inst_supply_ids]) >> simp[]
QED

Theorem transform_block_mode_supply_ids:
  !dfg mode s bb cc t.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    transform_block_mode_supply dfg mode s bb = (cc,t) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) cc.bb_instructions) /\
    s.irs_next_inst <= t.irs_next_inst /\
    EVERY (\i. i.inst_id < t.irs_next_inst) cc.bb_instructions /\
    (!i. MEM i cc.bb_instructions ==>
      MEM i.inst_id (MAP (\j. j.inst_id) bb.bb_instructions) \/
      (s.irs_next_inst <= i.inst_id /\ i.inst_id < t.irs_next_inst))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_ids >>
  disch_then (qspecl_then [`\i. i.inst_id`, `\u. u.irs_next_inst`] mp_tac) >>
  simp[] >>
  (impl_tac >- metis_tac[apply_groups_inst_supply_ids]) >> simp[]
QED

Theorem inst_id_interval_compose:
  !xs ys zs lo mid hi.
    lo <= mid /\ mid <= hi /\
    (!i. MEM i ys ==> MEM i.inst_id (MAP (\j. j.inst_id) xs) \/
      (lo <= i.inst_id /\ i.inst_id < mid)) /\
    (!i. MEM i zs ==> MEM i.inst_id (MAP (\j. j.inst_id) ys) \/
      (mid <= i.inst_id /\ i.inst_id < hi)) ==>
    !i. MEM i zs ==> MEM i.inst_id (MAP (\j. j.inst_id) xs) \/
      (lo <= i.inst_id /\ i.inst_id < hi)
Proof
  rpt strip_tac >>
  qpat_x_assum `!i. MEM i zs ==> _` (qspec_then `i` mp_tac) >>
  simp[MEM_MAP] >> strip_tac
  >- (rename1 `MEM source ys` >>
      qpat_x_assum `!i. MEM i ys ==> _` (qspec_then `source` mp_tac) >>
      simp[MEM_MAP] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem transform_block_supply_ids:
  !dfg s bb cc t.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    transform_block_supply dfg s bb = (cc,t) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) cc.bb_instructions) /\
    s.irs_next_inst <= t.irs_next_inst /\
    EVERY (\i. i.inst_id < t.irs_next_inst) cc.bb_instructions /\
    (!i. MEM i cc.bb_instructions ==>
      MEM i.inst_id (MAP (\j. j.inst_id) bb.bb_instructions) \/
      (s.irs_next_inst <= i.inst_id /\ i.inst_id < t.irs_next_inst))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `transform_block_supply _ _ _ = _` mp_tac >>
  simp[transform_block_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all transform_block_memzero_supply_ids >> strip_tac >>
  drule_all transform_block_mode_supply_ids >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ CalldataMerge _ _ = _` kall_tac >>
  drule_all transform_block_mode_supply_ids >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ DloadMerge _ _ = _` kall_tac >>
  drule_all transform_block_mode_supply_ids >> strip_tac >>
  simp[] >>
  match_mp_tac inst_id_interval_compose >>
  qexistsl_tac [`bb4.bb_instructions`, `s3.irs_next_inst`] >> simp[] >>
  match_mp_tac inst_id_interval_compose >>
  qexistsl_tac [`bb3.bb_instructions`, `s2.irs_next_inst`] >> simp[] >>
  match_mp_tac inst_id_interval_compose >>
  qexistsl_tac [`bb2.bb_instructions`, `s1.irs_next_inst`] >> simp[] >>
  simp[]
QED

Theorem supply_mode_step:
  !fn mode modes s bb cc t.
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\ ssa_form fn /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    bb_well_formed bb /\ MEM (LAST bb.bb_instructions) (fn_insts fn) /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==> MEM i (fn_insts fn)) /\
    MEM mode modes /\
    (!m i. MEM m modes /\ MEM i bb.bb_instructions /\
      i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
      MEM i (fn_insts fn)) /\
    transform_block_mode_supply (dfg_build_function fn) mode s bb = (cc,t) ==>
    bb_well_formed cc /\
    LAST cc.bb_instructions = LAST bb.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cc.bb_instructions) /\
    EVERY (\i. i.inst_id < t.irs_next_inst) cc.bb_instructions /\
    (!i. MEM i cc.bb_instructions /\ i.inst_opcode = PHI ==> MEM i (fn_insts fn)) /\
    (!m i. MEM m modes /\ m <> mode /\ MEM i cc.bb_instructions /\
      i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
      MEM i (fn_insts fn))
Proof
  rpt gen_tac >> strip_tac >>
  `!i j. MEM i bb.bb_instructions /\ MEM j bb.bb_instructions /\
    i.inst_id = j.inst_id ==> i = j` by metis_tac[all_distinct_map_inv] >>
  `!i. MEM i bb.bb_instructions /\
     i.inst_id = (LAST bb.bb_instructions).inst_id ==> i = LAST bb.bb_instructions` by
    (fs[bb_well_formed_def] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  drule_all transform_block_mode_supply_ids >> strip_tac >>
  `bb_well_formed cc` by
    (drule_at (Pat `transform_block_mode_supply _ _ _ _ = _`)
       transform_block_mode_supply_wf >>
     disch_then (qspec_then `fn` mp_tac) >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  `LAST cc.bb_instructions = LAST bb.bb_instructions` by
    (drule_at (Pat `transform_block_mode_supply _ _ _ _ = _`)
       transform_block_mode_supply_last >>
     disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  simp[] >> conj_tac
  >- metis_tac[transform_block_mode_supply_phi_origin] >>
  rpt strip_tac >>
  `MEM i bb.bb_instructions` by
    metis_tac[transform_block_mode_supply_other_load_origin] >>
  metis_tac[]
QED

Theorem supply_memzero_step:
  !fn dfg s bb cc t.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    bb_well_formed bb /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==> MEM i (fn_insts fn)) /\
    (!m i. MEM i bb.bb_instructions /\
      i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
      MEM i (fn_insts fn)) /\
    transform_block_memzero_supply dfg s bb = (cc,t) ==>
    bb_well_formed cc /\
    LAST cc.bb_instructions = LAST bb.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cc.bb_instructions) /\
    EVERY (\i. i.inst_id < t.irs_next_inst) cc.bb_instructions /\
    (!i. MEM i cc.bb_instructions /\ i.inst_opcode = PHI ==> MEM i (fn_insts fn)) /\
    (!m i. MEM i cc.bb_instructions /\
      i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
      MEM i (fn_insts fn))
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM i bb.bb_instructions /\
     i.inst_id = (LAST bb.bb_instructions).inst_id ==> i = LAST bb.bb_instructions` by
    (fs[bb_well_formed_def] >> metis_tac[all_distinct_map_inv, MEM_LAST_NOT_NIL]) >>
  drule_all transform_block_memzero_supply_ids >> strip_tac >>
  drule_all transform_block_memzero_supply_wf >> strip_tac >>
  drule_all transform_block_memzero_supply_last >> strip_tac >>
  simp[] >> conj_tac
  >- metis_tac[transform_block_memzero_supply_phi_origin] >>
  rpt strip_tac >>
  `MEM i bb.bb_instructions` by
    metis_tac[transform_block_memzero_supply_load_origin] >>
  metis_tac[]
QED

Theorem supply_modes_wf:
  !fn s bb s1 bb1 s2 bb2 t cc.
    fn_inst_wf fn /\ wf_function fn /\ fn_inst_ids_distinct fn /\ ssa_form fn /\
    bb_well_formed bb /\ MEM (LAST bb.bb_instructions) (fn_insts fn) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==> MEM i (fn_insts fn)) /\
    (!m i. MEM i bb.bb_instructions /\
      i.inst_opcode = mode_load_opcode m /\ i.inst_outputs <> [] ==>
      MEM i (fn_insts fn)) /\
    transform_block_mode_supply (dfg_build_function fn) CalldataMerge s bb = (bb1,s1) /\
    transform_block_mode_supply (dfg_build_function fn) DloadMerge s1 bb1 = (bb2,s2) /\
    transform_block_mode_supply (dfg_build_function fn) Mem2Mem s2 bb2 = (cc,t) ==>
    bb_well_formed cc /\ LAST cc.bb_instructions = LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `transform_block_mode_supply _ CalldataMerge _ _ = _`
    (mp_then (Pat `transform_block_mode_supply _ _ _ _ = _`) mp_tac supply_mode_step) >>
  disch_then (qspec_then `[CalldataMerge; DloadMerge; Mem2Mem]` mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[TypeBase.distinct_of ``:merge_mode``]) >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ CalldataMerge _ _ = _` kall_tac >>
  qpat_x_assum `!m i. MEM i bb.bb_instructions /\ _ ==> _` kall_tac >>
  qpat_assum `transform_block_mode_supply _ DloadMerge _ _ = _`
    (mp_then (Pat `transform_block_mode_supply _ _ _ _ = _`) mp_tac supply_mode_step) >>
  disch_then (qspec_then `[DloadMerge; Mem2Mem]` mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[TypeBase.distinct_of ``:merge_mode``]) >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ DloadMerge _ _ = _` kall_tac >>
  qpat_x_assum `!m i. _ /\ m <> CalldataMerge /\ _ ==> _` kall_tac >>
  qpat_assum `transform_block_mode_supply _ Mem2Mem _ _ = _`
    (mp_then (Pat `transform_block_mode_supply _ _ _ _ = _`) mp_tac supply_mode_step) >>
  disch_then (qspec_then `[Mem2Mem]` mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[TypeBase.distinct_of ``:merge_mode``]) >> simp[]
QED

Theorem transform_block_supply_wf_last:
  !fn s bb cc t.
    fn_inst_wf fn /\ wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    transform_block_supply (dfg_build_function fn) s bb = (cc,t) ==>
    bb_well_formed cc /\ LAST cc.bb_instructions = LAST bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `fn_inst_ids_distinct fn /\ bb_well_formed bb` by fs[wf_function_def] >>
  `MEM (LAST bb.bb_instructions) (fn_insts fn)` by
    (irule fn_insts_mem_block >> qexists_tac `bb` >> simp[] >>
     fs[bb_well_formed_def] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  qpat_x_assum `transform_block_supply _ _ _ = _` mp_tac >>
  simp[transform_block_supply_def, AllCaseEqs()] >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[fn_inst_ids_distinct_block] >>
  `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by
    metis_tac[fn_insts_mem_block] >>
  qpat_assum `transform_block_memzero_supply _ _ _ = _`
    (mp_then (Pat `transform_block_memzero_supply _ _ _ = _`) mp_tac supply_memzero_step) >>
  disch_then (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >>
  `MEM (LAST bb2.bb_instructions) (fn_insts fn)` by metis_tac[] >>
  `bb_well_formed cc /\ LAST cc.bb_instructions = LAST bb2.bb_instructions` by
    (drule_all supply_modes_wf >> simp[]) >>
  simp[]
QED

Theorem transform_block_supply_label:
  !dfg s bb cc t.
    transform_block_supply dfg s bb = (cc,t) ==> cc.bb_label = bb.bb_label
Proof
  simp[transform_block_supply_def, AllCaseEqs()] >> rpt strip_tac >>
  `cc.bb_label = bb4.bb_label` by metis_tac[transform_block_mode_supply_label] >>
  `bb4.bb_label = bb3.bb_label` by metis_tac[transform_block_mode_supply_label] >>
  `bb3.bb_label = bb2.bb_label` by metis_tac[transform_block_mode_supply_label] >>
  `bb2.bb_label = bb.bb_label` by
    metis_tac[transform_block_memzero_supply_label] >>
  gvs[]
QED

Theorem transform_block_supply_succs:
  !fn s bb cc t.
    fn_inst_wf fn /\ wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    transform_block_supply (dfg_build_function fn) s bb = (cc,t) ==>
    bb_succs cc = bb_succs bb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all transform_block_supply_wf_last >> strip_tac >>
  `bb.bb_instructions <> [] /\ cc.bb_instructions <> []` by
    fs[wf_function_def, bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> Cases_on `cc.bb_instructions` >>
  gvs[bb_succs_def]
QED

(* Supply invariant: only output names need coverage for later SSA freshness. *)
Definition mm_supply_wf_inv_def:
  mm_supply_wf_inv s fn <=>
    fn_inst_wf fn /\ wf_function fn /\ ssa_form fn /\
    EVERY (\id. id < s.irs_next_inst) (mm_ids fn) /\
    list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) s.irs_used_vars
End

Definition mm_frame_def:
  mm_frame U L X R <=>
    ALL_DISTINCT (L ++ X ++ R) /\ list_subset (L ++ X ++ R) U
End

Theorem mm_frame_delete:
  mm_frame U L X R ==> mm_frame U L [] R
Proof
  simp[mm_frame_def, ALL_DISTINCT_APPEND, list_subset_def,
       EVERY_APPEND, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_frame_fresh:
  mm_frame U L X R /\ ~MEM v U ==> mm_frame (v::U) L [v] R
Proof
  simp[mm_frame_def, ALL_DISTINCT_APPEND, list_subset_def,
       EVERY_APPEND, EVERY_MEM, MEM_APPEND] >> metis_tac[]
QED

Theorem mm_supply_outputs_covered:
  !bbs U. list_subset (FLAT (MAP block_ir_vars bbs)) U ==>
    list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) U
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND,
    list_subset_def, EVERY_APPEND, block_ir_vars_def] >>
  rpt strip_tac
  >- (gvs[EVERY_MEM, MEM_FLAT, MEM_MAP, inst_ir_vars_def] >> metis_tac[MEM_APPEND]) >>
  gvs[list_subset_def]
QED

Theorem mm_supply_wf_inv_init:
  fn_inst_wf fn /\ wf_function fn /\ ssa_form fn /\
  ir_supply_covers_fn s fn ==> mm_supply_wf_inv s fn
Proof
  simp[mm_supply_wf_inv_def, ir_supply_covers_fn_def,
    fn_ir_inst_ids_def, block_ir_inst_ids_def, mm_ids_def] >> strip_tac >>
  conj_tac
  >- gvs[EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF, block_ir_inst_ids_def] >>
  simp[fn_insts_def] >> irule mm_supply_outputs_covered >>
  gvs[fn_ir_vars_def]
QED

Theorem apply_groups_inst_supply_frame:
  apply_groups_inst_supply mode ns rm s i = (out,t) /\
  mm_frame s.irs_used_vars L i.inst_outputs R ==>
  mm_frame t.irs_used_vars L (FLAT (MAP (\j. j.inst_outputs) out)) R
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
      mk_mstore_from_load_def, fresh_inst_id_def]
  >- metis_tac[mm_frame_delete]
  >- metis_tac[mm_frame_delete]
  >- metis_tac[mm_frame_delete]
  >> drule fresh_ir_var_contract >> strip_tac >> gvs[] >>
  metis_tac[mm_frame_fresh]
QED

Theorem apply_memzero_inst_supply_frame:
  apply_memzero_inst_supply ns rm s i = (out,t) /\
  mm_frame s.irs_used_vars L i.inst_outputs R ==>
  mm_frame t.irs_used_vars L (FLAT (MAP (\j. j.inst_outputs) out)) R
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[mk_nop_from_def, mk_zero_store_inst_def,
      mk_memzero_calldatacopy_def, fresh_inst_id_def]
  >- metis_tac[mm_frame_delete]
  >- metis_tac[mm_frame_delete]
  >> drule fresh_ir_var_contract >> strip_tac >> gvs[] >>
  metis_tac[mm_frame_fresh]
QED

Theorem apply_groups_inst_supply_inst_wf:
  apply_groups_inst_supply mode ns rm s i = (out,t) /\ inst_wf i ==>
  EVERY inst_wf out
Proof
  rw[apply_groups_inst_supply_def, AllCaseEqs()] >>
  gvs[]
QED

Theorem apply_memzero_inst_supply_inst_wf:
  apply_memzero_inst_supply ns rm s i = (out,t) /\ inst_wf i ==>
  EVERY inst_wf out
Proof
  rw[apply_memzero_inst_supply_def, AllCaseEqs()] >>
  gvs[inst_wf_def]
QED

Theorem mm_flat_map_supply_frame:
  (!s i out t L R. f s i = (out,t) /\ mm_frame s.irs_used_vars L (p i) R ==>
    mm_frame t.irs_used_vars L (FLAT (MAP p out)) R) ==>
  !xs s ys t L R. mm_flat_map_supply f s xs = (ys,t) /\
    mm_frame s.irs_used_vars L (FLAT (MAP p xs)) R ==>
    mm_frame t.irs_used_vars L (FLAT (MAP p ys)) R
Proof
  strip_tac >> Induct
  >- simp[mm_flat_map_supply_def] >>
  simp[mm_flat_map_supply_def, AllCaseEqs()] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!s i out t L R. _` drule >>
  disch_then (qspecl_then [`L`, `FLAT (MAP p xs) ++ R`] mp_tac) >>
  simp[mm_frame_def, APPEND_ASSOC] >> strip_tac >>
  qpat_x_assum `!s ys t L R. _` drule >>
  disch_then (qspecl_then [`L ++ FLAT (MAP p out)`, `R`] mp_tac) >>
  gvs[mm_frame_def, APPEND_ASSOC]
QED

Theorem mm_flat_map_supply_every:
  (!s i out t. f s i = (out,t) /\ P i ==> EVERY P out) ==>
  !xs s ys t. EVERY P xs /\ mm_flat_map_supply f s xs = (ys,t) ==> EVERY P ys
Proof
  strip_tac >> Induct >> simp[mm_flat_map_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem transform_block_mode_supply_frame:
  transform_block_mode_supply dfg mode s bb = (cc,t) /\
  mm_frame s.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) R ==>
  mm_frame t.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) cc.bb_instructions)) R
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule mm_flat_map_supply_frame >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[apply_groups_inst_supply_frame]
QED

Theorem transform_block_memzero_supply_frame:
  transform_block_memzero_supply dfg s bb = (cc,t) /\
  mm_frame s.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) R ==>
  mm_frame t.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) cc.bb_instructions)) R
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule mm_flat_map_supply_frame >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[apply_memzero_inst_supply_frame]
QED

Theorem transform_block_supply_frame:
  transform_block_supply dfg s bb = (cc,t) /\
  mm_frame s.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) R ==>
  mm_frame t.irs_used_vars L (FLAT (MAP (\i. i.inst_outputs) cc.bb_instructions)) R
Proof
  simp[transform_block_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all transform_block_memzero_supply_frame >> strip_tac >>
  drule_all transform_block_mode_supply_frame >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ CalldataMerge _ _ = _` kall_tac >>
  drule_all transform_block_mode_supply_frame >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ DloadMerge _ _ = _` kall_tac >>
  drule_all transform_block_mode_supply_frame >> simp[]
QED

Theorem transform_block_mode_supply_inst_wf:
  transform_block_mode_supply dfg mode s bb = (cc,t) /\
  EVERY inst_wf bb.bb_instructions ==> EVERY inst_wf cc.bb_instructions
Proof
  simp[transform_block_mode_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_every >>
  simp[] >> disch_then irule >> metis_tac[apply_groups_inst_supply_inst_wf]
QED

Theorem transform_block_memzero_supply_inst_wf:
  transform_block_memzero_supply dfg s bb = (cc,t) /\
  EVERY inst_wf bb.bb_instructions ==> EVERY inst_wf cc.bb_instructions
Proof
  simp[transform_block_memzero_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_flat_map_supply_every >>
  simp[] >> disch_then irule >> metis_tac[apply_memzero_inst_supply_inst_wf]
QED

Theorem transform_block_supply_inst_wf:
  transform_block_supply dfg s bb = (cc,t) /\
  EVERY inst_wf bb.bb_instructions ==> EVERY inst_wf cc.bb_instructions
Proof
  simp[transform_block_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all transform_block_memzero_supply_inst_wf >> strip_tac >>
  drule_all transform_block_mode_supply_inst_wf >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ CalldataMerge _ _ = _` kall_tac >>
  drule_all transform_block_mode_supply_inst_wf >> strip_tac >>
  qpat_x_assum `transform_block_mode_supply _ DloadMerge _ _ = _` kall_tac >>
  drule_all transform_block_mode_supply_inst_wf >> simp[]
QED

Theorem mm_lupdate_split:
  !xs n x. n < LENGTH xs ==>
    LUPDATE x n xs = TAKE n xs ++ [x] ++ DROP (SUC n) xs
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[LUPDATE_def]
QED

Theorem mm_flat_projection_split:
  n < LENGTH xs ==>
  FLAT (MAP p xs) = FLAT (MAP p (TAKE n xs)) ++ p (EL n xs) ++
    FLAT (MAP p (DROP (SUC n) xs))
Proof
  map_every qid_spec_tac [`n`, `xs`] >>
  Induct >> simp[] >> Cases_on `n` >> simp[]
QED

Theorem mm_id_frame_replace:
  ALL_DISTINCT (L ++ X ++ R) /\ EVERY (\id:num. id < a) (L ++ X ++ R) /\
  ALL_DISTINCT Y /\ EVERY (\id. id < b) Y /\ a <= b /\
  (!id. MEM id Y ==> MEM id X \/ a <= id) ==>
  ALL_DISTINCT (L ++ Y ++ R) /\ EVERY (\id. id < b) (L ++ Y ++ R)
Proof
  simp[ALL_DISTINCT_APPEND, EVERY_APPEND, EVERY_MEM, MEM_APPEND] >>
  metis_tac[LESS_LESS_EQ_TRANS, NOT_LESS_EQUAL]
QED

Theorem mm_projection_lupdate_ids:
  n < LENGTH xs /\ ALL_DISTINCT (FLAT (MAP p xs)) /\
  EVERY (\id:num. id < a) (FLAT (MAP p xs)) /\
  ALL_DISTINCT (p x) /\ EVERY (\id. id < b) (p x) /\ a <= b /\
  (!id. MEM id (p x) ==> MEM id (p (EL n xs)) \/ a <= id) ==>
  ALL_DISTINCT (FLAT (MAP p (LUPDATE x n xs))) /\
  EVERY (\id. id < b) (FLAT (MAP p (LUPDATE x n xs)))
Proof
  strip_tac >>
  `FLAT (MAP p xs) = FLAT (MAP p (TAKE n xs)) ++ p (EL n xs) ++
    FLAT (MAP p (DROP (SUC n) xs))` by
    (irule mm_flat_projection_split >> simp[]) >>
  gvs[mm_lupdate_split, MAP_APPEND, FLAT_APPEND] >>
  metis_tac[mm_id_frame_replace, EVERY_APPEND]
QED

Theorem mm_projection_lupdate_frame:
  n < LENGTH xs /\ mm_frame U [] (FLAT (MAP p xs)) [] /\
  (!L R. mm_frame U L (p (EL n xs)) R ==> mm_frame V L (p x) R) ==>
  mm_frame V [] (FLAT (MAP p (LUPDATE x n xs))) []
Proof
  strip_tac >>
  `FLAT (MAP p xs) = FLAT (MAP p (TAKE n xs)) ++ p (EL n xs) ++
    FLAT (MAP p (DROP (SUC n) xs))` by
    (irule mm_flat_projection_split >> simp[]) >>
  gvs[mm_lupdate_split, MAP_APPEND, FLAT_APPEND, mm_frame_def] >>
  first_x_assum (qspecl_then [`FLAT (MAP p (TAKE n xs))`,
    `FLAT (MAP p (DROP (SUC n) xs))`] mp_tac) >> simp[]
QED

Theorem indexed_supply_ids:
  wf_function fn /\ EVERY (\id. id < s.irs_next_inst) (mm_ids fn) /\
  n < LENGTH fn.fn_blocks /\
  transform_block_supply (dfg_build_function fn) s (EL n fn.fn_blocks) = (cc,t) ==>
  fn_inst_ids_distinct (fn with fn_blocks := LUPDATE cc n fn.fn_blocks) /\
  EVERY (\id. id < t.irs_next_inst) (mm_ids (fn with fn_blocks := LUPDATE cc n fn.fn_blocks))
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (EL n fn.fn_blocks).bb_instructions)` by
    metis_tac[wf_function_def, fn_inst_ids_distinct_block, MEM_EL] >>
  `EVERY (\i. i.inst_id < s.irs_next_inst) (EL n fn.fn_blocks).bb_instructions` by
    (fs[mm_ids_def, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF] >> fs[EVERY_MEM] >>
     metis_tac[MEM_EL]) >>
  drule_all transform_block_supply_ids >> strip_tac >>
  simp[fn_inst_ids_distinct_def, mm_ids_def] >>
  irule mm_projection_lupdate_ids >>
  fs[wf_function_def, fn_inst_ids_distinct_def] >>
  simp[EVERY_MAP, combinTheory.o_DEF] >>
  qexists_tac `s.irs_next_inst` >> simp[GSYM mm_ids_def] >>
  metis_tac[MEM_MAP]
QED

Theorem indexed_supply_outputs:
  n < LENGTH fn.fn_blocks /\ ssa_form fn /\
  list_subset (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) s.irs_used_vars /\
  transform_block_supply (dfg_build_function fn) s (EL n fn.fn_blocks) = (cc,t) ==>
  ssa_form (fn with fn_blocks := LUPDATE cc n fn.fn_blocks) /\
  list_subset (FLAT (MAP (\i. i.inst_outputs)
    (fn_insts (fn with fn_blocks := LUPDATE cc n fn.fn_blocks)))) t.irs_used_vars
Proof
  strip_tac >>
  simp[ssa_form_def, fn_insts_def, block_outputs_projection] >>
  `mm_frame t.irs_used_vars []
    (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
      (LUPDATE cc n fn.fn_blocks))) []` suffices_by simp[mm_frame_def] >>
  irule mm_projection_lupdate_frame >>
  simp[] >> qexists_tac `s.irs_used_vars` >> simp[] >> reverse conj_tac
  >- gvs[mm_frame_def, ssa_form_def, fn_insts_def, block_outputs_projection] >>
  metis_tac[transform_block_supply_frame]
QED

Theorem indexed_supply_inv:
  mm_supply_wf_inv s fn /\ n < LENGTH fn.fn_blocks /\
  transform_block_supply (dfg_build_function fn) s (EL n fn.fn_blocks) = (cc,t) ==>
  mm_supply_wf_inv t (fn with fn_blocks := LUPDATE cc n fn.fn_blocks)
Proof
  simp[mm_supply_wf_inv_def] >> strip_tac >>
  drule_all indexed_supply_ids >> strip_tac >>
  drule_all indexed_supply_outputs >> strip_tac >>
  `MEM (EL n fn.fn_blocks) fn.fn_blocks` by metis_tac[MEM_EL] >>
  `EVERY (\i. i.inst_id < s.irs_next_inst) (EL n fn.fn_blocks).bb_instructions` by
    (fs[mm_ids_def, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all transform_block_supply_wf_last >> strip_tac >>
  drule_all transform_block_supply_succs >> strip_tac >>
  drule transform_block_supply_label >> strip_tac >>
  `EVERY inst_wf cc.bb_instructions` by
    (irule transform_block_supply_inst_wf >> goal_assum (drule_at Any) >>
     fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (fs[fn_inst_wf_def, EVERY_MEM] >> rw[MEM_LUPDATE] >> fs[] >> metis_tac[MEM_EL]) >>
  irule indexed_replacement_wf >> simp[]
QED

Theorem transform_blocks_supply_ids:
  !dfg bbs s ccs t.
    ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) /\
    EVERY (\id. id < s.irs_next_inst)
      (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) /\
    transform_blocks_supply dfg s bbs = (ccs,t) ==>
    ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) ccs)) /\
    s.irs_next_inst <= t.irs_next_inst /\
    EVERY (\id. id < t.irs_next_inst)
      (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) ccs)) /\
    (!id. MEM id (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) ccs)) ==>
      MEM id (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) \/
      (s.irs_next_inst <= id /\ id < t.irs_next_inst))
Proof
  gen_tac >> Induct
  >- simp[transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `transform_blocks_supply _ _ _ = _` mp_tac >>
  simp[Once transform_blocks_supply_def, AllCaseEqs()] >> strip_tac >>
  fs[ALL_DISTINCT_APPEND, EVERY_APPEND, EVERY_MAP, combinTheory.o_DEF] >>
  drule_all transform_block_supply_ids >> strip_tac >>
  `EVERY (\id. id < s1.irs_next_inst)
    (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs))` by
    (fs[EVERY_MEM] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  first_x_assum drule_all >> strip_tac >>
  `!i id. MEM i bb'.bb_instructions /\
    MEM id (FLAT (MAP (\b. MAP (\j. j.inst_id) b.bb_instructions) bbs')) ==>
    i.inst_id <> id` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. MEM i bb'.bb_instructions ==> _` (qspec_then `i` mp_tac) >>
     qpat_x_assum `!id. MEM id _ ==> _` (qspec_then `id` mp_tac) >>
     fs[EVERY_MEM] >> metis_tac[NOT_LESS_EQUAL]) >>
  gvs[] >> conj_tac
  >- (simp[ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]) >>
  conj_tac
  >- (simp[EVERY_MAP, combinTheory.o_DEF] >>
      fs[EVERY_MEM] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  gen_tac >> simp[MEM_MAP] >> strip_tac
  >- (gvs[] >>
      qpat_x_assum `!i. MEM i bb'.bb_instructions ==> _` drule >>
      simp[MEM_MAP] >> strip_tac
      >- metis_tac[] >>
      disj2_tac >> intLib.ARITH_TAC) >>
  qpat_x_assum `!id. MEM id _ ==> _` drule >> strip_tac
  >- simp[] >> disj2_tac >> intLib.ARITH_TAC
QED

Theorem transform_blocks_supply_structure:
  !fn bbs s ccs t.
    fn_inst_wf fn /\ wf_function fn /\ ssa_form fn /\
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) /\
    EVERY (\id. id < s.irs_next_inst)
      (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs)) /\
    transform_blocks_supply (dfg_build_function fn) s bbs = (ccs,t) ==>
    MAP (\b. b.bb_label) ccs = MAP (\b. b.bb_label) bbs /\
    EVERY bb_well_formed ccs /\
    (!cc. MEM cc ccs ==> ?bb. MEM bb bbs /\ bb_succs cc = bb_succs bb)
Proof
  gen_tac >> Induct
  >- simp[transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `transform_blocks_supply _ _ _ = _` mp_tac >>
  simp[Once transform_blocks_supply_def, AllCaseEqs()] >> strip_tac >>
  fs[ALL_DISTINCT_APPEND, EVERY_APPEND, EVERY_MAP, combinTheory.o_DEF] >>
  drule_all transform_block_supply_ids >> strip_tac >>
  drule_all transform_block_supply_wf_last >> strip_tac >>
  drule_all transform_block_supply_succs >> strip_tac >>
  drule transform_block_supply_label >> strip_tac >>
  `EVERY (\id. id < s1.irs_next_inst)
    (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) bbs))` by
    (fs[EVERY_MEM] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem mm_preserves_wf_function:
  ∀s fn fn' s'.
    fn_inst_wf fn ∧ wf_function fn ∧ ssa_form fn ∧
    ir_supply_covers_fn s fn ∧
    transform_function_supply s fn = (fn', s') ⇒
    wf_function fn'
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) fn.fn_blocks))` by
    fs[wf_function_def, fn_inst_ids_distinct_def] >>
  `EVERY (\id. id < s.irs_next_inst)
    (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) fn.fn_blocks))` by
    fs[ir_supply_covers_fn_def, fn_ir_inst_ids_def, EVERY_FLAT,
       EVERY_MAP, combinTheory.o_DEF, block_ir_inst_ids_def] >>
  qpat_x_assum `transform_function_supply _ _ = _` mp_tac >>
  simp[transform_function_supply_def, AllCaseEqs()] >> strip_tac >>
  drule_all transform_blocks_supply_ids >> strip_tac >>
  `EVERY (\bb. MEM bb fn.fn_blocks) fn.fn_blocks` by simp[EVERY_MEM] >>
  drule_all transform_blocks_supply_structure >> strip_tac >>
  gvs[wf_function_def, fn_labels_def, fn_has_entry_def,
      fn_inst_ids_distinct_def, EVERY_MEM, fn_succs_closed_def] >>
  conj_tac
  >- (Cases_on `bbs` >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `!cc. MEM cc bbs ==> _` drule >> strip_tac >>
  metis_tac[]
QED

