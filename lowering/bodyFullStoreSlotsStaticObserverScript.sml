Theory bodyFullStoreSlotsStaticObserver
Ancestors
  exprSimAbiGasBridge aggregateCountedRawRelabel
  compileEnv fragExec venomInst venomInstProps venomWf venomExecSemantics
  list rich_list

(* The straight-line relabel changes only the already executed prefix. *)
Theorem store_slots_same_block_relabel[local]:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  cs_extends (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_code (start_relabel L ids sa) (start_swap sa L ids sb) =
    frag_code sa sb /\
  emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb) = [] /\
  (start_swap sa L ids sb).cs_current_bb = L /\
  LENGTH (start_swap sa L ids sb).cs_current_insts = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `emitted_blocks sa sb = []` by simp[emitted_blocks_def] >>
  drule frag_extends_emitted_shape >> simp[] >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sb.cs_current_insts` by
    metis_tac[IS_PREFIX_LENGTH] >>
  simp[start_relabel_def, start_swap_def, emitted_blocks_def,
       frag_code_def, exprLoweringPropsTheory.emitted_insts_def, DROP_APPEND,
       cs_extends_def, IS_PREFIX_APPEND]
QED

(* Target readiness is a structural property of an idempotent observer. *)
Theorem store_slots_observer_targets[local]:
  cs_extends a b /\ frag_gas_free a b /\ fn_has_code a b obs /\
  frag_observer a b obs id = obs /\
  (!i l. MEM i (frag_code a b) /\
     (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
     MEM (Label l) i.inst_operands ==>
     l = b.cs_current_bb \/
     MEM l (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))) /\
  (!bb. MEM bb (FRONT (emitted_blocks a b)) ==>
     phi_prefix_length bb.bb_instructions = 0) ==>
  !i l. MEM i (frag_code a b) /\
    (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
    MEM (Label l) i.inst_operands ==>
    l <> a.cs_current_bb /\
    ?bb. lookup_block l obs.fn_blocks = SOME bb /\
         phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `l <> a.cs_current_bb` by
    (fs[frag_gas_free_def, EVERY_MEM] >> metis_tac[]) >>
  simp[] >>
  Cases_on `a.cs_blocks = b.cs_blocks`
  >- (drule frag_extends_emitted_shape >>
      simp[emitted_blocks_def] >> strip_tac >>
      fs[emitted_blocks_def] >> metis_tac[]) >>
  `!bb. lookup_block b.cs_current_bb obs.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    (drule_all frag_observer_end_phi_zero >> simp[] >> metis_tac[]) >>
  Cases_on `l = b.cs_current_bb`
  >- (gvs[] >> fs[fn_has_code_def] >> metis_tac[]) >>
  `MEM l (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))` by
    metis_tac[] >>
  gvs[MEM_MAP] >>
  rename1 `MEM bb (FRONT (emitted_blocks a b))` >>
  `MEM bb (emitted_blocks a b)` by
    (Cases_on `emitted_blocks a b` >> fs[] >>
     metis_tac[rich_listTheory.MEM_FRONT, MEM]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem store_slots_canonical_observer_exists:
  cs_extends sa sb /\ fn_has_code sa sb func /\ frag_ops_free sa sb /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  ~MEM sb.cs_current_bb
    (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  (!bb. MEM bb (FRONT (emitted_blocks sa sb)) ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (!L ids i l. LENGTH ids = LENGTH sa.cs_current_insts /\
    MEM i (frag_code (start_relabel L ids sa) (start_swap sa L ids sb)) /\
    (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
    MEM (Label l) i.inst_operands ==>
    l = (start_swap sa L ids sb).cs_current_bb \/
    MEM l (MAP (\bb. bb.bb_label)
      (FRONT (emitted_blocks (start_relabel L ids sa)
        (start_swap sa L ids sb))))) ==>
  ?L ids id obs.
    LENGTH ids = LENGTH sa.cs_current_insts /\ ALL_DISTINCT ids /\
    ~MEM id ids /\
    (!i. MEM i (frag_code sa sb) ==>
      ~MEM i.inst_id ids /\ i.inst_id <> id) /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
    let a = start_relabel L ids sa in
    let b = start_swap sa L ids sb in
      cs_extends a b /\ frag_code a b = frag_code sa sb /\
      frag_gas_free a b /\ fn_has_code a b obs /\
      fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
      frag_observer a b obs id = obs /\
      (sa.cs_blocks <> sb.cs_blocks ==>
        obs = frag_relabel_observer sa sb L ids func id) /\
      (sa.cs_blocks = sb.cs_blocks ==>
        obs = frag_observer a b func id) /\
      (!i l. MEM i (frag_code a b) /\
        (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
        MEM (Label l) i.inst_operands ==>
        l <> a.cs_current_bb /\
        ?bb. lookup_block l obs.fn_blocks = SOME bb /\
             phi_prefix_length bb.bb_instructions = 0) /\
      a.cs_current_bb = L /\
      LENGTH a.cs_current_insts = LENGTH sa.cs_current_insts /\
      a.cs_next_var = sa.cs_next_var /\
      a.cs_next_label = sa.cs_next_label /\ a.cs_next_id = sa.cs_next_id /\
      b.cs_next_var = sb.cs_next_var /\
      b.cs_next_label = sb.cs_next_label /\ b.cs_next_id = sb.cs_next_id /\
      LENGTH b.cs_current_insts = LENGTH sb.cs_current_insts /\
      (sa.cs_blocks <> sb.cs_blocks ==>
        b.cs_current_bb = sb.cs_current_bb /\
        b.cs_current_insts = sb.cs_current_insts) /\
      (sa.cs_blocks = sb.cs_blocks ==>
        b.cs_current_bb = L /\
        b.cs_current_insts = MAP (\k. mk_inst k NOP [] []) ids ++
          DROP (LENGTH sa.cs_current_insts) sb.cs_current_insts)
Proof
  strip_tac >>
  `?L. L <> sb.cs_current_bb /\
       ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
       EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb)` by
    metis_tac[frag_relabel_fresh_label] >>
  `?ids id. LENGTH ids = LENGTH sa.cs_current_insts /\ ALL_DISTINCT ids /\
       ~MEM id ids /\ (!i. MEM i (frag_code sa sb) ==>
         ~MEM i.inst_id ids /\ i.inst_id <> id)` by
    metis_tac[frag_relabel_fresh_ids] >>
  qexistsl_tac [`L`, `ids`, `id`] >> simp[] >>
  Cases_on `sa.cs_blocks = sb.cs_blocks`
  >- suspend "same_block" >>
  suspend "multiple_blocks"
QED

Resume store_slots_canonical_observer_exists[same_block]:
  qexists_tac `frag_observer (start_relabel L ids sa)
    (start_swap sa L ids sb) func id` >>
  drule_all store_slots_same_block_relabel >> strip_tac >>
  `emitted_blocks sa sb = []` by simp[emitted_blocks_def] >>
  `frag_gas_free (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (gvs[frag_gas_free_def, frag_ops_free_def, start_relabel_def, EVERY_MEM] >>
     metis_tac[]) >>
  qpat_x_assum `!L. cs_extends _ _ /\ _`
    (qspec_then `L` strip_assume_tac) >>
  `fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb)
     (frag_observer (start_relabel L ids sa) (start_swap sa L ids sb) func id)` by
    simp[fn_has_code_def, frag_observer_def, lookup_block_def, FIND_thm,
         IS_PREFIX_APPEND] >>
  `frag_observer (start_relabel L ids sa) (start_swap sa L ids sb)
     (frag_observer (start_relabel L ids sa) (start_swap sa L ids sb) func id) id =
     frag_observer (start_relabel L ids sa) (start_swap sa L ids sb) func id` by
    simp[frag_observer_def] >>
  `fn_inst_ids_distinct
    (frag_observer (start_relabel L ids sa) (start_swap sa L ids sb) func id)` by
    (gvs[fn_inst_ids_distinct_def, frag_observer_def, start_swap_def,
         frag_code_def, exprLoweringPropsTheory.emitted_insts_def,
         MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, mk_inst_def,
         ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]) >>
  simp[start_relabel_def, start_swap_def, frag_observer_def] >>
  qpat_x_assum `!L ids i l. _`
    (qspecl_then [`L`, `ids`] mp_tac) >> simp[] >>
  disch_tac >> rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED

Resume store_slots_canonical_observer_exists[multiple_blocks]:
  qexists_tac `frag_relabel_observer sa sb L ids func id` >>
  drule_all start_relabel_extends >> strip_tac >>
  drule_all start_relabel_frag_code >> strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  `frag_gas_free (start_relabel L ids sa) (start_swap sa L ids sb)` by
    metis_tac[start_relabel_gas_free] >>
  `fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb)
    (frag_relabel_observer sa sb L ids func id)` by
    metis_tac[frag_relabel_observer_has_code] >>
  `fn_inst_ids_distinct (frag_relabel_observer sa sb L ids func id)` by
    metis_tac[frag_relabel_observer_ids] >>
  `frag_observer (start_relabel L ids sa) (start_swap sa L ids sb)
     (frag_relabel_observer sa sb L ids func id) id =
     frag_relabel_observer sa sb L ids func id` by
    metis_tac[frag_relabel_observer_idempotent] >>
  `!i l. MEM i (frag_code (start_relabel L ids sa) (start_swap sa L ids sb)) /\
     (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
     MEM (Label l) i.inst_operands ==>
     l <> (start_relabel L ids sa).cs_current_bb /\
     ?bb. lookup_block l (frag_relabel_observer sa sb L ids func id).fn_blocks =
          SOME bb /\ phi_prefix_length bb.bb_instructions = 0` by
    (match_mp_tac store_slots_observer_targets >> simp[] >>
     conj_tac >- metis_tac[] >>
     drule_all start_swap_emitted_shape >> simp[]) >>
  `emitted_blocks sa sb <> []` by
    (strip_tac >> drule frag_extends_emitted_shape >> simp[]) >>
  gvs[start_relabel_def, start_swap_def, NULL_EQ] >>
  first_assum ACCEPT_TAC
QED

Finalise store_slots_canonical_observer_exists
