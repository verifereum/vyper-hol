(*
 * Assert Combiner — the transform preserves wf_function
 *
 * Why it holds: labels and each block's last instruction (a terminator,
 * never an ASSERT) are unchanged, so bb_succs and fn_succs_closed carry
 * over. Inserted OR/ISZERO and NOP'd/rewritten asserts are neither
 * terminators nor PHIs and sit where an ASSERT was, after the PHI prefix.
 * Original ids stay and are < ac_id_base fn; each rewritten assert with id
 * i adds ids ac_id_base fn + 2i and + 2i + 1, which are >= ac_id_base fn
 * and distinct for distinct i (ids are distinct under wf_function).
 * ac_transform_block_shape (acShapeProofs) gives the per-instruction shape.
 *)

Theory acWfPreserveProofs
Ancestors
  acShapeProofs acChainProofs venomWf venomInst assertCombinerDefs list rich_list irSupply

Theorem ac_shape_nonempty[local]:
  ac_out_shape b cs i out ==> out <> []
Proof
  rw[ac_out_shape_def] >> gvs[]
QED

Theorem ac_shape_unchanged[local]:
  ac_out_shape b cs i out /\ i.inst_opcode <> ASSERT ==> out = [i]
Proof
  rw[ac_out_shape_def] >> gvs[]
QED

Theorem ac_shape_no_terminator[local]:
  ac_out_shape b cs i out /\ ~is_terminator i.inst_opcode ==>
  EVERY (\j. ~is_terminator j.inst_opcode) out
Proof
  rw[ac_out_shape_def] >> gvs[is_terminator_def]
QED

Theorem ac_shape_no_phi[local]:
  ac_out_shape b cs i out /\ i.inst_opcode <> PHI ==>
  EVERY (\j. j.inst_opcode <> PHI) out
Proof
  rw[ac_out_shape_def] >> gvs[]
QED

Theorem ac_shape_ids[local]:
  ac_out_shape b cs i out ==>
  MAP (\j. j.inst_id) out = [i.inst_id] \/
  MAP (\j. j.inst_id) out =
    [ac_or_id b i.inst_id; ac_or_id b i.inst_id + 1; i.inst_id]
Proof
  rw[ac_out_shape_def] >> gvs[]
QED

Theorem ac_prefix_cons[local]:
  (!i j. i < j /\ j < LENGTH (h::xs) /\ P (EL j (h::xs)) ==>
     P (EL i (h::xs))) <=>
  (!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)) /\
  (~P h ==> EVERY (\x. ~P x) xs)
Proof
  simp[EVERY_EL] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  strip_tac >> map_every qx_gen_tac [`i`, `j`] >>
  Cases_on `i` >> Cases_on `j` >> simp[] >> metis_tac[]
QED

Theorem ac_prefix_split[local]:
  !xs. (!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)) <=>
    ?ps ns. xs = ps ++ ns /\ EVERY P ps /\ EVERY (\x. ~P x) ns
Proof
  Induct >> simp[ac_prefix_cons] >> gen_tac >>
  eq_tac
  >- (strip_tac >> Cases_on `P h`
      >- (qexistsl [`h::ps`, `ns`] >> simp[]) >>
      qexistsl [`[]`, `h::xs`] >> simp[]) >>
  strip_tac >> Cases_on `ps` >> gvs[]
  >- (qexistsl [`[]`, `xs`] >> simp[]) >>
  metis_tac[]
QED

Theorem ac_terminal_split[local]:
  !P xs. (xs <> [] /\ P (LAST xs) /\
   (!i. i < LENGTH xs /\ P (EL i xs) ==> i = PRE (LENGTH xs))) <=>
  ?front t. xs = front ++ [t] /\ EVERY (\x. ~P x) front /\ P t
Proof
  rpt gen_tac >> eq_tac
  >- (strip_tac >> qexistsl [`FRONT xs`, `LAST xs`] >>
      simp[APPEND_FRONT_LAST, EVERY_EL] >> rpt strip_tac >>
      gvs[EL_FRONT, LENGTH_FRONT, NULL_EQ] >>
      `n < LENGTH xs` by decide_tac >>
      first_x_assum drule >> simp[] >> decide_tac) >>
  strip_tac >> gvs[LAST_APPEND, EVERY_EL, EL_APPEND_EQN] >>
  rpt strip_tac >> Cases_on `i < LENGTH front` >> gvs[]
QED

Theorem ac_shape_every[local]:
  (!i out. ac_out_shape b cs i out /\ P i ==> EVERY P out) ==>
  !xs outs. LIST_REL (ac_out_shape b cs) xs outs /\ EVERY P xs ==>
    EVERY P (FLAT outs)
Proof
  strip_tac >> Induct >> simp[] >>
  Cases_on `outs` >> simp[] >> metis_tac[]
QED

Theorem ac_shape_prefix[local]:
  !xs outs. LIST_REL (ac_out_shape b cs) xs outs /\
    (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
       (EL i xs).inst_opcode = PHI) ==>
    (!i j. i < j /\ j < LENGTH (FLAT outs) /\
       (EL j (FLAT outs)).inst_opcode = PHI ==>
       (EL i (FLAT outs)).inst_opcode = PHI)
Proof
  simp[ac_prefix_split] >> rpt strip_tac >>
  gvs[LIST_REL_SPLIT1] >>
  rename1 `LIST_REL _ ps op` >> rename1 `LIST_REL _ ns on` >>
  qexistsl [`FLAT op`, `FLAT on`] >> simp[FLAT_APPEND] >> conj_tac
  >- (irule ac_shape_every >> qexistsl [`b`, `cs`, `ps`] >> simp[] >>
      rpt strip_tac >> drule ac_shape_unchanged >> simp[] >>
      strip_tac >> gvs[]) >>
  irule ac_shape_every >> qexistsl [`b`, `cs`, `ns`] >> simp[] >>
  metis_tac[ac_shape_no_phi]
QED

Theorem ac_shape_terminal[local]:
  LIST_REL (ac_out_shape b cs) xs outs /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
  (!i. i < LENGTH xs /\ is_terminator (EL i xs).inst_opcode ==>
       i = PRE (LENGTH xs)) ==>
  FLAT outs <> [] /\ LAST (FLAT outs) = LAST xs /\
  (!i. i < LENGTH (FLAT outs) /\
       is_terminator (EL i (FLAT outs)).inst_opcode ==>
       i = PRE (LENGTH (FLAT outs)))
Proof
  strip_tac >>
  `?front t. xs = front ++ [t] /\
     EVERY (\i. ~is_terminator i.inst_opcode) front /\
     is_terminator t.inst_opcode` by
    (qspecl_then [`\i. is_terminator i.inst_opcode`, `xs`]
       mp_tac ac_terminal_split >> simp[]) >>
  qpat_x_assum `!i. _ ==> i = _` kall_tac >>
  gvs[LIST_REL_SPLIT1] >>
  rename1 `ac_out_shape b cs t out` >>
  `t.inst_opcode <> ASSERT` by (strip_tac >> gvs[is_terminator_def]) >>
  `out = [t]` by metis_tac[ac_shape_unchanged] >> gvs[] >>
  rename1 `LIST_REL _ front pre` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (FLAT pre)` by
    (irule ac_shape_every >> qexistsl [`b`, `cs`, `front`] >>
     simp[] >> metis_tac[ac_shape_no_terminator]) >>
  simp[LAST_APPEND] >>
  rpt strip_tac >> Cases_on `i < LENGTH (FLAT pre)`
  >- (gvs[EVERY_EL, EL_APPEND_EQN]) >> decide_tac
QED

Theorem ac_block_well_formed[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  bb_well_formed bb ==>
  bb_well_formed (ac_transform_block dfg b bb)
Proof
  strip_tac >> drule ac_transform_block_shape >>
  disch_then (qspecl_then [`dfg`, `b`] strip_assume_tac) >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode /\
   (!i. i < LENGTH bb.bb_instructions /\
        is_terminator (EL i bb.bb_instructions).inst_opcode ==>
        i = PRE (LENGTH bb.bb_instructions))` by gvs[bb_well_formed_def] >>
  drule_all ac_shape_terminal >> strip_tac >>
  simp[bb_well_formed_def] >>
  qpat_x_assum `bb_well_formed bb` (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
  drule ac_shape_prefix >> disch_tac >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  qexists `j` >> simp[]
QED

Theorem ac_block_succs[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  bb_well_formed bb ==>
  bb_succs (ac_transform_block dfg b bb) = bb_succs bb
Proof
  strip_tac >> drule ac_transform_block_shape >>
  disch_then (qspecl_then [`dfg`, `b`] strip_assume_tac) >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode /\
   (!i. i < LENGTH bb.bb_instructions /\
        is_terminator (EL i bb.bb_instructions).inst_opcode ==>
        i = PRE (LENGTH bb.bb_instructions))` by gvs[bb_well_formed_def] >>
  drule_all ac_shape_terminal >> strip_tac >>
  Cases_on `bb.bb_instructions` >> Cases_on `FLAT outs` >>
  gvs[bb_succs_def]
QED

Theorem ac_id_namespaces[local]:
  i < b /\ j < b /\
  (k = i \/ k = ac_or_id b i \/ k = ac_or_id b i + 1) /\
  (k = j \/ k = ac_or_id b j \/ k = ac_or_id b j + 1) ==> i = j
Proof
  rw[ac_or_id_def] >> decide_tac
QED

Theorem ac_chunk_ids_distinct[local]:
  ac_out_shape b cs i out /\ i.inst_id < b ==>
  ALL_DISTINCT (MAP (\j. j.inst_id) out)
Proof
  strip_tac >> drule ac_shape_ids >>
  strip_tac >> simp[] >> simp[ac_or_id_def] >> decide_tac
QED

Theorem ac_shape_id_owner[local]:
  !xs outs. LIST_REL (ac_out_shape b cs) xs outs /\
    MEM k (MAP (\i. i.inst_id) (FLAT outs)) ==>
    ?i. MEM i xs /\
      (k = i.inst_id \/ k = ac_or_id b i.inst_id \/ k = ac_or_id b i.inst_id + 1)
Proof
  Induct >> simp[] >> Cases_on `outs` >> simp[] >> rpt strip_tac
  >- (drule ac_shape_ids >> strip_tac >> gvs[] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

Theorem ac_shape_ids_distinct[local]:
  !xs outs. LIST_REL (ac_out_shape b cs) xs outs /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    EVERY (\i. i.inst_id < b) xs ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (FLAT outs))
Proof
  Induct >> simp[] >> Cases_on `outs` >> simp[] >> rpt strip_tac >>
  simp[ALL_DISTINCT_APPEND] >> conj_tac
  >- metis_tac[ac_chunk_ids_distinct] >>
  rpt strip_tac >> drule_all ac_shape_id_owner >> strip_tac >>
  drule ac_shape_ids >> strip_tac >> gvs[EVERY_MEM] >>
  metis_tac[ac_id_namespaces, MEM_MAP]
QED

Theorem ac_block_id_bound[local]:
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions ==>
  i.inst_id < ac_id_base fn
Proof
  strip_tac >> simp[ac_id_base_def] >>
  irule arithmeticTheory.LESS_EQ_IMP_LESS_SUC >>
  irule foldl_max_bound >> disj2_tac >> simp[MEM_MAP] >>
  qexists `i` >> simp[fn_insts_def] >>
  qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >> Induct >> simp[fn_insts_blocks_def] >>
  metis_tac[]
QED

Theorem ac_blocks_ids_flat[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem ac_blocks_id_owner[local]:
  !bbs. ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) /\
    MEM k (MAP (\i. i.inst_id)
      (fn_insts_blocks (MAP (ac_transform_block dfg b) bbs))) ==>
    ?i. MEM i (fn_insts_blocks bbs) /\
      (k = i.inst_id \/ k = ac_or_id b i.inst_id \/ k = ac_or_id b i.inst_id + 1)
Proof
  Induct >> simp[fn_insts_blocks_def, ALL_DISTINCT_APPEND] >> rpt strip_tac
  >- (drule ac_transform_block_shape >>
      disch_then (qspecl_then [`dfg`, `b`] strip_assume_tac) >>
      gvs[] >> drule_all ac_shape_id_owner >> strip_tac >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED

Theorem ac_blocks_ids_distinct[local]:
  !bbs. ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) /\
    EVERY (\i. i.inst_id < b) (fn_insts_blocks bbs) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id)
      (fn_insts_blocks (MAP (ac_transform_block dfg b) bbs)))
Proof
  Induct >> simp[fn_insts_blocks_def, ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  drule ac_transform_block_shape >>
  disch_then (qspecl_then [`dfg`, `b`] strip_assume_tac) >>
  simp[ALL_DISTINCT_APPEND]
  >- metis_tac[ac_shape_ids_distinct] >>
  rpt strip_tac >> drule_all ac_blocks_id_owner >> strip_tac >>
  gvs[] >> drule_all ac_shape_id_owner >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[ac_id_namespaces, MEM_MAP]
QED

Theorem ac_function_ids_distinct[local]:
  fn_inst_ids_distinct fn ==>
  fn_inst_ids_distinct (ac_transform_function fn)
Proof
  simp[fn_inst_ids_distinct_def, GSYM ac_blocks_ids_flat,
       ac_transform_function_def] >> strip_tac >>
  irule ac_blocks_ids_distinct >> simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[ac_id_base_def] >>
  irule arithmeticTheory.LESS_EQ_IMP_LESS_SUC >>
  irule foldl_max_bound >> disj2_tac >>
  simp[MEM_MAP, fn_insts_def] >> metis_tac[]
QED

Theorem ac_wf_block_shape[local]:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  ?outs. LIST_REL
    (ac_out_shape (ac_id_base fn)
      (ac_scan_block (dfg_build_function fn) bb.bb_instructions NONE))
    bb.bb_instructions outs /\
    (ac_transform_block (dfg_build_function fn) (ac_id_base fn) bb).bb_instructions = FLAT outs
Proof
  strip_tac >> conj_asm1_tac
  >- (`fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
      qpat_x_assum `wf_function fn` kall_tac >>
      qpat_x_assum `fn_inst_ids_distinct fn`
        (mp_tac o REWRITE_RULE [fn_inst_ids_distinct_def]) >>
      qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
      qspec_tac (`fn.fn_blocks`, `bbs`) >> Induct >>
      simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  irule ac_transform_block_shape >> simp[]
QED

Theorem ac_preserves_wf_function_proof:
  ∀fn. wf_function fn ⇒ wf_function (ac_transform_function fn)
Proof
  rpt strip_tac >>
  `fn_inst_ids_distinct (ac_transform_function fn)` by
    (irule ac_function_ids_distinct >> gvs[wf_function_def]) >>
  `!bb. MEM bb fn.fn_blocks ==>
    bb_well_formed (ac_transform_block (dfg_build_function fn) (ac_id_base fn) bb) /\
    bb_succs (ac_transform_block (dfg_build_function fn) (ac_id_base fn) bb) = bb_succs bb` by
    (rpt strip_tac >> drule_all ac_wf_block_shape >> strip_tac >>
     `bb_well_formed bb` by metis_tac[wf_function_def] >>
     metis_tac[ac_block_well_formed, ac_block_succs]) >>
  gvs[wf_function_def, ac_transform_function_def, fn_has_entry_def,
      fn_labels_def, MAP_MAP_o, combinTheory.o_DEF, ac_transform_block_label,
      MEM_MAP, fn_succs_closed_def] >> metis_tac[]
QED
