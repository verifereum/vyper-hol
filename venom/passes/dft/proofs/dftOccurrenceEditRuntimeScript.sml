Theory dftOccurrenceEditRuntime
Ancestors
  dftOccurrenceRuntime dftOccurrenceGasEdit venomWf venomInst
  sccpCorrectnessProofs list rich_list sorting relation

Theorem dft_edit_block_mem:
  bb0.bb_instructions = pre ++ [x;y] ++ post ==>
  (MEM i (dft_gas_edit_block bb0 pre x y post bb).bb_instructions <=>
   MEM i bb.bb_instructions)
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem dft_edit_block_last[local]:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  bb_well_formed bb ==>
  (dft_gas_edit_block bb0 pre x y post bb).bb_instructions <> [] /\
  LAST (dft_gas_edit_block bb0 pre x y post bb).bb_instructions =
    LAST bb.bb_instructions
Proof
  strip_tac >> Cases_on `bb = bb0`
  >- (gvs[dft_gas_edit_block_def] >>
      `is_terminator (LAST (pre ++ [x;y] ++ post)).inst_opcode` by
        (fs[bb_well_formed_def] >> metis_tac[]) >>
      qpat_x_assum `bb_well_formed _` kall_tac >>
      Cases_on `post` >> fs[LAST_APPEND]) >>
  simp[dft_gas_edit_block_def] >> fs[bb_well_formed_def]
QED

Theorem dft_edit_block_succs:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  bb_well_formed bb ==>
  bb_succs (dft_gas_edit_block bb0 pre x y post bb) = bb_succs bb
Proof
  strip_tac >> drule_all dft_edit_block_last >> strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[bb_succs_def] >>
  Cases_on `(dft_gas_edit_block bb0 pre x y post bb).bb_instructions` >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem dft_edit_cfg:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  wf_function fn ==>
  fn_cfg_edge (dft_gas_edit_fn bb0 pre x y post fn) = fn_cfg_edge fn
Proof
  strip_tac >> simp[FUN_EQ_THM, fn_cfg_edge_def, dft_gas_edit_fn_def, MEM_MAP] >>
  rpt gen_tac >>
  `!bb. MEM bb fn.fn_blocks ==>
    bb_succs (dft_gas_edit_block bb0 pre x y post bb) = bb_succs bb` by
    (rpt strip_tac >> irule dft_edit_block_succs >> simp[] >>
     fs[wf_function_def]) >>
  eq_tac >> rpt strip_tac >> gvs[] >> metis_tac[dft_gas_edit_label]
QED

Theorem dft_edit_reachable:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  wf_function fn ==>
  (fn_reachable (dft_gas_edit_fn bb0 pre x y post fn) lbl <=> fn_reachable fn lbl)
Proof
  strip_tac >> drule_all dft_edit_cfg >> simp[fn_reachable_def, dft_gas_edit_entry_label]
QED

Theorem dft_edit_path[local]:
  !p. fn_cfg_edge fn' = fn_cfg_edge fn ==> (is_fn_path fn' p <=> is_fn_path fn p)
Proof
  Induct >> simp[is_fn_path_def] >> Cases_on `p` >> simp[is_fn_path_def]
QED

Theorem dft_edit_dominates:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  wf_function fn ==>
  (fn_dominates (dft_gas_edit_fn bb0 pre x y post fn) d lbl <=> fn_dominates fn d lbl)
Proof
  strip_tac >> drule_all dft_edit_cfg >> strip_tac >>
  `!p. is_fn_path (dft_gas_edit_fn bb0 pre x y post fn) p = is_fn_path fn p` by
    metis_tac[dft_edit_path] >>
  drule_all dft_edit_reachable >> strip_tac >>
  simp[fn_dominates_def, dft_gas_edit_entry_label]
QED

Theorem dft_edit_strict_dom:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  wf_function fn ==>
  (strict_dom_vars_defined (dft_gas_edit_fn bb0 pre x y post fn) s <=>
   strict_dom_vars_defined fn s)
Proof
  strip_tac >>
  `!d. fn_dominates (dft_gas_edit_fn bb0 pre x y post fn) d s.vs_current_bb =
       fn_dominates fn d s.vs_current_bb` by metis_tac[dft_edit_dominates] >>
  simp[strict_dom_vars_defined_def, dft_gas_edit_fn_def, MEM_MAP] >>
  eq_tac >> rpt strip_tac >>
  metis_tac[dft_edit_block_mem, dft_gas_edit_label]
QED

Theorem dft_edit_phi_cons[local]:
  (!i j. i < j /\ j < SUC (LENGTH t) /\
    (EL j (h::t)).inst_opcode = PHI ==> (EL i (h::t)).inst_opcode = PHI) <=>
  (!i j. i < j /\ j < LENGTH t /\
    (EL j t).inst_opcode = PHI ==> (EL i t).inst_opcode = PHI) /\
  (!inst. MEM inst t /\ inst.inst_opcode = PHI ==> h.inst_opcode = PHI)
Proof
  eq_tac
  >- (strip_tac >> conj_tac
      >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[MEM_EL] >> rpt strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `j` >- fs[] >> Cases_on `i` >> fs[] >>
  metis_tac[MEM_EL]
QED

Theorem dft_edit_wf_cons[local]:
  t <> [] ==>
  (bb_well_formed (bb with bb_instructions := h::t) <=>
   bb_well_formed (bb with bb_instructions := t) /\
   ~is_terminator h.inst_opcode /\
   (!i. MEM i t /\ i.inst_opcode = PHI ==> h.inst_opcode = PHI))
Proof
  strip_tac >>
  `!i. (SUC i = LENGTH t <=> i = PRE (LENGTH t))` by
    (Cases_on `t` >> fs[]) >>
  simp[bb_well_formed_def, LAST_DEF, dft_edit_phi_cons] >>
  simp[Once arithmeticTheory.FORALL_NUM] >> metis_tac[]
QED

Theorem dft_edit_wf_swap[local]:
  !pre bb. x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  bb_well_formed (bb with bb_instructions := pre ++ [x;y] ++ post) ==>
  bb_well_formed (bb with bb_instructions := pre ++ [y;x] ++ post)
Proof
  Induct >> simp[]
  >- (Cases_on `post`
      >- (rpt strip_tac >> fs[bb_well_formed_def]) >>
      simp[dft_edit_wf_cons] >> metis_tac[]) >>
  simp[dft_edit_wf_cons] >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[] >>
  fs[] >> metis_tac[]
QED

Theorem dft_edit_block_wf:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  bb_well_formed bb ==>
  bb_well_formed (dft_gas_edit_block bb0 pre x y post bb)
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >> gvs[] >>
  irule dft_edit_wf_swap >> simp[] >>
  qpat_x_assum `bb.bb_instructions = _` (rewrite_tac o single o GSYM) >> simp[]
QED

Theorem dft_edit_block_perm:
  bb0.bb_instructions = pre ++ [x;y] ++ post ==>
  PERM (dft_gas_edit_block bb0 pre x y post bb).bb_instructions bb.bb_instructions
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >>
  gvs[PERM_APPEND_IFF, PERM_SWAP_AT_FRONT]
QED

Theorem dft_edit_insts_perm_lists[local]:
  !bbs. bb0.bb_instructions = pre ++ [x;y] ++ post ==>
  PERM (FLAT (MAP (\bb. (dft_gas_edit_block bb0 pre x y post bb).bb_instructions) bbs))
       (FLAT (MAP (\bb. bb.bb_instructions) bbs))
Proof
  Induct >> simp[] >> rpt strip_tac >> irule PERM_CONG >>
  simp[dft_edit_block_perm]
QED

Theorem dft_edit_insts_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Theorem dft_edit_insts_perm:
  bb0.bb_instructions = pre ++ [x;y] ++ post ==>
  PERM (fn_insts (dft_gas_edit_fn bb0 pre x y post fn)) (fn_insts fn)
Proof
  simp[fn_insts_def, dft_edit_insts_flat, dft_gas_edit_fn_def, MAP_MAP_o, combinTheory.o_DEF,
       dft_edit_insts_perm_lists]
QED

Theorem dft_edit_ssa:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ ssa_form fn ==>
  ssa_form (dft_gas_edit_fn bb0 pre x y post fn)
Proof
  strip_tac >> drule dft_edit_insts_perm >>
  disch_then (qspec_then `fn` assume_tac) >>
  `PERM (FLAT (MAP (\i. i.inst_outputs) (fn_insts (dft_gas_edit_fn bb0 pre x y post fn))))
        (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` by
    metis_tac[PERM_MAP, PERM_FLAT] >>
  fs[ssa_form_def] >> metis_tac[ALL_DISTINCT_PERM]
QED

Theorem dft_edit_ids:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ fn_inst_ids_distinct fn ==>
  fn_inst_ids_distinct (dft_gas_edit_fn bb0 pre x y post fn)
Proof
  strip_tac >> drule dft_edit_insts_perm >>
  disch_then (qspec_then `fn` assume_tac) >>
  `PERM (MAP (\i. i.inst_id) (fn_insts (dft_gas_edit_fn bb0 pre x y post fn)))
        (MAP (\i. i.inst_id) (fn_insts fn))` by metis_tac[PERM_MAP] >>
  gvs[fn_insts_def, dft_edit_insts_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF,
      fn_inst_ids_distinct_def] >> metis_tac[ALL_DISTINCT_PERM]
QED

Theorem dft_edit_labels[simp]:
  fn_labels (dft_gas_edit_fn bb0 pre x y post fn) = fn_labels fn
Proof
  simp[fn_labels_def, dft_gas_edit_fn_def, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem dft_edit_succs_closed:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  wf_function fn ==>
  fn_succs_closed (dft_gas_edit_fn bb0 pre x y post fn)
Proof
  strip_tac >> simp[fn_succs_closed_def, dft_gas_edit_fn_def, MEM_MAP,
    fn_labels_def, MAP_MAP_o, combinTheory.o_DEF] >>
  rpt strip_tac >> gvs[] >> rename1 `MEM bb fn.fn_blocks` >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  drule_all dft_edit_block_succs >> strip_tac >>
  fs[wf_function_def, fn_succs_closed_def, fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem dft_edit_wf_function:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  wf_function fn ==>
  wf_function (dft_gas_edit_fn bb0 pre x y post fn)
Proof
  strip_tac >>
  `fn_succs_closed (dft_gas_edit_fn bb0 pre x y post fn)` by
    (irule dft_edit_succs_closed >> simp[]) >>
  `fn_inst_ids_distinct (dft_gas_edit_fn bb0 pre x y post fn)` by
    (irule dft_edit_ids >> fs[wf_function_def]) >>
  simp[wf_function_def] >>
  conj_tac >- fs[wf_function_def] >>
  conj_tac >- fs[fn_has_entry_def, dft_gas_edit_fn_def, wf_function_def] >>
  simp[dft_gas_edit_fn_def, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  irule dft_edit_block_wf >> fs[wf_function_def]
QED

Theorem dft_edit_insts_wf:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY inst_wf bb.bb_instructions)
    (dft_gas_edit_fn bb0 pre x y post fn).fn_blocks
Proof
  simp[EVERY_MEM, dft_gas_edit_fn_def, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  metis_tac[dft_edit_block_mem]
QED

Theorem dft_edit_runtime_fn_ok:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  dft_runtime_fn_ok fn ==>
  dft_runtime_fn_ok (dft_gas_edit_fn bb0 pre x y post fn)
Proof
  simp[dft_runtime_fn_ok_def] >> rpt strip_tac
  >- (irule dft_edit_wf_function >> simp[])
  >- (irule dft_edit_ssa >> simp[]) >>
  irule dft_edit_insts_wf >> simp[]
QED

Theorem dft_edit_runtime_context:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  EVERY dft_runtime_fn_ok C.ctx_functions ==>
  EVERY dft_runtime_fn_ok (dft_gas_edit_ctx bb0 pre x y post C).ctx_functions
Proof
  simp[dft_gas_edit_ctx_def, EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  irule dft_edit_runtime_fn_ok >> simp[]
QED

Theorem dft_edit_runtime_orbit:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  EVERY dft_runtime_fn_ok C.ctx_functions /\ dft_runtime_fn_ok fn /\
  fn_reachable fn s.vs_current_bb /\ strict_dom_vars_defined fn s ==>
  !k. dft_runtime_ready
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) k
      (dft_occ_init (DftOpen (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n)))
Proof
  strip_tac >> gen_tac >> irule dft_runtime_iter >> reverse conj_tac
  >- (irule dft_edit_runtime_context >> simp[]) >>
  irule dft_runtime_root >> conj_tac
  >- (irule dft_edit_runtime_fn_ok >> simp[]) >>
  `wf_function fn` by fs[dft_runtime_fn_ok_def] >>
  metis_tac[dft_edit_reachable, dft_edit_strict_dom]
QED
