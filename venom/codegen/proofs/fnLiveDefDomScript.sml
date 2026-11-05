(*
 * Where a live variable is defined.
 *
 * TOP-LEVEL:
 *   live_def_dominates — in a codegen-ready function, a variable live at a
 *                        point of a reachable block, other than as an
 *                        operand of a PHI at or after that point, has a
 *                        definition whose block dominates the block, and
 *                        that definition comes before the point when it is
 *                        in the same block
 *)

Theory fnLiveDefDom
Ancestors
  stackPlanGen livenessDefs venomWf codegenReadyCompute venomExecProps
  livenessTransferProofs dfAnalyzeDefs livenessBlockProofs
  livenessTerminationProofs worklistDefs

Definition ldd_available_def:
  ldd_available fn bb i v <=>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\
      fn_dominates fn db.bb_label bb.bb_label /\
      (db.bb_label = bb.bb_label ==>
       ?k. k < i /\ EL k bb.bb_instructions = di)
End

Definition ldd_pending_phi_def:
  ldd_pending_phi bb i v <=>
    ?j. i <= j /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = PHI /\
      MEM (Var v) (EL j bb.bb_instructions).inst_operands
End

Definition ldd_state_def:
  ldd_state fn st <=>
    !lbl bb i v. fn_reachable fn lbl /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      i <= LENGTH bb.bb_instructions /\
      MEM v (df_at [] st lbl i) ==>
      ldd_available fn bb i v \/ ldd_pending_phi bb i v
End

Theorem ldd_pending_phi_end[local]:
  ~ldd_pending_phi bb (LENGTH bb.bb_instructions) v
Proof
  rw[ldd_pending_phi_def] >> decide_tac
QED

Theorem ldd_pending_phi_back[local]:
  i <= j /\ ldd_pending_phi bb j v ==> ldd_pending_phi bb i v
Proof
  rw[ldd_pending_phi_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ldd_available_entry[local]:
  ldd_available fn bb 0 v ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\
    fn_dominates fn db.bb_label bb.bb_label /\
    db.bb_label <> bb.bb_label
Proof
  rw[ldd_available_def] >> metis_tac[]
QED

Theorem ldd_state_init[local]:
  ldd_state fn (init_df_state [] lbls)
Proof
  simp[ldd_state_def, init_df_state_def, df_at_def]
QED

Theorem ldd_block_inst_ids_distinct[local]:
  !bbs bb. MEM bb bbs /\
    ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id)
      b.bb_instructions) bbs)) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  Induct >> rw[] >> gvs[listTheory.ALL_DISTINCT_APPEND]
QED

Theorem ldd_inst_position[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
  EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule ldd_block_inst_ids_distinct >> qexists_tac `fn.fn_blocks` >>
     gvs[wf_function_def, fn_inst_ids_distinct_def]) >>
  drule listTheory.ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >>
  simp[listTheory.EL_MAP]
QED

Theorem ldd_available_at_inst[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\
  def_available_at fn bb (SOME (EL i bb.bb_instructions)) v ==>
  ldd_available fn bb i v
Proof
  rw[def_available_at_def, ldd_available_def] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >> strip_tac >>
  `def_bb = bb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >>
  `j = i` by metis_tac[ldd_inst_position] >> gvs[] >>
  metis_tac[]
QED

Theorem ldd_available_at_end[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  def_available_at fn bb NONE v ==>
  ldd_available fn bb (LENGTH bb.bb_instructions) v
Proof
  rw[def_available_at_def, ldd_available_def] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >> strip_tac >>
  `def_bb = bb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >> metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_ordinary_use[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
  ldd_available fn bb i v
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  irule ldd_available_at_inst >> simp[] >>
  gvs[codegen_ready_fn_def, def_dominates_uses_def] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_phi_edge_use[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM (pred,v) (phi_pairs inst.inst_operands) /\
  lookup_block pred fn.fn_blocks = SOME pred_bb ==>
  ldd_available fn pred_bb (LENGTH pred_bb.bb_instructions) v
Proof
  strip_tac >>
  `MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ phi_edge_uses_wf fn bb inst` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  gvs[phi_edge_uses_wf_def] >>
  first_x_assum (drule_then strip_assume_tac) >>
  rename1 `def_available_at fn edge_bb NONE v` >>
  `edge_bb = pred_bb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >> irule ldd_available_at_end >> simp[]
QED

Theorem ldd_input_fold_mem[local]:
  !xs acc placed op_map matching v.
    MEM v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed)) (acc, placed) xs)) ==>
    MEM v acc \/ (MEM v xs /\ FLOOKUP op_map v = NONE) \/
    ?i. FLOOKUP matching i = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >> rename1 `FLOOKUP op_map w` >>
  Cases_on `FLOOKUP op_map w` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[listTheory.MEM_APPEND] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map w = SOME phi_idx` >>
  Cases_on `MEM phi_idx placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  Cases_on `FLOOKUP matching phi_idx` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem ldd_phi_matching_fold[local]:
  !xs op_map matching src i v.
    FLOOKUP (SND (FOLDL (\(om, mt) (j,phi).
      (FOLDL (\m (l,w). m |+ (w,j)) om (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
         NONE => mt | SOME (_,w) => mt |+ (j,w)))
      (op_map, matching) xs)) i = SOME v ==>
    FLOOKUP matching i = SOME v \/
    ?j phi. MEM (j,phi) xs /\ MEM (src,v) (phi_pairs phi.inst_operands)
Proof
  Induct >- simp[] >> rpt gen_tac >> rename1 `ip :: xs` >>
  PairCases_on `ip` >> simp[] >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac)
  >- (Cases_on `FIND (\(l,w). l = src) (phi_pairs ip1.inst_operands)`
      >- gvs[] >>
      rename1 `FIND _ _ = SOME found` >> PairCases_on `found` >>
      gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `ip0 = i` >> gvs[] >>
      drule_then assume_tac venomExecProofsTheory.FIND_MEM >>
      drule_then assume_tac venomExecProofsTheory.FIND_P >> gvs[] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem ldd_phi_pair_domain[local]:
  !pairs m j v.
    v IN FDOM m \/ (?l. MEM (l,v) pairs) ==>
    v IN FDOM (FOLDL (\m (l,w). m |+ (w,j)) m pairs)
Proof
  Induct >- simp[] >> rpt gen_tac >> rename1 `lv :: pairs` >>
  PairCases_on `lv` >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[finite_mapTheory.FDOM_FUPDATE] >>
  metis_tac[]
QED

Theorem ldd_phi_maps_domain_fold[local]:
  !xs om mt src v.
    v IN FDOM om \/
    (?j phi l. MEM (j,phi) xs /\ MEM (l,v) (phi_pairs phi.inst_operands)) ==>
    v IN FDOM (FST (FOLDL (\(om, mt) (j,phi).
      (FOLDL (\m (l,w). m |+ (w,j)) om (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
         NONE => mt | SOME (_,w) => mt |+ (j,w))) (om,mt) xs))
Proof
  Induct >- simp[] >> rpt gen_tac >> rename1 `ip :: xs` >>
  PairCases_on `ip` >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[ldd_phi_pair_domain]
QED

Theorem ldd_phi_maps_domain[local]:
  MEM phi phis /\ MEM (l,v) (phi_pairs phi.inst_operands) ==>
  v IN FDOM (FST (build_phi_maps src phis))
Proof
  strip_tac >> simp[build_phi_maps_def] >>
  irule ldd_phi_maps_domain_fold >> simp[] >>
  simp[indexedListsTheory.MEM_MAPi] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_phi_maps_matching[local]:
  FLOOKUP (SND (build_phi_maps src phis)) i = SOME v ==>
  ?phi. MEM phi phis /\ MEM (src,v) (phi_pairs phi.inst_operands)
Proof
  simp[build_phi_maps_def] >> strip_tac >>
  drule ldd_phi_matching_fold >> simp[] >> strip_tac >>
  gvs[indexedListsTheory.MEM_MAPi] >> metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_collect_phi_prefix[local]:
  !xs j. j < LENGTH xs /\
    (!i. i <= j ==> (EL i xs).inst_opcode = PHI) ==>
    MEM (EL j xs) (collect_phis xs)
Proof
  Induct >- simp[] >> rpt gen_tac >> rename1 `inst :: xs` >>
  Cases_on `j` >- simp[collect_phis_def] >>
  simp[collect_phis_def] >> strip_tac >>
  `inst.inst_opcode = PHI` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >> disj2_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem ldd_pending_phi_domain[local]:
  bb_well_formed bb /\
  (!phi. MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI ==>
    phi_well_formed phi.inst_operands) /\
  ldd_pending_phi bb 0 v ==>
  v IN FDOM (FST (build_phi_maps src (collect_phis bb.bb_instructions)))
Proof
  rw[ldd_pending_phi_def] >>
  `MEM (EL j bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    (irule ldd_collect_phi_prefix >> simp[] >> rpt strip_tac >>
     Cases_on `i = j` >- gvs[] >>
     gvs[bb_well_formed_def] >> metis_tac[arithmeticTheory.LESS_OR_EQ]) >>
  `phi_well_formed (EL j bb.bb_instructions).inst_operands` by
    metis_tac[listTheory.MEM_EL] >>
  drule_all phi_well_formed_var_pair >> strip_tac >>
  irule ldd_phi_maps_domain >> metis_tac[]
QED

Theorem ldd_input_vars_from[local]:
  bb_well_formed bb /\
  (!phi. MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI ==>
    phi_well_formed phi.inst_operands) /\
  MEM v (input_vars_from pred bb.bb_instructions live) ==>
  (MEM v live /\ ~ldd_pending_phi bb 0 v) \/
  (?phi. MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
    MEM (pred,v) (phi_pairs phi.inst_operands))
Proof
  strip_tac >>
  qpat_x_assum `MEM v (input_vars_from _ _ _)` mp_tac >>
  simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis bb.bb_instructions)`
  >- (simp[] >> strip_tac >> disj1_tac >> simp[] >> strip_tac >>
      drule_all ldd_pending_phi_domain >>
      gvs[listTheory.NULL_EQ, build_phi_maps_def]) >>
  Cases_on `build_phi_maps pred (collect_phis bb.bb_instructions)` >>
  rename1 `build_phi_maps _ _ = (op_map, matching)` >> simp[] >>
  simp[Once pairTheory.UNCURRY] >> strip_tac >>
  drule ldd_input_fold_mem >> simp[] >> strip_tac
  >- (disj1_tac >> simp[] >> strip_tac >>
      drule_all ldd_pending_phi_domain >>
      disch_then (qspec_then `pred` mp_tac) >>
      gvs[finite_mapTheory.FLOOKUP_DEF]) >>
  `FLOOKUP (SND (build_phi_maps pred (collect_phis bb.bb_instructions))) i = SOME v`
    by gvs[] >>
  drule ldd_phi_maps_matching >> strip_tac >>
  disj2_tac >> metis_tac[collect_phis_mem]
QED

Theorem ldd_edge_successor[local]:
  codegen_ready_fn fn /\ fn_reachable fn p /\
  MEM s (cfg_succs_of (cfg_analyze fn) p) ==>
  fn_cfg_edge fn p s /\ fn_reachable fn s /\
  ?sb. lookup_block s fn.fn_blocks = SOME sb
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_cfg_edge fn p s` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  simp[] >> conj_tac
  >- metis_tac[venomExecProofsTheory.fn_reachable_step] >>
  gvs[fn_cfg_edge_def, wf_function_def, fn_succs_closed_def] >>
  `MEM s (fn_labels fn)` by metis_tac[] >>
  gvs[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
  metis_tac[MEM_lookup_block]
QED

Theorem ldd_available_predecessor[local]:
  codegen_ready_fn fn /\ fn_reachable fn p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block s fn.fn_blocks = SOME sb /\
  MEM s (cfg_succs_of (cfg_analyze fn) p) /\
  ldd_available fn sb 0 v ==>
  ldd_available fn pb (LENGTH pb.bb_instructions) v
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `pb.bb_label = p /\ sb.bb_label = s /\ MEM pb fn.fn_blocks` by
    metis_tac[lookup_block_label, lookup_block_MEM] >>
  drule ldd_available_entry >> strip_tac >>
  `fn_cfg_edge fn p s` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  `fn_dominates fn db.bb_label p` by
    metis_tac[venomExecProofsTheory.fn_dominates_predecessor] >>
  simp[ldd_available_def] >> qexistsl_tac [`db`, `di`] >> simp[] >>
  strip_tac >> `db = pb` by metis_tac[wf_function_blocks_same_label] >>
  gvs[] >> metis_tac[listTheory.MEM_EL]
QED

Theorem ldd_available_back[local]:
  ldd_available fn bb (SUC i) v /\
  ~MEM v (EL i bb.bb_instructions).inst_outputs ==>
  ldd_available fn bb i v
Proof
  rw[ldd_available_def] >> qexistsl_tac [`db`, `di`] >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  `k <> i` by metis_tac[] >>
  qexists_tac `k` >> simp[]
QED

Theorem ldd_instruction[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (!w. MEM w live ==> ldd_available fn bb (SUC i) w \/
                          ldd_pending_phi bb (SUC i) w) /\
  MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions) live) ==>
  ldd_available fn bb i v \/ ldd_pending_phi bb i v
Proof
  simp[liveness_transfer_def, live_update_mem] >> strip_tac
  >- (gvs[venomInstTheory.inst_defs_def] >>
      metis_tac[ldd_available_back, ldd_pending_phi_back,
                arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  gvs[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI`
  >- (disj2_tac >> simp[ldd_pending_phi_def] >>
      qexists_tac `i` >> simp[]) >>
  disj1_tac >> irule ldd_ordinary_use >> metis_tac[]
QED

Theorem ldd_edge_transfer[local]:
  codegen_ready_fn fn /\ ldd_state fn st /\ fn_reachable fn p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM s (cfg_succs_of (cfg_analyze fn) p) /\
  MEM v (liveness_edge_transfer fn.fn_blocks s p (df_at [] st s 0)) ==>
  ldd_available fn pb (LENGTH pb.bb_instructions) v
Proof
  strip_tac >> drule_all ldd_edge_successor >> strip_tac >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `MEM sb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed sb` by metis_tac[venomExecProofsTheory.wf_function_bb_well_formed] >>
  `!phi. MEM phi sb.bb_instructions /\ phi.inst_opcode = PHI ==>
    phi_well_formed phi.inst_operands` by
    (gvs[def_dominates_uses_def, phi_edge_uses_wf_def] >> metis_tac[]) >>
  gvs[liveness_edge_transfer_def] >>
  drule_all ldd_input_vars_from >> strip_tac
  >- (irule ldd_available_predecessor >> simp[] >>
      qexistsl_tac [`p`, `s`, `sb`] >> simp[] >>
      gvs[ldd_state_def] >> metis_tac[arithmeticTheory.ZERO_LESS_EQ]) >>
  irule ldd_phi_edge_use >> metis_tac[]
QED

Theorem ldd_live_out[local]:
  codegen_ready_fn fn /\ ldd_state fn st /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (liveness_out fn.fn_blocks (cfg_analyze fn) lbl st) ==>
  ldd_available fn bb (LENGTH bb.bb_instructions) v
Proof
  rw[livenessBlockProofsTheory.liveness_out_def, mem_foldl_list_union,
     listTheory.MEM_MAP] >>
  irule ldd_edge_transfer >> metis_tac[]
QED

Theorem ldd_block_point[local]:
  codegen_ready_fn fn /\ ldd_state fn st /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  !i v. i <= LENGTH bb.bb_instructions /\
    MEM v (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) lbl st) lbl i) ==>
    ldd_available fn bb i v \/ ldd_pending_phi bb i v
Proof
  strip_tac >>
  `!n i v. LENGTH bb.bb_instructions = n + i /\
    MEM v (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) lbl st) lbl i) ==>
    ldd_available fn bb i v \/ ldd_pending_phi bb i v` suffices_by
    (strip_tac >> rpt strip_tac >>
     first_x_assum (qspec_then `LENGTH bb.bb_instructions - i` mp_tac) >>
     simp[]) >>
  Induct >- (rpt strip_tac >> gvs[] >>
    `liveness_instrs fn.fn_blocks lbl = bb.bb_instructions` by
      simp[liveness_instrs_def] >>
    `MEM v (liveness_out fn.fn_blocks (cfg_analyze fn) lbl st)` by
      metis_tac[liveness_block_exit] >>
    disj1_tac >> irule ldd_live_out >> metis_tac[]) >>
  rpt strip_tac >>
  `i < LENGTH (liveness_instrs fn.fn_blocks lbl)` by simp[liveness_instrs_def] >>
  drule liveness_block_transfer >> simp[liveness_instrs_def] >> strip_tac >>
  irule ldd_instruction >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) lbl st) lbl (SUC i)` >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  metis_tac[]
QED

Theorem ldd_state_block[local]:
  codegen_ready_fn fn /\ ldd_state fn st ==>
  ldd_state fn (liveness_block fn.fn_blocks (cfg_analyze fn) lbl st)
Proof
  strip_tac >> rw[ldd_state_def] >>
  rename1 `lookup_block queried fn.fn_blocks = SOME bb` >>
  Cases_on `queried = lbl`
  >- (gvs[] >> drule_all ldd_block_point >> metis_tac[]) >>
  gvs[liveness_block_other_inst] >> metis_tac[ldd_state_def]
QED

Theorem ldd_state_fuel[local]:
  codegen_ready_fn fn ==>
  !fuel wl st. ldd_state fn st ==>
    ldd_state fn (SND (wl_iterate_fuel fuel (liveness_changed fn.fn_blocks)
      (liveness_block fn.fn_blocks (cfg_analyze fn))
      (cfg_preds_of (cfg_analyze fn)) wl st))
Proof
  strip_tac >> Induct >> simp[wl_iterate_fuel_def] >>
  rpt strip_tac >> Cases_on `wl` >> simp[wl_iterate_fuel_def] >>
  rename1 `label :: rest` >>
  Cases_on `liveness_changed fn.fn_blocks label st
    (liveness_block fn.fn_blocks (cfg_analyze fn) label st)` >>
  simp[wl_step_def, ldd_state_block]
QED

Theorem ldd_state_analyze[local]:
  codegen_ready_fn fn ==> ldd_state fn (liveness_analyze fn)
Proof
  strip_tac >>
  `?fuel. liveness_recompute_fuel fuel fn = liveness_recompute fn` by
    metis_tac[liveness_recompute_fuel_agreement] >>
  `ldd_state fn (liveness_recompute_fuel fuel fn)` by
    (simp_tac pure_ss [liveness_recompute_fuel_def, boolTheory.LET_THM] >>
     irule ldd_state_fuel >> simp[ldd_state_init]) >>
  gvs[liveness_analyze_def]
QED

(* Used by fnLineageStatic: no stack slot of a lineage state is an output
   of the block it enters.

   Why it should hold: v is live at (lbl, idx), so along some real
   execution path from that point (instructions run in order, a block left
   only after its last instruction, PHI operands read on the incoming edge)
   v is used before any definition of v.  That use has a definition
   available at it (def_dominates_uses: dominating the using block, and
   earlier in it when in the same block; for a PHI operand, available at
   the end of the incoming predecessor).  Prefixing an entry path to lbl
   that doesn't pass through lbl's own instructions after idx, the def must
   lie on the combined path before the use, hence on the entry path or
   before idx in lbl, since the part from (lbl, idx) defines no v.  A PHI
   operand of lbl itself at or after idx is a use on an edge into lbl,
   which this path doesn't reach; hence its exclusion.  Note that the
   liveness soundness witness (livenessProofs$liveness_sound_proof) uses
   cfg_exec_path, which may leave a block early; it is too weak by itself
   for the same-block case. *)
Theorem live_def_dominates:
  !fn lbl bb idx v.
    codegen_ready_fn fn /\ fn_reachable fn lbl /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) lbl idx) /\
    (!j. idx <= j /\ j < LENGTH bb.bb_instructions /\
         (EL j bb.bb_instructions).inst_opcode = PHI ==>
         ~MEM (Var v) (EL j bb.bb_instructions).inst_operands) ==>
    ?def_bb def_inst.
      MEM def_bb fn.fn_blocks /\ MEM def_inst def_bb.bb_instructions /\
      MEM v def_inst.inst_outputs /\
      fn_dominates fn def_bb.bb_label lbl /\
      (def_bb.bb_label = lbl ==>
       ?i. i < idx /\ EL i bb.bb_instructions = def_inst)
Proof
  rpt strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  drule ldd_state_analyze >>
  simp[ldd_state_def, GSYM live_vars_at_def] >>
  disch_then (drule_all_then strip_assume_tac)
  >- (gvs[ldd_available_def] >> metis_tac[]) >>
  gvs[ldd_pending_phi_def] >> metis_tac[]
QED
