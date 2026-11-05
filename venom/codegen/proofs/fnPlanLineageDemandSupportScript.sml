Theory fnPlanLineageDemandSupport
Ancestors
  livenessTransferProofs venomExecProps venomExecProofs finite_map indexedLists list rich_list
Libs
  venomInstTheory venomWfTheory livenessDefsTheory pairTheory

Definition raw_phi_inputs_def:
  raw_phi_inputs instrs =
    FLAT (MAP (\phi. MAP SND (phi_pairs phi.inst_operands))
      (collect_phis instrs))
End

Theorem foldl_pair_updates_domain:
  !pairs m j v.
    v IN FDOM (FOLDL (\m (l,w). m |+ (w,j)) m pairs) <=>
    v IN FDOM m \/ MEM v (MAP SND pairs)
Proof
  Induct_on `pairs` >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> metis_tac[]
QED

Theorem foldl_phi_maps_domain:
  !items op_map matching pred v.
    v IN FDOM (FST (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_,w) => matching |+ (j,w)))
      (op_map,matching) items)) <=>
    v IN FDOM op_map \/
    MEM v (FLAT (MAP (\item. MAP SND (phi_pairs (SND item).inst_operands)) items))
Proof
  Induct_on `items` >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[foldl_pair_updates_domain] >> metis_tac[]
QED

Theorem build_phi_maps_domain:
  !pred phis v.
    v IN FDOM (FST (build_phi_maps pred phis)) <=>
    MEM v (FLAT (MAP (\phi. MAP SND (phi_pairs phi.inst_operands)) phis))
Proof
  simp[build_phi_maps_def, foldl_phi_maps_domain, MAP_MAPi,
       combinTheory.o_DEF, MAPi_EQ_MAP]
QED

Theorem foldl_phi_maps_matching:
  !items op_map matching pred i v.
    FLOOKUP (SND (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_,w) => matching |+ (j,w)))
      (op_map,matching) items)) i = SOME v ==>
    FLOOKUP matching i = SOME v \/
    ?item. MEM item items /\ MEM (pred,v) (phi_pairs (SND item).inst_operands)
Proof
  Induct_on `items` >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (Cases_on `FIND (\(l,w). l = pred) (phi_pairs h1.inst_operands)` >> gvs[] >>
      PairCases_on `x` >> gvs[FLOOKUP_UPDATE] >>
      Cases_on `h0 = i` >> gvs[] >>
      disj2_tac >> qexists_tac `(h0,h1)` >> simp[] >>
      drule FIND_MEM >> drule FIND_P >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem build_phi_maps_matching:
  !pred phis i v.
    FLOOKUP (SND (build_phi_maps pred phis)) i = SOME v ==>
    ?phi. MEM phi phis /\ MEM (pred,v) (phi_pairs phi.inst_operands)
Proof
  rpt gen_tac >> rewrite_tac[build_phi_maps_def] >>
  simp[] >> strip_tac >> drule foldl_phi_maps_matching >>
  simp[MEM_MAPi] >> strip_tac >> gvs[] >>
  qexists_tac `EL i' phis` >> simp[MEM_EL] >>
  qexists_tac `i'` >> simp[]
QED

Theorem input_vars_foldl_origin:
  !base acc placed op_map matching v.
    MEM v (FST (FOLDL (\(acc,placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w],placed)
      | SOME i => if MEM i placed then (acc,placed)
          else case FLOOKUP matching i of
            NONE => (acc,placed)
          | SOME src_v => (acc ++ [src_v],i::placed))
      (acc,placed) base)) ==>
    MEM v acc \/ (MEM v base /\ FLOOKUP op_map v = NONE) \/
    ?i. FLOOKUP matching i = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >>
      simp[MEM_APPEND] >> metis_tac[]) >>
  rename1 `FLOOKUP op_map h = SOME i` >>
  Cases_on `MEM i placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  Cases_on `FLOOKUP matching i` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Theorem input_vars_from_projected_membership:
  !pred instrs base v.
    MEM v (input_vars_from pred instrs base) ==>
    (MEM v base /\ ~MEM v (raw_phi_inputs instrs)) \/
    ?phi. MEM phi (collect_phis instrs) /\
      MEM (pred,v) (phi_pairs phi.inst_operands)
Proof
  rpt gen_tac >> simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)`
  >- (gvs[NULL_EQ, raw_phi_inputs_def]) >>
  Cases_on `build_phi_maps pred (collect_phis instrs)` >>
  rename1 `build_phi_maps pred (collect_phis instrs) = (op_map,matching)` >>
  simp[Once UNCURRY] >> strip_tac >> drule input_vars_foldl_origin >>
  simp[] >> strip_tac
  >- (disj1_tac >> simp[] >>
      qspecl_then [`pred`, `collect_phis instrs`, `v`]
        mp_tac build_phi_maps_domain >>
      gvs[raw_phi_inputs_def, FLOOKUP_DEF]) >>
  disj2_tac >>
  qspecl_then [`pred`, `collect_phis instrs`, `i`, `v`]
    mp_tac build_phi_maps_matching >> gvs[]
QED

Definition demand_available_def:
  demand_available fn bb i v <=>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\
      fn_dominates fn db.bb_label bb.bb_label /\
      (db = bb ==> ?k. k < i /\ k < LENGTH bb.bb_instructions /\
                          EL k bb.bb_instructions = di)
End

Theorem demand_available_endpoint:
  !fn bb v.
    wf_function fn ==>
    (demand_available fn bb (LENGTH bb.bb_instructions) v <=>
     def_available_at fn bb NONE v)
Proof
  rpt gen_tac >> strip_tac >>
  simp[demand_available_def, def_available_at_def] >>
  eq_tac >> strip_tac
  >- metis_tac[] >>
  qexistsl_tac [`def_bb`, `def_inst`] >> simp[] >>
  strip_tac >> gvs[MEM_EL] >> metis_tac[]
QED

Theorem demand_available_predecessor:
  !fn pb bb v.
    wf_function fn /\ MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
    fn_reachable fn pb.bb_label /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
    demand_available fn bb 0 v ==>
    def_available_at fn pb NONE v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  `db.bb_label <> bb.bb_label` by metis_tac[same_label_same_block] >>
  `fn_dominates fn db.bb_label pb.bb_label` by
    (irule fn_dominates_predecessor >> metis_tac[]) >>
  simp[def_available_at_def] >> metis_tac[]
QED

Theorem demand_available_entry:
  !fn eb v.
    wf_function fn /\ entry_block fn = SOME eb ==>
    ~demand_available fn eb 0 v
Proof
  rpt strip_tac >> gvs[demand_available_def] >>
  `fn_entry_label fn = SOME eb.bb_label /\ MEM eb fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[entry_block_def, fn_entry_label_def]) >>
  `db.bb_label = eb.bb_label` by
    (qpat_x_assum `fn_dominates _ _ _` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum (qspec_then `[eb.bb_label]` mp_tac) >>
     simp[is_fn_path_def]) >>
  metis_tac[same_label_same_block]
QED
