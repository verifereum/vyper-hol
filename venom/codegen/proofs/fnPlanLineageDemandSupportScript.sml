Theory fnPlanLineageDemandSupport
Ancestors
  livenessTransferProofs venomExecProps finite_map indexedLists list rich_list
Libs
  venomInstTheory livenessDefsTheory pairTheory

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
