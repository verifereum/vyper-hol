Theory makeSsaCurrentDemandBoundary
Ancestors
  livenessDemandWitness livenessBlockProofs livenessTransferProofs
  livenessDefs list
Libs
  finite_mapTheory pairTheory indexedListsTheory rich_listTheory

Theorem foldl_pair_updates_none[local]:
  !pairs m. FLOOKUP (FOLDL (\m (l,w). m |+ (w, idx)) m pairs) v = NONE <=>
    FLOOKUP m v = NONE /\ ~MEM v (MAP SND pairs)
Proof
  Induct >> simp[] >> Cases >> simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem phi_maps_domain[local]:
  !items opm matching.
  FLOOKUP (FST (FOLDL
    (\(op_map,matching) (j,phi).
      (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (j,w)))
    (opm,matching) items)) v = NONE <=>
  FLOOKUP opm v = NONE /\
  !j phi. MEM (j,phi) items ==> ~MEM v (MAP SND (phi_pairs phi.inst_operands))
Proof
  Induct >- simp[] >> Cases >> rpt gen_tac >>
  simp[foldl_pair_updates_none] >> metis_tac[]
QED

Theorem current_phi_maps_absent:
  FLOOKUP (FST (build_phi_maps src phis)) v = NONE <=>
  !phi. MEM phi phis ==> ~MEM v (MAP SND (phi_pairs phi.inst_operands))
Proof
  simp[build_phi_maps_def, phi_maps_domain, MEM_MAPi] >>
  metis_tac[MEM_EL]
QED

Theorem find_every_selected[local]:
  !P Q xs. EVERY (\x. P x ==> Q x) xs ==>
    !x. FIND P xs = SOME x ==> Q x
Proof
  rpt gen_tac >> Induct_on `xs` >> simp[FIND_thm] >> strip_tac >>
  Cases_on `P h` >> simp[]
QED

Theorem phi_maps_matching_property[local]:
  !Q (items : (num # instruction) list) opm matching.
  (!i w. FLOOKUP matching i = SOME w ==> Q w) /\
  (!j phi w. MEM (j,phi) items /\ MEM (src,w) (phi_pairs phi.inst_operands) ==> Q w) ==>
  !i w. FLOOKUP (SND (FOLDL
    (\(op_map,matching) (j,phi).
      (FOLDL (\m (l,w). m |+ (w,j)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (j,w)))
    (opm,matching) items)) i = SOME w ==> Q w
Proof
  gen_tac >> Induct >- simp[] >> Cases >> rpt gen_tac >> strip_tac >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!opm matching. (_ /\ _) ==> _` irule >>
  conj_tac >- metis_tac[MEM] >>
  goal_assum (drule_at Any) >>
  Cases_on `FIND (\(l,w). l = src) (phi_pairs r.inst_operands)`
  >- (simp[] >> metis_tac[]) >> PairCases_on `x` >>
  `EVERY (\p. (FST p = src) ==> Q (SND p)) (phi_pairs r.inst_operands)` by
    (simp[EVERY_MEM, FORALL_PROD] >> metis_tac[MEM]) >>
  qspecl_then [`\(l,w). l = src`, `\p. Q (SND p)`,
    `phi_pairs r.inst_operands`] mp_tac find_every_selected >>
  simp[UNCURRY] >>
  strip_tac >>
  simp[FLOOKUP_UPDATE] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem current_phi_maps_selected[local]:
  FLOOKUP (SND (build_phi_maps src phis)) i = SOME v ==>
  ?phi. MEM phi phis /\ MEM (src,v) (phi_pairs phi.inst_operands)
Proof
  qspec_then `\w. ?phi. MEM phi phis /\ MEM (src,w) (phi_pairs phi.inst_operands)`
    mp_tac phi_maps_matching_property >>
  disch_then (qspecl_then [`MAPi (\i phi. (i,phi)) phis`, `FEMPTY`, `FEMPTY`] mp_tac) >>
  simp[MEM_MAPi, build_phi_maps_def] >>
  impl_tac >- metis_tac[MEM_EL] >> metis_tac[]
QED

Theorem input_vars_fold_property[local]:
  !base acc placed.
    EVERY Q acc /\
    (!w. MEM w base /\ FLOOKUP op_map w = NONE ==> Q w) /\
    (!i w. FLOOKUP matching i = SOME w ==> Q w) ==>
    EVERY Q (FST (FOLDL (\(acc,placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME idx => if MEM idx placed then (acc,placed)
                    else case FLOOKUP matching idx of
                      NONE => (acc,placed)
                    | SOME sv => (acc ++ [sv],idx::placed))
      (acc,placed) base))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (first_x_assum irule >> simp[EVERY_APPEND] >> metis_tac[MEM]) >>
  Cases_on `MEM x placed` >> simp[]
  >- (first_x_assum irule >> metis_tac[MEM]) >>
  Cases_on `FLOOKUP matching x` >> simp[]
  >- (first_x_assum irule >> metis_tac[MEM]) >>
  first_x_assum irule >> simp[EVERY_APPEND] >> metis_tac[MEM]
QED

Theorem current_input_vars_from_origin:
  MEM v (input_vars_from src instrs live) ==>
  (?phi. MEM phi (collect_phis instrs) /\ MEM (src,v) (phi_pairs phi.inst_operands)) \/
  (MEM v live /\ !phi. MEM phi (collect_phis instrs) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands)))
Proof
  `EVERY (\w.
    (?phi. MEM phi (collect_phis instrs) /\ MEM (src,w) (phi_pairs phi.inst_operands)) \/
    (MEM w live /\ !phi. MEM phi (collect_phis instrs) ==>
      ~MEM w (MAP SND (phi_pairs phi.inst_operands))))
    (input_vars_from src instrs live)` suffices_by
      (simp[EVERY_MEM] >> metis_tac[]) >>
  simp[input_vars_from_def] >>
  Cases_on `NULL (collect_phis instrs)`
  >- (gvs[NULL_EQ, EVERY_MEM]) >>
  Cases_on `build_phi_maps src (collect_phis instrs)` >> simp[] >>
  rename1 `build_phi_maps _ _ = (opm,matching)` >>
  simp[Once UNCURRY] >> irule input_vars_fold_property >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> disj2_tac >> simp[] >>
      metis_tac[current_phi_maps_absent, FST]) >>
  rpt strip_tac >> disj1_tac >>
  irule current_phi_maps_selected >> gvs[] >> metis_tac[]
QED
Theorem current_liveness_edge_origin:
  lookup_block succ bbs = SOME bb /\
  MEM v (liveness_edge_transfer bbs succ pred live) ==>
  (?phi. MEM phi (collect_phis bb.bb_instructions) /\
    MEM (pred,v) (phi_pairs phi.inst_operands)) \/
  (MEM v live /\ !phi. MEM phi (collect_phis bb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands)))
Proof
  strip_tac >> gvs[liveness_edge_transfer_def] >>
  irule current_input_vars_from_origin >> goal_assum (drule_at Any)
QED


Theorem finite_backward_slots[local]:
  !xs f.
    f (LENGTH xs) = out /\
    (!i. i < LENGTH xs ==> f i = transfer (EL i xs) (f (SUC i))) ==>
    !i. i <= LENGTH xs ==> f i = FOLDR transfer out (DROP i xs)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> fs[] >>
  `!i. i <= LENGTH xs ==> f (SUC i) = FOLDR transfer out (DROP i xs)` by
    (qpat_x_assum `!f. _` (qspec_then `\i. f (SUC i)` mp_tac) >>
     (impl_tac >-
       (simp[] >> rpt strip_tac >>
        first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])) >> simp[]) >>
  Cases >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem current_liveness_slot_fold:
  i <= LENGTH (liveness_instrs bbs lbl) ==>
  df_at [] (liveness_block bbs cfg lbl st) lbl i =
    FOLDR (liveness_transfer bbs) (liveness_out bbs cfg lbl st)
      (DROP i (liveness_instrs bbs lbl))
Proof
  strip_tac >> irule finite_backward_slots >>
  simp[liveness_block_exit, liveness_block_transfer]
QED
