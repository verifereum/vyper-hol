Theory fnPlanLineagePhiMaps
Ancestors
  livenessDefs finite_map list rich_list indexedLists stackPlanGen cfgNormSupplyProofs venomInst
  removeUnusedSsaProofs cfgNormBase

Definition phi_operand_map_step_def:
  phi_operand_map_step (m : (string, num) fmap) (i, phi) =
    FOLDL (\m (l,v). m |+ (v,i)) m (phi_pairs phi.inst_operands)
End

Definition phi_matching_map_step_def:
  phi_matching_map_step p (m : (num, string) fmap) (i, phi) =
    case FIND (\(l,v). l = p) (phi_pairs phi.inst_operands) of
      NONE => m
    | SOME (_,v) => m |+ (i,v)
End

Theorem phi_maps_fold_split[local]:
  !xs a b.
  FOLDL (\(om,mm) (i,phi).
    (FOLDL (\m (l,v). m |+ (v,i)) om (phi_pairs phi.inst_operands),
     case FIND (\(l,v). l = p) (phi_pairs phi.inst_operands) of
       NONE => mm | SOME (_,v) => mm |+ (i,v))) (a,b) xs =
  (FOLDL phi_operand_map_step a xs, FOLDL (phi_matching_map_step p) b xs)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[phi_operand_map_step_def, phi_matching_map_step_def]
QED

Theorem build_phi_maps_split:
  build_phi_maps p phis =
  (FOLDL phi_operand_map_step FEMPTY (MAPi (\i phi. (i,phi)) phis),
   FOLDL (phi_matching_map_step p) FEMPTY (MAPi (\i phi. (i,phi)) phis))
Proof
  simp[build_phi_maps_def, phi_maps_fold_split]
QED

Theorem build_phi_maps_source_independent:
  FST (build_phi_maps p phis) = FST (build_phi_maps q phis)
Proof
  simp[build_phi_maps_split]
QED

Theorem phi_matching_fold_below[local]:
  !phis n m i. i < n ==>
  FLOOKUP (FOLDL (phi_matching_map_step p) m
    (MAPi (\k phi. (n+k,phi)) phis)) i = FLOOKUP m i
Proof
  Induct >- (simp[] >> metis_tac[]) >> rpt gen_tac >> strip_tac >>
  simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (\k phi. (n + SUC k,phi)) phis =
   MAPi (\k phi. (SUC n + k,phi)) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`SUC n`, `phi_matching_map_step p m (n,h)`, `i`] mp_tac) >>
  simp[phi_matching_map_step_def] >>
  Cases_on `FIND (\(l,v). l = p) (phi_pairs h.inst_operands)`
  >- simp[] >> PairCases_on `x` >> simp[FLOOKUP_UPDATE]
QED

Theorem phi_matching_fold_index[local]:
  !phis n m j. j < LENGTH phis ==>
  FLOOKUP (FOLDL (phi_matching_map_step p) m
    (MAPi (\k phi. (n+k,phi)) phis)) (n+j) =
  (case FIND (\(l,v). l = p) (phi_pairs (EL j phis).inst_operands) of
     NONE => FLOOKUP m (n+j) | SOME (_,v) => SOME v)
Proof
  Induct >- (simp[] >> metis_tac[]) >> rpt gen_tac >> strip_tac >>
  simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (\k phi. (n + SUC k,phi)) phis =
   MAPi (\k phi. (SUC n + k,phi)) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >> Cases_on `j`
  >- (simp[] >>
      qspecl_then [`phis`, `SUC n`, `phi_matching_map_step p m (n,h)`, `n`]
        mp_tac phi_matching_fold_below >>
      simp[phi_matching_map_step_def] >>
      Cases_on `FIND (\(l,v). l = p) (phi_pairs h.inst_operands)`
      >- simp[] >> PairCases_on `x` >> simp[FLOOKUP_UPDATE]) >>
  gvs[] >> first_x_assum (qspecl_then
    [`SUC n`, `phi_matching_map_step p m (n,h)`, `n'`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
  `FLOOKUP (phi_matching_map_step p m (n,h)) (n + SUC n') =
   FLOOKUP m (n + SUC n')` by
    (simp[phi_matching_map_step_def] >>
     Cases_on `FIND (\(l,v). l = p) (phi_pairs h.inst_operands)`
     >- simp[] >> PairCases_on `x` >> simp[FLOOKUP_UPDATE]) >>
  gvs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem build_phi_maps_matching_index:
  i < LENGTH phis ==>
  FLOOKUP (SND (build_phi_maps p phis)) i =
  OPTION_MAP SND (FIND (\(l,v). l = p) (phi_pairs (EL i phis).inst_operands))
Proof
  strip_tac >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `i`] mp_tac phi_matching_fold_index >>
  simp[build_phi_maps_split] >>
  Cases_on `FIND (\(l,v). l = p) (phi_pairs (EL i phis).inst_operands)`
  >- simp[] >> PairCases_on `x` >> simp[]
QED

Theorem phi_operand_update_range[local]:
  !(pairs : (string # string) list) m (idx:num) (bound:num) v i.
  FLOOKUP (FOLDL (\m (l,w). m |+ (w,idx)) m pairs) v = SOME i ==>
  idx < bound ==>
  (!w j. FLOOKUP m w = SOME j ==> j < bound) ==> i < bound
Proof
  Induct >- (simp[] >> metis_tac[]) >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> disch_then irule >> simp[] >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
  Cases_on `h1 = w` >> simp[] >> metis_tac[]
QED

Theorem phi_operand_fold_range[local]:
  !phis n m bound. n + LENGTH phis <= bound /\
  (!v i. FLOOKUP m v = SOME i ==> i < bound) ==>
  !v i. FLOOKUP (FOLDL phi_operand_map_step m
    (MAPi (\k phi. (n+k,phi)) phis)) v = SOME i ==> i < bound
Proof
  Induct >- (simp[] >> metis_tac[]) >> rpt gen_tac >> strip_tac >>
  simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (\k phi. (n + SUC k,phi)) phis =
   MAPi (\k phi. (SUC n + k,phi)) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`SUC n`, `phi_operand_map_step m (n,h)`, `bound`] mp_tac) >>
  (impl_tac >- (conj_tac >- gvs[] >>
    simp[phi_operand_map_step_def] >>
    rpt gen_tac >> strip_tac >>
    `n < bound` by gvs[] >>
    drule phi_operand_update_range >>
    disch_then irule >> simp[] >> first_assum ACCEPT_TAC)) >> simp[]
QED

Theorem build_phi_maps_operand_range:
  FLOOKUP (FST (build_phi_maps p phis)) v = SOME i ==> i < LENGTH phis
Proof
  qspecl_then [`phis`, `0`, `FEMPTY`, `LENGTH phis`] mp_tac phi_operand_fold_range >>
  simp[build_phi_maps_split] >> metis_tac[]
QED

Theorem build_phi_maps_matching_total:
  EVERY (\phi. ?w. MEM (p,w) (phi_pairs phi.inst_operands)) phis ==>
  !v i. FLOOKUP (FST (build_phi_maps p phis)) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p phis)) i)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `i < LENGTH phis` by (drule build_phi_maps_operand_range >> simp[]) >>
  `?w. MEM (p,w) (phi_pairs (EL i phis).inst_operands)` by
    (gvs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  `!xs : (string # string) list.
     (?w. MEM (p,w) xs) ==> IS_SOME (FIND (\(l,w). l = p) xs)` by
    (Induct >- simp[] >> gen_tac >> PairCases_on `h` >> simp[FIND_thm] >>
     Cases_on `h0 = p` >> gvs[] >> metis_tac[]) >>
  drule build_phi_maps_matching_index >> disch_then (qspec_then `p` SUBST1_TAC) >>
  `IS_SOME (FIND (\(l,w). l = p) (phi_pairs (EL i phis).inst_operands))` by
    (first_x_assum irule >> metis_tac[]) >>
  Cases_on `FIND (\(l,w). l = p) (phi_pairs (EL i phis).inst_operands)` >> gvs[]
QED

Theorem phi_operand_update_lookup[local]:
  !(pairs : (string # string) list) m (idx:num) v.
  FLOOKUP (FOLDL (\m (l,w). m |+ (w,idx)) m pairs) v =
  if (?l. MEM (l,v) pairs) then SOME idx else FLOOKUP m v
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[FLOOKUP_UPDATE] >> Cases_on `h1 = v` >> gvs[] >>
  simp[EXISTS_OR_THM]
QED

Theorem phi_operand_fold_exact[local]:
  !phis n m v i.
  phi_uses_disjoint phis ==>
  (FLOOKUP (FOLDL phi_operand_map_step m
    (MAPi (\k phi. (n+k,phi)) phis)) v = SOME i <=>
   (?j l. j < LENGTH phis /\ i = n+j /\
      MEM (l,v) (phi_pairs (EL j phis).inst_operands)) \/
   (FLOOKUP m v = SOME i /\
      !phi. MEM phi phis ==> ~(?l. MEM (l,v) (phi_pairs phi.inst_operands))))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[phi_uses_disjoint_def] >> strip_tac >>
  simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (\k phi. (n + SUC k,phi)) phis =
   MAPi (\k phi. (SUC n + k,phi)) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`SUC n`, `phi_operand_map_step m (n,h)`, `v`, `i`] mp_tac) >>
  simp[phi_uses_disjoint_def] >> disch_then SUBST1_TAC >>
  `(?j l. j < SUC (LENGTH phis) /\ i = j+n /\
      MEM (l,v) (phi_pairs (EL j (h::phis)).inst_operands)) <=>
   (i = n /\ ?l. MEM (l,v) (phi_pairs h.inst_operands)) \/
   (?j l. j < LENGTH phis /\ i = SUC n+j /\
      MEM (l,v) (phi_pairs (EL j phis).inst_operands))` by
    (eq_tac >> rpt strip_tac
     >- (Cases_on `j` >> gvs[arithmeticTheory.ADD_CLAUSES]
         >- (qexists `l` >> simp[]) >>
         qexistsl [`n'`, `l`] >> simp[])
     >- (qexistsl [`0`, `l`] >> simp[])
     >- (qexistsl [`SUC j`, `l`] >> simp[arithmeticTheory.ADD_CLAUSES])) >>
  pop_assum (fn th => rewrite_tac[SRULE [] th]) >>
  `(?l. MEM (l,v) (phi_pairs h.inst_operands)) ==>
   !phi. MEM phi phis ==> ~(?l. MEM (l,v) (phi_pairs phi.inst_operands))` by
    (rpt strip_tac >>
     gvs[EVERY_MEM, inst_uses_def] >>
     imp_res_tac MEM_phi_pairs_SND_operand_vars >> metis_tac[]) >>
  simp[phi_operand_map_step_def, phi_operand_update_lookup] >>
  Cases_on `?l. MEM (l,v) (phi_pairs h.inst_operands)` >>
  gvs[EXISTS_OR_THM, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `EVERY _ phis` kall_tac >>
  qpat_x_assum `phi_uses_disjoint phis` kall_tac >>
  IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

(* No opcode or well-formedness premise is needed: pair membership alone
   implies operand use, even for malformed instructions. *)
Theorem build_phi_maps_operand_class:
  phi_uses_disjoint phis ==>
  (FLOOKUP (FST (build_phi_maps p phis)) v = SOME i <=>
   i < LENGTH phis /\
   ?l. MEM (l,v) (phi_pairs (EL i phis).inst_operands))
Proof
  strip_tac >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `v`, `i`] mp_tac phi_operand_fold_exact >>
  simp[build_phi_maps_split] >> metis_tac[]
QED

Theorem distinct_key_FIND_member:
  !key xs x. ALL_DISTINCT (MAP key xs) /\ MEM x xs ==>
    FIND (\y. key y = key x) xs = SOME x
Proof
  gen_tac >> Induct >> simp[listTheory.FIND_thm] >>
  rpt gen_tac >> strip_tac >> Cases_on `x = h` >> gvs[] >>
  `key h <> key x` by metis_tac[listTheory.MEM_MAP] >>
  simp[listTheory.FIND_thm]
QED

Definition native_phi_class_def:
  native_phi_class p phis op =
    case op of Var v => FLOOKUP (FST (build_phi_maps p phis)) v
    | _ => NONE
End

Theorem native_phi_class_exact:
  EVERY (\phi. phi_well_formed phi.inst_operands) phis /\
  phi_uses_disjoint phis /\ i < LENGTH phis ==>
  (MEM op (FILTER is_var_operand (EL i phis).inst_operands) <=>
   native_phi_class p phis op = SOME i)
Proof
  strip_tac >>
  `phi_well_formed (EL i phis).inst_operands` by
    (gvs[listTheory.EVERY_EL] >> first_x_assum irule >> simp[]) >>
  Cases_on `op` >>
  simp[native_phi_class_def, stackPlanTypesTheory.is_var_operand_def,
       listTheory.MEM_FILTER] >>
  drule build_phi_maps_operand_class >>
  disch_then (qspecl_then [`s`, `p`, `i`] mp_tac) >>
  metis_tac[venomWfTheory.phi_well_formed_var_pair,
            cfgNormBaseTheory.phi_pairs_mem_var]
QED

Theorem native_phi_class_use:
  phi_uses_disjoint phis /\ native_phi_class p phis (Var v) = SOME i ==>
  i < LENGTH phis /\ MEM v (inst_uses (EL i phis))
Proof
  simp[native_phi_class_def] >> strip_tac >>
  drule build_phi_maps_operand_class >>
  disch_then (qspecl_then [`v`, `p`, `i`] mp_tac) >>
  simp[] >> strip_tac >> simp[inst_uses_def] >>
  metis_tac[MEM_phi_pairs_SND_operand_vars]
QED

Theorem native_phi_matching_class:
  phi_uses_disjoint phis /\ i < LENGTH phis /\
  IS_SOME (FLOOKUP (SND (build_phi_maps q phis)) i) ==>
  native_phi_class p phis
    (Var (THE (FLOOKUP (SND (build_phi_maps q phis)) i))) = SOME i
Proof
  strip_tac >>
  drule build_phi_maps_matching_index >>
  disch_then (qspec_then `q` assume_tac) >>
  Cases_on `FIND (\(l,v). l = q) (phi_pairs (EL i phis).inst_operands)`
  >- gvs[] >> PairCases_on `x` >> gvs[] >>
  `MEM (x0,x1) (phi_pairs (EL i phis).inst_operands)` by
    (drule venomExecPropsTheory.FIND_MEM >> simp[]) >>
  simp[native_phi_class_def] >>
  drule build_phi_maps_operand_class >>
  disch_then (qspecl_then [`x1`, `p`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

(* Matching keys are indexed PHI classes, even when no input variable refers
   to them. This range fact lets consumers use native_phi_matching_class. *)
Theorem phi_matching_fold_range[local]:
  !phis n m bound.
    n + LENGTH phis <= bound /\
    (!i v. FLOOKUP m i = SOME v ==> i < bound) ==>
    !i v. FLOOKUP (FOLDL (phi_matching_map_step p) m
      (MAPi (\k phi. (n+k,phi)) phis)) i = SOME v ==> i < bound
Proof
  Induct >- (simp[] >> metis_tac[]) >> rpt gen_tac >> strip_tac >>
  simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (\k phi. (n + SUC k,phi)) phis =
   MAPi (\k phi. (SUC n + k,phi)) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`SUC n`, `phi_matching_map_step p m (n,h)`, `bound`] mp_tac) >>
  (impl_tac >- (conj_tac >- gvs[] >>
    simp[phi_matching_map_step_def] >>
    Cases_on `FIND (\(l,v). l = p) (phi_pairs h.inst_operands)`
    >- simp[] >> PairCases_on `x` >>
    simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
    Cases_on `n = i` >> gvs[] >> metis_tac[])) >> simp[]
QED

Theorem build_phi_maps_matching_range:
  FLOOKUP (SND (build_phi_maps p phis)) i = SOME v ==> i < LENGTH phis
Proof
  qspecl_then [`phis`, `0`, `FEMPTY`, `LENGTH phis`] mp_tac phi_matching_fold_range >>
  simp[build_phi_maps_split] >> metis_tac[]
QED

Theorem build_phi_maps_matching_operand:
  phi_uses_disjoint phis /\
  FLOOKUP (SND (build_phi_maps p phis)) i = SOME v ==>
  FLOOKUP (FST (build_phi_maps p phis)) v = SOME i
Proof
  rpt strip_tac >>
  `i < LENGTH phis` by metis_tac[build_phi_maps_matching_range] >>
  drule native_phi_matching_class >>
  disch_then (qspecl_then [`p`, `p`] mp_tac) >>
  simp[native_phi_class_def] >>
  disch_then (qspec_then `i` mp_tac) >> simp[]
QED

Theorem input_vars_fold_distinct[local]:
  !live acc placed om mm.
    ALL_DISTINCT (FILTER (\v. FLOOKUP om v = NONE) live) /\
    ALL_DISTINCT acc /\
    (!i v. FLOOKUP mm i = SOME v ==> FLOOKUP om v = SOME i) /\
    (!v. MEM v acc ==> case FLOOKUP om v of
       NONE => ~MEM v live | SOME i => MEM i placed) ==>
    ALL_DISTINCT (FST (FOLDL (\(acc,placed) v.
      case FLOOKUP om v of
        SOME i => if MEM i placed then (acc,placed)
          else (case FLOOKUP mm i of
                  SOME w => (acc ++ [w],i::placed)
                | NONE => (acc,placed))
      | NONE => (acc ++ [v],placed)) (acc,placed) live))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `FLOOKUP om h`
  >- (simp[] >> first_x_assum irule >>
      gvs[ALL_DISTINCT_APPEND, MEM_APPEND, MEM_FILTER] >>
      rpt strip_tac >> gvs[] >>
      first_x_assum drule >> Cases_on `FLOOKUP om v` >> simp[]) >>
  simp[] >> Cases_on `MEM x placed` >> simp[]
  >- (first_x_assum irule >> gvs[] >> rpt strip_tac >>
      first_x_assum drule >> Cases_on `FLOOKUP om v` >> simp[]) >>
  Cases_on `FLOOKUP mm x` >> simp[]
  >- (first_x_assum irule >> gvs[] >> rpt strip_tac >>
      first_x_assum drule >> Cases_on `FLOOKUP om v` >> simp[]) >>
  `FLOOKUP om x' = SOME x` by metis_tac[] >>
  `~MEM x' acc` by
    (strip_tac >> qpat_x_assum `!v. MEM v acc ==> _` drule >> simp[]) >>
  first_x_assum irule >> simp[ALL_DISTINCT_APPEND, MEM_APPEND] >>
  reverse conj_tac >- gvs[] >> gen_tac >> strip_tac
  >- (qpat_x_assum `!w. MEM w acc ==> P w` (qspec_then `v` mp_tac) >>
      simp[] >> Cases_on `FLOOKUP om v` >> simp[]) >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem input_vars_from_residual_distinct:
  !pred insts live om.
    phi_uses_disjoint (collect_phis insts) /\
    om = FST (build_phi_maps pred (collect_phis insts)) /\
    ALL_DISTINCT (FILTER (\v. FLOOKUP om v = NONE) live) ==>
    ALL_DISTINCT (input_vars_from pred insts live)
Proof
  rpt strip_tac >> simp[input_vars_from_def] >>
  IF_CASES_TAC
  >- (gvs[build_phi_maps_def] >> Cases_on `collect_phis insts` >> gvs[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qspecl_then [`live`, `[]`, `[]`, `op_map`, `matching`] mp_tac
    input_vars_fold_distinct >> simp[] >>
  impl_tac >- metis_tac[build_phi_maps_matching_operand, pairTheory.FST, pairTheory.SND] >>
  simp[]
QED

Theorem input_vars_fold_residual_count[local]:
  !live acc placed om mm v.
    (!i w. FLOOKUP mm i = SOME w ==> FLOOKUP om w = SOME i) /\
    FLOOKUP om v = NONE ==>
    LIST_ELEM_COUNT v (FST (FOLDL (\(acc,placed) w.
      case FLOOKUP om w of
        SOME i => if MEM i placed then (acc,placed)
          else (case FLOOKUP mm i of
                  SOME w => (acc ++ [w],i::placed)
                | NONE => (acc,placed))
      | NONE => (acc ++ [w],placed)) (acc,placed) live)) =
    LIST_ELEM_COUNT v acc + LIST_ELEM_COUNT v live
Proof
  Induct >- simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >> simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `FLOOKUP om h`
  >- (simp[] >> first_x_assum drule >>
      disch_then (qspecl_then [`acc ++ [h]`, `placed`, `v`] mp_tac) >>
      simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND, LIST_ELEM_COUNT_THM] >> Cases_on `v = h` >> simp[]) >>
  `v <> h` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  Cases_on `MEM x placed` >> simp[]
  >- (first_x_assum drule >>
      disch_then (qspecl_then [`acc`, `placed`, `v`] mp_tac) >> simp[LIST_ELEM_COUNT_THM]) >>
  Cases_on `FLOOKUP mm x` >> simp[]
  >- (first_x_assum drule >>
      disch_then (qspecl_then [`acc`, `placed`, `v`] mp_tac) >> simp[LIST_ELEM_COUNT_THM]) >>
  `v <> x'` by metis_tac[optionTheory.NOT_NONE_SOME] >>
  qpat_x_assum `!acc placed om mm v. _` drule >>
  disch_then (qspecl_then [`acc ++ [x']`, `x::placed`, `v`] mp_tac) >>
  simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND, LIST_ELEM_COUNT_THM]
QED

Theorem input_vars_from_residual_count:
  phi_uses_disjoint (collect_phis insts) /\
  om = FST (build_phi_maps p (collect_phis insts)) /\
  FLOOKUP om v = NONE ==>
  LIST_ELEM_COUNT v (input_vars_from p insts live) = LIST_ELEM_COUNT v live
Proof
  strip_tac >> simp[input_vars_from_def] >>
  IF_CASES_TAC >- simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qspecl_then [`live`, `[]`, `[]`, `op_map`, `matching`, `v`] mp_tac
    input_vars_fold_residual_count >> simp[LIST_ELEM_COUNT_THM] >>
  impl_tac >- metis_tac[build_phi_maps_matching_operand, pairTheory.FST, pairTheory.SND] >>
  simp[]
QED

Theorem input_vars_fold_selected_count[local]:
  !live acc placed om mm v i.
    (!j w. FLOOKUP mm j = SOME w ==> FLOOKUP om w = SOME j) /\
    FLOOKUP om v = SOME i /\ LIST_ELEM_COUNT v acc <= 1 /\
    (MEM v acc ==> MEM i placed) ==>
    LIST_ELEM_COUNT v (FST (FOLDL (\(acc,placed) w.
      case FLOOKUP om w of
        SOME j => if MEM j placed then (acc,placed)
          else (case FLOOKUP mm j of
                  SOME w => (acc ++ [w],j::placed)
                | NONE => (acc,placed))
      | NONE => (acc ++ [w],placed)) (acc,placed) live)) <= 1
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `FLOOKUP om h`
  >- (simp[] >> first_x_assum irule >> simp[MEM_APPEND] >>
      `v <> h` by metis_tac[optionTheory.NOT_NONE_SOME] >>
      gvs[LIST_ELEM_COUNT_DEF, FILTER_APPEND] >> metis_tac[]) >>
  Cases_on `MEM x placed` >- simp[] >> simp[] >>
  Cases_on `FLOOKUP mm x` >- simp[] >> simp[] >>
  `FLOOKUP om x' = SOME x` by metis_tac[] >>
  qpat_x_assum `!acc placed om mm v i. _` irule >>
  simp[MEM_APPEND, LIST_ELEM_COUNT_DEF, FILTER_APPEND] >>
  Cases_on `v = x'` >> gvs[] >>
  gvs[GSYM LIST_ELEM_COUNT_DEF, GSYM LIST_ELEM_COUNT_MEM] >>
  metis_tac[]
QED

Theorem input_vars_from_selected_count:
  phi_uses_disjoint (collect_phis insts) /\
  om = FST (build_phi_maps p (collect_phis insts)) /\
  FLOOKUP om v = SOME i ==>
  LIST_ELEM_COUNT v (input_vars_from p insts live) <= 1
Proof
  strip_tac >> simp[input_vars_from_def] >>
  IF_CASES_TAC
  >- (gvs[build_phi_maps_def] >> Cases_on `collect_phis insts` >> gvs[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qspecl_then [`live`, `[]`, `[]`, `op_map`, `matching`, `v`, `i`] mp_tac
    input_vars_fold_selected_count >> simp[LIST_ELEM_COUNT_THM] >>
  impl_tac >- metis_tac[build_phi_maps_matching_operand, pairTheory.FST, pairTheory.SND] >>
  simp[]
QED

Theorem input_vars_from_distinct:
  !pred insts live.
    phi_uses_disjoint (collect_phis insts) /\ ALL_DISTINCT live ==>
    ALL_DISTINCT (input_vars_from pred insts live)
Proof
  rpt strip_tac >> irule input_vars_from_residual_distinct >>
  simp[] >> metis_tac[FILTER_ALL_DISTINCT]
QED
