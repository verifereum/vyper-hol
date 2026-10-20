(* Set interfaces independent of the liveness worklist driver. *)
Theory livenessTransferProofs
Ancestors
  livenessDefs livenessBlockProofs dfHelperProofs
Libs
  listTheory rich_listTheory pred_setTheory arithmeticTheory venomInstTheory
  finite_mapTheory pairTheory indexedListsTheory dfHelperDefsTheory
  dfAnalyzeDefsTheory

Theorem live_update_mem:
  MEM v (live_update defs uses live) <=>
  (MEM v live /\ ~MEM v defs) \/ MEM v uses
Proof
  rw[live_update_def, MEM_APPEND, MEM_FILTER] >> metis_tac[]
QED

Theorem phi_pairs_subset_uses[local]:
  !ops v. MEM v (MAP SND (phi_pairs ops)) ==> MEM v (operand_vars ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  rw[phi_pairs_def, operand_vars_def, operand_var_def] >>
  rpt strip_tac >> TRY (Cases_on `operand_var v1`) >> fs[]
QED

Theorem collect_phis_mem:
  !instrs inst. MEM inst (collect_phis instrs) ==>
    MEM inst instrs /\ inst.inst_opcode = PHI
Proof
  Induct >> simp[collect_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >> gvs[]
QED

Theorem input_vars_foldl_mem[local]:
  !base acc placed op_map matching v.
    MEM v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) ==>
    MEM v acc \/ MEM v base \/ ?i. FLOOKUP matching i = SOME v
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[MEM_APPEND] >> metis_tac[])
  >> rename1 `FLOOKUP op_map h = SOME phi_idx` >>
  Cases_on `MEM phi_idx placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[])
  >> Cases_on `FLOOKUP matching phi_idx` >> simp[]
  >- (strip_tac >> first_x_assum drule >> metis_tac[])
  >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[MEM_APPEND] >> metis_tac[]
QED

Theorem find_some_mem[local]:
  !P ls x. FIND P ls = SOME x ==> MEM x ls /\ P x
Proof
  Induct_on `ls` >> simp[FIND_thm] >> rpt gen_tac >>
  Cases_on `P h` >> simp[] >> strip_tac >> gvs[] >> res_tac >> simp[]
QED

Theorem foldl_phi_matching_inv[local]:
  !phis n acc_op acc_m src i v.
    FLOOKUP (SND (FOLDL
      (\(op_map,matching) (j,phi).
        (FOLDL (\m (l,w). m |+ (w, j)) op_map (phi_pairs phi.inst_operands),
         case FIND (\(l,w). l = src) (phi_pairs phi.inst_operands) of
           NONE => matching
         | SOME (_, w) => matching |+ (j, w)))
      (acc_op, acc_m) (MAPi (\k phi. (n + k, phi)) phis))) i = SOME v ==>
    FLOOKUP acc_m i = SOME v \/
    ?phi. MEM phi phis /\ MEM (src, v) (phi_pairs phi.inst_operands)
Proof
  Induct_on `phis` >- simp[MAPi_def] >>
  rpt gen_tac >> simp[MAPi_def, combinTheory.o_DEF] >>
  `MAPi (\k phi'. (n + SUC k, phi')) phis =
   MAPi (\k phi'. (SUC n + k, phi')) phis` by
    (irule MAPi_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >> strip_tac >>
  first_x_assum (qspecl_then [
    `SUC n`,
    `FOLDL (\m (l,w). m |+ (w, n)) acc_op (phi_pairs h.inst_operands)`,
    `case FIND (\(l,w). l = src) (phi_pairs h.inst_operands) of
       NONE => acc_m | SOME (_, w) => acc_m |+ (n, w)`,
    `src`, `i`, `v`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
  >- (Cases_on `FIND (\(l,w). l = src) (phi_pairs h.inst_operands)`
      >- gvs[]
      >> PairCases_on `x` >> gvs[FLOOKUP_UPDATE] >>
      Cases_on `n = i` >> gvs[] >>
      disj2_tac >> qexists_tac `h` >> simp[] >>
      drule_then strip_assume_tac find_some_mem >> gvs[])
  >> disj2_tac >> metis_tac[]
QED

Theorem build_phi_maps_matching_mem[local]:
  !src phis i v.
    FLOOKUP (SND (build_phi_maps src phis)) i = SOME v ==>
    ?phi. MEM phi phis /\ MEM (src, v) (phi_pairs phi.inst_operands)
Proof
  rw[build_phi_maps_def, LET_THM] >>
  qspecl_then [`phis`, `0`, `FEMPTY`, `FEMPTY`, `src`, `i`, `v`]
    mp_tac foldl_phi_matching_inv >> simp[]
QED

Theorem input_vars_from_phi_correct_proof:
  !src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base \/
    ?inst. MEM inst instrs /\ inst.inst_opcode = PHI /\
           MEM (src_label, v) (phi_pairs inst.inst_operands)
Proof
  rpt gen_tac >> simp[input_vars_from_def, LET_THM] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps src_label (collect_phis instrs)` >>
  rename1 `build_phi_maps _ _ = (op_map, matching)` >> simp[] >>
  simp[Once UNCURRY] >> strip_tac >>
  drule input_vars_foldl_mem >> strip_tac >> gvs[] >>
  qspecl_then [`src_label`, `collect_phis instrs`, `i`, `v`]
    mp_tac build_phi_maps_matching_mem >>
  impl_tac >- gvs[] >> strip_tac >>
  disj2_tac >> qexists_tac `phi` >> simp[] >>
  metis_tac[collect_phis_mem]
QED

Theorem input_vars_from_vars_bounded:
  !src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base \/ ?inst. MEM inst instrs /\ MEM v (inst_uses inst)
Proof
  rpt strip_tac >>
  drule input_vars_from_phi_correct_proof >> strip_tac >> fs[] >>
  disj2_tac >> qexists_tac `inst` >> rw[inst_uses_def] >>
  irule phi_pairs_subset_uses >>
  simp[MEM_MAP] >> qexists_tac `(src_label, v)` >> simp[]
QED

Theorem fn_all_vars_mem:
  !bbs bb inst v.
    MEM bb bbs /\ MEM inst bb.bb_instructions /\
    (MEM v (inst_uses inst) \/ MEM v (inst_defs inst)) ==>
    MEM v (fn_all_vars bbs)
Proof
  rw[fn_all_vars_def, MEM_FLAT, MEM_MAP, MEM_APPEND] >> (
    qexists_tac `FLAT (MAP (\i. inst_uses i ++ inst_defs i)
      bb.bb_instructions)` >>
    rw[MEM_FLAT, MEM_MAP, MEM_APPEND] >>
    TRY (qexists_tac `bb` >> rw[]) >>
    qexists_tac `inst_uses inst ++ inst_defs inst` >>
    rw[MEM_APPEND] >> qexists_tac `inst` >> rw[])
QED

Theorem lookup_block_mem:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
  gvs[lookup_block_def] >> res_tac >> simp[]
QED

Theorem liveness_transfer_bounded:
  !bbs inst live U.
    (!v. MEM v live ==> MEM v U) /\
    (!v. MEM v (inst_uses inst) ==> MEM v U) ==>
    !v. MEM v (liveness_transfer bbs inst live) ==> MEM v U
Proof
  rw[liveness_transfer_def, live_update_mem] >> metis_tac[]
QED

Theorem liveness_edge_transfer_bounded:
  !bbs succ_lbl cur_lbl live U.
    (!v. MEM v live ==> MEM v U) /\
    (!bb inst v. MEM bb bbs /\ MEM inst bb.bb_instructions /\
                 MEM v (inst_uses inst) ==> MEM v U) ==>
    !v. MEM v (liveness_edge_transfer bbs succ_lbl cur_lbl live) ==> MEM v U
Proof
  rw[liveness_edge_transfer_def] >>
  Cases_on `lookup_block succ_lbl bbs` >> fs[] >>
  drule input_vars_from_vars_bounded >> strip_tac >> fs[] >>
  imp_res_tac lookup_block_mem >> metis_tac[]
QED

Theorem list_union_mem:
  MEM v (list_union a b) <=> MEM v a \/ MEM v b
Proof
  simp[list_union_mem_proof]
QED

Theorem list_union_set:
  set (list_union a b) = set a UNION set b
Proof
  simp[EXTENSION, list_union_mem]
QED

Theorem list_union_bounded:
  !a b U.
    (!v. MEM v a ==> MEM v U) /\ (!v. MEM v b ==> MEM v U) ==>
    !v. MEM v (list_union a b) ==> MEM v U
Proof
  rw[list_union_mem] >> metis_tac[]
QED

Theorem liveness_transfer_mono:
  !bbs inst a b.
    set a SUBSET set b ==>
    set (liveness_transfer bbs inst a) SUBSET set (liveness_transfer bbs inst b)
Proof
  rw[liveness_transfer_def, live_update_def,
     LIST_TO_SET_APPEND, LIST_TO_SET_FILTER, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem foldl_acc_persists[local]:
  !base acc placed op_map matching v.
    MEM v acc ==>
    MEM v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base))
Proof
  Induct >> rw[] >>
  Cases_on `FLOOKUP op_map h` >> simp[] >>
  Cases_on `MEM x placed` >> simp[] >>
  Cases_on `FLOOKUP matching x` >> simp[]
QED

Theorem foldl_mem_tight[local]:
  !base acc placed op_map matching v.
    MEM v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) ==>
    MEM v acc \/
    (MEM v base /\ FLOOKUP op_map v = NONE) \/
    (?idx w. MEM w base /\ FLOOKUP op_map w = SOME idx /\
             FLOOKUP matching idx = SOME v)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP op_map h` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[MEM_APPEND] >> metis_tac[])
  >> Cases_on `MEM x placed` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[] >> metis_tac[MEM])
  >> Cases_on `FLOOKUP matching x` >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[] >> metis_tac[MEM])
  >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[MEM_APPEND] >> metis_tac[MEM]
QED

Theorem foldl_passthrough[local]:
  !base acc placed op_map matching w.
    MEM w base /\ FLOOKUP op_map w = NONE ==>
    MEM w (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (irule foldl_acc_persists >> simp[])
  >> qmatch_goalsub_abbrev_tac `FOLDL _ init _` >>
  first_x_assum (qspecl_then [`FST init`, `SND init`,
    `op_map`, `matching`, `w`] mp_tac) >> simp[Abbr`init`, PAIR]
QED

Theorem foldl_replacement[local]:
  !base acc placed op_map matching idx src_v.
    (?w. MEM w base /\ FLOOKUP op_map w = SOME idx) /\
    FLOOKUP matching idx = SOME src_v ==>
    MEM src_v (FST (FOLDL (\(acc, placed) w.
      case FLOOKUP op_map w of
        NONE => (acc ++ [w], placed)
      | SOME phi_idx =>
          if MEM phi_idx placed then (acc, placed)
          else case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx::placed)
               | NONE => (acc, placed))
      (acc, placed) base)) \/ MEM idx placed
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (Cases_on `MEM idx placed` >> simp[] >>
      irule foldl_acc_persists >> simp[])
  >> qmatch_goalsub_abbrev_tac `FOLDL _ init _` >>
  first_x_assum (qspecl_then [`FST init`, `SND init`,
    `op_map`, `matching`, `idx`, `src_v`] mp_tac) >> simp[PAIR] >>
  impl_tac >- (simp[Abbr`init`] >> metis_tac[]) >>
  strip_tac >> gvs[] >> simp[Abbr`init`] >>
  Cases_on `FLOOKUP op_map h` >> gvs[] >>
  Cases_on `MEM x placed` >> gvs[] >>
  Cases_on `FLOOKUP matching x` >> gvs[IN_INSERT] >>
  irule foldl_acc_persists >> simp[]
QED

Theorem input_vars_from_mono:
  !instrs lbl a b.
    set a SUBSET set b ==>
    set (input_vars_from lbl instrs a) SUBSET
    set (input_vars_from lbl instrs b)
Proof
  rpt gen_tac >> simp[input_vars_from_def, LET_THM] >>
  Cases_on `NULL (collect_phis instrs)` >- simp[] >>
  Cases_on `build_phi_maps lbl (collect_phis instrs)` >>
  rename1 `_ = (op_map, matching)` >> simp[] >>
  simp[Ntimes UNCURRY 2] >>
  strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
  drule foldl_mem_tight >> strip_tac >> gvs[]
  >- (irule foldl_passthrough >> metis_tac[SUBSET_DEF])
  >> `MEM w b` by metis_tac[SUBSET_DEF] >>
  qspecl_then [`b`, `[]`, `[]`, `op_map`, `matching`, `idx`, `x`]
    mp_tac foldl_replacement >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

Theorem liveness_edge_transfer_mono:
  !bbs succ lbl a b.
    set a SUBSET set b ==>
    set (liveness_edge_transfer bbs succ lbl a) SUBSET
    set (liveness_edge_transfer bbs succ lbl b)
Proof
  rw[liveness_edge_transfer_def] >>
  Cases_on `lookup_block succ bbs` >> simp[SUBSET_REFL] >>
  irule input_vars_from_mono >> simp[]
QED

Theorem foldl_list_union_mono:
  !xs ys a b.
    LENGTH xs = LENGTH ys /\ set a SUBSET set b /\
    (!i. i < LENGTH xs ==> set (EL i xs) SUBSET set (EL i ys)) ==>
    set (FOLDL list_union a xs) SUBSET set (FOLDL list_union b ys)
Proof
  Induct >> rpt gen_tac >> strip_tac >> Cases_on `ys` >> fs[] >>
  first_x_assum irule >>
  `set h SUBSET set h'` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
  >- simp[]
  >> simp[list_union_set, SUBSET_DEF] >> metis_tac[SUBSET_DEF]
QED

Theorem mem_foldl_list_union:
  !xs acc v. MEM v (FOLDL list_union acc xs) <=>
    MEM v acc \/ ?ys. MEM ys xs /\ MEM v ys
Proof
  Induct >> simp[list_union_mem] >> metis_tac[]
QED

Theorem foldl_list_union_bounded:
  !xs acc U.
    (!v. MEM v acc ==> MEM v U) /\
    (!ys v. MEM ys xs /\ MEM v ys ==> MEM v U) ==>
    !v. MEM v (FOLDL list_union acc xs) ==> MEM v U
Proof
  simp[mem_foldl_list_union] >> metis_tac[]
QED

Theorem liveness_out_mono:
  (!s. set (df_at [] st s 0) SUBSET set (df_at [] st' s 0)) ==>
  set (liveness_out bbs cfg lbl st) SUBSET
  set (liveness_out bbs cfg lbl st')
Proof
  strip_tac >> simp[liveness_out_def] >>
  irule foldl_list_union_mono >> simp[] >>
  rpt strip_tac >> simp[EL_MAP] >>
  irule liveness_edge_transfer_mono >> simp[]
QED

Theorem liveness_out_bounded:
  (!s v. MEM v (df_at [] st s 0) ==> MEM v (fn_all_vars bbs)) ==>
  !v. MEM v (liveness_out bbs cfg lbl st) ==> MEM v (fn_all_vars bbs)
Proof
  strip_tac >> simp[liveness_out_def, mem_foldl_list_union, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  irule liveness_edge_transfer_bounded >>
  qexistsl_tac [`bbs`, `lbl`, `df_at [] st s 0`, `s`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule fn_all_vars_mem >>
      qexistsl_tac [`bb`, `inst`] >> simp[])
  >> metis_tac[]
QED

(* Compare complete backward folds, including their instruction slots. *)
Theorem liveness_backward_mono[local]:
  !instrs idx a b.
    set a SUBSET set b ==>
    set (FST (df_fold_backward (liveness_transfer bbs) lbl instrs idx a FEMPTY))
      SUBSET
    set (FST (df_fold_backward (liveness_transfer bbs) lbl instrs idx b FEMPTY)) /\
    (!k. set (THE (FLOOKUP (SND (df_fold_backward (liveness_transfer bbs)
                     lbl instrs idx a FEMPTY)) k)) SUBSET
         set (THE (FLOOKUP (SND (df_fold_backward (liveness_transfer bbs)
                     lbl instrs idx b FEMPTY)) k)))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[df_fold_backward_def, FLOOKUP_UPDATE] >>
      gen_tac >> IF_CASES_TAC >> simp[])
  >> first_x_assum (qspecl_then [`idx + 1`, `a`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `df_fold_backward (liveness_transfer bbs) lbl instrs (idx + 1) a FEMPTY` >>
  rename1 `df_fold_backward _ _ _ _ a _ = (entry_a, map_a)` >>
  Cases_on `df_fold_backward (liveness_transfer bbs) lbl instrs (idx + 1) b FEMPTY` >>
  rename1 `df_fold_backward _ _ _ _ b _ = (entry_b, map_b)` >>
  gvs[] >> simp[df_fold_backward_def] >>
  `set (liveness_transfer bbs h entry_a) SUBSET
   set (liveness_transfer bbs h entry_b)` by
     (irule liveness_transfer_mono >> simp[]) >>
  simp[FLOOKUP_UPDATE] >> gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem liveness_fold_entry_mono:
  set a SUBSET set b ==>
  set (FST (df_fold_block Backward (liveness_transfer bbs) lbl instrs a)) SUBSET
  set (FST (df_fold_block Backward (liveness_transfer bbs) lbl instrs b))
Proof
  simp[df_fold_block_def] >> metis_tac[liveness_backward_mono]
QED

Theorem liveness_fold_slot_mono:
  set a SUBSET set b ==>
  set (THE (FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs)
               lbl instrs a)) (lbl,i))) SUBSET
  set (THE (FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs)
               lbl instrs b)) (lbl,i)))
Proof
  simp[df_fold_block_def] >> metis_tac[liveness_backward_mono]
QED

Theorem liveness_backward_bounded[local]:
  !instrs idx a U.
    (!v. MEM v a ==> MEM v U) /\
    (!inst v. MEM inst instrs /\ MEM v (inst_uses inst) ==> MEM v U) ==>
    (!v. MEM v (FST (df_fold_backward (liveness_transfer bbs)
                      lbl instrs idx a FEMPTY)) ==> MEM v U) /\
    (!k vs v. FLOOKUP (SND (df_fold_backward (liveness_transfer bbs)
                      lbl instrs idx a FEMPTY)) k = SOME vs /\ MEM v vs ==>
              MEM v U)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[df_fold_backward_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[])
  >> qpat_x_assum `!inst v. MEM inst (h::instrs) /\ _ ==> _` mp_tac >>
  pure_rewrite_tac[MEM] >> strip_tac >>
  first_x_assum (qspecl_then [`idx + 1`, `a`, `U`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  Cases_on `df_fold_backward (liveness_transfer bbs) lbl instrs (idx + 1) a FEMPTY` >>
  rename1 `df_fold_backward _ _ _ _ a _ = (entry, im)` >>
  gvs[] >> simp[df_fold_backward_def] >>
  `!v. MEM v (liveness_transfer bbs h entry) ==> MEM v U` by
    (metis_tac[liveness_transfer_bounded]) >>
  simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem liveness_fold_entry_bounded:
  (!v. MEM v a ==> MEM v U) /\
  (!inst v. MEM inst instrs /\ MEM v (inst_uses inst) ==> MEM v U) ==>
  !v. MEM v (FST (df_fold_block Backward (liveness_transfer bbs)
                   lbl instrs a)) ==> MEM v U
Proof
  strip_tac >> simp[df_fold_block_def] >>
  qspecl_then [`instrs`, `0`, `a`, `U`] mp_tac liveness_backward_bounded >>
  (impl_tac >- metis_tac[]) >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem liveness_fold_map_bounded:
  (!v. MEM v a ==> MEM v U) /\
  (!inst v. MEM inst instrs /\ MEM v (inst_uses inst) ==> MEM v U) ==>
  !k vs v. FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs)
                   lbl instrs a)) k = SOME vs /\ MEM v vs ==> MEM v U
Proof
  strip_tac >> simp[df_fold_block_def] >>
  qspecl_then [`instrs`, `0`, `a`, `U`] mp_tac liveness_backward_bounded >>
  (impl_tac >- metis_tac[]) >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem liveness_fold_slot_bounded:
  (!v. MEM v a ==> MEM v U) /\
  (!inst v. MEM inst instrs /\ MEM v (inst_uses inst) ==> MEM v U) /\
  i <= LENGTH instrs ==>
  !v. MEM v (THE (FLOOKUP (SND (df_fold_block Backward (liveness_transfer bbs)
                   lbl instrs a)) (lbl,i))) ==> MEM v U
Proof
  strip_tac >>
  qspecl_then [`instrs`, `0`, `a`, `U`] mp_tac liveness_backward_bounded >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  Cases_on `df_fold_block Backward (liveness_transfer bbs) lbl instrs a` >>
  drule backward_fold_lookup >> disch_then (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >> gvs[df_fold_block_def] >> metis_tac[]
QED

(* Each exported set interface is kernel proved. *)
val _ = List.app (fn (_,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "oracle in liveness transfer API")
  (DB.thms "livenessTransferProofs");
