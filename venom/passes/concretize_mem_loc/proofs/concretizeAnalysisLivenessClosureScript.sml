Theory concretizeAnalysisLivenessClosure
Ancestors concretizeAnalysisLivenessTransfer singleWriterScan cfgWf
  list pred_set finite_map

(* The boundary transfer is Boolean affine: a constant generator or the
   incoming boundary bit passed through a fixed propagation guard. *)
Theorem ml_liveat_before_bit_increasing:
  ml_liveat_before_bit a bpr mems sizes insts F ==>
  ml_liveat_before_bit a bpr mems sizes insts T
Proof
  Induct_on `insts` >- simp[ml_liveat_before_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_before_bit_def] >> metis_tac[]
QED

Theorem ml_liveat_before_bit_affine:
  ml_liveat_before_bit a bpr mems sizes insts bit <=>
    ml_liveat_before_bit a bpr mems sizes insts F \/
    (bit /\ ml_liveat_before_bit a bpr mems sizes insts T)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_liveat_before_bit_increasing]
QED

Theorem ml_liveat_record_bit_increasing:
  ml_liveat_record_bit a bpr mems sizes lbl addr insts F F ==>
  ml_liveat_record_bit a bpr mems sizes lbl addr insts T F
Proof
  Induct_on `insts` >- simp[ml_liveat_record_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_liveat_record_bit_def] >>
  Cases_on `addr = (lbl,h0)` >> simp[] >>
  metis_tac[ml_liveat_before_bit_increasing]
QED

Theorem ml_liveat_record_bit_affine:
  ml_liveat_record_bit a bpr mems sizes lbl addr insts bit F <=>
    ml_liveat_record_bit a bpr mems sizes lbl addr insts F F \/
    (bit /\ ml_liveat_record_bit a bpr mems sizes lbl addr insts T F)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_liveat_record_bit_increasing]
QED

Theorem ml_used_after_bit_increasing:
  !x y. (x ==> y) ==>
  (ml_used_after_bit a bpr mems insts x ==> ml_used_after_bit a bpr mems insts y)
Proof
  Induct_on `insts` >- simp[ml_used_after_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_used_after_bit_def] >>
  Cases_on `ml_used_gen a bpr mems h1` >> simp[] >> first_x_assum ACCEPT_TAC
QED

Theorem ml_used_after_bit_affine:
  ml_used_after_bit a bpr mems insts bit <=>
    ml_used_after_bit a bpr mems insts F \/
    (bit /\ ml_used_after_bit a bpr mems insts T)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_used_after_bit_increasing]
QED

Theorem ml_used_record_bit_increasing:
  !x y old old2. (x ==> y) /\ (old ==> old2) ==>
  (ml_used_record_bit a bpr mems lbl addr insts x old ==>
   ml_used_record_bit a bpr mems lbl addr insts y old2)
Proof
  Induct_on `insts` >- simp[ml_used_record_bit_def] >>
  gen_tac >> PairCases_on `h` >> simp[ml_used_record_bit_def] >>
  rpt gen_tac >> Cases_on `addr = (lbl,h0)` >> gvs[] >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at (Pat `ml_used_record_bit _ _ _ _ _ _ _ _`)) >> metis_tac[]
QED

Theorem ml_used_record_bit_affine:
  ml_used_record_bit a bpr mems lbl addr insts bit F <=>
    ml_used_record_bit a bpr mems lbl addr insts F F \/
    (bit /\ ml_used_record_bit a bpr mems lbl addr insts T F)
Proof
  Cases_on `bit` >> simp[] >> metis_tac[ml_used_record_bit_increasing]
QED

Theorem ml_liveat_record_bit_old_irrelevant:
  !bit old old2 idx inst.
  MEM (idx,inst) insts ==>
  ml_liveat_record_bit a bpr mems sizes lbl (lbl,idx) insts bit old =
  ml_liveat_record_bit a bpr mems sizes lbl (lbl,idx) insts bit old2
Proof
  Induct_on `insts` >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[ml_liveat_record_bit_def] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `idx = h0` >> simp[] >> first_x_assum drule >> simp[]
QED

Theorem ml_used_record_bit_old_irrelevant:
  !bit old old2 idx inst.
  MEM (idx,inst) insts ==>
  ml_used_record_bit a bpr mems lbl (lbl,idx) insts bit old =
  ml_used_record_bit a bpr mems lbl (lbl,idx) insts bit old2
Proof
  Induct_on `insts` >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp[ml_used_record_bit_def] >> rpt gen_tac >> strip_tac >> simp[] >>
  Cases_on `idx = h0` >> simp[] >> first_x_assum drule >> simp[]
QED

Definition ml_liveat_boundary_bit_def:
  ml_liveat_boundary_bit a bpr mems sizes bb bit =
    ml_liveat_record_bit a bpr mems sizes bb.bb_label (bb.bb_label,0)
      (MAPi (\i inst. (i,inst)) bb.bb_instructions) bit F
End

Definition ml_used_boundary_bit_def:
  ml_used_boundary_bit a bpr mems bb bit =
    ml_used_record_bit a bpr mems bb.bb_label
      (bb.bb_label,PRE (LENGTH bb.bb_instructions))
      (MAPi (\i inst. (i,inst)) bb.bb_instructions) bit F
End

Theorem ml_liveat_boundary_bit_affine:
  ml_liveat_boundary_bit a bpr mems sizes bb bit <=>
  ml_liveat_boundary_bit a bpr mems sizes bb F \/
  (bit /\ ml_liveat_boundary_bit a bpr mems sizes bb T)
Proof
  pure_rewrite_tac[ml_liveat_boundary_bit_def] >>
  MATCH_ACCEPT_TAC ml_liveat_record_bit_affine
QED

Theorem ml_used_boundary_bit_affine:
  ml_used_boundary_bit a bpr mems bb bit <=>
  ml_used_boundary_bit a bpr mems bb F \/
  (bit /\ ml_used_boundary_bit a bpr mems bb T)
Proof
  pure_rewrite_tac[ml_used_boundary_bit_def] >>
  MATCH_ACCEPT_TAC ml_used_record_bit_affine
QED

Definition ml_liveat_boundary_desc_def:
  ml_liveat_boundary_desc a bpr mems sizes cfg bb =
    (bb.bb_label,
     if ml_liveat_boundary_bit a bpr mems sizes bb F then {T} else {},
     if ml_liveat_boundary_bit a bpr mems sizes bb T then
       set (cfg_succs_of cfg bb.bb_label) else {})
End

Definition ml_used_boundary_desc_def:
  ml_used_boundary_desc a bpr mems pallocas cfg bb =
    (bb.bb_label,
     if ml_used_boundary_bit a bpr mems bb (MEM a pallocas) then {T} else {},
     if ml_used_boundary_bit a bpr mems bb T then
       set (cfg_preds_of cfg bb.bb_label) else {})
End

Theorem ml_boundary_desc_out:
  sw_out (ml_liveat_boundary_desc a bpr mems sizes cfg bb) = bb.bb_label /\
  sw_out (ml_used_boundary_desc a bpr mems pallocas cfg bb) = bb.bb_label
Proof simp[ml_liveat_boundary_desc_def, ml_used_boundary_desc_def, sw_out_def]
QED

Theorem ml_liveat_boundary_desc_rhs:
  T IN sw_rhs (ml_liveat_boundary_desc a bpr mems sizes cfg bb) X <=>
  ml_liveat_boundary_bit a bpr mems sizes bb
    (?lbl. MEM lbl (cfg_succs_of cfg bb.bb_label) /\ T IN X lbl)
Proof
  simp[ml_liveat_boundary_desc_def, sw_rhs_def] >>
  once_rewrite_tac[ml_liveat_boundary_bit_affine] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem ml_used_boundary_desc_rhs:
  T IN sw_rhs (ml_used_boundary_desc a bpr mems pallocas cfg bb) X <=>
  ml_used_boundary_bit a bpr mems bb
    (MEM a pallocas \/ (?lbl. MEM lbl (cfg_preds_of cfg bb.bb_label) /\ T IN X lbl))
Proof
  simp[ml_used_boundary_desc_def, sw_rhs_def] >>
  once_rewrite_tac[ml_used_boundary_bit_affine] >>
  rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED
