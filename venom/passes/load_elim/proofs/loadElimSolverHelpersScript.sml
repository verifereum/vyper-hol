Theory loadElimSolverHelpers
Ancestors
  loadElimDefs loadElimSupportHelpers loadElimOrderHelpers
  dfAnalyzeDefs dfAnalyzeProofs latticeDefs cfgAnalysisProps
  venomInst livenessTransferProofs finite_map pred_set list rich_list arithmetic
Libs
  pairLib

Definition le_solver_inv_def:
  le_solver_inv labels keys vals (st : load_lattice df_state) <=>
    st.ds_inst = FEMPTY /\ FDOM st.ds_boundary = labels /\
    (!lbl v. FLOOKUP st.ds_boundary lbl = SOME v ==>
      le_lattice_supported keys vals v)
End

Definition le_solver_leq_def:
  le_solver_leq (a : load_lattice df_state) b <=>
    !lbl. le_lattice_leq (df_boundary NONE a lbl) (df_boundary NONE b lbl)
End

Definition le_solver_rank_def:
  le_solver_rank labels keys vals (st : load_lattice df_state) =
    SIGMA (\lbl. le_lattice_rank keys vals (df_boundary NONE st lbl)) labels
End

Theorem le_solver_boundary_supported:
  le_solver_inv labels keys vals st ==>
  le_lattice_supported keys vals (df_boundary NONE st lbl)
Proof
  simp[le_solver_inv_def, df_boundary_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >> metis_tac[]
QED

Theorem le_solver_rank_bound:
  FINITE labels /\ FINITE keys /\ FINITE vals /\
  le_solver_inv labels keys vals st ==>
  le_solver_rank labels keys vals st <=
    CARD labels * (1 + CARD keys * (CARD vals + 1))
Proof
  rpt strip_tac >> simp[le_solver_rank_def] >>
  `SIGMA (\lbl. le_lattice_rank keys vals (df_boundary NONE st lbl)) labels <=
   SIGMA (K (1 + CARD keys * (CARD vals + 1))) labels`
    suffices_by simp[SUM_IMAGE_CONSTANT, MULT_COMM] >>
  irule SUM_IMAGE_MONO_LESS_EQ >> simp[] >> rpt strip_tac >>
  metis_tac[le_lattice_rank_bound, le_solver_boundary_supported, ADD_COMM]
QED

Theorem le_solver_boundary_ext:
  le_solver_inv labels keys vals a /\ le_solver_inv labels keys vals b /\
  (!lbl. lbl IN labels ==> df_boundary NONE a lbl = df_boundary NONE b lbl) ==>
  a = b
Proof
  simp[le_solver_inv_def] >> rpt strip_tac >>
  `a.ds_boundary = b.ds_boundary` by
    (simp[fmap_eq_flookup] >> qx_gen_tac `lbl` >>
     Cases_on `lbl IN labels` >>
     fs[df_boundary_def, FLOOKUP_DEF] >>
     first_x_assum (qspec_then `lbl` mp_tac) >> simp[]) >>
  Cases_on `a` >> Cases_on `b` >> gvs[]
QED

Theorem le_solver_rank_strict:
  FINITE labels /\ FINITE keys /\ FINITE vals /\
  le_solver_inv labels keys vals a /\ le_solver_inv labels keys vals b /\
  le_solver_leq a b /\ a <> b ==>
  le_solver_rank labels keys vals a < le_solver_rank labels keys vals b
Proof
  rpt strip_tac >> simp[le_solver_rank_def] >>
  irule SUM_IMAGE_MONO_LESS >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule le_lattice_rank_mono >>
      fs[le_solver_leq_def] >> metis_tac[le_solver_boundary_supported]) >>
  `?lbl. lbl IN labels /\ df_boundary NONE a lbl <> df_boundary NONE b lbl`
    by metis_tac[le_solver_boundary_ext] >>
  qexists `lbl` >> simp[] >> irule le_lattice_rank_strict >>
  fs[le_solver_leq_def] >> metis_tac[le_solver_boundary_supported]
QED

Theorem le_solver_bounded_measure:
  FINITE labels /\ FINITE keys /\ FINITE vals ==>
  bounded_measure (le_solver_inv labels keys vals) le_solver_leq
    (le_solver_rank labels keys vals)
    (CARD labels * (1 + CARD keys * (CARD vals + 1)))
Proof
  rewrite_tac[bounded_measure_def] >>
  metis_tac[le_solver_rank_bound, le_solver_rank_strict]
QED

Theorem le_init_domain_fold[local]:
  !ls m. FDOM (FOLDL (\m lbl. m |+ (lbl, v)) m ls) =
    FDOM m UNION set ls
Proof
  Induct >> simp[UNION_ASSOC, EXTENSION] >> metis_tac[]
QED

Theorem le_solver_init:
  le_solver_inv (set labels) keys vals (init_df_state NONE labels)
Proof
  simp[le_solver_inv_def, init_df_state_def, le_init_domain_fold] >>
  rpt strip_tac >> drule foldl_fupdate_const >> strip_tac >> simp[]
QED

Definition le_solver_process_def:
  le_solver_process ctx fn =
    df_process_block Forward NONE load_join load_transfer load_edge_transfer
      ctx (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks
End

Theorem le_lattice_leq_refl:
  le_lattice_leq a a
Proof
  Cases_on `a` >> simp[le_lattice_leq_def] >> metis_tac[APPEND_NIL]
QED

Theorem le_solver_process_inflationary:
  le_solver_leq st (le_solver_process ctx fn lbl st)
Proof
  simp[le_solver_process_def, df_process_block_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC
  >- simp[le_solver_leq_def, le_lattice_leq_refl] >>
  simp[le_solver_leq_def, df_boundary_def, FLOOKUP_UPDATE] >>
  qx_gen_tac `other` >> Cases_on `lbl = other` >>
  simp[le_lattice_leq_refl] >> gvs[] >>
  metis_tac[le_join_inflationary, df_boundary_def]
QED

Theorem le_solver_process_outside:
  wf_function fn /\ ~MEM lbl (fn_labels fn) ==>
  le_solver_process ctx fn lbl st = st
Proof
  rpt strip_tac >>
  `cfg_preds_of (cfg_analyze fn) lbl = []` by
    metis_tac[cfg_analyze_preds_domain] >>
  `lookup_block lbl fn.fn_blocks = NONE` by
    (`!bbs. ~MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
        FIND (\bb. bb.bb_label = lbl) bbs = NONE` by
       (Induct >> simp[FIND_thm] >> metis_tac[]) >>
     fs[lookup_block_def, fn_labels_def]) >>
  `!entry. fn_entry_label fn = SOME entry ==> lbl <> entry` by
    (Cases_on `fn.fn_blocks` >>
     fs[fn_entry_label_def, entry_block_def, fn_labels_def]) >>
  simp[le_solver_process_def, df_process_block_def, df_joined_val_def,
       load_edge_transfer_def] >>
  Cases_on `fn_entry_label fn` >>
  Cases_on `df_boundary NONE st lbl` >>
  simp[df_fold_block_def, df_fold_forward_def, load_join_def] >>
  metis_tac[]
QED

Theorem le_join_fold_supported:
  !vs acc. le_lattice_supported keys vals acc /\
    EVERY (le_lattice_supported keys vals) vs ==>
    le_lattice_supported keys vals (FOLDL load_join acc vs)
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[le_join_supported]
QED

Theorem le_boundary_joined_supported:
  (!lbl. le_lattice_supported keys vals (df_boundary NONE st lbl)) ==>
  le_lattice_supported keys vals
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st lbl)
Proof
  strip_tac >> simp[df_joined_val_def, load_edge_transfer_def, SF ETA_ss] >>
  `le_lattice_supported keys vals
    (FOLDL load_join NONE
      (MAP (df_boundary NONE st) (cfg_preds_of (cfg_analyze fn) lbl)))` by
    (irule le_join_fold_supported >>
     simp[EVERY_MAP, EVERY_MEM]) >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
  Cases_on `lbl = x` >> gvs[] >> metis_tac[le_join_supported, le_lattice_supported_empty]
QED

Theorem le_solver_joined_supported:
  le_solver_inv labels keys vals st ==>
  le_lattice_supported keys vals
    (df_joined_val Forward NONE load_join load_edge_transfer ctx
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st lbl)
Proof
  strip_tac >> irule le_boundary_joined_supported >>
  metis_tac[le_solver_boundary_supported]
QED

Theorem le_solver_fold_supported:
  df_fold_block Forward (load_transfer ctx) lbl
    (case lookup_block lbl fn.fn_blocks of NONE => [] | SOME bb => bb.bb_instructions)
    initial = (fv, im) /\
  le_lattice_supported (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn)) initial ==>
  le_lattice_supported (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn)) fv
Proof
  rpt strip_tac >> drule df_fold_block_forward_invariant >>
  disch_then (qspec_then
    `le_lattice_supported (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn))` mp_tac) >>
  simp[] >> impl_tac
  >- (rpt strip_tac >> irule le_transfer_supported >> simp[] >>
      Cases_on `lookup_block lbl fn.fn_blocks` >> gvs[] >>
      `!bbs. MEM x bbs ==> MEM inst (fn_insts_blocks bbs)` by
        (Induct >> simp[fn_insts_blocks_def] >> metis_tac[]) >>
      drule lookup_block_mem >> simp[fn_insts_def]) >>
  simp[]
QED

Theorem le_solver_process_closed:
  wf_function fn /\
  le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn)) st ==>
  le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn)) (le_solver_process ctx fn lbl st)
Proof
  rpt strip_tac >> Cases_on `MEM lbl (fn_labels fn)`
  >- (simp[le_solver_process_def, df_process_block_def] >>
      pairarg_tac >> simp[] >>
      `le_lattice_supported (le_generated_keys ctx (fn_insts fn))
        (le_generated_operands (fn_insts fn)) final_val` by
        (irule le_solver_fold_supported >>
         goal_assum (drule_at Any) >>
         metis_tac[le_solver_joined_supported]) >>
      `le_lattice_supported (le_generated_keys ctx (fn_insts fn))
        (le_generated_operands (fn_insts fn))
        (load_join (df_boundary NONE st lbl) final_val)` by
        metis_tac[le_join_supported, le_solver_boundary_supported] >>
      IF_CASES_TAC >- simp[] >>
      fs[le_solver_inv_def] >>
      simp[le_solver_inv_def, EXTENSION, FLOOKUP_UPDATE] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> Cases_on `lbl = lbl'` >> gvs[] >> metis_tac[]) >>
  drule_all le_solver_process_outside >> simp[]
QED

(* All labels are quantified here, including labels outside the function. *)
Theorem le_solver_premises:
  wf_function fn ==>
  le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn))
    (init_df_state NONE (fn_labels fn)) /\
  bounded_measure
    (le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn))) le_solver_leq
    (le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn)))
    (CARD (set (fn_labels fn)) *
      (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
        (CARD (le_generated_operands (fn_insts fn)) + 1))) /\
  (!lbl st.
    le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn)) st ==>
    le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn)) (le_solver_process ctx fn lbl st) /\
    le_solver_leq st (le_solver_process ctx fn lbl st))
Proof
  strip_tac >> conj_tac >- irule le_solver_init >>
  conj_tac >- (irule le_solver_bounded_measure >> simp[]) >>
  metis_tac[le_solver_process_closed, le_solver_process_inflationary]
QED
