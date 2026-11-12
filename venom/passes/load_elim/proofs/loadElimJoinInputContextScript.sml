Theory loadElimJoinInputContext
Ancestors
  loadElimDefs loadElimBoundaryProvenance loadElimOrderHelpers
  loadElimJoinInputDiagnostic loadElimLatticeSoundHelpers
  dfAnalyzeDefs cfgDefs finite_map pred_set list
Libs
  pairLib

(* Key-local set order: NONE is bottom; among reached values, losing a
   key is upward, and a retained key's alternatives may only grow. *)
Definition le_key_set_leq_def:
  le_key_set_leq k a b <=>
    a = NONE \/
    (b <> NONE /\
     !ys. FLOOKUP (unwrap_load_lattice b) k = SOME ys ==>
       ?xs. FLOOKUP (unwrap_load_lattice a) k = SOME xs /\
            set xs SUBSET set ys)
End

Theorem le_key_set_leq_refl:
  le_key_set_leq k a a
Proof
  Cases_on `a` >> simp[le_key_set_leq_def]
QED

Theorem le_key_set_leq_join:
  le_key_set_leq k a (load_join a fresh)
Proof
  Cases_on `a` >> Cases_on `fresh` >>
  simp[le_key_set_leq_def, load_join_def, unwrap_load_lattice_def,
       le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF]
QED

Theorem le_key_set_leq_join_mono:
  le_key_set_leq k a a' /\ le_key_set_leq k b b' ==>
  le_key_set_leq k (load_join a b) (load_join a' b')
Proof
  Cases_on `a` >> Cases_on `a'` >> Cases_on `b` >> Cases_on `b'` >>
  simp[le_key_set_leq_def, load_join_def, unwrap_load_lattice_def,
       le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF] >>
  metis_tac[]
QED

Theorem le_key_set_leq_rel_transport:
  le_key_set_leq k a a' /\ le_pred_lookup_rel k a b ==>
  le_pred_lookup_rel k a' b
Proof
  Cases_on `a` >> Cases_on `a'` >>
  simp[le_key_set_leq_def, le_pred_lookup_rel_def,
       unwrap_load_lattice_def] >>
  rpt strip_tac >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem le_key_set_leq_fold_map:
  !ls a a'. le_key_set_leq k a a' /\
    (!p. MEM p ls ==> le_key_set_leq k (f p) (g p)) ==>
    le_key_set_leq k (FOLDL load_join a (MAP f ls))
                     (FOLDL load_join a' (MAP g ls))
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[le_key_set_leq_join_mono]
QED

Theorem le_joined_input_key_set_leq:
  (!p. le_key_set_leq k (df_boundary NONE st p)
                         (df_boundary NONE st' p)) ==>
  le_key_set_leq k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg st target)
    (df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg st' target)
Proof
  strip_tac >>
  `le_key_set_leq k
    (FOLDL load_join NONE (MAP (df_boundary NONE st) (cfg_preds_of cfg target)))
    (FOLDL load_join NONE (MAP (df_boundary NONE st') (cfg_preds_of cfg target)))`
    by (irule le_key_set_leq_fold_map >>
        simp[le_key_set_leq_refl]) >>
  simp[df_joined_val_def, load_edge_transfer_def, SF ETA_ss] >>
  Cases_on `cfg_preds_of cfg target` >> fs[] >>
  Cases_on `seed` >> simp[le_key_set_leq_refl] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `target = x0` >> simp[] >>
  irule le_key_set_leq_join_mono >> simp[le_key_set_leq_refl] >> gvs[]
QED

Theorem le_joined_input_boundary_accumulate:
  (!q. df_boundary NONE st' q =
       if q = p then load_join (df_boundary NONE st p) fresh
       else df_boundary NONE st q) /\
  le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg st target) b ==>
  le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg st' target) b
Proof
  strip_tac >> irule le_key_set_leq_rel_transport >>
  qexists `df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg st target` >>
  simp[] >> irule le_joined_input_key_set_leq >> gen_tac >>
  simp[] >> IF_CASES_TAC >>
  simp[le_key_set_leq_join, le_key_set_leq_refl]
QED

Theorem le_joined_input_boundary_update:
  le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg st target) b ==>
  le_pred_lookup_rel k
    (df_joined_val Forward NONE load_join load_edge_transfer ctx seed cfg
      (st with ds_boundary := st.ds_boundary |+
        (p, load_join (df_boundary NONE st p) fresh)) target) b
Proof
  strip_tac >> irule le_joined_input_boundary_accumulate >>
  qexistsl [`fresh`, `p`, `st`] >> simp[] >>
  simp[df_boundary_def, FLOOKUP_UPDATE] >> gen_tac >>
  Cases_on `q = p` >> simp[]
QED
