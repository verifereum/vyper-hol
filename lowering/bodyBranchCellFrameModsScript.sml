Theory bodyBranchCellFrameMods
Ancestors bodyFullPredsMods constSubstCorrect vyperState finite_map

(* The linked certificate depends on the evaluation state only through the
   immutable store; the replay obligations already quantify over states. *)
Theorem body_const_cells_agree_mods_immutables:
  st.immutables = st'.immutables ==>
  (body_const_cells_agree_mods mods cx env st <=>
   body_const_cells_agree_mods mods cx env st')
Proof
  simp[body_const_cells_agree_mods_def, const_cells_agree_def]
QED

Theorem body_const_cells_agree_mods_branch_updates[simp]:
  (body_const_cells_agree_mods mods cx env (st with gas_obs := obs) <=>
   body_const_cells_agree_mods mods cx env st) /\
  (body_const_cells_agree_mods mods cx env (st with scopes updated_by update) <=>
   body_const_cells_agree_mods mods cx env st)
Proof
  conj_tac >> irule body_const_cells_agree_mods_immutables >> simp[]
QED

Theorem body_const_cells_agree_mods_push_scope:
  push_scope st = (res, st') ==>
  (body_const_cells_agree_mods mods cx env st' <=>
   body_const_cells_agree_mods mods cx env st)
Proof
  simp[push_scope_def, return_def] >> strip_tac >> gvs[]
QED
