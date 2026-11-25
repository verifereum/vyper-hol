Theory bodyBopBytestringHashLocationMods
Ancestors
  bodyFullPostsMods loweringPosts

Theorem bytestring_hash_location_mods:
  is_bytestring_type (expr_type e) /\
  expr_post_mods H ctx func cenv cx e es sa cb s ee v m t ==>
  expr_val_at cenv cx (expr_type e) sa cb ee v m t
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    simp[post_value_type_bytestring] >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_post_mods_def, expr_post_def] >>
  strip_tac >>
  qpat_assum `expr_val_at _ _ (post_value_type _ _) _ _ _ _ _ _` mp_tac >>
  qpat_assum `post_value_type cenv e = expr_type e` (fn eq =>
    pure_once_rewrite_tac[eq]) >>
  disch_then ACCEPT_TAC
QED
