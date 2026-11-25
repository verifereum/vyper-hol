(* Join the linked flag and nonliteral-array membership routes. *)
Theory bodyMembershipOrdinaryMods
Ancestors
  bodyMembershipOrdinaryShapeMods bodyMembershipFlagValueMods
  bodyMembershipArrayValueMods bodyFullPredsMods

Theorem membership_ordinary_value_mods:
  (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\
  ((word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) \/
   (!a t n elems. e2 <> Builtin a (MakeArray t n) elems)) /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac membership_ordinary_shape_mods
  >- (irule membership_flag_value_mods >>
      qpat_assum `contract_inv mods exps _ _ _` (irule_at Any) >>
      qpat_assum `module_body_inv mods _ _ _ _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods mods _ _ _` (irule_at Any) >>
      qexists_tac `fid` >> simp[]) >>
  qpat_x_assum `ann = BaseT BoolT` SUBST_ALL_TAC >>
  irule membership_array_value_mods >>
  qpat_assum `contract_inv mods exps _ _ _` (irule_at Any) >>
  qpat_assum `module_body_inv mods _ _ _ _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree_mods mods _ _ _` (irule_at Any) >>
  qexists_tac `bd` >> simp[]
QED
