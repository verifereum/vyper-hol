(* Public linked scalar builtin rules. *)
Theory bodyBuiltinScalarRoutesMods
Ancestors
  bodyBuiltinEnvFamilyMods bodyBuiltinWordFamilyMods bodyBuiltinBopFamilyMods
  bodyWordNotRouteMods bodyWordRoundRouteMods bodyTypeBoundWordsMods
  bodyFullPredsMods vyperInterpreter vyperState vyperAST list

Theorem env_builtin_expr_full_ok_mods:
  !mods exps cx ty bt es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_full_ok_mods mods exps cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok_mods mods exps cx (HD es)) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ty bt es)
Proof
  ACCEPT_TAC env_family_full_ok_mods
QED

Theorem word_builtin_expr_full_ok_mods:
  !mods exps cx ty bt es.
    (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok_mods mods exps cx es) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ty bt es)
Proof
  mp_tac word_family_from_routes_mods >>
  rewrite_tac[word_not_sim_mods, word_rounding_sim_mods]
QED

Theorem bop_expr_full_ok_mods:
  !mods exps cx ty bop es.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==>
      body_exprs_full_ok_mods mods exps cx es) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ty (Bop bop) es)
Proof
  ACCEPT_TAC bop_family_full_ok_mods
QED
