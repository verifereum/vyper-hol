(* Linked value and VV simulation of non-membership binary operators. *)
Theory bodyBuiltinBopFamilyMods
Ancestors
  bodyFullPredsMods bodyBopBytestringEqMods bodyBopWordResultMods
  bodyBopAddressBytesEqMods bodyBopFixedBytesBitsMods bodyScalarStackVVMods
  exprBodyPreProps exprSimOperators exprSimSource exprSimHypsDefs exprLoweringProps
  loweringPosts compileEnv vyperTypeSystem vyperValue vyperContext vyperAST list

Theorem bop_nonmembership_word_ann[local]:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  well_formed_type tenv ann ==> is_word_type ann
Proof
  strip_tac >>
  `word_value_type ann \/ ?m. ann = BaseT (BytesT (Fixed m))` by
    (Cases_on `bop` >> fs[well_typed_binop_def, word_value_type_def, is_bool_type_def] >>
     metis_tac[]) >>
  pop_assum strip_assume_tac
  >- (drule word_value_type_word >> simp[]) >>
  gvs[well_formed_type_def, evaluate_type_def, is_word_type_def]
QED

Theorem bop_family_full_ok_mods:
  !mods exps cx ty bop es.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==>
      body_exprs_full_ok_mods mods exps cx es) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ty (Bop bop) es)
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_full_ok_mods_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_mods_well_typed >>
  disch_then (mp_tac o ONCE_REWRITE_RULE [well_typed_expr_def]) >>
  simp[well_typed_builtin_app_def] >> strip_tac >>
  rename1 `well_formed_type _ ann` >>
  `?e1 e2. es = [e1;e2]` by fs[LENGTH_EQ_NUM_compute] >> gvs[] >>
  `is_word_type ann` by metis_tac[bop_nonmembership_word_ann] >>
  `body_exprs_full_ok_mods mods exps cx [e1;e2]` by fs[builtin_args_length_ok_def] >>
  conj_asm1_tac
  >- (Cases_on `(bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)`
      >- (irule bop_bytestring_eq_value_sim_mods >> metis_tac[]) >>
      Cases_on `word_value_type (expr_type e1) /\ word_value_type (expr_type e2)`
      >- (irule bop_word_value_sim_mods >> metis_tac[]) >>
      Cases_on `(bop = Eq \/ bop = NotEq) /\
                (expr_type e1 = BaseT AddressT \/
                 ?m. expr_type e1 = BaseT (BytesT (Fixed m)))`
      >- (irule bop_address_bytes_eq_value_sim_mods >> metis_tac[]) >>
      irule bop_rest_bits_value_sim_mods >> metis_tac[]) >>
  match_mp_tac scalar_stack_vv_sim_full_mods >>
  simp[post_value_type_word, expr_type_def, compile_bop_stack] >>
  rpt strip_tac >> drule eval_expr_builtin_value >> simp[]
QED
