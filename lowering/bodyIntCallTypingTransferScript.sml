(* Permission-enlargement boundaries for callee typing witnesses. *)
Theory bodyIntCallTypingTransfer
Ancestors
  vyperTypeSystem finite_map

Theorem permission_lookup_update:
  (!n. FLOOKUP m n = SOME T ==> FLOOKUP m' n = SOME T) ==>
  !n. FLOOKUP (m |+ (id,b)) n = SOME T ==>
      FLOOKUP (m' |+ (id,b)) n = SOME T
Proof
  rpt strip_tac >> Cases_on `n = id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem type_place_target_name_permission:
  e' = e with var_assignable := m /\
  (!n. FLOOKUP e.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  type_place_target e (NameTarget id) = SOME vt ==>
  type_place_target e' (NameTarget id) = SOME vt
Proof
  strip_tac >> gvs[Once well_typed_expr_def, AllCaseEqs()] >>
  simp[Once well_typed_expr_def]
QED

Theorem permission_true_map_domain:
  FDOM ((K T) o_f m) = FDOM m
Proof
  simp[]
QED

Theorem permission_true_map_lookup:
  IS_SOME (FLOOKUP m n) ==> FLOOKUP ((K T) o_f m) n = SOME T
Proof
  Cases_on `FLOOKUP m n` >> simp[FLOOKUP_o_f]
QED

Theorem typing_permission_transfer:
  (!env x. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) ==>
    well_typed_expr env x ==> well_typed_expr (env with var_assignable := m) x) /\
  (!env x. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) ==>
    !vt. type_place_expr env x = SOME vt ==>
      type_place_expr (env with var_assignable := m) x = SOME vt) /\
  (!env x. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) ==>
    !vt. type_place_target env x = SOME vt ==>
      type_place_target (env with var_assignable := m) x = SOME vt) /\
  (!env x. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) ==>
    well_typed_exprs env x ==> well_typed_exprs (env with var_assignable := m) x) /\
  (!env x. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) ==>
    well_typed_opt env x ==> well_typed_opt (env with var_assignable := m) x) /\
  (!env x. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) ==>
    well_typed_named_exprs env x ==>
      well_typed_named_exprs (env with var_assignable := m) x)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt strip_tac >>
  rpt (pop_assum mp_tac) >>
  rw[well_typed_expr_def, AllCaseEqs()] >> gvs[] >> metis_tac[]
QED

Theorem well_typed_expr_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_expr env x ==> well_typed_expr env' x
Proof
  strip_tac >> gvs[] >> irule (cj 1 typing_permission_transfer) >> simp[]
QED

Theorem type_place_expr_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  type_place_expr env x = SOME vt ==> type_place_expr env' x = SOME vt
Proof
  strip_tac >> gvs[] >> irule (cj 2 typing_permission_transfer) >> simp[]
QED

Theorem type_place_target_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  type_place_target env x = SOME vt ==> type_place_target env' x = SOME vt
Proof
  strip_tac >> gvs[] >> irule (cj 3 typing_permission_transfer) >> simp[]
QED

Theorem well_typed_exprs_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_exprs env x ==> well_typed_exprs env' x
Proof
  strip_tac >> gvs[] >> irule (cj 4 typing_permission_transfer) >> simp[]
QED

Theorem well_typed_opt_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_opt env x ==> well_typed_opt env' x
Proof
  strip_tac >> gvs[] >> irule (cj 5 typing_permission_transfer) >> simp[]
QED

Theorem well_typed_named_exprs_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_named_exprs env x ==> well_typed_named_exprs env' x
Proof
  strip_tac >> gvs[] >> irule (cj 6 typing_permission_transfer) >> simp[]
QED

Theorem type_place_expr_permission_compatible:
  !x env m vt vt'.
    type_place_expr env x = SOME vt /\
    type_place_expr (env with var_assignable := m) x = SOME vt' ==>
    vt = vt'
Proof
  measureInduct_on `expr_size x` >> Cases_on `x` >>
  simp[well_typed_expr_def, AllCaseEqs()] >> rpt strip_tac
  >~ [`type_place_expr _ (TopLevelName _ p) = _`]
  >- (PairCases_on `p` >> gvs[well_typed_expr_def, AllCaseEqs()]) >>
  gvs[well_typed_expr_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `e` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >> gvs[]
QED

Theorem typed_place_expr_permission_eq:
  !x env m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
    well_typed_expr env x ==>
    type_place_expr (env with var_assignable := m) x = type_place_expr env x
Proof
  measureInduct_on `expr_size x` >> Cases_on `x` >>
  simp[well_typed_expr_def] >> rpt strip_tac
  >~ [`type_place_expr _ (TopLevelName _ p)`]
  >- (PairCases_on `p` >> simp[well_typed_expr_def])
  >- (`well_typed_expr (env with var_assignable := m) e0` by
        (irule (cj 1 typing_permission_transfer) >> simp[]) >>
      first_x_assum (qspec_then `e` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  `well_typed_expr (env with var_assignable := m) e0` by
    (irule (cj 1 typing_permission_transfer) >> simp[]) >>
  drule_all (cj 2 typing_permission_transfer) >> simp[]
QED

Theorem typed_expr_no_hashmap_permission_transfer:
  env' = env with var_assignable := m /\
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_expr env x /\
  ~(?kt vt. type_place_expr env x = SOME (HashMapT kt vt)) ==>
  ~(?kt vt. type_place_expr env' x = SOME (HashMapT kt vt))
Proof
  strip_tac >> gvs[] >>
  drule_all typed_place_expr_permission_eq >> simp[]
QED
