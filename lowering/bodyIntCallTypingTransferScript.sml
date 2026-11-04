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

Theorem extend_local_permission_update:
  extend_local (env with var_assignable := m) id ty b =
  (extend_local env id ty b) with var_assignable := (m |+ (id,b))
Proof
  simp[extend_local_def, typing_env_component_equality]
QED

Theorem well_typed_target_permission_transfer:
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_target env tgt ty ==>
  well_typed_target (env with var_assignable := m) tgt ty
Proof
  simp[well_typed_target_def] >> rpt strip_tac >>
  irule (cj 3 typing_permission_transfer) >> simp[]
QED

Theorem well_typed_atarget_permission_transfer:
  !env tgt ty. !m.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
    well_typed_atarget env tgt ty ==>
    well_typed_atarget (env with var_assignable := m) tgt ty
Proof
  ho_match_mp_tac well_typed_atarget_ind >> rpt strip_tac >>
  gvs[well_typed_atarget_def]
  >- (irule well_typed_target_permission_transfer >> simp[]) >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >> qid_spec_tac `tys` >>
  Induct_on `tgts` >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> simp[] >> rpt strip_tac
  >- (rename1 `well_typed_atarget env head headty` >>
      first_x_assum irule >> simp[] >> qexists `[headty]` >> simp[]) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> goal_assum (drule_at Any)
QED

Theorem atarget_accepts_permission_transfer:
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  atarget_accepts env tgt ty ==>
  atarget_accepts (env with var_assignable := m) tgt ty
Proof
  Cases_on `tgt` >> simp[atarget_accepts_def] >> rpt strip_tac
  >- (Cases_on `type_place_target env b` >> gvs[] >>
      rename1 `type_place_target env b = SOME vt` >> Cases_on `vt` >> gvs[] >>
      drule_all (cj 3 typing_permission_transfer) >> simp[]) >>
  irule well_typed_atarget_permission_transfer >> simp[]
QED

Theorem well_typed_iterator_permission_transfer:
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_iterator env ty it ==>
  well_typed_iterator (env with var_assignable := m) ty it
Proof
  Cases_on `it` >> simp[well_typed_iterator_def] >> rpt strip_tac >>
  metis_tac[cj 1 typing_permission_transfer]
QED

Theorem well_typed_custom_error_permission_transfer:
  (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  well_typed_custom_error env err ==>
  well_typed_custom_error (env with var_assignable := m) err
Proof
  simp[well_typed_custom_error_def] >> rpt strip_tac >>
  irule (cj 4 typing_permission_transfer) >> simp[]
QED

Theorem stmt_permission_transfer:
  (!env rt s. !m out.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
    type_stmt env rt s = SOME out ==>
    ?m_out. type_stmt (env with var_assignable := m) rt s =
      SOME (out with var_assignable := m_out) /\
      (!n. FLOOKUP out.var_assignable n = SOME T ==>
           FLOOKUP m_out n = SOME T)) /\
  (!env rt ss. !m out.
    (!n. FLOOKUP env.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
    type_stmts env rt ss = SOME out ==>
    ?m_out. type_stmts (env with var_assignable := m) rt ss =
      SOME (out with var_assignable := m_out) /\
      (!n. FLOOKUP out.var_assignable n = SOME T ==>
           FLOOKUP m_out n = SOME T))
Proof
  ho_match_mp_tac type_stmt_ind >> rpt strip_tac >>
  gvs[type_stmt_def, AllCaseEqs()]
  >- (qexists `m` >> simp[])
  >- (qexists `m` >> simp[])
  >- (qexists `m` >> simp[])
  >- (qexists `m` >> simp[] >>
      metis_tac[cj 1 typing_permission_transfer, typed_expr_no_hashmap_permission_transfer])
  >- (qexists `m` >> simp[])
  >- (qexists `m` >> simp[] >> metis_tac[cj 1 typing_permission_transfer])
  >- (qexists `m` >> simp[])
  >- (qexists `m` >> simp[])
  >- (qexists `m` >> simp[] >> metis_tac[cj 1 typing_permission_transfer])
  >- (qexists `m` >> simp[] >> metis_tac[well_typed_custom_error_permission_transfer])
  >- (qexists `m` >> simp[] >> metis_tac[cj 1 typing_permission_transfer])
  >- (qexists `m` >> simp[] >> metis_tac[cj 1 typing_permission_transfer])
  >- (qexists `m` >> simp[] >> metis_tac[cj 1 typing_permission_transfer])
  >- (qexists `m` >> simp[] >>
      metis_tac[cj 1 typing_permission_transfer, well_typed_custom_error_permission_transfer])
  >- (qexists `m` >> simp[] >> metis_tac[cj 4 typing_permission_transfer])
  >- (qexists `m |+ (id,T)` >> simp[extend_local_permission_update] >> conj_tac
      >- metis_tac[cj 1 typing_permission_transfer] >>
      simp[extend_local_def] >> drule permission_lookup_update >> simp[])
  >- (drule_all (cj 3 typing_permission_transfer) >> strip_tac >>
      qexists `m` >> simp[] >> metis_tac[cj 1 typing_permission_transfer])
  >- (qexists `m` >> simp[] >>
      metis_tac[cj 1 typing_permission_transfer, atarget_accepts_permission_transfer])
  >- (qexists `m` >> simp[] >>
      metis_tac[cj 1 typing_permission_transfer, well_typed_target_permission_transfer])
  >- (qexists `m` >> simp[] >> gvs[optionTheory.IS_SOME_EXISTS] >>
      metis_tac[cj 1 typing_permission_transfer])
  >- suspend "loop"
  >- (qexists `m` >> simp[]) >>
  suspend "cons"
QED

Resume stmt_permission_transfer[loop]:
  qexists `m` >> simp[extend_local_permission_update] >> conj_tac
  >- (irule well_typed_iterator_permission_transfer >> simp[]) >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  first_x_assum (qspec_then `m |+ (id,F)` mp_tac) >>
  simp[extend_local_def] >>
  (impl_tac >- (drule permission_lookup_update >> simp[])) >>
  strip_tac >> goal_assum (drule_at Any)
QED

Resume stmt_permission_transfer[cons]:
  qpat_x_assum `!m'. _ ==> ?m_out. type_stmt _ _ _ = _ /\ _`
    (qspec_then `m` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Finalise stmt_permission_transfer
