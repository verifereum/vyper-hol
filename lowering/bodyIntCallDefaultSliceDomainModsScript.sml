Theory bodyIntCallDefaultSliceDomainMods
Ancestors
  runtimeDefaultCompile bodyFullPreds bodyFullPredsMods constSubstMods constSubstCorrect
  vyperTypeContract vyperTypeEvalProofs vyperContext gasShadow
  supportedExprTraverse gasShadowShape whitelistCheckerConsts
  constSubstModsCorrect vyperTypeExternalDefaults vyperTypeContractContext
  vyperTypeContractFunction vyperTypeSystem vyperTypeInvariants
  rich_list alist pair option list

val bad_builtin_arity = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem default_shadow_builtin_arity[local]:
  builtin_args_length_ok (gas_shadow_builtin bi) n =
  builtin_args_length_ok bi n
Proof
  rw[gas_shadow_builtin_def, builtin_args_length_ok_def]
QED

Theorem default_shadow_arity[local]:
  supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr es) =
  supported_exprs_exists ^bad_builtin_arity es
Proof
  irule (cj 3 gas_shadow_expr_exists_invariant) >>
  Cases >> simp[gas_shadow_expr_def, default_shadow_builtin_arity]
QED

Theorem default_slice_arity[local]:
  well_typed_exprs env xs ==>
  ~supported_exprs_exists ^bad_builtin_arity xs /\
  ~supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr xs)
Proof
  strip_tac >> drule (cj 4 well_typed_expr_builtin_args_length) >>
  simp[default_shadow_arity]
QED

Theorem default_runtime_subst[local]:
  (!key r. ALOOKUP E key = SOME r ==> constant_expr mods r) ==>
  (!e. runtime_constant_expr mods e ==>
       runtime_constant_expr mods (subst_consts_expr_mods E e)) /\
  (!xs. EVERY (runtime_constant_expr mods) xs ==>
        EVERY (runtime_constant_expr mods) (subst_consts_exprs_mods E xs)) /\
  (!fs. EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
        EVERY (runtime_constant_expr mods) (MAP SND (subst_consts_fields_mods E fs))) /\
  (!e. constant_expr mods e ==> constant_expr mods (subst_consts_expr_mods E e)) /\
  (!xs. EVERY (constant_expr mods) xs ==>
        EVERY (constant_expr mods) (subst_consts_exprs_mods E xs)) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
        EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods E fs)))
Proof
  strip_tac >>
  `!e. bool_literal_expr e ==> bool_literal_expr (subst_consts_expr_mods E e)` by
    (Cases >> simp[bool_literal_expr_def, subst_consts_expr_mods_def]) >>
  `(!e. (runtime_constant_expr mods e ==>
       runtime_constant_expr mods (subst_consts_expr_mods E e)) /\
       (constant_expr mods e ==> constant_expr mods (subst_consts_expr_mods E e))) /\
   (!xs. (EVERY (runtime_constant_expr mods) xs ==>
        EVERY (runtime_constant_expr mods) (subst_consts_exprs_mods E xs)) /\
        (EVERY (constant_expr mods) xs ==>
        EVERY (constant_expr mods) (subst_consts_exprs_mods E xs))) /\
   (!fs. (EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
        EVERY (runtime_constant_expr mods) (MAP SND (subst_consts_fields_mods E fs))) /\
        (EVERY (constant_expr mods) (MAP SND fs) ==>
        EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods E fs))))`
    suffices_by simp[FORALL_AND_THM] >>
  `(!E' e. E' = E ==>
      (runtime_constant_expr mods e ==>
       runtime_constant_expr mods (subst_consts_expr_mods E' e)) /\
      (constant_expr mods e ==> constant_expr mods (subst_consts_expr_mods E' e))) /\
   (!E' (t:base_assignment_target). E' = E ==> T) /\
   (!E' xs. E' = E ==>
      (EVERY (runtime_constant_expr mods) xs ==>
       EVERY (runtime_constant_expr mods) (subst_consts_exprs_mods E' xs)) /\
      (EVERY (constant_expr mods) xs ==> EVERY (constant_expr mods) (subst_consts_exprs_mods E' xs))) /\
   (!E' (opt:expr option). E' = E ==> T) /\
   (!E' fs. E' = E ==>
      (EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
       EVERY (runtime_constant_expr mods) (MAP SND (subst_consts_fields_mods E' fs))) /\
      (EVERY (constant_expr mods) (MAP SND fs) ==>
       EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods E' fs))))`
    suffices_by simp[] >>
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  simp[subst_consts_expr_mods_def, runtime_constant_expr_def, constant_expr_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `ALOOKUP E (ns,id)` >>
  simp[constant_expr_def, runtime_constant_expr_def] >>
  metis_tac[constant_expr_runtime_constant]
QED

Theorem default_slice_runtime_shadow[local]:
  EVERY (runtime_constant_expr mods) xs ==>
  EVERY (runtime_constant_expr mods) (MAP gas_shadow_expr xs)
Proof
  simp[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  metis_tac[runtime_constant_expr_gas_shadow]
QED

(* The checked entry environment has an empty local map for defaults. *)
Theorem default_checked_typing[local]:
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss ==>
  well_typed_exprs (artifact_env art mods src) (DROP n dflts) /\
  well_typed_exprs (artifact_env art mods src)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) /\
  EVERY (runtime_constant_expr mods) dflts
Proof
  simp[check_function_body_def, LET_THM, defaults_env_function_entry_env] >>
  strip_tac >> simp[well_typed_exprs_DROP]
QED

Theorem default_const_range[local]:
  body_const_cells_agree mods cx env st ==>
  !key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==> constant_expr mods rhs
Proof
  simp[body_const_cells_agree_def, FORALL_PROD] >>
  rpt strip_tac >>
  qpat_assum `!s id rhs. ALOOKUP (consts_env_mods mods) _ = SOME rhs ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Theorem intcall_default_slice_domain_mods:
  check_function_body cx.layouts cx.txn.target mods art src vis mut nr args dflts ret ss /\
  body_const_cells_agree mods cx env st ==>
  let raw = DROP n dflts in
  let ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts) in
  well_typed_exprs (artifact_env art mods src) raw /\
  well_typed_exprs (artifact_env art mods src) ds /\
  EVERY (runtime_constant_expr mods) raw /\
  EVERY (runtime_constant_expr mods) ds /\
  EVERY (runtime_constant_expr mods) (MAP gas_shadow_expr raw) /\
  EVERY (runtime_constant_expr mods) (MAP gas_shadow_expr ds) /\
  ~supported_exprs_exists ^bad_builtin_arity raw /\
  ~supported_exprs_exists ^bad_builtin_arity ds /\
  ~supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr raw) /\
  ~supported_exprs_exists ^bad_builtin_arity (MAP gas_shadow_expr ds)
Proof
  strip_tac >> simp[LET_THM] >>
  drule default_checked_typing >> disch_then (qspec_then `n` strip_assume_tac) >>
  drule default_const_range >> disch_then (mp_tac o MATCH_MP default_runtime_subst) >>
  strip_tac >>
  `EVERY (runtime_constant_expr mods) (subst_consts_exprs_mods (consts_env_mods mods) dflts)` by
    (qpat_assum `!xs. EVERY (runtime_constant_expr mods) xs ==> _` irule >> simp[]) >>
  qpat_assum `well_typed_exprs _ (DROP n dflts)`
    (mp_then Any strip_assume_tac default_slice_arity) >>
  qpat_assum `well_typed_exprs _ (DROP _ (subst_consts_exprs_mods _ _))`
    (mp_then Any strip_assume_tac default_slice_arity) >>
  simp[EVERY_DROP, default_slice_runtime_shadow]
QED

(* Transfer from the checked function entry to the selected proof view,
   still with the type checker's empty local maps for defaults. *)
Theorem default_slice_static_maps:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  env_context_consistent env cx /\ frame_maps env art /\ env.current_src = src ==>
  !xs. well_typed_exprs (artifact_env art mods src) xs ==>
       well_typed_exprs (defaults_env env) xs
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `static_maps_transfer_env (function_entry_env art mods src Internal [])
    (function_entry_env art mods src Internal [] with
      <|toplevel_vtypes := env.toplevel_vtypes; flag_members := env.flag_members|>)` by
    (irule function_entry_env_static_maps_transfer >>
     fs[frame_maps_def] >> qexists_tac `cx` >> simp[]) >>
  qpat_assum `well_typed_exprs (artifact_env _ _ _) _`
    (mp_then Any mp_tac (cj 4 well_typed_static_maps_transfer)) >>
  disch_then (qspec_then `defaults_env env` mp_tac) >>
  qpat_x_assum `static_maps_transfer_env _ _` mp_tac >>
  simp[static_maps_transfer_env_def, defaults_env_def, function_entry_env_def,
       artifact_env_def] >>
  rpt strip_tac >> first_x_assum irule >>
  fs[frame_maps_def, env_context_consistent_def, get_tenv_def]
QED
