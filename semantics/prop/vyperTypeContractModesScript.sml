Theory vyperTypeContractModes
Ancestors
  list pair finite_map pred_set
  vyperAST vyperTypeSystem vyperTypeContract vyperTypeContractStaticMaps

Triviality add_toplevel_static_maps_runtime_fn_sigs:
  check_toplevel_decl mods art src tl /\
  runtime.cta_fn_sigs =
    DRESTRICT dep.cta_fn_sigs (\key. SND key <> "__init__") ==>
  (add_toplevel_static_maps F src tl runtime).cta_fn_sigs =
    DRESTRICT (add_toplevel_static_maps T src tl dep).cta_fn_sigs
      (\key. SND key <> "__init__")
Proof
  Cases_on `tl` >>
  TRY (rename1 `VariableDecl _ mut _ _ _` >> Cases_on `mut`) >>
  simp[add_toplevel_static_maps_def] >>
  rename1 `FunctionDecl vis _ _ _ name _ _ _ _` >>
  Cases_on `vis` >>
  simp[check_toplevel_decl_def, function_header_ok_def, include_fn_sig_def,
       IN_runtime_fn_sig_keys] >>
  metis_tac[]
QED

Triviality add_module_static_maps_runtime_fn_sigs:
  !tls dep runtime.
    EVERY (check_toplevel_decl mods art src) tls /\
    runtime.cta_fn_sigs =
      DRESTRICT dep.cta_fn_sigs (\key. SND key <> "__init__") ==>
    (add_module_static_maps F src tls runtime).cta_fn_sigs =
      DRESTRICT (add_module_static_maps T src tls dep).cta_fn_sigs
        (\key. SND key <> "__init__")
Proof
  Induct >> simp[add_module_static_maps_def] >>
  rpt strip_tac >> simp[GSYM add_module_static_maps_def] >>
  first_x_assum irule >> simp[] >>
  metis_tac[add_toplevel_static_maps_runtime_fn_sigs]
QED

Triviality fold_static_maps_runtime_fn_sigs:
  !units dep runtime.
    EVERY (\(src,tls). EVERY (check_toplevel_decl mods art src) tls) units /\
    runtime.cta_fn_sigs =
      DRESTRICT dep.cta_fn_sigs (\key. SND key <> "__init__") ==>
    (FOLDL (\a (src,tls). add_module_static_maps F src tls a) runtime units).
      cta_fn_sigs =
    DRESTRICT
      (FOLDL (\a (src,tls). add_module_static_maps T src tls a) dep units).
        cta_fn_sigs (\key. SND key <> "__init__")
Proof
  Induct >- simp[] >>
  Cases >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[add_module_static_maps_runtime_fn_sigs]
QED

Triviality live_artifact_runtime_projection:
  EVERY (check_module T layouts addr mods live art) mods ==>
  live_artifact layouts addr mods live (build_contract_type_artifact F mods) =
    (live_artifact layouts addr mods live (build_contract_type_artifact T mods))
      with <| cta_fn_sigs :=
                DRESTRICT
                  (live_artifact layouts addr mods live
                    (build_contract_type_artifact T mods)).cta_fn_sigs
                  (\key. SND key <> "__init__");
              cta_bare_global_assignable := FEMPTY |>
Proof
  strip_tac >>
  `EVERY (\(src,tls). EVERY (check_toplevel_decl mods art src) tls) mods` by
    (gvs[EVERY_MEM, FORALL_PROD, check_module_def] >> metis_tac[]) >>
  `(build_contract_type_artifact F mods).cta_fn_sigs =
    DRESTRICT (build_contract_type_artifact T mods).cta_fn_sigs
      (\key. SND key <> "__init__")` by
    (simp[build_contract_type_artifact_def] >>
     drule (Q.SPECL [`mods`, `empty_contract_type_artifact`,
                      `empty_contract_type_artifact`]
                     fold_static_maps_runtime_fn_sigs) >>
     impl_tac >- simp[empty_contract_type_artifact_def] >> simp[]) >>
  simp[contract_type_artifact_component_equality, live_artifact_def,
       build_contract_type_artifact_runtime_assignable,
       build_contract_type_artifact_nonsig_mode_irrelevant,
       INTER_COMM]
QED

Triviality well_typed_exprs_cong_on:
  !es. (!e. MEM e es ==> (well_typed_expr env e <=> well_typed_expr env' e)) ==>
    (well_typed_exprs env es <=> well_typed_exprs env' es)
Proof
  Induct >> simp[well_typed_expr_def]
QED

Triviality well_typed_named_exprs_cong_on:
  !kes. (!e. MEM e (MAP SND kes) ==>
    (well_typed_expr env e <=> well_typed_expr env' e)) ==>
    (well_typed_named_exprs env kes <=> well_typed_named_exprs env' kes)
Proof
  Induct >- simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

(* A constant initializer cannot call a function or write an immutable. *)
Triviality well_typed_constant_expr_runtime_artifact:
  !mods e. constant_expr mods e ==>
    (well_typed_expr (artifact_env art mods src) e <=>
     well_typed_expr (artifact_env
       (art with <| cta_fn_sigs := sigs; cta_bare_global_assignable := FEMPTY |>)
       mods src) e) /\
    type_place_expr (artifact_env art mods src) e =
    type_place_expr (artifact_env
      (art with <| cta_fn_sigs := sigs; cta_bare_global_assignable := FEMPTY |>)
      mods src) e
Proof
  recInduct constant_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[constant_expr_def, well_typed_expr_def, artifact_env_def]
  >~ [`well_typed_named_exprs`] >-
    (rpt strip_tac >> cong_tac (SOME 1) >>
     irule well_typed_named_exprs_cong_on >> gvs[EVERY_MEM] >> metis_tac[])
  >~ [`subscript_base_type_exact`] >-
    (rpt strip_tac >> gvs[] >>
     Cases_on `e1` >>
     gvs[constant_expr_def, subscript_base_type_exact_def])
  >> rpt strip_tac >> cong_tac (SOME 1) >>
     irule well_typed_exprs_cong_on >> gvs[EVERY_MEM] >> metis_tac[]
QED

Triviality check_toplevel_decl_runtime_artifact:
  check_toplevel_decl mods art src tl ==>
  check_toplevel_decl mods
    (art with <| cta_fn_sigs := sigs; cta_bare_global_assignable := FEMPTY |>)
    src tl
Proof
  Cases_on `tl` >>
  TRY (rename1 `VariableDecl _ mut _ _ _` >> Cases_on `mut`) >>
  simp[check_toplevel_decl_def] >>
  metis_tac[well_typed_constant_expr_runtime_artifact]
QED

Triviality check_module_deploy_implies_runtime:
  art' = (art with <|
    cta_fn_sigs := DRESTRICT art.cta_fn_sigs (\key. SND key <> "__init__");
    cta_bare_global_assignable := FEMPTY |>) /\
  check_module T layouts addr mods live art unit ==>
  check_module F layouts addr mods live art' unit
Proof
  Cases_on `unit` >> simp[check_module_def] >> strip_tac >> conj_tac
  >- (gvs[EVERY_MEM] >> metis_tac[check_toplevel_decl_runtime_artifact]) >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> rename1 `check_toplevel_body T _ _ _ _ _ _ tl ==> _` >>
  Cases_on `tl` >>
  simp[check_toplevel_body_def, check_function_body_in_mode_def] >>
  metis_tac[]
QED

Theorem check_contract_deploy_implies_runtime:
  check_contract T layouts addr mods = SOME deploy_art ==>
  ?runtime_art. check_contract F layouts addr mods = SOME runtime_art
Proof
  simp[check_contract_def, AllCaseEqs(), LET_THM] >> strip_tac >>
  drule contract_namespaces_ok_deploy_implies_runtime >> strip_tac >>
  drule live_artifact_runtime_projection >> strip_tac >>
  simp[] >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule check_module_deploy_implies_runtime >>
  qexists_tac `live_artifact layouts addr mods (live_functions layouts addr mods)
    (build_contract_type_artifact T mods)` >>
  gvs[EVERY_MEM]
QED
