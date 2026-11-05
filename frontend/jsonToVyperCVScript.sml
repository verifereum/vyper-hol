Theory jsonToVyperCV
Ancestors
  jsonToVyper jsonToVyperTopLevel jsonToVyperExprCV jsonNominalSources
  jsonAST list option
Libs
  cv_transLib jsonToVyperCVLib

(* Preserve the source frontend's defined-input conditions, rather than
   choosing a value for its undefined empty interface-constructor case. *)
val translate_var_mutability_pre_def = cv_auto_trans_pre
  "translate_var_mutability_pre" translate_var_mutability_def;


val translate_toplevel_compute = save_thm ("translate_toplevel_compute",
  PURE_REWRITE_RULE [GSYM translate_expr_list_map] translate_toplevel_def);
val translate_toplevel_pre_def = cv_auto_trans_pre
  "translate_toplevel_pre" translate_toplevel_compute;

Definition translate_toplevels_def:
  translate_toplevels ni im ec tc nr declaration_only tops =
    MAP (λtop. if declaration_only ∧ is_function_toplevel top then NONE
               else translate_toplevel ni im ec tc nr top) tops
End

Theorem translate_toplevels_compute:
  (translate_toplevels ni im ec tc nr declaration_only [] = []) /\
  (translate_toplevels ni im ec tc nr declaration_only (top::tops) =
    (if declaration_only ∧ is_function_toplevel top then NONE
     else translate_toplevel ni im ec tc nr top) ::
    translate_toplevels ni im ec tc nr declaration_only tops)
Proof
  simp[translate_toplevels_def]
QED

val translate_toplevels_pre_def = cv_auto_trans_pre
  "translate_toplevels_pre" translate_toplevels_compute;

Theorem translate_toplevels_implementation:
  translate_toplevels ni im ec tc nr F tops =
    MAP (translate_toplevel ni im ec tc nr) tops
Proof
  simp[translate_toplevels_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

val translate_module_compute = save_thm ("translate_module_compute",
  PURE_REWRITE_RULE [GSYM translate_toplevels_implementation] translate_module_def);
val translate_module_pre_def = cv_auto_trans_pre
  "translate_module_pre" translate_module_compute;
val translate_imported_module_compute = save_thm ("translate_imported_module_compute",
  PURE_REWRITE_RULE [GSYM translate_toplevels_def] translate_imported_module_def);
val translate_imported_module_pre_def = cv_auto_trans_pre
  "translate_imported_module_pre" translate_imported_module_compute;
val translate_imported_modules_pre_def = cv_auto_trans_pre
  "translate_imported_modules_pre" translate_imported_modules_def;

(* Expose the override-default traversal's nested MAP calls as first-order
   recursion, retaining equations about the original canonicalizer. *)
Definition canonical_default_list_def:
  canonical_default_list fuel imports nsid consts es =
    MAP (canonical_default_aux fuel imports nsid consts) es
End

Definition canonical_default_keywords_def:
  canonical_default_keywords fuel imports nsid consts kws =
    MAP (λkw. case kw of JKeyword k v =>
      JKeyword k (canonical_default_aux fuel imports nsid consts v)) kws
End

Theorem canonical_default_list_compute:
  (canonical_default_list fuel imports nsid consts [] = []) ∧
  (canonical_default_list fuel imports nsid consts (e::es) =
    canonical_default_aux fuel imports nsid consts e ::
    canonical_default_list fuel imports nsid consts es)
Proof
  simp[canonical_default_list_def]
QED

Theorem canonical_default_keywords_compute:
  (canonical_default_keywords fuel imports nsid consts [] = []) ∧
  (canonical_default_keywords fuel imports nsid consts (JKeyword k v::kws) =
    JKeyword k (canonical_default_aux fuel imports nsid consts v) ::
    canonical_default_keywords fuel imports nsid consts kws)
Proof
  simp[canonical_default_keywords_def]
QED

val canonical_default_compute = save_thm ("canonical_default_compute",
  LIST_CONJ
    [canonical_default_aux_def
       |> PURE_REWRITE_RULE [LET_THM]
       |> CONV_RULE (DEPTH_CONV BETA_CONV)
       |> PURE_REWRITE_RULE [GSYM canonical_default_list_def,
                             GSYM canonical_default_keywords_def],
     canonical_default_list_compute, canonical_default_keywords_compute]);
val canonical_default_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "canonical_default_exec"
    canonical_default_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (_,_,_,_,e) => json_expr_size e
     | INR (INL (_,_,_,_,es)) => list_size json_expr_size es
     | INR (INR (_,_,_,_,kws)) => list_size json_keyword_size kws)` >>
     rw[] >> simp[json_expr_size_def]);
val canonical_default_pre_def = cv_auto_trans_pre
  "canonical_default_aux_pre canonical_default_list_pre canonical_default_keywords_pre"
  canonical_default_compute;

Theorem canonical_default_pre[cv_pre]:
  (∀fuel imports nsid consts e.
    canonical_default_aux_pre fuel imports nsid consts e) ∧
  (∀fuel imports nsid consts es.
    canonical_default_list_pre fuel imports nsid consts es) ∧
  (∀fuel imports nsid consts kws.
    canonical_default_keywords_pre fuel imports nsid consts kws)
Proof
  ho_match_mp_tac canonical_default_compute_ind >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC [canonical_default_pre_def] >> rw[] >> gvs[]
QED

(* canonical_default chooses its fuel using the datatype size. Specialize
   nested list_size recursions so the same size equations translate to CV. *)
Definition json_type_list_size_def:
  json_type_list_size tys = list_size json_type_size tys
End

Theorem json_type_list_size_compute:
  (json_type_list_size [] = 0) ∧
  (json_type_list_size (ty::tys) =
    SUC (json_type_size ty + json_type_list_size tys))
Proof
  simp[json_type_list_size_def]
QED

val json_type_size_compute = save_thm ("json_type_size_compute",
  CONJ (PURE_REWRITE_RULE [GSYM json_type_list_size_def] json_type_size_def)
       json_type_list_size_compute);
val json_type_size_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "json_type_size_exec"
    json_type_size_compute
    (WF_REL_TAC `measure (λx. case x of
       INL ty => json_type_size ty
     | INR tys => list_size json_type_size tys)` >>
     simp[json_type_size_def]);
val () = cv_auto_trans json_type_size_compute;

Definition json_expr_list_size_def:
  json_expr_list_size es = list_size json_expr_size es
End

Definition json_keyword_list_size_def:
  json_keyword_list_size kws = list_size json_keyword_size kws
End

Theorem json_expr_list_size_compute:
  (json_expr_list_size [] = 0) ∧
  (json_expr_list_size (e::es) =
    SUC (json_expr_size e + json_expr_list_size es))
Proof
  simp[json_expr_list_size_def]
QED

Theorem json_keyword_list_size_compute:
  (json_keyword_list_size [] = 0) ∧
  (json_keyword_list_size (kw::kws) =
    SUC (json_keyword_size kw + json_keyword_list_size kws))
Proof
  simp[json_keyword_list_size_def]
QED

val json_expr_size_compute = save_thm ("json_expr_size_compute",
  LIST_CONJ
    [PURE_REWRITE_RULE [GSYM json_type_list_size_def,
       GSYM json_expr_list_size_def, GSYM json_keyword_list_size_def]
       json_expr_size_def,
     json_expr_list_size_compute, json_keyword_list_size_compute]);
val json_expr_size_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "json_expr_size_exec"
    json_expr_size_compute
    (WF_REL_TAC `measure (λx. case x of
       INL e => json_expr_size e
     | INR (INL kw) => json_keyword_size kw
     | INR (INR (INL es)) => list_size json_expr_size es
     | INR (INR (INR kws)) => list_size json_keyword_size kws)` >>
     simp[json_expr_size_def]);
val json_expr_size_pre_def = cv_auto_trans_pre
  "json_expr_size_pre json_keyword_size_pre json_expr_list_size_pre json_keyword_list_size_pre"
  json_expr_size_compute;

Theorem json_expr_size_pre[cv_pre]:
  (∀e. json_expr_size_pre e) ∧
  (∀kw. json_keyword_size_pre kw) ∧
  (∀es. json_expr_list_size_pre es) ∧
  (∀kws. json_keyword_list_size_pre kws)
Proof
  ho_match_mp_tac json_expr_size_compute_ind >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC [json_expr_size_pre_def] >> rw[] >> gvs[]
QED

(* Keep both halves of the override signature check in one translation. *)
val () = cv_auto_trans json_type_supertype_def;

(* Enumerate initialized alias paths without hiding recursion under MAP. *)
Definition initialized_chain_paths_def:
  initialized_chain_paths fuel all_import_maps imports import_map prefix chains =
    FLAT (MAP (λchain.
      case resolve_module_chain all_import_maps import_map chain of
      | NONE => []
      | SOME nsid =>
          let path = prefix ++ LAST chain in
          (path, nsid) ::
          initialized_module_paths fuel all_import_maps imports
            (case ALOOKUP all_import_maps nsid of
             | SOME child_map => child_map
             | NONE => [])
            (find_module_body_nsid nsid imports) (path ++ ".")) chains)
End

Theorem initialized_chain_paths_compute:
  (initialized_chain_paths fuel all_import_maps imports import_map prefix [] = []) ∧
  (initialized_chain_paths fuel all_import_maps imports import_map prefix
      (alias_path::chains) =
    (case resolve_module_chain all_import_maps import_map alias_path of
     | NONE => []
     | SOME nsid =>
         let path = prefix ++ LAST alias_path in
         (path, nsid) ::
         initialized_module_paths fuel all_import_maps imports
           (case ALOOKUP all_import_maps nsid of
            | SOME child_map => child_map
            | NONE => [])
           (find_module_body_nsid nsid imports) (path ++ ".")) ++
    initialized_chain_paths fuel all_import_maps imports import_map prefix chains)
Proof
  simp[initialized_chain_paths_def]
QED

val initialized_module_paths_compute =
  save_thm ("initialized_module_paths_compute",
    CONJ (PURE_REWRITE_RULE [GSYM initialized_chain_paths_def]
            initialized_module_paths_def) initialized_chain_paths_compute);
val initialized_module_paths_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "initialized_module_paths_exec"
    initialized_module_paths_compute
    (WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       INL (fuel,_,_,_,_,_) => (fuel,0)
     | INR (fuel,_,_,_,_,chains) => (fuel,LENGTH chains + 1))` >>
     simp[]);
val initialized_chains_pre_def = cv_auto_trans_pre
  "initialized_chains_pre" initialized_chains_def;

Theorem initialized_chains_pre[cv_pre]:
  ∀tops. initialized_chains_pre tops
Proof
  Induct >> simp[Once initialized_chains_pre_def]
QED

val initialized_module_paths_pre_def = cv_auto_trans_pre_rec
  "initialized_module_paths_pre initialized_chain_paths_pre"
  initialized_module_paths_compute
  (WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
     INL (fuel,_,_,_,_,_) => (cv$c2n fuel,0)
   | INR (fuel,_,_,_,_,chains) => (cv$c2n fuel,cv_size chains + 1))` >>
   cv_termination_tac);
val layout_import_map_pre_def = cv_auto_trans_pre
  "layout_import_map_pre" layout_import_map_def;

val translate_annotated_ast_canonical_pre_def = cv_auto_trans_pre
  "translate_annotated_ast_canonical_pre" translate_annotated_ast_canonical_def;

(* Register each mutually recursive nominal-resolution family together. *)
val () = cv_auto_trans resolve_json_type_def;
val resolve_json_expr_pre_def = cv_auto_trans_pre
  "resolve_json_expr_pre resolve_json_exprs_pre resolve_json_keywords_pre"
  resolve_json_expr_def;

Theorem resolve_json_expr_pre[cv_pre]:
  (∀decls e. resolve_json_expr_pre decls e) ∧
  (∀decls es. resolve_json_exprs_pre decls es) ∧
  (∀decls kws. resolve_json_keywords_pre decls kws)
Proof
  ho_match_mp_tac resolve_json_expr_ind >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC [resolve_json_expr_pre_def] >> rw[] >> gvs[]
QED

val () = cv_auto_trans resolve_json_target_def;
val resolve_json_stmt_pre_def = cv_auto_trans_pre
  "resolve_json_stmt_pre resolve_json_stmts_pre" resolve_json_stmt_def;

Theorem resolve_json_stmt_pre[cv_pre]:
  (∀decls stmt. resolve_json_stmt_pre decls stmt) ∧
  (∀decls stmts. resolve_json_stmts_pre decls stmts)
Proof
  ho_match_mp_tac resolve_json_stmt_ind >>
  rpt strip_tac >>
  ONCE_REWRITE_TAC [resolve_json_stmt_pre_def] >> rw[] >> gvs[]
QED

val translate_annotated_ast_pre_def = cv_auto_trans_pre
  "translate_annotated_ast_pre" translate_annotated_ast_def;
