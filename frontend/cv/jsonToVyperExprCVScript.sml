Theory jsonToVyperExprCV
Ancestors
  jsonToVyperExpr jsonToVyperTypeCV jsonAST vyperAST list option cv cv_rep
Libs
  cv_transLib jsonToVyperCVLib wordsLib Omega

(* Eliminate higher-order recursive OPTION_MAP specializations without changing
   which optional operands are translated. *)
Theorem OPTION_MAP_as_case:
  OPTION_MAP f x = case x of NONE => NONE | SOME y => SOME (f y)
Proof
  Cases_on `x` >> simp[]
QED

val () = cv_auto_trans fold_pin_constant_def;
val () = cv_auto_trans pin_fold_value_def;
val () = cv_auto_trans interface_constructor_result_def;
val () = cv_auto_trans translate_module_call_def;
val () = cv_auto_trans translate_call_def;

val origin_hex_byte_pre_def = cv_trans_pre "origin_hex_byte_pre"
  (SIMP_RULE list_ss [] origin_hex_byte_def);

Theorem origin_hex_byte_pre[cv_pre]:
  origin_hex_byte_pre (b : word8)
Proof
  rw[origin_hex_byte_pre_def] >>
  qspec_then `b` mp_tac wordsTheory.w2n_lt >>
  simp[wordsTheory.dimword_def] >> Omega.OMEGA_TAC
QED

val () = cv_auto_trans origin_hex_bytes_def;
val () = cv_auto_trans origin_int_string_def;
val () = cv_auto_trans canonical_literal_origin_def;
val () = cv_auto_trans origin_node_kind_def;
val () = cv_auto_trans origin_numeric_def;
val () = cv_auto_trans origin_text_def;
val () = cv_auto_trans origin_bytes_def;
val () = cv_auto_trans origin_same_value_def;
val () = cv_auto_trans origin_homogeneous_def;
val () = cv_auto_trans origin_membership_def;
val origin_select_pre_def = cv_auto_trans_pre "origin_select_pre" origin_select_def;

Theorem origin_select_pre[cv_pre]:
  origin_select_pre origin index
Proof
  rw[origin_select_pre_def, AllCaseEqs()]
QED

val () = cv_auto_trans origin_retype_def;
val () = cv_auto_trans expr_origin_key_def;
val () = cv_auto_trans lookup_origin_entry_def;
val () = cv_auto_trans lookup_origin_pair_def;
val () = cv_auto_trans membership_operand_def;

val () = cv_auto_trans find_keyword_def;
fun cv_equation name =
  case DefnBase.lookup_userdef
    (prim_mk_const {Thy = current_theory (), Name = name}) of
    SOME {thm = DefnBase.STDEQNS th,...} => th
  | _ => raise Fail ("missing CV equation: " ^ name);
val keyword_cv_def = cv_equation "cv_find_keyword";

Theorem cv_find_keyword_size:
  cv_size (cv_snd (cv_find_keyword name kws)) ≤ cv_size kws
Proof
  Induct_on `kws` >- simp[Once keyword_cv_def, cv_if_def] >>
  rename1 `cv_find_keyword name (cv$Pair head tail)` >>
  Cases_on `head` >>
  simp[Once keyword_cv_def, cv_if_def] >>
  rw[] >> simp[]
QED


Theorem cv_find_keyword_pair_size:
  cv_find_keyword name kws = cv$Pair a b ⇒ cv_size b ≤ cv_size kws
Proof
  strip_tac >>
  `cv_size (cv_snd (cv_find_keyword name kws)) ≤ cv_size kws`
    by irule cv_find_keyword_size >>
  gvs[]
QED


val translate_expr_with_policy_compute = save_thm
  ("translate_expr_with_policy_compute",
   PURE_REWRITE_RULE [OPTION_MAP_as_case, optionTheory.OPTION_BIND_eq_case]
     translate_expr_with_policy_def);

val translate_expr_with_policy_compute_ind =
  jsonToVyperCVLib.register_first_order_induction
    "translate_expr_with_policy_exec" translate_expr_with_policy_compute
    (WF_REL_TAC `measure (λx. case x of
       | INL (_, _, e) => json_expr_size e
       | INR (INL (_, _, es)) => list_size json_expr_size es
       | INR (INR (INL (_, _, kws))) => list_size json_keyword_size kws
       | INR (INR (INR (INL (_, _, e, value)))) => json_expr_size e
       | INR (INR (INR (INR (_, _, es, value)))) => list_size json_expr_size es)` >>
     rw[] >> imp_res_tac find_keyword_size >> gvs[] >>
     drule is_raw_call_calldata_call_nonempty >> Cases_on `args` >> gvs[]);

val translate_expr_with_policy_pre_def = cv_auto_trans_pre_rec
  "translate_expr_with_policy_pre translate_expr_list_with_policy_pre translate_kwargs_with_policy_pre resolved_origin_expr_pre resolved_origin_list_pre"
  translate_expr_with_policy_compute
  (WF_REL_TAC `measure (λx. case x of
       | INL (_, _, e) => cv_size e
       | INR (INL (_, _, es)) => cv_size es
       | INR (INR (INL (_, _, kws))) => cv_size kws
       | INR (INR (INR (INL (_, _, e, value)))) => cv_size e
       | INR (INR (INR (INR (_, _, es, value)))) => cv_size es)` >>
   cv_termination_tac >> imp_res_tac cv_find_keyword_pair_size >>
   first_assum (fn th =>
     match_mp_tac (MATCH_MP
       (REWRITE_RULE [GSYM AND_IMP_INTRO] arithmeticTheory.LESS_EQ_LESS_TRANS)
       th)) >> cv_termination_tac);

(* Default-mode APIs are nonrecursive aliases of the total policy translator. *)
val translate_expr_pre_def = cv_auto_trans_pre
  "translate_expr_pre" translate_expr_api_def;
val translate_expr_list_pre_def = cv_auto_trans_pre
  "translate_expr_list_pre" translate_expr_list_api_def;
val translate_kwargs_pre_def = cv_auto_trans_pre
  "translate_kwargs_pre" translate_kwargs_api_def;
val translate_origin_expr_pre_def = cv_auto_trans_pre
  "translate_origin_expr_pre" translate_origin_expr_api_def;
val translate_origin_list_pre_def = cv_auto_trans_pre
  "translate_origin_list_pre" translate_origin_list_api_def;


Theorem translate_expr_list_with_policy_map:
  translate_expr_list_with_policy resolve ctx es =
    MAP (translate_expr_with_policy resolve ctx) es
Proof
  Induct_on `es` >> simp[translate_expr_with_policy_def]
QED

Theorem translate_expr_with_policy_pre[cv_pre]:
  (∀resolve ctx e. translate_expr_with_policy_pre resolve ctx e) ∧
  (∀resolve ctx es. translate_expr_list_with_policy_pre resolve ctx es) ∧
  (∀resolve ctx kws. translate_kwargs_with_policy_pre resolve ctx kws) ∧
  (∀resolve ctx e value. resolved_origin_expr_pre resolve ctx e value) ∧
  (∀resolve ctx es values. resolved_origin_list_pre resolve ctx es values)
Proof
  ho_match_mp_tac translate_expr_with_policy_ind >>
  rpt strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [translate_expr_with_policy_pre_def] >> simp[] >>
  rpt strip_tac >>
  imp_res_tac calldata_slice_bound_length >>
  imp_res_tac is_raw_call_calldata_call_nonempty >>
  gvs[translate_expr_list_with_policy_map]
QED


Theorem translate_expr_list_map:
  translate_expr_list ctx es = MAP (translate_expr ctx) es
Proof
  Induct_on `es` >> simp[translate_expr_def]
QED

Theorem translate_expr_pre[cv_pre]:
  (∀ctx e. translate_expr_pre ctx e) ∧
  (∀ctx es. translate_expr_list_pre ctx es) ∧
  (∀ctx kws. translate_kwargs_pre ctx kws) ∧
  (∀ctx e value. translate_origin_expr_pre ctx e value) ∧
  (∀ctx es values. translate_origin_list_pre ctx es values)
Proof
  simp[translate_expr_pre_def, translate_expr_list_pre_def,
       translate_kwargs_pre_def, translate_origin_expr_pre_def,
       translate_origin_list_pre_def, translate_expr_with_policy_pre]
QED

(* These list helpers expose the original nested MAP recursions as ordinary
   mutually recursive equations. Their definitions retain an explicit bridge
   to the original logical API. *)
val () = cv_auto_trans translate_base_target_def;

Definition translate_target_list_def:
  translate_target_list ctx tgts = MAP (translate_target ctx) tgts
End

Theorem translate_target_list_compute:
  (translate_target_list ctx [] = []) /\
  (translate_target_list ctx (tgt::tgts) =
    translate_target ctx tgt :: translate_target_list ctx tgts)
Proof
  simp[translate_target_list_def]
QED

val translate_target_compute = save_thm ("translate_target_compute",
  CONJ (PURE_REWRITE_RULE [GSYM translate_target_list_def]
          translate_target_def)
       translate_target_list_compute);

val translate_target_compute_ind =
  jsonToVyperCVLib.register_first_order_induction "translate_target_exec"
    translate_target_compute
    (WF_REL_TAC `measure (λx. case x of
       | INL (_, tgt) => json_target_size tgt
       | INR (_, tgts) => list_size json_target_size tgts)` >> simp[]);

val () = cv_auto_trans translate_target_compute;

val () = cv_auto_trans translate_iter_def;

(* Annotation bounds are evaluated source expressions, so the annotation
   traversals follow the expression translation. *)
Definition annotations_resolved_cv_def:
  annotations_resolved_cv nominal_index all_import_maps ctx anns =
    EVERY (annotation_resolved nominal_index all_import_maps ctx) anns
End

Theorem annotations_resolved_cv_compute:
  (annotations_resolved_cv nominal_index all_import_maps ctx [] = T) /\
  (annotations_resolved_cv nominal_index all_import_maps ctx (ann::anns) =
    (annotation_resolved nominal_index all_import_maps ctx ann /\
     annotations_resolved_cv nominal_index all_import_maps ctx anns))
Proof
  simp[annotations_resolved_cv_def]
QED

val annotation_resolved_compute = save_thm ("annotation_resolved_compute",
  CONJ (PURE_REWRITE_RULE [GSYM annotations_resolved_cv_def] annotation_resolved_def)
       annotations_resolved_cv_compute);
val annotation_resolved_compute_ind = save_thm ("annotation_resolved_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "annotation_resolved_first_order"
    annotation_resolved_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (ni,im,ctx,ann) => json_type_annotation_size ann
     | INR (ni,im,ctx,anns) => list_size json_type_annotation_size anns)` >> simp[]));
val () = cv_auto_trans annotation_resolved_compute;

Definition elaborate_annotations_cv_def:
  elaborate_annotations_cv nominal_index all_import_maps ctx anns =
    MAP (elaborate_annotation nominal_index all_import_maps ctx) anns
End

Theorem elaborate_annotations_cv_compute:
  (elaborate_annotations_cv nominal_index all_import_maps ctx [] = []) /\
  (elaborate_annotations_cv nominal_index all_import_maps ctx (ann::anns) =
    elaborate_annotation nominal_index all_import_maps ctx ann ::
    elaborate_annotations_cv nominal_index all_import_maps ctx anns)
Proof
  simp[elaborate_annotations_cv_def]
QED

val elaborate_annotation_compute = save_thm ("elaborate_annotation_compute",
  CONJ (PURE_REWRITE_RULE [GSYM elaborate_annotations_cv_def] elaborate_annotation_def)
       elaborate_annotations_cv_compute);
val elaborate_annotation_compute_ind = save_thm ("elaborate_annotation_compute_ind",
  jsonToVyperCVLib.register_first_order_induction "elaborate_annotation_first_order"
    elaborate_annotation_compute
    (WF_REL_TAC `measure (λx. case x of
       INL (ni,im,ctx,ann) => json_type_annotation_size ann
     | INR (ni,im,ctx,anns) => list_size json_type_annotation_size anns)` >> simp[]));
val () = cv_auto_trans elaborate_annotation_compute;

(* Put the typeclass string test in the body: CV's pattern compiler cannot
   turn the literal-pattern presentation into a single case expression. *)
Theorem custom_error_target_compute:
  custom_error_target ctx e =
    case e of
      JE_Name name tc src ty =>
        if tc = SOME "error" then SOME (resolve_source_ref ctx src, name)
        else NONE
    | JE_Attribute obj name tc base_name base_tc src ty =>
        if tc = SOME "error" then
          SOME (resolve_func_module_ref ctx
            (JE_Attribute obj name tc base_name base_tc src ty) src, name)
        else NONE
    | _ => NONE
Proof
  map_every qid_spec_tac [`e`,`ctx`] >>
  ho_match_mp_tac custom_error_target_ind >>
  rw[custom_error_target_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

val () = cv_auto_trans custom_error_target_compute;
val translate_custom_error_compute = save_thm ("translate_custom_error_compute",
  PURE_REWRITE_RULE [GSYM translate_expr_list_map] translate_custom_error_def);
val () = cv_auto_trans translate_custom_error_compute;

(* The frontend's statement-list recursion threads lexical bindings itself.
   Retain that mutual recursion rather than translating each statement under
   one unchanged context. *)
val () = cv_auto_trans empty_value_tree_def;
val () = cv_auto_trans assign_value_def;
val translate_stmt_compute = save_thm ("translate_stmt_compute",
  PURE_REWRITE_RULE [GSYM translate_expr_list_map] translate_stmt_def);

val () = cv_auto_trans translate_stmt_compute;
