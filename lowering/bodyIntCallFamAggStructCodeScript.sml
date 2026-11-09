(* Code slices for the counted struct-field traversal. *)
Theory bodyIntCallFamAggStructCode
Ancestors
  bodyIntCallFamAggStructFields exprLoweringProps fragExec compileEnv pair
  exprSimHyps exprSimHypsDefs exprSimAggregateChildren vyperTypeInvariants

Theorem compile_struct_lit_cons_code:
  ALOOKUP (get_struct_fields ce.ce_struct_fields
    (case ty of StructT n => nsid_to_string n | _ => "")) name = SOME (fty,sz) /\
  compile_struct_lit compile_expr ce ty ((name,e)::fields) buf off sa = (out,sb) /\
  fn_has_code sa sb func ==>
  ?vv sm dst sn op su st.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst fty (lowered_value_type ce e) su = ((),st) /\
    compile_struct_lit compile_expr ce ty fields buf (off+sz) st = (out,sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\
    fn_has_code sn su func /\ fn_has_code su st func /\ fn_has_code st sb func /\
    sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id
Proof
  strip_tac >> drule_all compile_struct_lit_cons_inv >> strip_tac >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, SND] >>
  `ci_mono su st` by metis_tac[ci_mono_compile_store_memory, SND] >>
  `ci_mono st sb` by
    metis_tac[ci_mono_compile_struct_lit_cfn, compile_expr_ci_mono, SND] >>
  gvs[ci_mono_def] >>
  `cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

(* The destination is the source annotation, not the possibly smaller
   lowered representation.  Only the store compiler is normalized. *)
Theorem struct_child_store_types:
  expr_body_pre ce cx env e es ==>
  type_widens_to env.type_defs (expr_type e) (expr_type e) /\
  type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e) /\
  (?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv) /\
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
  compile_store_memory ce src dst (expr_type e) (post_value_type ce e)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def,
       env_consistent_def, env_context_consistent_def] >>
  metis_tac[vyperTypeArgFitsTheory.type_widens_to_refl,
    post_value_type_widens, post_type_evaluates,
    compile_store_memory_post_type, expr_body_pre_def]
QED
