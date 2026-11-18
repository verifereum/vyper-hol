Theory deploySymSrcFrameStmtModule
Ancestors
  symbolicSourceCompilerStmtFrame
  deploySymSrcBlockFrame deploySymSrcFrameExprHelpers
  stmtLowering moduleLowering compileEnv

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks` (Q.GEN `R` theorem));

Theorem deploy_blocks_frame_option_case[local,simp]:
  deploy_blocks_frame (case x of NONE => m | SOME y => f y) =
  (case x of NONE => deploy_blocks_frame m | SOME y => deploy_blocks_frame (f y))
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_stmt_option_case)
QED

Theorem deploy_blocks_frame_pair_case[local,simp]:
  deploy_blocks_frame ((\(x,y). f x y) p) =
  (\(x,y). deploy_blocks_frame (f x y)) p
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_stmt_pair_case)
QED

Theorem deploy_blocks_frame_get_terminated:
  (!b. deploy_blocks_frame (k b)) ==>
  deploy_blocks_frame (comp_bind comp_get (\s. k (block_is_terminated s)))
Proof
  simp[deploy_blocks_frame_def, comp_bind_def, comp_get_def] >>
  metis_tac[]
QED

Theorem deploy_blocks_frame_internal_param_decls[simp]:
  !params idx. deploy_blocks_frame (compile_internal_param_decls params idx)
Proof
  Induct >> simp[compile_internal_param_decls_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_internal_param_decls_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_materialize_internal_params[simp]:
  !params cenv. deploy_blocks_frame (materialize_internal_params cenv params)
Proof
  Induct >> simp[materialize_internal_params_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h1` >> simp[materialize_internal_params_def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[] >>
  Cases_on `x` >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_internal_function_cond:
  (!n. deploy_blocks_frame (compile_fixed_region_with_id n)) /\
  (!key trans view. deploy_blocks_frame (compile_nonreentrant_lock key trans view)) /\
  (!key trans view. deploy_blocks_frame (compile_nonreentrant_unlock key trans view)) /\
  (!ce loop ty ss. deploy_blocks_frame (compile_stmts ce loop ty ss)) ==>
  deploy_blocks_frame (compile_internal_function cenv params has_buf nr key trans view
                                               ctor imm_len ss ret)
Proof
  strip_tac >> simp[compile_internal_function_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  Cases_on `ret` >> simp[] >>
  rpt (match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  ho_match_mp_tac deploy_blocks_frame_get_terminated >>
  gen_tac >> Cases_on `b` >> simp[]
QED

Theorem deploy_blocks_frame_load_tuple_elements:
  (!v b. deploy_blocks_frame (compile_load_memory v b)) ==>
  !tys cenv op off. deploy_blocks_frame (compile_load_tuple_elements cenv op tys off)
Proof
  strip_tac >> Induct >> simp[compile_load_tuple_elements_def]
QED

Theorem deploy_blocks_frame_range_bound_checks[simp]:
  deploy_blocks_frame (compile_range_bound_checks a b c d s)
Proof
  Cases_on `s` >> simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem deploy_blocks_frame_declare_local:
  (!n. deploy_blocks_frame (compile_fixed_region_with_id n)) ==>
  deploy_blocks_frame (declare_local cenv id ty)
Proof
  strip_tac >> simp[declare_local_def] >> IF_CASES_TAC >> simp[]
QED

Theorem deploy_blocks_frame_emit_local_alloca[simp]:
  deploy_blocks_frame (emit_local_alloca cenv id)
Proof
  simp[emit_local_alloca_def] >> rpt BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem deploy_blocks_frame_declare_stmt_local:
  (!ce id ty. deploy_blocks_frame (declare_local ce id ty)) ==>
  deploy_blocks_frame (declare_stmt_local cenv s)
Proof
  strip_tac >> Cases_on `s` >> simp[declare_stmt_local_def]
QED

Theorem deploy_blocks_frame_mcopy_guard[simp]:
  deploy_blocks_frame m ==> deploy_blocks_frame (compile_mcopy_guard cenv m)
Proof
  strip_tac >> match_mp_tac (specialize_frame symbolic_frame_mcopy_guard) >> simp[]
QED

Theorem deploy_blocks_frame_return_unlock:
  (!k t v. deploy_blocks_frame (compile_nonreentrant_unlock k t v)) ==>
  deploy_blocks_frame (compile_return_unlock cenv)
Proof
  strip_tac >> simp[compile_return_unlock_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem deploy_blocks_frame_internal_return:
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) /\
  (!v b. deploy_blocks_frame (compile_load_memory v b)) ==>
  deploy_blocks_frame (compile_internal_return cenv rv rpc n ty sty tys rb)
Proof
  strip_tac >> simp[compile_internal_return_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC]) >>
  disj2_tac >> simp[deploy_blocks_frame_load_tuple_elements]
QED

Theorem deploy_blocks_frame_external_return:
  (!k t v. deploy_blocks_frame (compile_nonreentrant_unlock k t v)) /\
  (!a b i. deploy_blocks_frame (compile_abi_encode_to_buf a b i)) ==>
  deploy_blocks_frame (compile_external_return rv prim raw info maxsize nr k t v)
Proof
  strip_tac >> simp[compile_external_return_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_internal_return_from_env:
  (!c. deploy_blocks_frame (compile_return_unlock c)) /\
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) /\
  (!v b. deploy_blocks_frame (compile_load_memory v b)) ==>
  deploy_blocks_frame (compile_internal_return_from_env cenv ty sty op rpc)
Proof
  strip_tac >> simp[compile_internal_return_from_env_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[deploy_blocks_frame_internal_return]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_revert_with_reason:
  (!c v. deploy_blocks_frame (unwrap_value c v)) ==>
  deploy_blocks_frame (compile_revert_with_reason cenv msg ty n)
Proof
  strip_tac >> match_mp_tac (specialize_frame symbolic_frame_revert_with_reason) >> simp[]
QED

Theorem deploy_blocks_frame_reason_message:
  (!c t e. deploy_blocks_frame (compile_expr c t e)) ==>
  deploy_blocks_frame (compile_reason_message cenv e)
Proof
  strip_tac >> match_mp_tac (specialize_frame symbolic_frame_reason_message) >> simp[]
QED

Theorem deploy_blocks_frame_log_save_arg:
  (!c t v. deploy_blocks_frame (compile_materialize_vv c t v)) ==>
  deploy_blocks_frame (compile_log_save_arg cenv ty op es)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_log_save_arg))) >>
  simp[]
QED

Theorem deploy_blocks_frame_log_eval_all:
  (!c t e. deploy_blocks_frame (lower_value compile_expr c t e)) /\
  (!c t v. deploy_blocks_frame (compile_materialize_vv c t v)) ==>
  !es cenv. deploy_blocks_frame (compile_log_eval_all cenv es)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_log_eval_all))) >>
  simp[]
QED

Theorem deploy_blocks_frame_log_topic_ops:
  (!op b. deploy_blocks_frame (compile_encode_log_topic op b)) ==>
  !ops. deploy_blocks_frame (compile_log_topic_ops ops)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_log_topic_ops))) >>
  simp[]
QED

Theorem deploy_blocks_frame_log_store_data:
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) ==>
  !ops tys cenv buf off. deploy_blocks_frame (compile_log_store_data cenv ops tys buf off)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_log_store_data))) >>
  simp[]
QED

Theorem deploy_blocks_frame_tuple_load_all:
  (!op b. deploy_blocks_frame (compile_load_memory op b)) ==>
  !tys cenv op off. deploy_blocks_frame (compile_tuple_load_all cenv op tys off)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_tuple_load_all))) >>
  simp[]
QED

Theorem deploy_blocks_frame_store_at_loc:
  (!imm dst v. deploy_blocks_frame (compile_imm_store_word imm dst v)) ==>
  deploy_blocks_frame (compile_store_at_loc imm dst v loc)
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_store_at_loc_def] >>
  rename1 `SOME l` >> Cases_on `l` >> simp[compile_store_at_loc_def]
QED

Theorem deploy_blocks_frame_assign_value:
  (!a b n. deploy_blocks_frame (compile_copy_memory a b n)) /\
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) /\
  (!c b t v s. deploy_blocks_frame (compile_store_memory_typed c b t v s)) /\
  (!c v b t tr. deploy_blocks_frame (compile_store_slots c v b t tr)) /\
  (!v b n. deploy_blocks_frame (compile_memory_to_storage v b n)) /\
  (!v b n. deploy_blocks_frame (compile_memory_to_transient v b n)) /\
  (!i b v. deploy_blocks_frame (compile_imm_store_word i b v)) /\
  (!i v b. deploy_blocks_frame (compile_store_immutable_bytestring i v b)) /\
  (!i v b n k. deploy_blocks_frame (compile_imm_store_words i v b n k)) ==>
  deploy_blocks_frame (compile_assign_value cenv dst loc v prim sloc ty sty n)
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_assign_value_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_tuple_store_all:
  (!c bt. deploy_blocks_frame (compile_get_target_ptr compile_expr c bt)) /\
  (!i b v. deploy_blocks_frame (compile_imm_store_word i b v)) /\
  (!c b l v p sl t s n.
    deploy_blocks_frame (compile_assign_value c b l v p sl t s n)) ==>
  !tys targets vals cenv.
    deploy_blocks_frame (compile_tuple_store_all cenv tys targets vals)
Proof
  strip_tac >> Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def] >> rpt gen_tac >>
  rename1 `compile_tuple_store_all env (src::srctys) (tgt::tgts) (value::values)` >>
  Cases_on `tgt` >> simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[deploy_blocks_frame_store_at_loc]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_tuple_unpack:
  (!op b. deploy_blocks_frame (compile_load_memory op b)) /\
  (!c tys ts vs. deploy_blocks_frame (compile_tuple_store_all c tys ts vs)) ==>
  deploy_blocks_frame (compile_tuple_unpack cenv ty stage ts op)
Proof
  strip_tac >> simp[compile_tuple_unpack_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[deploy_blocks_frame_tuple_load_all]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_iter_elem_copy:
  (!v b n l. deploy_blocks_frame (compile_slot_to_memory v b n l)) /\
  (!ctor i l v. deploy_blocks_frame (compile_ptr_load ctor i l v)) /\
  (!ctor i v b n k. deploy_blocks_frame (compile_imm_copy_to_memory ctor i v b n k)) /\
  (!a b n. deploy_blocks_frame (compile_copy_memory a b n)) /\
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) ==>
  deploy_blocks_frame (compile_iter_elem_copy cenv a b n loc slot ty sty)
Proof
  strip_tac >> simp[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_custom_error_store_args:
  (!c t e. deploy_blocks_frame (compile_expr c t e)) /\
  (!c v. deploy_blocks_frame (unwrap_value c v)) /\
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) ==>
  !es tys cenv dst off.
    deploy_blocks_frame (compile_custom_error_store_args cenv es tys dst off)
Proof
  strip_tac >> Induct >> Cases_on `tys` >>
  simp[compile_custom_error_store_args_def, comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_revert_with_custom_error:
  (!c t e. deploy_blocks_frame (compile_expr c t e)) /\
  (!c v. deploy_blocks_frame (unwrap_value c v)) /\
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) /\
  (!a b i. deploy_blocks_frame (compile_abi_encode_to_buf a b i)) ==>
  deploy_blocks_frame (compile_revert_with_custom_error cenv err)
Proof
  strip_tac >> Cases_on `err` >>
  simp[compile_revert_with_custom_error_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[deploy_blocks_frame_custom_error_store_args]),
    match_mp_tac deploy_blocks_frame_bind >> conj_tac
      >- simp[deploy_blocks_frame_custom_error_store_args] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem deploy_blocks_frame_stmt_cond:
  (!n. deploy_blocks_frame (compile_fixed_region_with_id n)) /\
  (!c t e. deploy_blocks_frame (compile_expr c t e)) /\
  (!c t e. deploy_blocks_frame (lower_value compile_expr c t e)) /\
  (!c bt. deploy_blocks_frame (compile_get_target_ptr compile_expr c bt)) /\
  (!c v. deploy_blocks_frame (unwrap_value c v)) /\
  (!c b v. deploy_blocks_frame (compile_snapshot_vv c b v)) /\
  (!op a b t lo hi. deploy_blocks_frame (compile_binop op a b t lo hi)) /\
  (!c dst loc v p sl t s n.
    deploy_blocks_frame (compile_assign_value c dst loc v p sl t s n)) /\
  (!i b v loc. deploy_blocks_frame (compile_store_at_loc i b v loc)) /\
  (!c e. deploy_blocks_frame (compile_reason_message c e)) /\
  (!c v (t:type) n. deploy_blocks_frame (compile_revert_with_reason c v t n)) /\
  (!c es. deploy_blocks_frame (compile_log_eval_all c es)) /\
  (!ops. deploy_blocks_frame (compile_log_topic_ops ops)) /\
  (!c ops tys buf off. deploy_blocks_frame (compile_log_store_data c ops tys buf off)) /\
  (!a b i. deploy_blocks_frame (compile_abi_encode_to_buf a b i)) /\
  (!c. deploy_blocks_frame (compile_return_unlock c)) /\
  (!k t v. deploy_blocks_frame (compile_nonreentrant_unlock k t v)) /\
  (!c t s v rpc. deploy_blocks_frame (compile_internal_return_from_env c t s v rpc)) /\
  (!rv p r i n nr k t v.
    deploy_blocks_frame (compile_external_return rv p r i n nr k t v)) /\
  (!c b t v s. deploy_blocks_frame (compile_store_memory_typed c b t v s)) /\
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) /\
  (!c a b w n t s cap p loc.
    deploy_blocks_frame (compile_dynarray_append c a b w n t s cap p loc)) /\
  (!c ty stage ts op. deploy_blocks_frame (compile_tuple_unpack c ty stage ts op)) /\
  (!ctor i l v. deploy_blocks_frame (compile_ptr_load ctor i l v)) /\
  (!c a b n l slot t s.
    deploy_blocks_frame (compile_iter_elem_copy c a b n l slot t s)) ==>
  (!cenv lctx ty s. deploy_blocks_frame (compile_stmt cenv lctx ty s)) /\
  (!cenv lctx ty ss. deploy_blocks_frame (compile_stmts cenv lctx ty ss))
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_stmt_cond))) >>
  simp[block_is_terminated_def, deploy_blocks_frame_declare_local, deploy_blocks_frame_revert_with_custom_error]
QED
