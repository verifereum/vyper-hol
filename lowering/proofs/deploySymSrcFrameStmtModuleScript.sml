Theory deploySymSrcFrameStmtModule
Ancestors
  deploySymSrcBlockFrame deploySymSrcFrameExprHelpers
  stmtLowering moduleLowering compileEnv

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

Theorem deploy_blocks_frame_if[simp]:
  deploy_blocks_frame (if b then m else n) =
  (if b then deploy_blocks_frame m else deploy_blocks_frame n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem deploy_blocks_frame_option_case[local,simp]:
  deploy_blocks_frame (case x of NONE => m | SOME y => f y) =
  (case x of NONE => deploy_blocks_frame m | SOME y => deploy_blocks_frame (f y))
Proof
  Cases_on `x` >> simp[]
QED

Theorem deploy_blocks_frame_pair_case[local,simp]:
  deploy_blocks_frame ((\(x,y). f x y) p) =
  (\(x,y). deploy_blocks_frame (f x y)) p
Proof
  Cases_on `p` >> simp[]
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
  simp[compile_mcopy_guard_def] >> IF_CASES_TAC >> simp[]
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
  strip_tac >> simp[compile_revert_with_reason_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem deploy_blocks_frame_reason_message:
  (!c t e. deploy_blocks_frame (compile_expr c t e)) ==>
  deploy_blocks_frame (compile_reason_message cenv e)
Proof
  strip_tac >> Cases_on `e` >> simp[compile_reason_message_def] >>
  rename1 `Literal t l` >> Cases_on `t` >> simp[compile_reason_message_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[compile_reason_message_def] >>
  Cases_on `l` >> simp[compile_reason_message_def]
QED

Theorem deploy_blocks_frame_log_save_arg:
  (!c t v. deploy_blocks_frame (compile_materialize_vv c t v)) ==>
  deploy_blocks_frame (compile_log_save_arg cenv ty op es)
Proof
  strip_tac >> simp[compile_log_save_arg_def] >> IF_CASES_TAC >> simp[]
QED

Theorem deploy_blocks_frame_log_eval_all:
  (!c t e. deploy_blocks_frame (lower_value compile_expr c t e)) /\
  (!c t v. deploy_blocks_frame (compile_materialize_vv c t v)) ==>
  !es cenv. deploy_blocks_frame (compile_log_eval_all cenv es)
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac
       >- simp[deploy_blocks_frame_log_save_arg] >> gen_tac) >> simp[]
QED

Theorem deploy_blocks_frame_log_topic_ops:
  (!op b. deploy_blocks_frame (compile_encode_log_topic op b)) ==>
  !ops. deploy_blocks_frame (compile_log_topic_ops ops)
Proof
  strip_tac >> Induct >> simp[compile_log_topic_ops_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem deploy_blocks_frame_log_store_data:
  (!c v b t s. deploy_blocks_frame (compile_store_memory c v b t s)) ==>
  !ops tys cenv buf off. deploy_blocks_frame (compile_log_store_data cenv ops tys buf off)
Proof
  strip_tac >> Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, comp_ignore_bind_def] >> rpt gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem deploy_blocks_frame_tuple_load_all:
  (!op b. deploy_blocks_frame (compile_load_memory op b)) ==>
  !tys cenv op off. deploy_blocks_frame (compile_tuple_load_all cenv op tys off)
Proof
  strip_tac >> Induct >> simp[compile_tuple_load_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
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

Theorem deploy_blocks_frame_annassign[local]:
  (!c t e. deploy_blocks_frame (compile_expr c t e)) /\
  (!c v. deploy_blocks_frame (unwrap_value c v)) /\
  (!c dst loc v p sl t s n.
    deploy_blocks_frame (compile_assign_value c dst loc v p sl t s n)) ==>
  deploy_blocks_frame (compile_stmt cenv lctx ty (AnnAssign id vtyp e))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  rename1 `SOME binding` >> Cases_on `binding` >> simp[]
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
  (!c a b w n t s cap p load store.
    deploy_blocks_frame (compile_dynarray_append c a b w n t s cap p load store)) /\
  (!c ty stage ts op. deploy_blocks_frame (compile_tuple_unpack c ty stage ts op)) /\
  (!ctor i l v. deploy_blocks_frame (compile_ptr_load ctor i l v)) /\
  (!c a b n l slot t s.
    deploy_blocks_frame (compile_iter_elem_copy c a b n l slot t s)) ==>
  (!cenv lctx ty s. deploy_blocks_frame (compile_stmt cenv lctx ty s)) /\
  (!cenv lctx ty ss. deploy_blocks_frame (compile_stmts cenv lctx ty ss))
Proof
  strip_tac >>
  `!c err. deploy_blocks_frame (compile_revert_with_custom_error c err)` by
    (rpt gen_tac >> irule deploy_blocks_frame_revert_with_custom_error >> simp[]) >>
  `!c id t. deploy_blocks_frame (declare_local c id t)` by
    (simp[deploy_blocks_frame_declare_local]) >>
  ho_match_mp_tac compile_stmt_ind >> rpt strip_tac >>
  simp[deploy_blocks_frame_annassign]
  >~ [`compile_stmt _ _ _ (Assign (BaseTarget _) _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- suspend "log"
  >~ [`compile_stmt _ _ _ (Return NONE)`] >- suspend "return_none"
  >~ [`compile_stmt _ _ _ (Return (SOME _))`] >- suspend "return_some"
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- suspend "if"
  >~ [`compile_stmt _ _ _ (For _ _ (Range _ _) _ _)`] >- suspend "range"
  >~ [`compile_stmt _ _ _ (For _ _ (Array _) _ _)`] >- suspend "iter" >>
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  simp[] >> suspend "cons"
QED

Resume deploy_blocks_frame_stmt_cond[assign]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >> disj2_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[augassign]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[log]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >> rename1 `SOME info` >> PairCases_on `info` >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  disj2_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[return_none]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- (Cases_on `cenv.ce_ctor_exit_label` >> simp[] >>
      pairarg_tac >> simp[] >>
      match_mp_tac deploy_blocks_frame_bind >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  Cases_on `cenv.ce_ctor_exit_label` >> simp[] >> pairarg_tac >> simp[] >>
  match_mp_tac deploy_blocks_frame_bind >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[return_some]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- suspend "external_return" >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  suspend "external_return"
QED

Resume deploy_blocks_frame_stmt_cond[external_return]:
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[if]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  simp[] >> suspend "if_get"
QED

Resume deploy_blocks_frame_stmt_cond[iter]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  qpat_x_assum `!arr_ty isdyn count elem c ex inc. _` (assume_tac o SRULE []) >>
  irule deploy_blocks_frame_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[range]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  qpat_x_assum `!sgn c ex inc. _` (assume_tac o SRULE []) >>
  irule deploy_blocks_frame_bind >> reverse conj_tac
  >- (POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `start_e` >> simp[] >>
      Cases_on `end_e` >> simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  gen_tac >> BETA_TAC >>
  irule deploy_blocks_frame_bind >> reverse conj_tac
  >- (POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `start_e` >> simp[] >>
      Cases_on `end_e` >> simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[] >>
  irule deploy_blocks_frame_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume deploy_blocks_frame_stmt_cond[cons]:
  qpat_x_assum `!cs cenv. _ ==> deploy_blocks_frame (compile_stmt _ _ _ _)`
    (qspec_then `ARB with cs_current_insts := []`
       (assume_tac o SRULE [block_is_terminated_def])) >>
  qpat_x_assum `!cs cenv. _ ==> deploy_blocks_frame (compile_stmts _ _ _ _)`
    (qspec_then `ARB with cs_current_insts := []`
       (assume_tac o SRULE [block_is_terminated_def])) >>
  ho_match_mp_tac deploy_blocks_frame_get_terminated >>
  gen_tac >> Cases_on `b` >> simp[deploy_blocks_frame_declare_stmt_local]
QED
Resume deploy_blocks_frame_stmt_cond[if_get]:
  ho_match_mp_tac deploy_blocks_frame_get_terminated >> gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  BETA_TAC >> ho_match_mp_tac deploy_blocks_frame_get_terminated >> gen_tac >>
  rpt (BETA_TAC >> match_mp_tac deploy_blocks_frame_bind >> conj_tac >- simp[] >> gen_tac) >>
  simp[]
QED
Finalise deploy_blocks_frame_stmt_cond
