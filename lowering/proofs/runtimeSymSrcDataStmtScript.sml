Theory runtimeSymSrcDataStmt
Ancestors
  runtimeSymSrcDataFrame stmtLowering compileEnv

(* Distribute the projection frame through control selection, keeping branch
   conditions opaque rather than duplicating compiler continuations. *)
Theorem runtime_data_frame_if[simp]:
  runtime_data_frame (if b then m else n) =
  (if b then runtime_data_frame m else runtime_data_frame n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem runtime_data_frame_option_case[local,simp]:
  runtime_data_frame (case x of NONE => m | SOME y => f y) =
  (case x of NONE => runtime_data_frame m | SOME y => runtime_data_frame (f y))
Proof
  Cases_on `x` >> simp[]
QED

Theorem runtime_data_frame_pair_case[local,simp]:
  runtime_data_frame ((\(x,y). f x y) p) =
  (\(x,y). runtime_data_frame (f x y)) p
Proof
  Cases_on `p` >> simp[]
QED

Theorem runtime_data_frame_var_location_case[local,simp]:
  runtime_data_frame (case l of MemLoc a b => f a b |
    StorageLoc s => g s | TransientLoc s => h s |
    ImmutableLoc s => i s | PtrVar a b => j a b) =
  (case l of MemLoc a b => runtime_data_frame (f a b) |
    StorageLoc s => runtime_data_frame (g s) |
    TransientLoc s => runtime_data_frame (h s) |
    ImmutableLoc s => runtime_data_frame (i s) |
    PtrVar a b => runtime_data_frame (j a b))
Proof
  Cases_on `l` >> simp[]
QED

Theorem runtime_data_frame_compile_load_tuple_elements[simp]:
  !tys cenv op off.
  runtime_data_frame (compile_load_tuple_elements cenv op tys off)
Proof
  Induct >> simp[compile_load_tuple_elements_def]
QED

Theorem runtime_data_frame_compile_range_bound_checks[simp]:
  runtime_data_frame (compile_range_bound_checks a b c d s)
Proof
  Cases_on `s` >> simp[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem runtime_data_frame_declare_local[simp]:
  runtime_data_frame (declare_local cenv id ty)
Proof
  simp[declare_local_def] >> IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_emit_local_alloca[simp]:
  runtime_data_frame (emit_local_alloca cenv id)
Proof
  simp[emit_local_alloca_def] >> rpt BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem runtime_data_frame_declare_stmt_local[simp]:
  runtime_data_frame (declare_stmt_local cenv s)
Proof
  Cases_on `s` >> simp[declare_stmt_local_def]
QED

Theorem runtime_data_frame_compile_mcopy_guard[simp]:
  runtime_data_frame m ==> runtime_data_frame (compile_mcopy_guard cenv m)
Proof
  simp[compile_mcopy_guard_def] >> IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_compile_return_unlock:
  (!k t v. runtime_data_frame (compile_nonreentrant_unlock k t v)) ==>
  runtime_data_frame (compile_return_unlock cenv)
Proof
  strip_tac >> simp[compile_return_unlock_def] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_compile_internal_return:
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) ==>
  runtime_data_frame (compile_internal_return cenv rv rpc n ty sty tys rb)
Proof
  strip_tac >> simp[compile_internal_return_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_external_return:
  (!k t v. runtime_data_frame (compile_nonreentrant_unlock k t v)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!a b i. runtime_data_frame (compile_abi_encode_to_buf a b i)) ==>
  runtime_data_frame (compile_external_return rv prim raw info maxsize nr k t v)
Proof
  strip_tac >> simp[compile_external_return_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_internal_return_from_env:
  (!c. runtime_data_frame (compile_return_unlock c)) /\
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) ==>
  runtime_data_frame (compile_internal_return_from_env cenv ty sty op rpc)
Proof
  strip_tac >> simp[compile_internal_return_from_env_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[runtime_data_frame_compile_internal_return]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_revert_with_reason:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!c v. runtime_data_frame (unwrap_value c v)) ==>
  runtime_data_frame (compile_revert_with_reason cenv msg ty n)
Proof
  strip_tac >> simp[compile_revert_with_reason_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem runtime_data_frame_compile_reason_message:
  (!c t e. runtime_data_frame (compile_expr c t e)) /\
  (!bs n. runtime_data_frame (compile_bytelike_literal bs n)) ==>
  runtime_data_frame (compile_reason_message cenv e)
Proof
  strip_tac >> Cases_on `e` >> simp[compile_reason_message_def] >>
  rename1 `Literal t l` >> Cases_on `t` >> simp[compile_reason_message_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[compile_reason_message_def] >>
  Cases_on `l` >> simp[compile_reason_message_def]
QED

Theorem runtime_data_frame_compile_log_save_arg:
  (!c t v. runtime_data_frame (compile_materialize_vv c t v)) ==>
  runtime_data_frame (compile_log_save_arg cenv ty op es)
Proof
  strip_tac >> simp[compile_log_save_arg_def] >> IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_compile_log_eval_all:
  (!c t e. runtime_data_frame (lower_value compile_expr c t e)) /\
  (!c t v. runtime_data_frame (compile_materialize_vv c t v)) ==>
  !es cenv. runtime_data_frame (compile_log_eval_all cenv es)
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac
       >- simp[runtime_data_frame_compile_log_save_arg] >> gen_tac) >> simp[]
QED

Theorem runtime_data_frame_compile_log_topic_ops:
  (!op b. runtime_data_frame (compile_encode_log_topic op b)) ==>
  !ops. runtime_data_frame (compile_log_topic_ops ops)
Proof
  strip_tac >> Induct >> simp[compile_log_topic_ops_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem runtime_data_frame_compile_log_store_data:
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) ==>
  !ops tys cenv buf off.
    runtime_data_frame (compile_log_store_data cenv ops tys buf off)
Proof
  strip_tac >> Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem runtime_data_frame_compile_tuple_load_all:
  (!op b. runtime_data_frame (compile_load_memory op b)) ==>
  !tys cenv op off. runtime_data_frame (compile_tuple_load_all cenv op tys off)
Proof
  strip_tac >> Induct >> simp[compile_tuple_load_all_def, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Theorem runtime_data_frame_compile_store_at_loc:
  (!imm dst v. runtime_data_frame (compile_imm_store_word imm dst v)) ==>
  runtime_data_frame (compile_store_at_loc imm dst v loc)
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_store_at_loc_def] >>
  rename1 `SOME l` >> Cases_on `l` >> simp[compile_store_at_loc_def]
QED

Theorem runtime_data_frame_compile_assign_value:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!a b n. runtime_data_frame (compile_copy_memory a b n)) /\
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) /\
  (!c b t v s. runtime_data_frame (compile_store_memory_typed c b t v s)) /\
  (!v b w n t. runtime_data_frame (compile_dynarray_to_storage v b w n t)) /\
  (!v b n. runtime_data_frame (compile_memory_to_storage v b n)) /\
  (!v b n. runtime_data_frame (compile_memory_to_transient v b n)) /\
  (!i b v. runtime_data_frame (compile_imm_store_word i b v)) /\
  (!i v b. runtime_data_frame (compile_store_immutable_bytestring i v b)) /\
  (!i v b n k. runtime_data_frame (compile_imm_store_words i v b n k)) ==>
  runtime_data_frame (compile_assign_value cenv dst loc v prim sloc ty sty di n)
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_assign_value_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_tuple_store_all:
  (!c bt. runtime_data_frame (compile_get_target_ptr compile_expr c bt)) /\
  (!i b v. runtime_data_frame (compile_imm_store_word i b v)) /\
  (!c b l v p sl t s di n.
    runtime_data_frame (compile_assign_value c b l v p sl t s di n)) ==>
  !tys targets vals cenv.
    runtime_data_frame (compile_tuple_store_all cenv tys targets vals)
Proof
  strip_tac >> Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def] >> rpt gen_tac >>
  rename1 `compile_tuple_store_all env (src::srctys) (tgt::tgts) (value::values)` >>
  Cases_on `tgt` >> simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[runtime_data_frame_compile_store_at_loc]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_tuple_unpack:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!op b. runtime_data_frame (compile_load_memory op b)) /\
  (!c tys ts vs. runtime_data_frame (compile_tuple_store_all c tys ts vs)) ==>
  runtime_data_frame (compile_tuple_unpack cenv ty stage ts op)
Proof
  strip_tac >> simp[compile_tuple_unpack_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[runtime_data_frame_compile_tuple_load_all]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_iter_elem_copy:
  (!v b n l. runtime_data_frame (compile_slot_to_memory v b n l)) /\
  (!ctor i l v. runtime_data_frame (compile_ptr_load ctor i l v)) /\
  (!ctor i v b n k. runtime_data_frame (compile_imm_copy_to_memory ctor i v b n k)) /\
  (!a b n. runtime_data_frame (compile_copy_memory a b n)) /\
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) ==>
  runtime_data_frame (compile_iter_elem_copy cenv a b n loc slot ty sty)
Proof
  strip_tac >> simp[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_annassign[local]:
  (!c t e. runtime_data_frame (compile_expr c t e)) /\
  (!c v. runtime_data_frame (unwrap_value c v)) /\
  (!c dst loc v p sl t s di n.
    runtime_data_frame (compile_assign_value c dst loc v p sl t s di n)) ==>
  runtime_data_frame (compile_stmt cenv lctx ty (AnnAssign id vtyp e))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  rename1 `SOME binding` >> Cases_on `binding` >> simp[]
QED

(* This conditional interface deliberately leaves expression-family actions
   opaque. Its uniform premises can be discharged by the expression publication. *)
Theorem runtime_data_frame_compile_stmt_conditional:
  (!c t e. runtime_data_frame (compile_expr c t e)) /\
  (!c t e. runtime_data_frame (lower_value compile_expr c t e)) /\
  (!c bt. runtime_data_frame (compile_get_target_ptr compile_expr c bt)) /\
  (!c v. runtime_data_frame (unwrap_value c v)) /\
  (!c b v. runtime_data_frame (compile_snapshot_vv c b v)) /\
  (!op a b t lo hi. runtime_data_frame (compile_binop op a b t lo hi)) /\
  (!c dst loc v p sl t s di n.
    runtime_data_frame (compile_assign_value c dst loc v p sl t s di n)) /\
  (!i b v loc. runtime_data_frame (compile_store_at_loc i b v loc)) /\
  (!c e. runtime_data_frame (compile_reason_message c e)) /\
  (!c v (t:type) n. runtime_data_frame (compile_revert_with_reason c v t n)) /\
  (!c es. runtime_data_frame (compile_log_eval_all c es)) /\
  (!ops. runtime_data_frame (compile_log_topic_ops ops)) /\
  (!c ops tys buf off. runtime_data_frame (compile_log_store_data c ops tys buf off)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!a b i. runtime_data_frame (compile_abi_encode_to_buf a b i)) /\
  (!c. runtime_data_frame (compile_return_unlock c)) /\
  (!k t v. runtime_data_frame (compile_nonreentrant_unlock k t v)) /\
  (!c t s v rpc. runtime_data_frame (compile_internal_return_from_env c t s v rpc)) /\
  (!rv p r i n nr k t v.
    runtime_data_frame (compile_external_return rv p r i n nr k t v)) /\
  (!c b t v s. runtime_data_frame (compile_store_memory_typed c b t v s)) /\
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) /\
  (!c a b w n t s cap p load store.
    runtime_data_frame (compile_dynarray_append c a b w n t s cap p load store)) /\
  (!c ty stage ts op. runtime_data_frame (compile_tuple_unpack c ty stage ts op)) /\
  (!ctor i l v. runtime_data_frame (compile_ptr_load ctor i l v)) /\
  (!c a b n l slot t s.
    runtime_data_frame (compile_iter_elem_copy c a b n l slot t s)) ==>
  (!cenv lctx ty s. runtime_data_frame (compile_stmt cenv lctx ty s)) /\
  (!cenv lctx ty ss. runtime_data_frame (compile_stmts cenv lctx ty ss))
Proof
  suspend "rest"
QED

Resume runtime_data_frame_compile_stmt_conditional[rest]:
  strip_tac >> ho_match_mp_tac compile_stmt_ind >> rpt strip_tac >>
  simp[runtime_data_frame_compile_annassign]
  >~ [`compile_stmt _ _ _ (Assign (BaseTarget _) _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- suspend "log"
  >~ [`compile_stmt _ _ _ (Return NONE)`] >- suspend "return_none"
  >~ [`compile_stmt _ _ _ (Return (SOME _))`] >- suspend "return_some"
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- suspend "if"
  >~ [`compile_stmt _ _ _ (For _ _ (Range _ _) _ _)`] >- suspend "range"
  >~ [`compile_stmt _ _ _ (For _ _ (Array _) _ _)`] >- suspend "iter" >>
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >>
  simp[] >> Cases_on `block_is_terminated x` >> simp[] >>
  qpat_x_assum `!cs cenv. _ ==> runtime_data_frame (compile_stmt _ _ _ _)`
    (qspec_then `x` assume_tac) >>
  qpat_x_assum `!cs cenv. _ ==> runtime_data_frame (compile_stmts _ _ _ _)`
    (qspec_then `x` assume_tac) >>
  gvs[] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED
Resume runtime_data_frame_compile_stmt_conditional[return_none]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- (Cases_on `cenv.ce_ctor_exit_label` >> simp[] >>
      pairarg_tac >> simp[] >>
      irule runtime_data_frame_bind >> simp[]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  Cases_on `cenv.ce_ctor_exit_label` >> simp[] >> pairarg_tac >> simp[] >>
  irule runtime_data_frame_bind >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[assign]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >> disj2_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[augassign]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[log]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >> rename1 `SOME info` >> PairCases_on `info` >> simp[] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  disj2_tac >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[if]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[return_some]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC >>
  Cases_on `cenv.ce_return_pc` >> simp[]
  >- suspend "external_return" >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  suspend "external_return"
QED

Resume runtime_data_frame_compile_stmt_conditional[external_return]:
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[iter]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  qpat_x_assum `!arr_ty isdyn count elem c ex inc. _` (assume_tac o SRULE []) >>
  irule runtime_data_frame_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Resume runtime_data_frame_compile_stmt_conditional[range]:
  simp[Once compile_stmt_def, comp_ignore_bind_def] >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  qpat_x_assum `!sgn c ex inc. _` (assume_tac o SRULE []) >>
  irule runtime_data_frame_bind >> reverse conj_tac
  >- (POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `start_e` >> simp[] >>
      Cases_on `end_e` >> simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  gen_tac >> BETA_TAC >>
  irule runtime_data_frame_bind >> reverse conj_tac
  >- (POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `start_e` >> simp[] >>
      Cases_on `end_e` >> simp[] >> rpt (BasicProvers.TOP_CASE_TAC >> simp[])) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[] >>
  irule runtime_data_frame_bind >> reverse conj_tac
  >- (BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  gen_tac >> BETA_TAC >>
  rpt (BETA_TAC >> irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac) >> simp[]
QED

Finalise runtime_data_frame_compile_stmt_conditional
