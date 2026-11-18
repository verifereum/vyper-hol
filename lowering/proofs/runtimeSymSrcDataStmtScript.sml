Theory runtimeSymSrcDataStmt
Ancestors runtimeSymSrcDataCustomError runtimeSymSrcDataContext
  symbolicSourceCompilerStmtFrame
  runtimeSymSrcDataFrame stmtLowering compileEnv

(* Distribute the projection frame through control selection, keeping branch
   conditions opaque rather than duplicating compiler continuations. *)
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
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_log_save_arg))) >>
  simp[]
QED

Theorem runtime_data_frame_compile_log_eval_all:
  (!c t e. runtime_data_frame (lower_value compile_expr c t e)) /\
  (!c t v. runtime_data_frame (compile_materialize_vv c t v)) ==>
  !es cenv. runtime_data_frame (compile_log_eval_all cenv es)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_log_eval_all))) >>
  simp[]
QED

Theorem runtime_data_frame_compile_log_topic_ops:
  (!op b. runtime_data_frame (compile_encode_log_topic op b)) ==>
  !ops. runtime_data_frame (compile_log_topic_ops ops)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_log_topic_ops))) >>
  simp[]
QED

Theorem runtime_data_frame_compile_log_store_data:
  (!c v b t s. runtime_data_frame (compile_store_memory c v b t s)) ==>
  !ops tys cenv buf off.
    runtime_data_frame (compile_log_store_data cenv ops tys buf off)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_log_store_data))) >>
  simp[]
QED

Theorem runtime_data_frame_compile_tuple_load_all:
  (!op b. runtime_data_frame (compile_load_memory op b)) ==>
  !tys cenv op off. runtime_data_frame (compile_tuple_load_all cenv op tys off)
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_tuple_load_all))) >>
  simp[]
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
  (!c v b t tr. runtime_data_frame (compile_store_slots c v b t tr)) /\
  (!v b n. runtime_data_frame (compile_memory_to_storage v b n)) /\
  (!v b n. runtime_data_frame (compile_memory_to_transient v b n)) /\
  (!i b v. runtime_data_frame (compile_imm_store_word i b v)) /\
  (!i v b. runtime_data_frame (compile_store_immutable_bytestring i v b)) /\
  (!i v b n k. runtime_data_frame (compile_imm_store_words i v b n k)) ==>
  runtime_data_frame (compile_assign_value cenv dst loc v prim sloc ty sty n)
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_assign_value_def, comp_ignore_bind_def] >>
  rpt (FIRST [CHANGED_TAC (simp[]),
    irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac,
    BasicProvers.TOP_CASE_TAC])
QED

Theorem runtime_data_frame_compile_tuple_store_all:
  (!c bt. runtime_data_frame (compile_get_target_ptr compile_expr c bt)) /\
  (!i b v. runtime_data_frame (compile_imm_store_word i b v)) /\
  (!c b l v p sl t s n.
    runtime_data_frame (compile_assign_value c b l v p sl t s n)) ==>
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

Theorem runtime_data_frame_compile_stmt_conditional:
  (!c t e. runtime_data_frame (compile_expr c t e)) /\
  (!c t e. runtime_data_frame (lower_value compile_expr c t e)) /\
  (!c bt. runtime_data_frame (compile_get_target_ptr compile_expr c bt)) /\
  (!c v. runtime_data_frame (unwrap_value c v)) /\
  (!c b v. runtime_data_frame (compile_snapshot_vv c b v)) /\
  (!op a b t lo hi. runtime_data_frame (compile_binop op a b t lo hi)) /\
  (!c dst loc v p sl t s n.
    runtime_data_frame (compile_assign_value c dst loc v p sl t s n)) /\
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
  (!c a b w n t s cap p loc.
    runtime_data_frame (compile_dynarray_append c a b w n t s cap p loc)) /\
  (!c ty stage ts op. runtime_data_frame (compile_tuple_unpack c ty stage ts op)) /\
  (!ctor i l v. runtime_data_frame (compile_ptr_load ctor i l v)) /\
  (!c a b n l slot t s.
    runtime_data_frame (compile_iter_elem_copy c a b n l slot t s)) ==>
  (!cenv lctx ty s. runtime_data_frame (compile_stmt cenv lctx ty s)) /\
  (!cenv lctx ty ss. runtime_data_frame (compile_stmts cenv lctx ty ss))
Proof
  strip_tac >>
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_stmt_cond))) >>
  simp[block_is_terminated_def, runtime_data_frame_revert_with_custom_error]
QED
