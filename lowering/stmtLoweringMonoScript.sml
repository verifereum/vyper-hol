(*
 * compile_stmt only appends (#637)
 *
 * compile_stmt and compile_stmts only append code and hand out variables
 * and instruction ids forward (ci_mono), as compile_expr does
 * (exprLoweringProps' compile_expr_ci_mono).
 *
 * TOP-LEVEL:
 *   compile_stmt_ci_mono — compile_stmt and compile_stmts
 *   compile_stmt_cs_mono — the same as cs_mono, which stmt_frag_cons_env
 *                          and compile_if_stmt_frag ask
 *
 * Helper:
 *   ci_mono_compile_expr_sa, ci_mono_context_helpers,
 *   ci_mono_compile_dynarray_append, ci_mono_comp_get,
 *   ci_mono_compile_get_target_ptr, ci_mono_stmt_helpers,
 *   ci_mono_list_helpers, ci_mono_return_helpers — the helpers
 *                          compile_stmt calls
 *   ci_mono_cs_mono      — ci_mono from every start gives cs_mono
 *)

Theory stmtLoweringMono
Ancestors
  fragExec exprLoweringProps stmtLowering exprLowering context compileEnv
  abiEncoder emitHelper

(* ===== The helpers of compile_stmt ===== *)

(* Sequence ci_mono through binds, lets, conditionals and case splits,
   down to the operations named in rws.  A goal the operations close is
   closed before any case split, so the cases of an operation's arguments
   are never split. *)
fun ci_mono_chain_tac rws =
  let val close =
        FIRST (map MATCH_ACCEPT_TAC
                 (List.concat (map BODY_CONJUNCTS (ci_mono_comp_return :: rws))))
  in
    rpt gen_tac >>
    rpt (FIRST [MATCH_MP_TAC ci_mono_bind, MATCH_MP_TAC ci_mono_ignore_bind,
                close, FIRST_ASSUM MATCH_ACCEPT_TAC,
                IF_CASES_TAC, BasicProvers.TOP_CASE_TAC] >>
         rpt conj_tac >> rpt gen_tac >> PURE_REWRITE_TAC[LET_THM] >>
         BETA_TAC) >>
    simp (ci_mono_comp_return :: rws)
  end;

val ci_mono_grows_rws = [
  ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_fresh_var,
  ci_mono_fresh_label, ci_mono_new_block, ci_mono_compile_alloc_buffer,
  ci_mono_unwrap_value, ci_mono_compile_store_memory,
  ci_mono_compile_copy_memory, ci_mono_compile_word_copy_loop,
  ci_mono_compile_store_bytestring, ci_mono_compile_keccak256_key,
  ci_mono_compile_mapping_subscript, ci_mono_compile_array_subscript,
  ci_mono_compile_bytelike_literal, cj 1 ci_mono_typed_memory_family,
  cj 2 ci_mono_compile_abi_encode];

(* compile_expr, lower_value and compile_binop in ci_mono's form. *)
Theorem ci_mono_compile_expr_sa:
  (!cenv ty e sa. ci_mono sa (SND (compile_expr cenv ty e sa))) /\
  (!cenv ty e sa. ci_mono sa (SND (lower_value compile_expr cenv ty e sa))) /\
  (!op x y ty b el sa. ci_mono sa (SND (compile_binop op x y ty b el sa)))
Proof
  rpt conj_tac >> rpt gen_tac >| [
    Cases_on `compile_expr cenv ty e sa` >>
    drule (cj 1 compile_expr_grows),
    Cases_on `lower_value compile_expr cenv ty e sa` >>
    drule (cj 2 compile_expr_grows),
    Cases_on `compile_binop op x y ty b el sa` >> drule compile_binop_grows] >>
  simp[ci_mono_def]
QED

Theorem ci_mono_context_helpers:
  (!buf slot n sa. ci_mono sa (SND (compile_memory_to_storage buf slot n sa))) /\
  (!buf slot n sa.
     ci_mono sa (SND (compile_memory_to_transient buf slot n sa))) /\
  (!src dst n loc sa.
     ci_mono sa (SND (compile_slot_to_memory src dst n loc sa))) /\
  (!p b sa. ci_mono sa (SND (compile_load_memory p b sa))) /\
  (!v b sa. ci_mono sa (SND (compile_encode_log_topic v b sa))) /\
  (!k t v sa. ci_mono sa (SND (compile_nonreentrant_unlock k t v sa))) /\
  (!src dst ew ems t sa.
     ci_mono sa (SND (compile_dynarray_to_storage src dst ew ems t sa)))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       compile_slot_to_memory_def, compile_load_memory_def,
       compile_encode_log_topic_def, compile_nonreentrant_unlock_def,
       compile_dynarray_to_storage_def] >>
  ci_mono_chain_tac ci_mono_grows_rws
QED

Theorem ci_mono_compile_dynarray_append:
  !cenv b v ws es dt st cap p lo so sa.
    ci_mono sa
      (SND (compile_dynarray_append cenv b v ws es dt st cap p lo so sa))
Proof
  rpt gen_tac >> simp[compile_dynarray_append_def, LET_THM] >>
  (* name the store location, so the case split does not go over opcodes *)
  qmatch_goalsub_abbrev_tac `compile_word_copy_loop _ _ _ LocMemory dl F` >>
  ci_mono_chain_tac ci_mono_grows_rws
QED

Theorem ci_mono_comp_get:
  !sa. ci_mono sa (SND (comp_get sa))
Proof
  simp[comp_get_def, ci_mono_refl]
QED

val ci_mono_stmt_rws =
  ci_mono_grows_rws @
  [ci_mono_compile_expr_sa, ci_mono_context_helpers,
   ci_mono_compile_dynarray_append, ci_mono_comp_get,
   ci_mono_compile_ptr_load, ci_mono_compile_imm_store_word,
   ci_mono_compile_imm_store_words, ci_mono_compile_imm_copy_to_memory];

Theorem ci_mono_compile_get_target_ptr:
  !bt cenv sa. ci_mono sa (SND (compile_get_target_ptr cenv bt sa))
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >> simp[Once compile_get_target_ptr_def] >|
  [ci_mono_chain_tac ci_mono_stmt_rws, ci_mono_chain_tac ci_mono_stmt_rws,
   ci_mono_chain_tac ci_mono_stmt_rws, ci_mono_chain_tac ci_mono_stmt_rws]
QED

Theorem ci_mono_stmt_helpers:
  (!cenv d l v p sl dt st da m sa.
     ci_mono sa (SND (compile_assign_value cenv d l v p sl dt st da m sa))) /\
  (!imm d v l sa. ci_mono sa (SND (compile_store_at_loc imm d v l sa))) /\
  (!cenv e sa. ci_mono sa (SND (compile_reason_message cenv e sa))) /\
  (!cenv m t sz sa.
     ci_mono sa (SND (compile_revert_with_reason cenv m t sz sa))) /\
  (!s e r rb b sa.
     ci_mono sa (SND (compile_range_bound_checks s e r rb b sa))) /\
  (!cenv e i sz l a t et sa.
     ci_mono sa (SND (compile_iter_elem_copy cenv e i sz l a t et sa))) /\
  (!cenv id ty sa. ci_mono sa (SND (declare_local cenv id ty sa))) /\
  (!cenv id sa. ci_mono sa (SND (emit_local_alloca cenv id sa))) /\
  (!cenv s sa. ci_mono sa (SND (declare_stmt_local cenv s sa))) /\
  (!l sa. ci_mono sa (SND (emit_jmp_if_not_terminated l sa)))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (simp[compile_assign_value_def] >> Cases_on `l` >> simp[] >|
      [ci_mono_chain_tac ci_mono_stmt_rws, ci_mono_chain_tac ci_mono_stmt_rws,
       ci_mono_chain_tac ci_mono_stmt_rws, ci_mono_chain_tac ci_mono_stmt_rws,
       ci_mono_chain_tac ci_mono_stmt_rws])
  >- (Cases_on `l` >> TRY (rename1 `SOME loc` >> Cases_on `loc`) >>
      simp[compile_store_at_loc_def, ci_mono_emit_void,
           ci_mono_compile_imm_store_word])
  >- (Cases_on `e` >> simp[compile_reason_message_def, ci_mono_compile_expr_sa] >>
      rename1 `Literal ty lit` >> Cases_on `ty` >> Cases_on `lit` >>
      simp[compile_reason_message_def, ci_mono_compile_expr_sa] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[compile_reason_message_def, ci_mono_compile_expr_sa] >>
      ci_mono_chain_tac ci_mono_stmt_rws)
  >- (simp[compile_revert_with_reason_def] >>
      ci_mono_chain_tac ci_mono_stmt_rws)
  >- (simp[compile_range_bound_checks_def] >>
      ci_mono_chain_tac ci_mono_stmt_rws)
  >- (simp[compile_iter_elem_copy_def] >> ci_mono_chain_tac ci_mono_stmt_rws)
  >- (simp[declare_local_def] >> ci_mono_chain_tac ci_mono_stmt_rws)
  >- (simp[emit_local_alloca_def] >> ci_mono_chain_tac ci_mono_stmt_rws)
  >- (Cases_on `s` >> simp[declare_stmt_local_def, declare_local_def] >>
      ci_mono_chain_tac ci_mono_stmt_rws) >>
  simp[emit_jmp_if_not_terminated_def] >> ci_mono_chain_tac ci_mono_stmt_rws
QED

Theorem ci_mono_list_helpers:
  (!cenv es sa. ci_mono sa (SND (compile_log_eval_all cenv es sa))) /\
  (!xs sa. ci_mono sa (SND (compile_log_topic_ops xs sa))) /\
  (!cenv xs b off sa.
     ci_mono sa (SND (compile_log_store_data cenv xs b off sa))) /\
  (!cenv s tys off sa.
     ci_mono sa (SND (compile_tuple_load_all cenv s tys off sa))) /\
  (!cenv tys ts vs sa.
     ci_mono sa (SND (compile_tuple_store_all cenv tys ts vs sa))) /\
  (!cenv b tys off sa.
     ci_mono sa (SND (compile_load_tuple_elements cenv b tys off sa)))
Proof
  rpt conj_tac
  >- (gen_tac >> Induct >> simp[compile_log_eval_all_def] >>
      ci_mono_chain_tac ci_mono_stmt_rws)
  >- (Induct >> simp[compile_log_topic_ops_def] >>
      ci_mono_chain_tac ci_mono_stmt_rws)
  >- (gen_tac >> Induct >> simp[compile_log_store_data_def] >>
      ci_mono_chain_tac ci_mono_stmt_rws)
  >- (gen_tac >> gen_tac >> Induct >> simp[compile_tuple_load_all_def] >>
      ci_mono_chain_tac (ci_mono_context_helpers :: ci_mono_stmt_rws))
  >- (ho_match_mp_tac compile_tuple_store_all_ind >> rpt conj_tac >>
      rpt gen_tac >> TRY strip_tac >>
      simp[compile_tuple_store_all_def] >>
      ci_mono_chain_tac
        (ci_mono_compile_get_target_ptr :: ci_mono_stmt_helpers ::
         ci_mono_stmt_rws)) >>
  gen_tac >> gen_tac >> Induct >> simp[compile_load_tuple_elements_def] >>
  ci_mono_chain_tac ci_mono_stmt_rws
QED

Theorem ci_mono_return_helpers:
  (!cenv v pc n rt st ets rb sa.
     ci_mono sa (SND (compile_internal_return cenv v pc n rt st ets rb sa))) /\
  (!cenv ty st v pc sa.
     ci_mono sa (SND (compile_internal_return_from_env cenv ty st v pc sa))) /\
  (!v p r ei m n k t w sa.
     ci_mono sa (SND (compile_external_return v p r ei m n k t w sa))) /\
  (!cenv t m tgs s sa.
     ci_mono sa (SND (compile_tuple_unpack cenv t m tgs s sa)))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_internal_return_def, compile_internal_return_from_env_def,
       compile_external_return_def, compile_tuple_unpack_def] >>
  ci_mono_chain_tac
    (ci_mono_list_helpers :: ci_mono_stmt_helpers :: ci_mono_stmt_rws)
QED

(* ===== compile_stmt ===== *)

(* Return NONE's tuple let survives the first chain as an UNCURRY applied
   to cenv.ce_nonreentrant; projecting it lets the second chain finish. *)
val stmt_ci_tac =
  let val chain =
        ci_mono_chain_tac
          (ci_mono_return_helpers :: ci_mono_list_helpers ::
           ci_mono_stmt_helpers :: ci_mono_compile_get_target_ptr ::
           ci_mono_stmt_rws)
  in
    rpt gen_tac >> simp[Once compile_stmt_def] >> chain >>
    simp[pairTheory.ELIM_UNCURRY] >> chain
  end;

val loop_ci_tac = RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >> stmt_ci_tac;

val cons_ci_tac =
  qpat_x_assum `!cs cenv. _ ==> !sa. ci_mono _ (SND (compile_stmt _ _ _ _ _))`
    (qspec_then `ARB with cs_current_insts := []`
       (assume_tac o SIMP_RULE (srw_ss()) [block_is_terminated_def])) >>
  qpat_x_assum `!cs cenv. _ ==> !sa. ci_mono _ (SND (compile_stmts _ _ _ _ _))`
    (qspec_then `ARB with cs_current_insts := []`
       (assume_tac o SIMP_RULE (srw_ss()) [block_is_terminated_def])) >>
  stmt_ci_tac;

Theorem compile_stmt_ci_mono:
  (!cenv lctx ty s sa. ci_mono sa (SND (compile_stmt cenv lctx ty s sa))) /\
  (!cenv lctx ty ss sa. ci_mono sa (SND (compile_stmts cenv lctx ty ss sa)))
Proof
  (* One step per induction case: a single chain over all 27 cases runs
     past the step timeout.  The cons case's hypotheses assume some
     unterminated state; the For cases' bind the loop's derived names. *)
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY strip_tac >|
  [stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   loop_ci_tac,
   loop_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   stmt_ci_tac,
   cons_ci_tac]
QED

Theorem ci_mono_cs_mono:
  !m. (!sa. ci_mono sa (SND (m sa))) ==> cs_mono m
Proof
  rw[cs_mono_def] >> first_x_assum (qspec_then `sa` mp_tac) >>
  simp[ci_mono_def]
QED

Theorem compile_stmt_cs_mono:
  (!cenv lctx ty s. cs_mono (compile_stmt cenv lctx ty s)) /\
  (!cenv lctx ty ss. cs_mono (compile_stmts cenv lctx ty ss))
Proof
  rw[] >> irule ci_mono_cs_mono >> simp[compile_stmt_ci_mono]
QED
