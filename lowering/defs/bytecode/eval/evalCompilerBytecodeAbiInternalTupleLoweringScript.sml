(* Checked source-lowering staging for the internal_tuple_call fixture. *)

Theory evalCompilerBytecodeAbiInternalTupleLowering
Ancestors evalCompilerSubsetAbiInternalCalls compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib pairLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

val internal_tuple_call_policy_eval = save_thm
  ("internal_tuple_call_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
val internal_tuple_call_rpolicy = optionSyntax.dest_some
  (rhs (concl internal_tuple_call_policy_eval))
val internal_tuple_call_tops = ``task090_internal_tuple_call_program``
val internal_tuple_call_type_env_eval = save_thm
  ("internal_tuple_call_type_env_eval",
   EVAL ``type_env ^internal_tuple_call_tops``)
val internal_tuple_call_type_env = rhs (concl internal_tuple_call_type_env_eval)
val internal_tuple_call_nkeys_eval = save_thm
  ("internal_tuple_call_nkeys_eval",
   EVAL ``assign_nkeys ^internal_tuple_call_tops 0``)
val internal_tuple_call_nkeys = rhs (concl internal_tuple_call_nkeys_eval)
val internal_tuple_call_classify_eval = save_thm
  ("internal_tuple_call_classify_eval",
   EVAL ``classify_functions ^internal_tuple_call_tops``)
val internal_tuple_call_classified = rhs (concl internal_tuple_call_classify_eval)
val internal_tuple_call_external_sources =
  #1 (pairSyntax.dest_pair internal_tuple_call_classified)
val internal_tuple_call_classified_tail1 =
  #2 (pairSyntax.dest_pair internal_tuple_call_classified)
val internal_tuple_call_internal_sources =
  #1 (pairSyntax.dest_pair internal_tuple_call_classified_tail1)
val internal_tuple_call_classified_tail2 =
  #2 (pairSyntax.dest_pair internal_tuple_call_classified_tail1)
val internal_tuple_call_fallback_source =
  #1 (pairSyntax.dest_pair internal_tuple_call_classified_tail2)
val internal_tuple_call_selectors_eval = save_thm
  ("internal_tuple_call_selectors_eval",
   EVAL ``build_selectors ^internal_tuple_call_type_env
           ^internal_tuple_call_external_sources``)
val internal_tuple_call_selectors = rhs (concl internal_tuple_call_selectors_eval)
val internal_tuple_call_external_fns_eval = save_thm
  ("internal_tuple_call_external_fns_eval",
   EVAL
     ``MAP (set_external_package_target
              (^internal_tuple_call_rpolicy).rpol_target o
            package_external_fn ^internal_tuple_call_tops F
              ^internal_tuple_call_nkeys)
         ^internal_tuple_call_external_sources``)
val internal_tuple_call_external_fns =
  rhs (concl internal_tuple_call_external_fns_eval)
val internal_tuple_call_internal_fns_eval = save_thm
  ("internal_tuple_call_internal_fns_eval",
   EVAL
     ``MAP (set_internal_package_target
              (^internal_tuple_call_rpolicy).rpol_target o
            package_internal_fn ^internal_tuple_call_tops F
              ^internal_tuple_call_nkeys F 0)
         ^internal_tuple_call_internal_sources``)
val internal_tuple_call_internal_fns =
  rhs (concl internal_tuple_call_internal_fns_eval)
val internal_tuple_call_fallback_fn_eval = save_thm
  ("internal_tuple_call_fallback_fn_eval",
   EVAL
     ``set_fallback_package_target
         (^internal_tuple_call_rpolicy).rpol_target
         (package_fallback_fn ^internal_tuple_call_tops F
           ^internal_tuple_call_nkeys ^internal_tuple_call_fallback_source)``)
val internal_tuple_call_fallback_fn =
  rhs (concl internal_tuple_call_fallback_fn_eval)
val internal_tuple_call_entry_info_eval = save_thm
  ("internal_tuple_call_entry_info_eval",
   EVAL ``build_dense_entry_info ^internal_tuple_call_selectors
           ^internal_tuple_call_external_fns``)
val internal_tuple_call_entry_info = rhs (concl internal_tuple_call_entry_info_eval)

val internal_tuple_call_state0_eval = save_thm
  ("internal_tuple_call_state0_eval",
   EVAL ``initial_compile_state "__entry"``)
val internal_tuple_call_state0 = rhs (concl internal_tuple_call_state0_eval)
val internal_tuple_call_fallback_label_eval = save_thm
  ("internal_tuple_call_fallback_label_eval",
   EVAL ``fresh_label "fallback" ^internal_tuple_call_state0``)
val internal_tuple_call_fallback_label_pair =
  rhs (concl internal_tuple_call_fallback_label_eval)
val internal_tuple_call_fallback_label =
  #1 (pairSyntax.dest_pair internal_tuple_call_fallback_label_pair)
val internal_tuple_call_state1 =
  #2 (pairSyntax.dest_pair internal_tuple_call_fallback_label_pair)
val internal_tuple_call_linear_selectors_eval = save_thm
  ("internal_tuple_call_linear_selectors_eval",
   EVAL ``MAP (λ(sel,lbl,_). (sel,lbl)) ^internal_tuple_call_selectors``)
val internal_tuple_call_linear_selectors =
  rhs (concl internal_tuple_call_linear_selectors_eval)
val internal_tuple_call_dispatch_eval = save_thm
  ("internal_tuple_call_dispatch_eval",
   EVAL ``compile_selector_dispatch_linear
           ^internal_tuple_call_linear_selectors
           ^internal_tuple_call_fallback_label ^internal_tuple_call_state1``)
val internal_tuple_call_dispatch_pair = rhs (concl internal_tuple_call_dispatch_eval)
val internal_tuple_call_state2 =
  #2 (pairSyntax.dest_pair internal_tuple_call_dispatch_pair)
val internal_tuple_call_external_bodies_eval = save_thm
  ("internal_tuple_call_external_bodies_eval",
   EVAL ``compile_external_fn_bodies ^internal_tuple_call_external_fns
           ^internal_tuple_call_state2``)
val internal_tuple_call_external_bodies_pair =
  rhs (concl internal_tuple_call_external_bodies_eval)
val internal_tuple_call_state3 =
  #2 (pairSyntax.dest_pair internal_tuple_call_external_bodies_pair)
val internal_tuple_call_fallback_block_eval = save_thm
  ("internal_tuple_call_fallback_block_eval",
   EVAL ``new_block ^internal_tuple_call_fallback_label
           ^internal_tuple_call_state3``)
val internal_tuple_call_fallback_block_pair =
  rhs (concl internal_tuple_call_fallback_block_eval)
val internal_tuple_call_state4 =
  #2 (pairSyntax.dest_pair internal_tuple_call_fallback_block_pair)
val internal_tuple_call_fallback_revert_eval = save_thm
  ("internal_tuple_call_fallback_revert_eval",
   EVAL ``emit_inst REVERT [Lit 0w; Lit 0w] []
           ^internal_tuple_call_state4``)
val internal_tuple_call_fallback_revert_pair =
  rhs (concl internal_tuple_call_fallback_revert_eval)
val internal_tuple_call_state5 =
  #2 (pairSyntax.dest_pair internal_tuple_call_fallback_revert_pair)
val (internal_tuple_call_internal_fn_terms, _) =
  listSyntax.dest_list internal_tuple_call_internal_fns
val internal_tuple_call_internal_fn = hd internal_tuple_call_internal_fn_terms
fun internal_tuple_call_dest_tuple tm =
  case total pairSyntax.dest_pair tm of
    SOME (x,xs) => x :: internal_tuple_call_dest_tuple xs
  | NONE => [tm]
val [internal_tuple_call_fn_lbl, internal_tuple_call_cenv,
     internal_tuple_call_params, internal_tuple_call_has_ret_buf,
     internal_tuple_call_is_nr, internal_tuple_call_nkey,
     internal_tuple_call_use_trans, internal_tuple_call_is_view,
     internal_tuple_call_is_ctor, internal_tuple_call_imm_len,
     internal_tuple_call_body, internal_tuple_call_ret_type] =
  internal_tuple_call_dest_tuple internal_tuple_call_internal_fn
val internal_tuple_call_internal_block_eval = save_thm
  ("internal_tuple_call_internal_block_eval",
   EVAL ``new_block ^internal_tuple_call_fn_lbl ^internal_tuple_call_state5``)
val internal_tuple_call_internal_block_pair =
  rhs (concl internal_tuple_call_internal_block_eval)
val internal_tuple_call_state6 =
  #2 (pairSyntax.dest_pair internal_tuple_call_internal_block_pair)
val internal_tuple_call_return_buf_eval = save_thm
  ("internal_tuple_call_return_buf_eval",
   EVAL
     ``(if ^internal_tuple_call_has_ret_buf then
          do param_op <- emit_op PARAM [Lit 0w];
             return (SOME param_op)
          od
        else return NONE) ^internal_tuple_call_state6``)
val internal_tuple_call_return_buf_pair =
  rhs (concl internal_tuple_call_return_buf_eval)
val internal_tuple_call_return_buf =
  #1 (pairSyntax.dest_pair internal_tuple_call_return_buf_pair)
val internal_tuple_call_state7 =
  #2 (pairSyntax.dest_pair internal_tuple_call_return_buf_pair)
val internal_tuple_call_param_idx_eval = save_thm
  ("internal_tuple_call_param_idx_eval",
   EVAL ``if ^internal_tuple_call_has_ret_buf then 1 else 0``)
val internal_tuple_call_param_idx = rhs (concl internal_tuple_call_param_idx_eval)
val internal_tuple_call_param_decls_eval = save_thm
  ("internal_tuple_call_param_decls_eval",
   EVAL ``compile_internal_param_decls ^internal_tuple_call_params
           ^internal_tuple_call_param_idx ^internal_tuple_call_state7``)
val internal_tuple_call_param_decls_pair =
  rhs (concl internal_tuple_call_param_decls_eval)
val internal_tuple_call_params_result =
  #1 (pairSyntax.dest_pair internal_tuple_call_param_decls_pair)
val internal_tuple_call_state8 =
  #2 (pairSyntax.dest_pair internal_tuple_call_param_decls_pair)
val internal_tuple_call_captured_params =
  #1 (pairSyntax.dest_pair internal_tuple_call_params_result)
val internal_tuple_call_next_idx =
  #2 (pairSyntax.dest_pair internal_tuple_call_params_result)
val internal_tuple_call_retpc_eval = save_thm
  ("internal_tuple_call_retpc_eval",
   EVAL ``emit_op RETPC_PARAM [Lit (n2w ^internal_tuple_call_next_idx)]
           ^internal_tuple_call_state8``)
val internal_tuple_call_retpc_pair = rhs (concl internal_tuple_call_retpc_eval)
val internal_tuple_call_retpc =
  #1 (pairSyntax.dest_pair internal_tuple_call_retpc_pair)
val internal_tuple_call_state9 =
  #2 (pairSyntax.dest_pair internal_tuple_call_retpc_pair)
val internal_tuple_call_cenv1_eval = save_thm
  ("internal_tuple_call_cenv1_eval",
   EVAL
     ``^internal_tuple_call_cenv with ce_vars updated_by (λvars.
          let vars1 = case ^internal_tuple_call_return_buf of
                SOME param_op =>
                  (case FLOOKUP vars "__return_buf__" of
                     SOME (MemLoc _ sz) =>
                       vars |+ ("__return_buf__", PtrVar param_op sz)
                   | _ => vars)
              | NONE => vars in
          vars1 |+ ("__return_pc__", PtrVar ^internal_tuple_call_retpc 0))``)
val internal_tuple_call_cenv1 = rhs (concl internal_tuple_call_cenv1_eval)
val internal_tuple_call_materialize_eval = save_thm
  ("internal_tuple_call_materialize_eval",
   EVAL ``materialize_internal_params ^internal_tuple_call_cenv1
           ^internal_tuple_call_captured_params ^internal_tuple_call_state9``)
val internal_tuple_call_materialize_pair =
  rhs (concl internal_tuple_call_materialize_eval)
val internal_tuple_call_cenv2 =
  #1 (pairSyntax.dest_pair internal_tuple_call_materialize_pair)
val internal_tuple_call_state10 =
  #2 (pairSyntax.dest_pair internal_tuple_call_materialize_pair)
val internal_tuple_call_ret_alloc_eval = save_thm
  ("internal_tuple_call_ret_alloc_eval",
   EVAL
     ``(case ^internal_tuple_call_ret_type of
          SOME ret_ty =>
            if (^internal_tuple_call_cenv).ce_returns_count > 0 then
              do compile_alloc_buffer
                   (type_memory_bytes ^internal_tuple_call_cenv ret_ty);
                 return ()
              od
            else return ()
        | NONE => return ()) ^internal_tuple_call_state10``)
val internal_tuple_call_ret_alloc_pair =
  rhs (concl internal_tuple_call_ret_alloc_eval)
val internal_tuple_call_state11 =
  #2 (pairSyntax.dest_pair internal_tuple_call_ret_alloc_pair)
val internal_tuple_call_forced_alloc_eval = save_thm
  ("internal_tuple_call_forced_alloc_eval",
   EVAL
     ``(if ^internal_tuple_call_is_ctor ∧ ^internal_tuple_call_imm_len > 0 then
          let touch_offset = if ^internal_tuple_call_imm_len > 32 then
                               ^internal_tuple_call_imm_len - 32
                             else 0 in
          do alloc_result <-
               compile_alloc_buffer_with_id ^internal_tuple_call_imm_len;
             emit_op MLOAD [Lit (n2w touch_offset)];
             return (SOME (FST alloc_result))
          od
        else return NONE) ^internal_tuple_call_state11``)
val internal_tuple_call_forced_alloc_pair =
  rhs (concl internal_tuple_call_forced_alloc_eval)
val internal_tuple_call_forced_id =
  #1 (pairSyntax.dest_pair internal_tuple_call_forced_alloc_pair)
val internal_tuple_call_state12 =
  #2 (pairSyntax.dest_pair internal_tuple_call_forced_alloc_pair)
val internal_tuple_call_lock_eval = save_thm
  ("internal_tuple_call_lock_eval",
   EVAL
     ``(if ^internal_tuple_call_is_nr then
          compile_nonreentrant_lock ^internal_tuple_call_nkey
            ^internal_tuple_call_use_trans ^internal_tuple_call_is_view
        else return ()) ^internal_tuple_call_state12``)
val internal_tuple_call_lock_pair = rhs (concl internal_tuple_call_lock_eval)
val internal_tuple_call_state13 =
  #2 (pairSyntax.dest_pair internal_tuple_call_lock_pair)
val internal_tuple_call_body_ret_ty_eval = save_thm
  ("internal_tuple_call_body_ret_ty_eval",
   EVAL ``case ^internal_tuple_call_ret_type of
           SOME t => t
         | NONE => BaseT BoolT``)
val internal_tuple_call_body_ret_ty =
  rhs (concl internal_tuple_call_body_ret_ty_eval)
val internal_tuple_call_return_expr_eval = save_thm
  ("internal_tuple_call_return_expr_eval",
   EVAL ``case ^internal_tuple_call_body of
           [Return (SOME e)] => SOME e
         | _ => NONE``)
val internal_tuple_call_return_expr = optionSyntax.dest_some
  (rhs (concl internal_tuple_call_return_expr_eval))
val internal_tuple_call_return_value_eval = save_thm
  ("internal_tuple_call_return_value_eval",
   EVAL ``lower_value compile_expr ^internal_tuple_call_cenv2
           ^internal_tuple_call_body_ret_ty
           ^internal_tuple_call_return_expr ^internal_tuple_call_state13``)
val internal_tuple_call_return_value_pair =
  rhs (concl internal_tuple_call_return_value_eval)
val internal_tuple_call_return_value =
  #1 (pairSyntax.dest_pair internal_tuple_call_return_value_pair)
val internal_tuple_call_state14 =
  #2 (pairSyntax.dest_pair internal_tuple_call_return_value_pair)
val internal_tuple_call_rpc_lookup_eval = save_thm
  ("internal_tuple_call_rpc_lookup_eval",
   EVAL ``FLOOKUP (^internal_tuple_call_cenv2).ce_vars "__return_pc__"``)
val internal_tuple_call_rpc_lookup = optionSyntax.dest_some
  (rhs (concl internal_tuple_call_rpc_lookup_eval))
val internal_tuple_call_rpc =
  #2 (dest_comb (#1 (dest_comb internal_tuple_call_rpc_lookup)))
val internal_tuple_call_ret_buf_eval = save_thm
  ("internal_tuple_call_ret_buf_eval",
   EVAL
     ``(case FLOOKUP (^internal_tuple_call_cenv2).ce_vars "__return_buf__" of
          SOME (MemLoc rbuf_off _) =>
            do buf_ptr <- emit_op MLOAD [Lit (n2w rbuf_off)];
               return (SOME buf_ptr)
            od
        | SOME (PtrVar buf_ptr _) => return (SOME buf_ptr)
        | _ => return NONE) ^internal_tuple_call_state14``)
val internal_tuple_call_ret_buf_pair = rhs (concl internal_tuple_call_ret_buf_eval)
val internal_tuple_call_ret_buf =
  #1 (pairSyntax.dest_pair internal_tuple_call_ret_buf_pair)
val internal_tuple_call_state15 =
  #2 (pairSyntax.dest_pair internal_tuple_call_ret_buf_pair)
val internal_tuple_call_elem_types_eval = save_thm
  ("internal_tuple_call_elem_types_eval",
   EVAL
     ``case ^internal_tuple_call_body_ret_ty of
         TupleT tys => tys
       | StructT nsid =>
           MAP (FST o SND)
             (get_struct_fields (^internal_tuple_call_cenv2).ce_struct_fields
               (nsid_to_string nsid))
       | _ => []``)
val internal_tuple_call_elem_types = rhs (concl internal_tuple_call_elem_types_eval)
val internal_tuple_call_returns_count_eval = save_thm
  ("internal_tuple_call_returns_count_eval",
   EVAL ``(^internal_tuple_call_cenv2).ce_returns_count``)
val internal_tuple_call_is_dynamic_eval = save_thm
  ("internal_tuple_call_is_dynamic_eval",
   EVAL ``is_abi_dynamic (^internal_tuple_call_cenv2).ce_struct_fields
           ^internal_tuple_call_body_ret_ty``)
val internal_tuple_call_return_shape_eval = save_thm
  ("internal_tuple_call_return_shape_eval",
   EVAL ``(^internal_tuple_call_cenv2).ce_returns_count > 0``)
val internal_tuple_call_ret_buf_operand =
  optionSyntax.dest_some internal_tuple_call_ret_buf

Definition internal_tuple_call_copy_field_def:
  internal_tuple_call_copy_field cenv dst src dst_ty src_ty dst_off src_off =
    do dst_ptr <- compile_with_byte_offset dst dst_off;
       src_ptr <- compile_with_byte_offset src src_off;
       compile_store_memory_typed cenv dst_ptr dst_ty src_ptr src_ty
    od
End

Theorem internal_tuple_call_copy_field_word:
  is_word_type dst_ty ⇒
  internal_tuple_call_copy_field cenv dst src dst_ty src_ty dst_off src_off =
    do dst_ptr <- compile_with_byte_offset dst dst_off;
       src_ptr <- compile_with_byte_offset src src_off;
       val_op <- emit_op MLOAD [src_ptr];
       emit_void MSTORE [dst_ptr; val_op]
    od
Proof
  simp[internal_tuple_call_copy_field_def,
       Once contextTheory.compile_store_memory_typed_def]
QED

Theorem compile_typed_copy_fields_cons_as_field:
  compile_typed_copy_fields cenv dst src (dst_ty::dst_rest)
      (src_ty::src_rest) dst_off src_off =
    do internal_tuple_call_copy_field cenv dst src dst_ty src_ty
         dst_off src_off;
       compile_typed_copy_fields cenv dst src dst_rest src_rest
         (dst_off + type_memory_bytes cenv dst_ty)
         (src_off + type_memory_bytes cenv src_ty)
    od
Proof
  simp[Once contextTheory.compile_store_memory_typed_def,
       internal_tuple_call_copy_field_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       FUN_EQ_THM, pairTheory.FORALL_PROD, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

val (internal_tuple_call_elem_type_terms, _) =
  listSyntax.dest_list internal_tuple_call_elem_types
val internal_tuple_call_elem_type1 = hd internal_tuple_call_elem_type_terms
val internal_tuple_call_elem_type2 = hd (tl internal_tuple_call_elem_type_terms)
val internal_tuple_call_elem_type3 = hd (tl (tl internal_tuple_call_elem_type_terms))
val internal_tuple_call_elem_size1_eval =
  EVAL ``type_memory_bytes ^internal_tuple_call_cenv2
          ^internal_tuple_call_elem_type1``
val internal_tuple_call_elem_size2_eval =
  EVAL ``type_memory_bytes ^internal_tuple_call_cenv2
          ^internal_tuple_call_elem_type2``
val internal_tuple_call_elem_size3_eval =
  EVAL ``type_memory_bytes ^internal_tuple_call_cenv2
          ^internal_tuple_call_elem_type3``
val internal_tuple_call_copy_field1_eval = save_thm
  ("internal_tuple_call_copy_field1_eval",
   EVAL ``internal_tuple_call_copy_field ^internal_tuple_call_cenv2
           ^internal_tuple_call_ret_buf_operand
           ^internal_tuple_call_return_value
           ^internal_tuple_call_elem_type1 ^internal_tuple_call_elem_type1
           0 0 ^internal_tuple_call_state15``)
val internal_tuple_call_copy_field1_pair =
  rhs (concl internal_tuple_call_copy_field1_eval)
val internal_tuple_call_state16 =
  #2 (pairSyntax.dest_pair internal_tuple_call_copy_field1_pair)
val internal_tuple_call_elem_type2_word_eval =
  EVAL ``is_word_type ^internal_tuple_call_elem_type2``
val internal_tuple_call_field2_dst_step1 = RATOR_CONV (FIRST_CONV
  (map REWR_CONV (CONJUNCTS contextTheory.compile_with_byte_offset_def)))
  ``compile_with_byte_offset ^internal_tuple_call_ret_buf_operand (SUC 31)
      ^internal_tuple_call_state16``
val internal_tuple_call_field2_dst_step2 =
  EVAL (rhs (concl internal_tuple_call_field2_dst_step1))
val internal_tuple_call_field2_dst_eval = save_thm
  ("internal_tuple_call_field2_dst_eval",
   TRANS internal_tuple_call_field2_dst_step1
     internal_tuple_call_field2_dst_step2)
val internal_tuple_call_field2_dst_pair =
  rhs (concl internal_tuple_call_field2_dst_eval)
val internal_tuple_call_field2_dst =
  #1 (pairSyntax.dest_pair internal_tuple_call_field2_dst_pair)
val internal_tuple_call_field2_state1 =
  #2 (pairSyntax.dest_pair internal_tuple_call_field2_dst_pair)
val internal_tuple_call_field2_src_step1 = RATOR_CONV (FIRST_CONV
  (map REWR_CONV (CONJUNCTS contextTheory.compile_with_byte_offset_def)))
  ``compile_with_byte_offset ^internal_tuple_call_return_value (SUC 31)
      ^internal_tuple_call_field2_state1``
val internal_tuple_call_field2_src_step2 =
  EVAL (rhs (concl internal_tuple_call_field2_src_step1))
val internal_tuple_call_field2_src_eval = save_thm
  ("internal_tuple_call_field2_src_eval",
   TRANS internal_tuple_call_field2_src_step1
     internal_tuple_call_field2_src_step2)
val internal_tuple_call_field2_src_pair =
  rhs (concl internal_tuple_call_field2_src_eval)
val internal_tuple_call_field2_src =
  #1 (pairSyntax.dest_pair internal_tuple_call_field2_src_pair)
val internal_tuple_call_field2_state2 =
  #2 (pairSyntax.dest_pair internal_tuple_call_field2_src_pair)
val internal_tuple_call_field2_load_eval = save_thm
  ("internal_tuple_call_field2_load_eval",
   EVAL ``emit_op MLOAD [^internal_tuple_call_field2_src]
           ^internal_tuple_call_field2_state2``)
val internal_tuple_call_field2_load_pair =
  rhs (concl internal_tuple_call_field2_load_eval)
val internal_tuple_call_field2_value =
  #1 (pairSyntax.dest_pair internal_tuple_call_field2_load_pair)
val internal_tuple_call_field2_state3 =
  #2 (pairSyntax.dest_pair internal_tuple_call_field2_load_pair)
val internal_tuple_call_field2_store_eval = save_thm
  ("internal_tuple_call_field2_store_eval",
   EVAL ``emit_void MSTORE
           [^internal_tuple_call_field2_dst;
            ^internal_tuple_call_field2_value]
           ^internal_tuple_call_field2_state3``)
val internal_tuple_call_copy_field2_pair =
  rhs (concl internal_tuple_call_field2_store_eval)
val internal_tuple_call_state17 =
  #2 (pairSyntax.dest_pair internal_tuple_call_copy_field2_pair)
val internal_tuple_call_copy_field2_word_base =
  MATCH_MP internal_tuple_call_copy_field_word
    (EQT_ELIM internal_tuple_call_elem_type2_word_eval)
val internal_tuple_call_copy_field2_word =
  internal_tuple_call_copy_field2_word_base
val internal_tuple_call_copy_field2_step1 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_copy_field2_word])
  ``internal_tuple_call_copy_field ^internal_tuple_call_cenv2
      ^internal_tuple_call_ret_buf_operand
      ^internal_tuple_call_return_value
      ^internal_tuple_call_elem_type2 ^internal_tuple_call_elem_type2
      (SUC 31) (SUC 31) ^internal_tuple_call_state16``
val internal_tuple_call_copy_field2_step2 = QCONV
  (PURE_REWRITE_CONV
    [compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_field2_dst_eval,
     internal_tuple_call_field2_src_eval,
     internal_tuple_call_field2_load_eval,
     internal_tuple_call_field2_store_eval])
  (rhs (concl internal_tuple_call_copy_field2_step1))
val internal_tuple_call_copy_field2_eval = save_thm
  ("internal_tuple_call_copy_field2_eval",
   TRANS internal_tuple_call_copy_field2_step1
     internal_tuple_call_copy_field2_step2)
val internal_tuple_call_elem_type3_word_eval =
  EVAL ``is_word_type ^internal_tuple_call_elem_type3``
val internal_tuple_call_field3_dst_step1 = RATOR_CONV (FIRST_CONV
  (map REWR_CONV (CONJUNCTS contextTheory.compile_with_byte_offset_def)))
  ``compile_with_byte_offset ^internal_tuple_call_ret_buf_operand (SUC 63)
      ^internal_tuple_call_state17``
val internal_tuple_call_field3_dst_step2 =
  EVAL (rhs (concl internal_tuple_call_field3_dst_step1))
val internal_tuple_call_field3_dst_eval = save_thm
  ("internal_tuple_call_field3_dst_eval",
   TRANS internal_tuple_call_field3_dst_step1
     internal_tuple_call_field3_dst_step2)
val internal_tuple_call_field3_dst_pair =
  rhs (concl internal_tuple_call_field3_dst_eval)
val internal_tuple_call_field3_dst =
  #1 (pairSyntax.dest_pair internal_tuple_call_field3_dst_pair)
val internal_tuple_call_field3_state1 =
  #2 (pairSyntax.dest_pair internal_tuple_call_field3_dst_pair)
val internal_tuple_call_field3_src_step1 = RATOR_CONV (FIRST_CONV
  (map REWR_CONV (CONJUNCTS contextTheory.compile_with_byte_offset_def)))
  ``compile_with_byte_offset ^internal_tuple_call_return_value (SUC 63)
      ^internal_tuple_call_field3_state1``
val internal_tuple_call_field3_src_step2 =
  EVAL (rhs (concl internal_tuple_call_field3_src_step1))
val internal_tuple_call_field3_src_eval = save_thm
  ("internal_tuple_call_field3_src_eval",
   TRANS internal_tuple_call_field3_src_step1
     internal_tuple_call_field3_src_step2)
val internal_tuple_call_field3_src_pair =
  rhs (concl internal_tuple_call_field3_src_eval)
val internal_tuple_call_field3_src =
  #1 (pairSyntax.dest_pair internal_tuple_call_field3_src_pair)
val internal_tuple_call_field3_state2 =
  #2 (pairSyntax.dest_pair internal_tuple_call_field3_src_pair)
val internal_tuple_call_field3_load_eval = save_thm
  ("internal_tuple_call_field3_load_eval",
   EVAL ``emit_op MLOAD [^internal_tuple_call_field3_src]
           ^internal_tuple_call_field3_state2``)
val internal_tuple_call_field3_load_pair =
  rhs (concl internal_tuple_call_field3_load_eval)
val internal_tuple_call_field3_value =
  #1 (pairSyntax.dest_pair internal_tuple_call_field3_load_pair)
val internal_tuple_call_field3_state3 =
  #2 (pairSyntax.dest_pair internal_tuple_call_field3_load_pair)
val internal_tuple_call_field3_store_eval = save_thm
  ("internal_tuple_call_field3_store_eval",
   EVAL ``emit_void MSTORE
           [^internal_tuple_call_field3_dst;
            ^internal_tuple_call_field3_value]
           ^internal_tuple_call_field3_state3``)
val internal_tuple_call_copy_field3_pair =
  rhs (concl internal_tuple_call_field3_store_eval)
val internal_tuple_call_state18 =
  #2 (pairSyntax.dest_pair internal_tuple_call_copy_field3_pair)
val internal_tuple_call_copy_field3_word =
  MATCH_MP internal_tuple_call_copy_field_word
    (EQT_ELIM internal_tuple_call_elem_type3_word_eval)
val internal_tuple_call_copy_field3_step1 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_copy_field3_word])
  ``internal_tuple_call_copy_field ^internal_tuple_call_cenv2
      ^internal_tuple_call_ret_buf_operand
      ^internal_tuple_call_return_value
      ^internal_tuple_call_elem_type3 ^internal_tuple_call_elem_type3
      (SUC 63) (SUC 63) ^internal_tuple_call_state17``
val internal_tuple_call_copy_field3_step2 = QCONV
  (PURE_REWRITE_CONV
    [compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_field3_dst_eval,
     internal_tuple_call_field3_src_eval,
     internal_tuple_call_field3_load_eval,
     internal_tuple_call_field3_store_eval])
  (rhs (concl internal_tuple_call_copy_field3_step1))
val internal_tuple_call_copy_field3_eval = save_thm
  ("internal_tuple_call_copy_field3_eval",
   TRANS internal_tuple_call_copy_field3_step1
     internal_tuple_call_copy_field3_step2)
val internal_tuple_call_typed_copy_step = QCONV
  (PURE_REWRITE_CONV
    [compile_typed_copy_fields_cons_as_field,
     compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_copy_field1_eval,
     internal_tuple_call_copy_field2_eval,
     internal_tuple_call_copy_field3_eval])
  ``compile_typed_copy_fields ^internal_tuple_call_cenv2
      ^internal_tuple_call_ret_buf_operand
      ^internal_tuple_call_return_value
      ^internal_tuple_call_elem_types ^internal_tuple_call_elem_types
      0 0 ^internal_tuple_call_state15``
val internal_tuple_call_typed_copy_eval = save_thm
  ("internal_tuple_call_typed_copy_eval",
   internal_tuple_call_typed_copy_step)
val internal_tuple_call_typed_copy_pair =
  rhs (concl internal_tuple_call_typed_copy_eval)
val internal_tuple_call_copy_memory_eval = save_thm
  ("internal_tuple_call_copy_memory_eval",
   EVAL ``compile_copy_memory ^internal_tuple_call_ret_buf_operand
       ^internal_tuple_call_return_value
       (type_memory_bytes ^internal_tuple_call_cenv2
          ^internal_tuple_call_body_ret_ty)
       ^internal_tuple_call_state15``)
val internal_tuple_call_copy_memory_pair =
  rhs (concl internal_tuple_call_copy_memory_eval)
val internal_tuple_call_copy_memory_state =
  #2 (pairSyntax.dest_pair internal_tuple_call_copy_memory_pair)
val internal_tuple_call_ret_eval = save_thm
  ("internal_tuple_call_ret_eval",
   EVAL ``emit_inst RET [^internal_tuple_call_rpc] []
           ^internal_tuple_call_copy_memory_state``)
val internal_tuple_call_ret_pair = rhs (concl internal_tuple_call_ret_eval)
val internal_tuple_call_state19 =
  #2 (pairSyntax.dest_pair internal_tuple_call_ret_pair)
(* Staging beyond the three checked tuple-field copies is retained here while
   the remaining internal-return monad reconstruction is decomposed further.
val internal_tuple_call_internal_return_step1 = SIMP_CONV (srw_ss())
  [stmtLoweringTheory.compile_internal_return_def,
   internal_tuple_call_returns_count_eval,
   internal_tuple_call_is_dynamic_eval,
   Once contextTheory.compile_store_memory_typed_def]
  ``compile_internal_return ^internal_tuple_call_cenv2
      (SOME ^internal_tuple_call_return_value) ^internal_tuple_call_rpc
      (^internal_tuple_call_cenv2).ce_returns_count
      ^internal_tuple_call_body_ret_ty
      (expr_type ^internal_tuple_call_return_expr)
      ^internal_tuple_call_elem_types ^internal_tuple_call_ret_buf
      ^internal_tuple_call_state15``
val internal_tuple_call_internal_return_step2 = QCONV
  (PURE_REWRITE_CONV
    [compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_typed_copy_eval,
     internal_tuple_call_ret_eval])
  (rhs (concl internal_tuple_call_internal_return_step1))
val internal_tuple_call_typed_copy_norm = CONV_RULE
  (LAND_CONV (SIMP_CONV (srw_ss()) []))
  internal_tuple_call_typed_copy_eval
val internal_tuple_call_ret_norm = CONV_RULE
  (LAND_CONV (SIMP_CONV (srw_ss()) []))
  internal_tuple_call_ret_eval
val internal_tuple_call_internal_return_step3 = SIMP_CONV (srw_ss())
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   internal_tuple_call_typed_copy_norm,
   internal_tuple_call_ret_norm]
  (rhs (concl internal_tuple_call_internal_return_step2))
val internal_tuple_call_internal_return_eval = save_thm
  ("internal_tuple_call_internal_return_eval",
   TRANS internal_tuple_call_internal_return_step1
     (TRANS internal_tuple_call_internal_return_step2
       internal_tuple_call_internal_return_step3))
val internal_tuple_call_return_from_env_step1 = QCONV
  (PURE_REWRITE_CONV
    [stmtLoweringTheory.compile_internal_return_from_env_def,
     compileEnvTheory.comp_bind_def,
     internal_tuple_call_ret_buf_eval,
     internal_tuple_call_elem_types_eval,
     internal_tuple_call_internal_return_eval])
  ``compile_internal_return_from_env ^internal_tuple_call_cenv2
      ^internal_tuple_call_body_ret_ty
      (expr_type ^internal_tuple_call_return_expr)
      ^internal_tuple_call_return_value ^internal_tuple_call_rpc
      ^internal_tuple_call_state14``
val internal_tuple_call_return_from_env_step2 = REWR_CONV LET_THM
  (rhs (concl internal_tuple_call_return_from_env_step1))
val internal_tuple_call_return_from_env_step3 = pairLib.PAIRED_BETA_CONV
  (rhs (concl internal_tuple_call_return_from_env_step2))
val internal_tuple_call_return_from_env_step4 = RATOR_CONV BETA_CONV
  (rhs (concl internal_tuple_call_return_from_env_step3))
val internal_tuple_call_return_from_env_step5 = REWR_CONV
  compileEnvTheory.comp_bind_def
  (rhs (concl internal_tuple_call_return_from_env_step4))
val internal_tuple_call_return_from_env_step6 = REWR_CONV LET_THM
  (rhs (concl internal_tuple_call_return_from_env_step5))
val (_, internal_tuple_call_return_from_env_step6_args) =
  strip_comb (rhs (concl internal_tuple_call_return_from_env_step6))
val internal_tuple_call_return_buf_term =
  List.nth (internal_tuple_call_return_from_env_step6_args, 1)
val internal_tuple_call_return_buf_exact_eval = save_thm
  ("internal_tuple_call_return_buf_exact_eval",
   EVAL internal_tuple_call_return_buf_term)
val internal_tuple_call_return_from_env_step7 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_buf_exact_eval])
  (rhs (concl internal_tuple_call_return_from_env_step6))
val internal_tuple_call_return_from_env_step8 = SIMP_CONV pure_ss
  [pairTheory.UNCURRY_DEF]
  (rhs (concl internal_tuple_call_return_from_env_step7))
val internal_tuple_call_return_from_env_step9 = QCONV
  (PURE_REWRITE_CONV
    [compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_return_def,
     internal_tuple_call_elem_types_eval,
     internal_tuple_call_internal_return_eval])
  (rhs (concl internal_tuple_call_return_from_env_step8))
val internal_tuple_call_return_from_env_step10 = RATOR_CONV BETA_CONV
  (rhs (concl internal_tuple_call_return_from_env_step9))
val internal_tuple_call_return_from_env_step11 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_internal_return_eval])
  (rhs (concl internal_tuple_call_return_from_env_step10))
val internal_tuple_call_return_from_env_step12 = SIMP_CONV (srw_ss())
  [LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   internal_tuple_call_returns_count_eval,
   internal_tuple_call_is_dynamic_eval,
   internal_tuple_call_return_shape_eval,
   internal_tuple_call_typed_copy_norm,
   internal_tuple_call_ret_norm]
  (rhs (concl internal_tuple_call_return_from_env_step11))
val (_, internal_tuple_call_return_from_env_step12_args) =
  strip_comb (rhs (concl internal_tuple_call_return_from_env_step12))
val internal_tuple_call_return_from_env_scrut =
  List.nth (internal_tuple_call_return_from_env_step12_args, 1)
val (_, internal_tuple_call_return_from_env_scrut_args) =
  strip_comb internal_tuple_call_return_from_env_scrut
val internal_tuple_call_return_from_env_cond =
  hd internal_tuple_call_return_from_env_scrut_args
val internal_tuple_call_return_from_env_cond_eval = save_thm
  ("internal_tuple_call_return_from_env_cond_eval",
   EVAL internal_tuple_call_return_from_env_cond)
val internal_tuple_call_return_from_env_step13 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_from_env_cond_eval])
  (rhs (concl internal_tuple_call_return_from_env_step12))
val internal_tuple_call_return_from_env_step14 = SIMP_CONV (srw_ss())
  [pairTheory.UNCURRY_DEF,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   internal_tuple_call_typed_copy_norm,
   internal_tuple_call_ret_norm]
  (rhs (concl internal_tuple_call_return_from_env_step13))
val (_, internal_tuple_call_return_from_env_step14_args) =
  strip_comb (rhs (concl internal_tuple_call_return_from_env_step14))
val internal_tuple_call_return_from_env_scrut2 =
  List.nth (internal_tuple_call_return_from_env_step14_args, 1)
val (_, internal_tuple_call_return_from_env_scrut2_args) =
  strip_comb internal_tuple_call_return_from_env_scrut2
val internal_tuple_call_return_from_env_cond2 =
  hd internal_tuple_call_return_from_env_scrut2_args
val internal_tuple_call_return_from_env_cond2_eval = save_thm
  ("internal_tuple_call_return_from_env_cond2_eval",
   EVAL internal_tuple_call_return_from_env_cond2)
val internal_tuple_call_return_from_env_step15 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_from_env_cond2_eval])
  (rhs (concl internal_tuple_call_return_from_env_step14))
val internal_tuple_call_return_from_env_step16 = SIMP_CONV (srw_ss())
  [pairTheory.UNCURRY_DEF,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   internal_tuple_call_typed_copy_norm,
   internal_tuple_call_ret_norm]
  (rhs (concl internal_tuple_call_return_from_env_step15))
val (_, internal_tuple_call_return_from_env_step16_args) =
  strip_comb (rhs (concl internal_tuple_call_return_from_env_step16))
val internal_tuple_call_return_from_env_scrut3 =
  List.nth (internal_tuple_call_return_from_env_step16_args, 1)
val (_, internal_tuple_call_return_from_env_scrut3_args) =
  strip_comb internal_tuple_call_return_from_env_scrut3
val internal_tuple_call_return_from_env_case_arg =
  hd internal_tuple_call_return_from_env_scrut3_args
val internal_tuple_call_return_from_env_case_arg_eval = save_thm
  ("internal_tuple_call_return_from_env_case_arg_eval",
   EVAL internal_tuple_call_return_from_env_case_arg)
val internal_tuple_call_return_from_env_step17 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_from_env_case_arg_eval])
  (rhs (concl internal_tuple_call_return_from_env_step16))
val internal_tuple_call_return_from_env_step18 = SIMP_CONV (srw_ss())
  [pairTheory.UNCURRY_DEF,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   internal_tuple_call_typed_copy_norm,
   internal_tuple_call_ret_norm]
  (rhs (concl internal_tuple_call_return_from_env_step17))
val (_, internal_tuple_call_return_from_env_step18_args) =
  strip_comb (rhs (concl internal_tuple_call_return_from_env_step18))
val internal_tuple_call_return_from_env_scrut4 =
  List.nth (internal_tuple_call_return_from_env_step18_args, 1)
val (_, internal_tuple_call_return_from_env_scrut4_args) =
  strip_comb internal_tuple_call_return_from_env_scrut4
val internal_tuple_call_return_from_env_field1_term =
  List.nth (internal_tuple_call_return_from_env_scrut4_args, 1)
val internal_tuple_call_return_from_env_field1_eval = save_thm
  ("internal_tuple_call_return_from_env_field1_eval",
   EVAL internal_tuple_call_return_from_env_field1_term)
val internal_tuple_call_return_from_env_step19 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_from_env_field1_eval])
  (rhs (concl internal_tuple_call_return_from_env_step18))
val internal_tuple_call_return_from_env_step20 = SIMP_CONV (srw_ss())
  [LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   internal_tuple_call_elem_size1_eval,
   internal_tuple_call_elem_size2_eval,
   internal_tuple_call_elem_size3_eval,
   internal_tuple_call_copy_field1_eval,
   internal_tuple_call_copy_field2_eval,
   internal_tuple_call_copy_field3_eval,
   internal_tuple_call_ret_norm]
  (rhs (concl internal_tuple_call_return_from_env_step19))
val internal_tuple_call_return_from_env_eval = save_thm
  ("internal_tuple_call_return_from_env_eval",
   List.foldl (fn (th, acc) => TRANS acc th)
     internal_tuple_call_return_from_env_step1
     [internal_tuple_call_return_from_env_step2,
      internal_tuple_call_return_from_env_step3,
      internal_tuple_call_return_from_env_step4,
      internal_tuple_call_return_from_env_step5,
      internal_tuple_call_return_from_env_step6,
      internal_tuple_call_return_from_env_step7,
      internal_tuple_call_return_from_env_step8,
      internal_tuple_call_return_from_env_step9,
      internal_tuple_call_return_from_env_step10,
      internal_tuple_call_return_from_env_step11,
      internal_tuple_call_return_from_env_step12,
      internal_tuple_call_return_from_env_step13,
      internal_tuple_call_return_from_env_step14,
      internal_tuple_call_return_from_env_step15,
      internal_tuple_call_return_from_env_step16,
      internal_tuple_call_return_from_env_step17,
      internal_tuple_call_return_from_env_step18,
      internal_tuple_call_return_from_env_step19,
      internal_tuple_call_return_from_env_step20])
val internal_tuple_call_return_from_env_pair =
  rhs (concl internal_tuple_call_return_from_env_eval)
val internal_tuple_call_return_from_env_state =
  #2 (pairSyntax.dest_pair internal_tuple_call_return_from_env_pair)
val internal_tuple_call_cenv2_vars_eval =
  EVAL ``(^internal_tuple_call_cenv2).ce_vars``
val internal_tuple_call_cenv2_vars =
  rhs (concl internal_tuple_call_cenv2_vars_eval)
val internal_tuple_call_rpc_direct_eval =
  EVAL ``FLOOKUP ^internal_tuple_call_cenv2_vars "__return_pc__"``
fun internal_tuple_call_eq_lhs th =
  fst (dest_eq (snd (strip_forall (concl th))))
val internal_tuple_call_return_some_pat =
  ``compile_stmt cenv lctx ty (Return (SOME e))``
val internal_tuple_call_return_some_def = valOf (List.find
  (fn th => can (match_term internal_tuple_call_return_some_pat)
                   (internal_tuple_call_eq_lhs th))
  (CONJUNCTS stmtLoweringTheory.compile_stmt_def))
val internal_tuple_call_stmt_step1 = RATOR_CONV
  (REWR_CONV internal_tuple_call_return_some_def)
  ``compile_stmt ^internal_tuple_call_cenv2 NoLoop
      ^internal_tuple_call_body_ret_ty
      (Return (SOME ^internal_tuple_call_return_expr))
      ^internal_tuple_call_state13``
val internal_tuple_call_stmt_step2 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_rpc_lookup_eval])
  (rhs (concl internal_tuple_call_stmt_step1))
val internal_tuple_call_stmt_step3 = QCONV
  (PURE_REWRITE_CONV
    [compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_return_value_eval,
     internal_tuple_call_return_from_env_eval])
  (rhs (concl internal_tuple_call_stmt_step2))
val internal_tuple_call_stmt_step4 = QCONV
  (PURE_REWRITE_CONV
    [pairTheory.pair_case_def,
     compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_return_value_eval,
     internal_tuple_call_return_from_env_eval])
  (rhs (concl internal_tuple_call_stmt_step3))
val internal_tuple_call_stmt_step5 = REWR_CONV LET_THM
  (rhs (concl internal_tuple_call_stmt_step4))
val internal_tuple_call_stmt_step6 = pairLib.PAIRED_BETA_CONV
  (rhs (concl internal_tuple_call_stmt_step5))
val internal_tuple_call_stmt_step7 = QCONV
  (PURE_REWRITE_CONV
    [compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     internal_tuple_call_return_value_eval,
     internal_tuple_call_return_from_env_eval])
  (rhs (concl internal_tuple_call_stmt_step6))
val internal_tuple_call_stmt_step8 = SIMP_CONV pure_ss [LET_THM]
  (rhs (concl internal_tuple_call_stmt_step7))
val internal_tuple_call_stmt_step9 = RATOR_CONV BETA_CONV
  (rhs (concl internal_tuple_call_stmt_step8))
val internal_tuple_call_stmt_step10 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_from_env_eval])
  (rhs (concl internal_tuple_call_stmt_step9))
val internal_tuple_call_stmt_step11 = SIMP_CONV (srw_ss()) []
  (rhs (concl internal_tuple_call_stmt_step10))
val internal_tuple_call_return_from_env_norm = CONV_RULE
  (LAND_CONV (SIMP_CONV (srw_ss()) []))
  internal_tuple_call_return_from_env_eval
val internal_tuple_call_stmt_step12 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_return_from_env_norm])
  (rhs (concl internal_tuple_call_stmt_step11))
val internal_tuple_call_stmt_eval = save_thm
  ("internal_tuple_call_stmt_eval",
   TRANS internal_tuple_call_stmt_step1
     (TRANS internal_tuple_call_stmt_step2
       (TRANS internal_tuple_call_stmt_step3
         (TRANS internal_tuple_call_stmt_step4
           (TRANS internal_tuple_call_stmt_step5
             (TRANS internal_tuple_call_stmt_step6
               (TRANS internal_tuple_call_stmt_step7
                 (TRANS internal_tuple_call_stmt_step8
                   (TRANS internal_tuple_call_stmt_step9
                     (TRANS internal_tuple_call_stmt_step10
                       (TRANS internal_tuple_call_stmt_step11 internal_tuple_call_stmt_step12)))))))))))
val internal_tuple_call_stmt_pair =
  rhs (concl internal_tuple_call_stmt_eval)
val internal_tuple_call_stmt_state =
  #2 (pairSyntax.dest_pair internal_tuple_call_stmt_pair)
val internal_tuple_call_get13_eval =
  EVAL ``comp_get ^internal_tuple_call_state13``
val internal_tuple_call_terminated13_eval =
  EVAL ``block_is_terminated ^internal_tuple_call_state13``
val internal_tuple_call_stmts_cons_pat =
  ``compile_stmts cenv lctx ty (s::ss)``
val internal_tuple_call_stmts_cons_def = valOf (List.find
  (fn th => can (match_term internal_tuple_call_stmts_cons_pat)
                   (internal_tuple_call_eq_lhs th))
  (CONJUNCTS stmtLoweringTheory.compile_stmt_def))
val internal_tuple_call_stmts_nil_pat =
  ``compile_stmts cenv lctx ty []``
val internal_tuple_call_stmts_nil_def = valOf (List.find
  (fn th => can (match_term internal_tuple_call_stmts_nil_pat)
                   (internal_tuple_call_eq_lhs th))
  (CONJUNCTS stmtLoweringTheory.compile_stmt_def))
val internal_tuple_call_stmts_step = QCONV
  (PURE_REWRITE_CONV
    [internal_tuple_call_stmts_cons_def,
     internal_tuple_call_stmts_nil_def,
     compileEnvTheory.comp_get_def,
     compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def,
     internal_tuple_call_get13_eval,
     internal_tuple_call_terminated13_eval,
     internal_tuple_call_stmt_eval])
  ``compile_stmts ^internal_tuple_call_cenv2 NoLoop
      ^internal_tuple_call_body_ret_ty
      [Return (SOME ^internal_tuple_call_return_expr)]
      ^internal_tuple_call_state13``
val internal_tuple_call_stmts_step2 = QCONV
  (PURE_REWRITE_CONV
    [internal_tuple_call_stmts_cons_def,
     internal_tuple_call_stmts_nil_def,
     compileEnvTheory.comp_get_def,
     compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def,
     internal_tuple_call_get13_eval,
     internal_tuple_call_terminated13_eval,
     internal_tuple_call_stmt_eval])
  (rhs (concl internal_tuple_call_stmts_step))
val internal_tuple_call_stmts_step3 = QCONV
  (PURE_REWRITE_CONV
    [internal_tuple_call_stmts_cons_def,
     internal_tuple_call_stmts_nil_def,
     compileEnvTheory.comp_get_def,
     compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def,
     internal_tuple_call_get13_eval,
     internal_tuple_call_terminated13_eval,
     internal_tuple_call_stmt_eval])
  (rhs (concl internal_tuple_call_stmts_step2))
val () = computeLib.upd_compset (computeLib.add_thms
  [internal_tuple_call_stmt_eval,
   internal_tuple_call_terminated13_eval])
val internal_tuple_call_stmts_step4 =
  EVAL (rhs (concl internal_tuple_call_stmts_step3))
val internal_tuple_call_stmts_eval = save_thm
  ("internal_tuple_call_stmts_eval",
   TRANS internal_tuple_call_stmts_step
     (TRANS internal_tuple_call_stmts_step2
       (TRANS internal_tuple_call_stmts_step3 internal_tuple_call_stmts_step4)))
val internal_tuple_call_stmts_pair =
  rhs (concl internal_tuple_call_stmts_eval)
val internal_tuple_call_state20 =
  #2 (pairSyntax.dest_pair internal_tuple_call_stmts_pair)
val internal_tuple_call_get20_eval =
  EVAL ``comp_get ^internal_tuple_call_state20``
val internal_tuple_call_terminated20_eval =
  EVAL ``block_is_terminated ^internal_tuple_call_state20``
val internal_tuple_call_internal_function_step = QCONV
  (PURE_REWRITE_CONV
    [moduleLoweringTheory.compile_internal_function_def,
     compileEnvTheory.comp_get_def,
     compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def,
     internal_tuple_call_return_buf_eval,
     internal_tuple_call_param_idx_eval,
     internal_tuple_call_param_decls_eval,
     internal_tuple_call_cenv1_eval,
     internal_tuple_call_materialize_eval,
     internal_tuple_call_ret_alloc_eval,
     internal_tuple_call_forced_alloc_eval,
     internal_tuple_call_lock_eval,
     internal_tuple_call_body_ret_ty_eval,
     internal_tuple_call_stmts_eval,
     internal_tuple_call_get20_eval,
     internal_tuple_call_terminated20_eval])
  ``compile_internal_function ^internal_tuple_call_cenv
      ^internal_tuple_call_params ^internal_tuple_call_has_ret_buf
      ^internal_tuple_call_is_nr ^internal_tuple_call_nkey
      ^internal_tuple_call_use_trans ^internal_tuple_call_is_view
      ^internal_tuple_call_is_ctor ^internal_tuple_call_imm_len
      ^internal_tuple_call_body ^internal_tuple_call_ret_type
      ^internal_tuple_call_state6``
val internal_tuple_call_internal_function_eval = save_thm
  ("internal_tuple_call_internal_function_eval",
   internal_tuple_call_internal_function_step)

*)

Theorem compile_internal_return_fixed_tuple:
  ¬is_abi_dynamic cenv.ce_struct_fields (TupleT dst_tys) ⇒
  compile_internal_return cenv (SOME val_op) return_pc 0
      (TupleT dst_tys) (TupleT src_tys) elem_types (SOME buf_op) =
    do (if dst_tys = src_tys then
          compile_copy_memory buf_op val_op
            (type_memory_bytes cenv (TupleT dst_tys))
        else
          compile_typed_copy_fields cenv buf_op val_op
            dst_tys src_tys 0 0);
       emit_inst RET [return_pc] []
    od
Proof
  simp[stmtLoweringTheory.compile_internal_return_def,
       Once contextTheory.compile_store_memory_typed_def,
       compileEnvTheory.is_word_type_def,
       compileEnvTheory.is_bytestring_type_def]
QED

val internal_tuple_call_src_ty_eval =
  EVAL ``expr_type ^internal_tuple_call_return_expr``
val internal_tuple_call_internal_return_clean_step0 = QCONV
  (PURE_REWRITE_CONV
    [internal_tuple_call_returns_count_eval,
     internal_tuple_call_src_ty_eval])
  ``compile_internal_return ^internal_tuple_call_cenv2
      (SOME ^internal_tuple_call_return_value) ^internal_tuple_call_rpc
      (^internal_tuple_call_cenv2).ce_returns_count
      ^internal_tuple_call_body_ret_ty
      (expr_type ^internal_tuple_call_return_expr)
      ^internal_tuple_call_elem_types ^internal_tuple_call_ret_buf
      ^internal_tuple_call_state15``
val internal_tuple_call_internal_return_clean_step1 = SIMP_CONV (srw_ss())
  [compile_internal_return_fixed_tuple,
   internal_tuple_call_is_dynamic_eval]
  (rhs (concl internal_tuple_call_internal_return_clean_step0))
val internal_tuple_call_internal_return_clean_step2 = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_copy_memory_eval,
   internal_tuple_call_ret_eval,
   LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_internal_return_clean_step1))
val internal_tuple_call_internal_return_clean_eval = save_thm
  ("internal_tuple_call_internal_return_clean_eval",
   TRANS internal_tuple_call_internal_return_clean_step0
     (TRANS internal_tuple_call_internal_return_clean_step1
       internal_tuple_call_internal_return_clean_step2))

Theorem compile_internal_return_from_ptr_env:
  FLOOKUP cenv.ce_vars "__return_buf__" = SOME (PtrVar buf_op sz) ⇒
  compile_internal_return_from_env cenv (TupleT tys) src_ty val_op return_pc =
    compile_internal_return cenv (SOME val_op) return_pc
      cenv.ce_returns_count (TupleT tys) src_ty tys (SOME buf_op)
Proof
  simp[stmtLoweringTheory.compile_internal_return_from_env_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def,
       FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

val internal_tuple_call_ret_buf_lookup_eval =
  EVAL ``FLOOKUP (^internal_tuple_call_cenv2).ce_vars "__return_buf__"``
val internal_tuple_call_return_from_env_clean_step0 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_src_ty_eval])
  ``compile_internal_return_from_env ^internal_tuple_call_cenv2
      ^internal_tuple_call_body_ret_ty
      (expr_type ^internal_tuple_call_return_expr)
      ^internal_tuple_call_return_value ^internal_tuple_call_rpc
      ^internal_tuple_call_state14``
val internal_tuple_call_return_from_env_clean_step1 = SIMP_CONV (srw_ss())
  [compile_internal_return_from_ptr_env,
   internal_tuple_call_ret_buf_lookup_eval]
  (rhs (concl internal_tuple_call_return_from_env_clean_step0))
val internal_tuple_call_return_from_env_clean_step2 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_internal_return_clean_eval])
  (rhs (concl internal_tuple_call_return_from_env_clean_step1))
val internal_tuple_call_return_from_env_clean_eval = save_thm
  ("internal_tuple_call_return_from_env_clean_eval",
   TRANS internal_tuple_call_return_from_env_clean_step0
     (TRANS internal_tuple_call_return_from_env_clean_step1
       internal_tuple_call_return_from_env_clean_step2))

Theorem compile_stmt_return_ptr:
  FLOOKUP cenv.ce_vars "__return_pc__" = SOME (PtrVar return_pc sz) ⇒
  compile_stmt cenv lctx ty (Return (SOME e)) =
    do val_op <- lower_value compile_expr cenv ty e;
       compile_internal_return_from_env cenv ty (expr_type e)
         val_op return_pc
    od
Proof
  simp[Once stmtLoweringTheory.compile_stmt_def]
QED

val internal_tuple_call_stmt_return_rule = MATCH_MP
  compile_stmt_return_ptr internal_tuple_call_rpc_lookup_eval
val internal_tuple_call_stmt_clean_step1 = RATOR_CONV
  (REWR_CONV internal_tuple_call_stmt_return_rule)
  ``compile_stmt ^internal_tuple_call_cenv2 NoLoop
      ^internal_tuple_call_body_ret_ty
      (Return (SOME ^internal_tuple_call_return_expr))
      ^internal_tuple_call_state13``
val internal_tuple_call_stmt_clean_step2 = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   internal_tuple_call_return_value_eval,
   internal_tuple_call_return_from_env_clean_eval,
   LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_stmt_clean_step1))
val internal_tuple_call_stmt_clean_eval = save_thm
  ("internal_tuple_call_stmt_clean_eval",
   TRANS internal_tuple_call_stmt_clean_step1
     internal_tuple_call_stmt_clean_step2)
val internal_tuple_call_terminated13_clean_eval =
  EVAL ``block_is_terminated ^internal_tuple_call_state13``
fun internal_tuple_call_clean_eq_lhs th =
  fst (dest_eq (snd (strip_forall (concl th))))
val internal_tuple_call_stmts_cons_pat_clean =
  ``compile_stmts cenv lctx ty (s::ss)``
val internal_tuple_call_stmts_cons_def_clean = valOf (List.find
  (fn th => can (match_term internal_tuple_call_stmts_cons_pat_clean)
                   (internal_tuple_call_clean_eq_lhs th))
  (CONJUNCTS stmtLoweringTheory.compile_stmt_def))
val internal_tuple_call_stmts_nil_pat_clean =
  ``compile_stmts cenv lctx ty []``
val internal_tuple_call_stmts_nil_def_clean = valOf (List.find
  (fn th => can (match_term internal_tuple_call_stmts_nil_pat_clean)
                   (internal_tuple_call_clean_eq_lhs th))
  (CONJUNCTS stmtLoweringTheory.compile_stmt_def))
val internal_tuple_call_stmts_clean_step1 = RATOR_CONV
  (REWR_CONV internal_tuple_call_stmts_cons_def_clean)
  ``compile_stmts ^internal_tuple_call_cenv2 NoLoop
      ^internal_tuple_call_body_ret_ty
      [Return (SOME ^internal_tuple_call_return_expr)]
      ^internal_tuple_call_state13``
val internal_tuple_call_stmts_clean_step2 = SIMP_CONV pure_ss
  [internal_tuple_call_stmts_nil_def_clean,
   compileEnvTheory.comp_get_def,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_terminated13_clean_eval,
   internal_tuple_call_stmt_clean_eval,
   LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_stmts_clean_step1))
val internal_tuple_call_stmts_clean_eval = save_thm
  ("internal_tuple_call_stmts_clean_eval",
   TRANS internal_tuple_call_stmts_clean_step1
     internal_tuple_call_stmts_clean_step2)
val internal_tuple_call_get19_eval =
  EVAL ``comp_get ^internal_tuple_call_state19``
val internal_tuple_call_terminated19_eval =
  EVAL ``block_is_terminated ^internal_tuple_call_state19``
val () = computeLib.upd_compset (computeLib.add_thms
  [internal_tuple_call_return_buf_eval,
   internal_tuple_call_param_idx_eval,
   internal_tuple_call_param_decls_eval,
   internal_tuple_call_retpc_eval,
   internal_tuple_call_cenv1_eval,
   internal_tuple_call_materialize_eval,
   internal_tuple_call_ret_alloc_eval,
   internal_tuple_call_forced_alloc_eval,
   internal_tuple_call_lock_eval,
   internal_tuple_call_body_ret_ty_eval,
   internal_tuple_call_stmts_clean_eval])
val internal_tuple_call_internal_function_clean_step1 = RATOR_CONV
  (REWR_CONV moduleLoweringTheory.compile_internal_function_def)
  ``compile_internal_function ^internal_tuple_call_cenv
      ^internal_tuple_call_params ^internal_tuple_call_has_ret_buf
      ^internal_tuple_call_is_nr ^internal_tuple_call_nkey
      ^internal_tuple_call_use_trans ^internal_tuple_call_is_view
      ^internal_tuple_call_is_ctor ^internal_tuple_call_imm_len
      ^internal_tuple_call_body ^internal_tuple_call_ret_type
      ^internal_tuple_call_state6``
val internal_tuple_call_internal_function_stage_thms =
  [internal_tuple_call_return_buf_eval,
   internal_tuple_call_param_idx_eval,
   internal_tuple_call_param_decls_eval,
   internal_tuple_call_retpc_eval,
   internal_tuple_call_cenv1_eval,
   internal_tuple_call_materialize_eval,
   internal_tuple_call_ret_alloc_eval,
   internal_tuple_call_forced_alloc_eval,
   internal_tuple_call_lock_eval,
   internal_tuple_call_body_ret_ty_eval,
   internal_tuple_call_stmts_clean_eval,
   internal_tuple_call_get19_eval,
   internal_tuple_call_terminated19_eval]
val internal_tuple_call_internal_function_admin_thms =
  internal_tuple_call_internal_function_stage_thms @
  [compileEnvTheory.comp_get_def,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
fun internal_tuple_call_refine_internal_function acc =
  let
    val stage = QCONV
      (PURE_REWRITE_CONV internal_tuple_call_internal_function_stage_thms)
      (rhs (concl acc))
    val admin = QCONV
      (SIMP_CONV pure_ss internal_tuple_call_internal_function_admin_thms)
      (rhs (concl stage))
  in
    TRANS acc (TRANS stage admin)
  end
val internal_tuple_call_internal_function_clean_raw =
  List.foldl (fn (_, acc) => internal_tuple_call_refine_internal_function acc)
    internal_tuple_call_internal_function_clean_step1
    (List.tabulate (16, fn i => i))
val internal_tuple_call_internal_function_partial_eval = save_thm
  ("internal_tuple_call_internal_function_partial_eval",
   internal_tuple_call_internal_function_clean_raw)
val internal_tuple_call_internal_function_partial_pair =
  rhs (concl internal_tuple_call_internal_function_partial_eval)
val (_, internal_tuple_call_if_args) =
  strip_comb internal_tuple_call_internal_function_partial_pair
val internal_tuple_call_if_scrut = List.nth (internal_tuple_call_if_args, 1)
val internal_tuple_call_materialize_exact_eval = save_thm
  ("internal_tuple_call_materialize_exact_eval",
   EVAL internal_tuple_call_if_scrut)
val internal_tuple_call_internal_function_refine = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_materialize_exact_eval])
  internal_tuple_call_internal_function_partial_pair
val internal_tuple_call_internal_function_refined =
  TRANS internal_tuple_call_internal_function_partial_eval
    internal_tuple_call_internal_function_refine
val internal_tuple_call_internal_function_clean_raw2 =
  List.foldl (fn (_, acc) => internal_tuple_call_refine_internal_function acc)
    internal_tuple_call_internal_function_refined
    (List.tabulate (16, fn i => i))
val internal_tuple_call_internal_function_clean_eval = save_thm
  ("internal_tuple_call_internal_function_clean_eval",
   internal_tuple_call_internal_function_clean_raw2)
val (_, internal_tuple_call_if2_args) =
  strip_comb (rhs (concl internal_tuple_call_internal_function_clean_eval))
val internal_tuple_call_if2_scrut = List.nth (internal_tuple_call_if2_args, 1)
val internal_tuple_call_ret_alloc_exact_eval = save_thm
  ("internal_tuple_call_ret_alloc_exact_eval",
   EVAL internal_tuple_call_if2_scrut)
val internal_tuple_call_internal_function_refine2 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_ret_alloc_exact_eval])
  (rhs (concl internal_tuple_call_internal_function_clean_eval))
val internal_tuple_call_internal_function_refined2 =
  TRANS internal_tuple_call_internal_function_clean_eval
    internal_tuple_call_internal_function_refine2
val internal_tuple_call_internal_function_clean_raw3 =
  List.foldl (fn (_, acc) => internal_tuple_call_refine_internal_function acc)
    internal_tuple_call_internal_function_refined2
    (List.tabulate (16, fn i => i))
val internal_tuple_call_internal_function_clean_eval2 = save_thm
  ("internal_tuple_call_internal_function_clean_eval2",
   internal_tuple_call_internal_function_clean_raw3)
val (_, internal_tuple_call_if3_args) =
  strip_comb (rhs (concl internal_tuple_call_internal_function_clean_eval2))
val internal_tuple_call_if3_scrut = List.nth (internal_tuple_call_if3_args, 1)
val internal_tuple_call_forced_alloc_exact_eval = save_thm
  ("internal_tuple_call_forced_alloc_exact_eval",
   EVAL internal_tuple_call_if3_scrut)
val internal_tuple_call_internal_function_refine3 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_forced_alloc_exact_eval])
  (rhs (concl internal_tuple_call_internal_function_clean_eval2))
val internal_tuple_call_internal_function_refined3 =
  TRANS internal_tuple_call_internal_function_clean_eval2
    internal_tuple_call_internal_function_refine3
val internal_tuple_call_internal_function_clean_raw4 =
  List.foldl (fn (_, acc) => internal_tuple_call_refine_internal_function acc)
    internal_tuple_call_internal_function_refined3
    (List.tabulate (16, fn i => i))
val internal_tuple_call_internal_function_clean_eval3 = save_thm
  ("internal_tuple_call_internal_function_clean_eval3",
   internal_tuple_call_internal_function_clean_raw4)
val (_, internal_tuple_call_if4_args) =
  strip_comb (rhs (concl internal_tuple_call_internal_function_clean_eval3))
val internal_tuple_call_if4_scrut = List.nth (internal_tuple_call_if4_args, 1)
val internal_tuple_call_lock_exact_eval = save_thm
  ("internal_tuple_call_lock_exact_eval",
   SIMP_CONV (srw_ss()) [] internal_tuple_call_if4_scrut)
val internal_tuple_call_internal_function_refine4 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_lock_exact_eval])
  (rhs (concl internal_tuple_call_internal_function_clean_eval3))
val internal_tuple_call_internal_function_refined4 =
  TRANS internal_tuple_call_internal_function_clean_eval3
    internal_tuple_call_internal_function_refine4
val internal_tuple_call_internal_function_clean_raw5 =
  List.foldl (fn (_, acc) => internal_tuple_call_refine_internal_function acc)
    internal_tuple_call_internal_function_refined4
    (List.tabulate (16, fn i => i))
val internal_tuple_call_internal_function_clean_eval4 = save_thm
  ("internal_tuple_call_internal_function_clean_eval4",
   internal_tuple_call_internal_function_clean_raw5)
val (_, internal_tuple_call_if5_args) =
  strip_comb (rhs (concl internal_tuple_call_internal_function_clean_eval4))
val internal_tuple_call_if5_scrut = List.nth (internal_tuple_call_if5_args, 1)
fun internal_tuple_call_is_compile_stmt tm =
  same_const (fst (strip_comb tm)) ``compile_stmt``
  handle HOL_ERR _ => false
val internal_tuple_call_stmt_exact_term = find_term
  internal_tuple_call_is_compile_stmt internal_tuple_call_if5_scrut
val internal_tuple_call_stmt_norm = CONV_RULE
  (LAND_CONV (SIMP_CONV (srw_ss()) []))
  internal_tuple_call_stmt_clean_eval
val internal_tuple_call_internal_function_refine5 = QCONV
  (PURE_REWRITE_CONV [internal_tuple_call_stmt_norm])
  (rhs (concl internal_tuple_call_internal_function_clean_eval4))
val internal_tuple_call_internal_function_refined5 =
  TRANS internal_tuple_call_internal_function_clean_eval4
    internal_tuple_call_internal_function_refine5
val internal_tuple_call_internal_function_clean_raw6 =
  List.foldl (fn (_, acc) => internal_tuple_call_refine_internal_function acc)
    internal_tuple_call_internal_function_refined5
    (List.tabulate (16, fn i => i))
val internal_tuple_call_internal_function_clean_eval5 = save_thm
  ("internal_tuple_call_internal_function_clean_eval5",
   internal_tuple_call_internal_function_clean_raw6)
val internal_tuple_call_internal_function_clean_pair5 =
  rhs (concl internal_tuple_call_internal_function_clean_eval5)
fun internal_tuple_call_is_return_from_env tm =
  same_const (fst (strip_comb tm)) ``compile_internal_return_from_env``
  handle HOL_ERR _ => false
val internal_tuple_call_return_exact_term = find_term
  internal_tuple_call_is_return_from_env
  internal_tuple_call_internal_function_clean_pair5
val (_, internal_tuple_call_return_exact_args) =
  strip_comb internal_tuple_call_return_exact_term
val internal_tuple_call_return_exact_cenv =
  List.nth (internal_tuple_call_return_exact_args, 0)
val internal_tuple_call_return_from_ptr_env_spec =
  SPEC_ALL compile_internal_return_from_ptr_env
val (internal_tuple_call_return_lookup_premise, _) = dest_imp
  (concl internal_tuple_call_return_from_ptr_env_spec)
val (internal_tuple_call_return_lookup_lhs, _) = dest_eq
  internal_tuple_call_return_lookup_premise
val internal_tuple_call_return_lookup_cenv_var = valOf (List.find
  (fn tm => fst (dest_var tm) = "cenv")
  (free_vars internal_tuple_call_return_lookup_lhs))
val internal_tuple_call_return_exact_lookup_term = subst
  [internal_tuple_call_return_lookup_cenv_var |->
     internal_tuple_call_return_exact_cenv]
  internal_tuple_call_return_lookup_lhs
val internal_tuple_call_return_exact_lookup_eval = save_thm
  ("internal_tuple_call_return_exact_lookup_eval",
   EVAL internal_tuple_call_return_exact_lookup_term)
val internal_tuple_call_return_from_env_exact_rule = MATCH_MP
  compile_internal_return_from_ptr_env
  internal_tuple_call_return_exact_lookup_eval
val internal_tuple_call_return_from_env_exact_eval = save_thm
  ("internal_tuple_call_return_from_env_exact_eval",
   RATOR_CONV
     (REWR_CONV internal_tuple_call_return_from_env_exact_rule)
     internal_tuple_call_return_exact_term)
val internal_tuple_call_internal_function_refine6 =
  RAND_CONV (RAND_CONV
    (REWR_CONV internal_tuple_call_return_from_env_exact_eval))
  internal_tuple_call_internal_function_clean_pair5
val internal_tuple_call_internal_function_refined6 =
  TRANS internal_tuple_call_internal_function_clean_eval5
    internal_tuple_call_internal_function_refine6
val internal_tuple_call_internal_function_admin6 = REFL
  (rhs (concl internal_tuple_call_internal_function_refined6))
val internal_tuple_call_internal_function_clean_eval6 = save_thm
  ("internal_tuple_call_internal_function_clean_eval6",
   TRANS internal_tuple_call_internal_function_refined6
     internal_tuple_call_internal_function_admin6)
val internal_tuple_call_internal_function_term6 =
  rhs (concl internal_tuple_call_internal_function_clean_eval6)
val (_, internal_tuple_call_function_args6) =
  strip_comb internal_tuple_call_internal_function_term6
val internal_tuple_call_function_scrut6 =
  List.nth (internal_tuple_call_function_args6, 1)
val (_, internal_tuple_call_function_scrut_args6) =
  strip_comb internal_tuple_call_function_scrut6
val internal_tuple_call_function_inner_scrut6 =
  List.nth (internal_tuple_call_function_scrut_args6, 1)
val (internal_tuple_call_function_inner_head6,
     internal_tuple_call_function_inner_args6) =
  strip_comb internal_tuple_call_function_inner_scrut6
val internal_tuple_call_internal_return_exact_term =
  internal_tuple_call_function_inner_scrut6
val internal_tuple_call_fixed_return_spec =
  SPEC_ALL compile_internal_return_fixed_tuple
val (internal_tuple_call_fixed_return_premise,
     internal_tuple_call_fixed_return_conclusion) = dest_imp
  (concl internal_tuple_call_fixed_return_spec)
val (internal_tuple_call_fixed_return_lhs, _) = dest_eq
  internal_tuple_call_fixed_return_conclusion
val (internal_tuple_call_fixed_return_lhs_head,
     internal_tuple_call_fixed_return_lhs_args) = strip_comb
  internal_tuple_call_fixed_return_lhs
val (internal_tuple_call_fixed_return_exact_head,
     internal_tuple_call_fixed_return_exact_args) = strip_comb
  (rator internal_tuple_call_internal_return_exact_term)
val internal_tuple_call_fixed_return_count_eval = save_thm
  ("internal_tuple_call_fixed_return_count_eval",
   EVAL (List.nth (internal_tuple_call_fixed_return_exact_args, 3)))
fun internal_tuple_call_rator_n 0 conv = conv
  | internal_tuple_call_rator_n n conv =
      RATOR_CONV (internal_tuple_call_rator_n (n - 1) conv)
val internal_tuple_call_internal_return_count_norm =
  internal_tuple_call_rator_n 5
    (RAND_CONV (REWR_CONV internal_tuple_call_fixed_return_count_eval))
    internal_tuple_call_internal_return_exact_term
val internal_tuple_call_internal_return_normalized_term =
  rhs (concl internal_tuple_call_internal_return_count_norm)
val (internal_tuple_call_fixed_return_subst,
     internal_tuple_call_fixed_return_ty_subst) = match_term
  internal_tuple_call_fixed_return_lhs
  (rator internal_tuple_call_internal_return_normalized_term)
val internal_tuple_call_fixed_return_inst =
  INST_TYPE internal_tuple_call_fixed_return_ty_subst
    (INST internal_tuple_call_fixed_return_subst
      internal_tuple_call_fixed_return_spec)
val (internal_tuple_call_fixed_return_exact_premise, _) = dest_imp
  (concl internal_tuple_call_fixed_return_inst)
val internal_tuple_call_fixed_return_exact_premise_thm = prove
  (internal_tuple_call_fixed_return_exact_premise, EVAL_TAC)
val internal_tuple_call_fixed_return_exact_rule = MATCH_MP
  internal_tuple_call_fixed_return_inst
  internal_tuple_call_fixed_return_exact_premise_thm
val internal_tuple_call_internal_return_fixed_step =
  RATOR_CONV (REWR_CONV internal_tuple_call_fixed_return_exact_rule)
    internal_tuple_call_internal_return_normalized_term
val internal_tuple_call_internal_return_fixed_eval = save_thm
  ("internal_tuple_call_internal_return_fixed_eval",
   TRANS internal_tuple_call_internal_return_count_norm
     internal_tuple_call_internal_return_fixed_step)
val internal_tuple_call_internal_return_bind_step =
  SIMP_CONV pure_ss
    [compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_bind_def]
    (rhs (concl internal_tuple_call_internal_return_fixed_eval))
val internal_tuple_call_internal_return_bind_eval = save_thm
  ("internal_tuple_call_internal_return_bind_eval",
   TRANS internal_tuple_call_internal_return_fixed_eval
     internal_tuple_call_internal_return_bind_step)
(* Obsolete field-by-field staging retained for reference after the pinned
   Python path was corrected to use one fixed-size MCOPY for equal types.
fun internal_tuple_call_is_typed_copy tm =
  let val (head,args) = strip_comb tm in
    same_const head ``compile_typed_copy_fields`` andalso length args = 8
  end handle HOL_ERR _ => false
val internal_tuple_call_typed_copy_exact_term = find_term
  internal_tuple_call_is_typed_copy
  (rhs (concl internal_tuple_call_internal_return_bind_eval))
val (_, internal_tuple_call_typed_copy_exact_args) =
  strip_comb internal_tuple_call_typed_copy_exact_term
val (_, internal_tuple_call_typed_copy_old_args) =
  strip_comb (lhs (concl internal_tuple_call_typed_copy_eval))
val internal_tuple_call_typed_copy_cenv_eq = save_thm
  ("internal_tuple_call_typed_copy_cenv_eq",
   prove
     (mk_eq (List.nth (internal_tuple_call_typed_copy_old_args, 0),
             List.nth (internal_tuple_call_typed_copy_exact_args, 0)),
      simp[FUN_EQ_THM]))
val internal_tuple_call_typed_copy_cenv_conv =
  internal_tuple_call_rator_n 7
    (RAND_CONV (REWR_CONV internal_tuple_call_typed_copy_cenv_eq))
val internal_tuple_call_typed_copy_exact_eval = save_thm
  ("internal_tuple_call_typed_copy_exact_eval",
   CONV_RULE (LAND_CONV internal_tuple_call_typed_copy_cenv_conv)
     internal_tuple_call_typed_copy_eval)
val internal_tuple_call_internal_return_typed_step =
  RAND_CONV (REWR_CONV internal_tuple_call_typed_copy_exact_eval)
    (rhs (concl internal_tuple_call_internal_return_bind_eval))
val internal_tuple_call_internal_return_typed_eval = save_thm
  ("internal_tuple_call_internal_return_typed_eval",
   TRANS internal_tuple_call_internal_return_bind_eval
     internal_tuple_call_internal_return_typed_step)
val (internal_tuple_call_internal_return_typed_head,
     internal_tuple_call_internal_return_typed_args) = strip_comb
  (rhs (concl internal_tuple_call_internal_return_typed_eval))
val (internal_tuple_call_typed_copy_rhs_head,
     internal_tuple_call_typed_copy_rhs_args) = strip_comb
  (rhs (concl internal_tuple_call_typed_copy_exact_eval))
fun internal_tuple_call_exact_field_eval name th = save_thm
  (name, CONV_RULE
    (LAND_CONV internal_tuple_call_typed_copy_cenv_conv) th)
val internal_tuple_call_copy_field1_exact_eval =
  internal_tuple_call_exact_field_eval
    "internal_tuple_call_copy_field1_exact_eval"
    internal_tuple_call_copy_field1_eval
val internal_tuple_call_copy_field2_exact_eval =
  internal_tuple_call_exact_field_eval
    "internal_tuple_call_copy_field2_exact_eval"
    internal_tuple_call_copy_field2_eval
val internal_tuple_call_copy_field3_exact_eval =
  internal_tuple_call_exact_field_eval
    "internal_tuple_call_copy_field3_exact_eval"
    internal_tuple_call_copy_field3_eval
val internal_tuple_call_typed_copy_finish_step = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_copy_field1_eval,
   internal_tuple_call_copy_field2_eval,
   internal_tuple_call_copy_field3_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_typed_copy_exact_eval))
val internal_tuple_call_typed_copy_finished_eval = save_thm
  ("internal_tuple_call_typed_copy_finished_eval",
   TRANS internal_tuple_call_typed_copy_exact_eval
     internal_tuple_call_typed_copy_finish_step)
val (_, internal_tuple_call_typed_copy_finished_args) = strip_comb
  (rhs (concl internal_tuple_call_typed_copy_finished_eval))
val internal_tuple_call_typed_copy_finished_scrut =
  List.nth (internal_tuple_call_typed_copy_finished_args, 1)
val (_, internal_tuple_call_typed_copy_finished_scrut_args) = strip_comb
  internal_tuple_call_typed_copy_finished_scrut
val (_, internal_tuple_call_field2_old_args) = strip_comb
  (lhs (concl internal_tuple_call_copy_field2_eval))
val internal_tuple_call_field2_dst_off_eq = prove
  (mk_eq (List.nth (internal_tuple_call_field2_old_args, 5),
          List.nth (internal_tuple_call_typed_copy_finished_scrut_args, 5)),
   simp[internal_tuple_call_elem_size1_eval])
val internal_tuple_call_field2_src_off_eq = prove
  (mk_eq (List.nth (internal_tuple_call_field2_old_args, 6),
          List.nth (internal_tuple_call_typed_copy_finished_scrut_args, 6)),
   simp[internal_tuple_call_elem_size1_eval])
val internal_tuple_call_copy_field2_finish_step = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_elem_size1_eval,
   internal_tuple_call_field2_dst_eval,
   internal_tuple_call_field2_src_eval,
   internal_tuple_call_field2_load_eval,
   internal_tuple_call_field2_store_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_copy_field2_eval))
val internal_tuple_call_copy_field2_finished_eval = save_thm
  ("internal_tuple_call_copy_field2_finished_eval",
   TRANS internal_tuple_call_copy_field2_eval
     internal_tuple_call_copy_field2_finish_step)
val internal_tuple_call_copy_field2_beta_step =
  RATOR_CONV BETA_CONV
    (rhs (concl internal_tuple_call_copy_field2_finished_eval))
val internal_tuple_call_copy_field2_after_beta =
  TRANS internal_tuple_call_copy_field2_finished_eval
    internal_tuple_call_copy_field2_beta_step
val internal_tuple_call_copy_field2_final_step = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_field2_src_eval,
   internal_tuple_call_field2_load_eval,
   internal_tuple_call_field2_store_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_copy_field2_after_beta))
val internal_tuple_call_copy_field2_complete_eval = save_thm
  ("internal_tuple_call_copy_field2_complete_eval",
   TRANS internal_tuple_call_copy_field2_after_beta
     internal_tuple_call_copy_field2_final_step)
val internal_tuple_call_copy_field2_aligned_eval = save_thm
  ("internal_tuple_call_copy_field2_aligned_eval",
   PURE_REWRITE_RULE
     [internal_tuple_call_field2_dst_off_eq,
      internal_tuple_call_field2_src_off_eq]
     internal_tuple_call_copy_field2_complete_eval)
val internal_tuple_call_typed_copy_field2_step =
  RAND_CONV (REWR_CONV internal_tuple_call_copy_field2_aligned_eval)
    (rhs (concl internal_tuple_call_typed_copy_finished_eval))
val internal_tuple_call_typed_copy_field2_eval = save_thm
  ("internal_tuple_call_typed_copy_field2_eval",
   TRANS internal_tuple_call_typed_copy_finished_eval
     internal_tuple_call_typed_copy_field2_step)
val internal_tuple_call_typed_copy_field2_beta =
  pairLib.PAIRED_BETA_CONV
    (rhs (concl internal_tuple_call_typed_copy_field2_eval))
val internal_tuple_call_typed_copy_after_field2_eval = save_thm
  ("internal_tuple_call_typed_copy_after_field2_eval",
   TRANS internal_tuple_call_typed_copy_field2_eval
     internal_tuple_call_typed_copy_field2_beta)
val (internal_tuple_call_after_field2_head,
     internal_tuple_call_after_field2_args) = strip_comb
  (rhs (concl internal_tuple_call_typed_copy_after_field2_eval))
val internal_tuple_call_after_field2_scrut =
  List.nth (internal_tuple_call_after_field2_args, 1)
val (_, internal_tuple_call_after_field2_scrut_args) = strip_comb
  internal_tuple_call_after_field2_scrut
val (_, internal_tuple_call_field3_old_args) = strip_comb
  (lhs (concl internal_tuple_call_copy_field3_eval))
val internal_tuple_call_field3_dst_off_eq = prove
  (mk_eq (List.nth (internal_tuple_call_field3_old_args, 5),
          List.nth (internal_tuple_call_after_field2_scrut_args, 5)),
   simp[internal_tuple_call_elem_size1_eval,
        internal_tuple_call_elem_size2_eval])
val internal_tuple_call_field3_src_off_eq = prove
  (mk_eq (List.nth (internal_tuple_call_field3_old_args, 6),
          List.nth (internal_tuple_call_after_field2_scrut_args, 6)),
   simp[internal_tuple_call_elem_size1_eval,
        internal_tuple_call_elem_size2_eval])
val internal_tuple_call_copy_field3_finish_step = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_elem_size1_eval,
   internal_tuple_call_elem_size2_eval,
   internal_tuple_call_field3_dst_eval,
   internal_tuple_call_field3_src_eval,
   internal_tuple_call_field3_load_eval,
   internal_tuple_call_field3_store_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_copy_field3_eval))
val internal_tuple_call_copy_field3_finished_eval =
  TRANS internal_tuple_call_copy_field3_eval
    internal_tuple_call_copy_field3_finish_step
val internal_tuple_call_copy_field3_beta_step =
  RATOR_CONV BETA_CONV
    (rhs (concl internal_tuple_call_copy_field3_finished_eval))
val internal_tuple_call_copy_field3_after_beta =
  TRANS internal_tuple_call_copy_field3_finished_eval
    internal_tuple_call_copy_field3_beta_step
val internal_tuple_call_copy_field3_final_step = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_field3_src_eval,
   internal_tuple_call_field3_load_eval,
   internal_tuple_call_field3_store_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_copy_field3_after_beta))
val internal_tuple_call_copy_field3_complete_eval = save_thm
  ("internal_tuple_call_copy_field3_complete_eval",
   TRANS internal_tuple_call_copy_field3_after_beta
     internal_tuple_call_copy_field3_final_step)
val internal_tuple_call_copy_field3_aligned_eval = save_thm
  ("internal_tuple_call_copy_field3_aligned_eval",
   PURE_REWRITE_RULE
     [internal_tuple_call_field3_dst_off_eq,
      internal_tuple_call_field3_src_off_eq]
     internal_tuple_call_copy_field3_complete_eval)
val internal_tuple_call_typed_copy_field3_step =
  RAND_CONV (REWR_CONV internal_tuple_call_copy_field3_aligned_eval)
    (rhs (concl internal_tuple_call_typed_copy_after_field2_eval))
val internal_tuple_call_typed_copy_field3_eval = save_thm
  ("internal_tuple_call_typed_copy_field3_eval",
   TRANS internal_tuple_call_typed_copy_after_field2_eval
     internal_tuple_call_typed_copy_field3_step)
val internal_tuple_call_typed_copy_field3_beta =
  pairLib.PAIRED_BETA_CONV
    (rhs (concl internal_tuple_call_typed_copy_field3_eval))
val internal_tuple_call_typed_copy_after_field3_eval = save_thm
  ("internal_tuple_call_typed_copy_after_field3_eval",
   TRANS internal_tuple_call_typed_copy_field3_eval
     internal_tuple_call_typed_copy_field3_beta)
val (internal_tuple_call_after_field3_head,
     internal_tuple_call_after_field3_args) = strip_comb
  (rhs (concl internal_tuple_call_typed_copy_after_field3_eval))
val internal_tuple_call_typed_copy_nil_eval = save_thm
  ("internal_tuple_call_typed_copy_nil_eval",
   EVAL (rhs (concl internal_tuple_call_typed_copy_after_field3_eval)))
val internal_tuple_call_typed_copy_complete_eval = save_thm
  ("internal_tuple_call_typed_copy_complete_eval",
   TRANS internal_tuple_call_typed_copy_after_field3_eval
     internal_tuple_call_typed_copy_nil_eval)
val internal_tuple_call_internal_return_copy_step =
  RAND_CONV (REWR_CONV internal_tuple_call_typed_copy_complete_eval)
    (rhs (concl internal_tuple_call_internal_return_bind_eval))
val internal_tuple_call_internal_return_copy_eval =
  TRANS internal_tuple_call_internal_return_bind_eval
    internal_tuple_call_internal_return_copy_step
val internal_tuple_call_internal_return_copy_beta =
  SIMP_CONV pure_ss
    [LET_THM, pairTheory.FST, pairTheory.SND,
     pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
    (rhs (concl internal_tuple_call_internal_return_copy_eval))
val internal_tuple_call_internal_return_after_copy_eval = save_thm
  ("internal_tuple_call_internal_return_after_copy_eval",
   TRANS internal_tuple_call_internal_return_copy_eval
     internal_tuple_call_internal_return_copy_beta)
val (internal_tuple_call_after_copy_head,
     internal_tuple_call_after_copy_args) = strip_comb
  (rhs (concl internal_tuple_call_internal_return_after_copy_eval))
val internal_tuple_call_internal_return_ret_step =
  REWR_CONV internal_tuple_call_ret_eval
    (rhs (concl internal_tuple_call_internal_return_after_copy_eval))
val internal_tuple_call_internal_return_complete_eval = save_thm
  ("internal_tuple_call_internal_return_complete_eval",
   TRANS internal_tuple_call_internal_return_after_copy_eval
     internal_tuple_call_internal_return_ret_step)
*)

val internal_tuple_call_internal_return_branch_step =
  SIMP_CONV pure_ss [REFL_CLAUSE, COND_CLAUSES]
    (rhs (concl internal_tuple_call_internal_return_bind_eval))
val internal_tuple_call_internal_return_branch_eval =
  TRANS internal_tuple_call_internal_return_bind_eval
    internal_tuple_call_internal_return_branch_step
val internal_tuple_call_fixed_copy_exact_term = find_term
  (can (match_term ``compile_copy_memory dst src (n:num) st``))
  (rhs (concl internal_tuple_call_internal_return_branch_eval))
val internal_tuple_call_fixed_copy_exact_eval = save_thm
  ("internal_tuple_call_fixed_copy_exact_eval",
   EVAL internal_tuple_call_fixed_copy_exact_term)
val internal_tuple_call_internal_return_copy_step =
  RAND_CONV (REWR_CONV internal_tuple_call_fixed_copy_exact_eval)
    (rhs (concl internal_tuple_call_internal_return_branch_eval))
val internal_tuple_call_internal_return_copy_eval =
  TRANS internal_tuple_call_internal_return_branch_eval
    internal_tuple_call_internal_return_copy_step
val internal_tuple_call_internal_return_finish_eval =
  EVAL (rhs (concl internal_tuple_call_internal_return_copy_eval))
val internal_tuple_call_internal_return_complete_eval = save_thm
  ("internal_tuple_call_internal_return_complete_eval",
   TRANS internal_tuple_call_internal_return_copy_eval
     internal_tuple_call_internal_return_finish_eval)

val internal_tuple_call_return_from_env_complete_eval = save_thm
  ("internal_tuple_call_return_from_env_complete_eval",
   TRANS internal_tuple_call_return_from_env_exact_eval
     internal_tuple_call_internal_return_complete_eval)
val internal_tuple_call_internal_function_return_step =
  RAND_CONV (RAND_CONV
    (REWR_CONV internal_tuple_call_return_from_env_complete_eval))
  internal_tuple_call_internal_function_clean_pair5
val internal_tuple_call_internal_function_after_return =
  TRANS internal_tuple_call_internal_function_clean_eval5
    internal_tuple_call_internal_function_return_step
val internal_tuple_call_internal_function_inner_beta =
  RAND_CONV pairLib.PAIRED_BETA_CONV
    (rhs (concl internal_tuple_call_internal_function_after_return))
val internal_tuple_call_internal_function_after_inner_beta =
  TRANS internal_tuple_call_internal_function_after_return
    internal_tuple_call_internal_function_inner_beta
val internal_tuple_call_internal_function_outer_beta =
  pairLib.PAIRED_BETA_CONV
    (rhs (concl internal_tuple_call_internal_function_after_inner_beta))
val internal_tuple_call_internal_function_after_outer_beta = save_thm
  ("internal_tuple_call_internal_function_after_outer_beta",
   TRANS internal_tuple_call_internal_function_after_inner_beta
     internal_tuple_call_internal_function_outer_beta)
val (internal_tuple_call_after_outer_head,
     internal_tuple_call_after_outer_args) = strip_comb
  (rhs (concl internal_tuple_call_internal_function_after_outer_beta))
val internal_tuple_call_after_outer_scrut =
  List.nth (internal_tuple_call_after_outer_args, 1)
val internal_tuple_call_after_outer_scrut_eval = save_thm
  ("internal_tuple_call_after_outer_scrut_eval",
   EVAL internal_tuple_call_after_outer_scrut)
val internal_tuple_call_internal_function_terminated_step =
  RAND_CONV (REWR_CONV internal_tuple_call_after_outer_scrut_eval)
    (rhs (concl internal_tuple_call_internal_function_after_outer_beta))
val internal_tuple_call_internal_function_after_terminated =
  TRANS internal_tuple_call_internal_function_after_outer_beta
    internal_tuple_call_internal_function_terminated_step
val internal_tuple_call_internal_function_final_beta =
  pairLib.PAIRED_BETA_CONV
    (rhs (concl internal_tuple_call_internal_function_after_terminated))
val internal_tuple_call_internal_function_complete_eval = save_thm
  ("internal_tuple_call_internal_function_complete_eval",
   TRANS internal_tuple_call_internal_function_after_terminated
     internal_tuple_call_internal_function_final_beta)
val internal_tuple_call_internal_function_final_pair =
  rhs (concl internal_tuple_call_internal_function_complete_eval)
val internal_tuple_call_state20_complete =
  #2 (pairSyntax.dest_pair internal_tuple_call_internal_function_final_pair)
val internal_tuple_call_internal_bodies_clean_step = SIMP_CONV pure_ss
  [moduleLoweringTheory.compile_internal_fn_bodies_def,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_internal_block_eval,
   internal_tuple_call_internal_function_complete_eval,
   LET_THM, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  ``compile_internal_fn_bodies ^internal_tuple_call_internal_fns
      ^internal_tuple_call_state5``
val internal_tuple_call_internal_bodies_clean_eval = save_thm
  ("internal_tuple_call_internal_bodies_clean_eval",
   internal_tuple_call_internal_bodies_clean_step)
val internal_tuple_call_internal_bodies_pair =
  rhs (concl internal_tuple_call_internal_bodies_clean_eval)
val internal_tuple_call_state21 =
  #2 (pairSyntax.dest_pair internal_tuple_call_internal_bodies_pair)
val internal_tuple_call_dispatch_strategy_eval = save_thm
  ("internal_tuple_call_dispatch_strategy_eval",
   EVAL ``(^internal_tuple_call_rpolicy).rpol_frontend_dispatch``)
val internal_tuple_call_generate_runtime_term =
  ``compile_generate_runtime ^internal_tuple_call_selectors
      ^internal_tuple_call_external_fns ^internal_tuple_call_internal_fns
      ^internal_tuple_call_fallback_fn
      (^internal_tuple_call_rpolicy).rpol_frontend_dispatch
      0 0 [] ^internal_tuple_call_entry_info
      ^internal_tuple_call_state0``
val internal_tuple_call_generate_runtime_step0 =
  internal_tuple_call_rator_n 5
    (RAND_CONV (REWR_CONV internal_tuple_call_dispatch_strategy_eval))
    internal_tuple_call_generate_runtime_term
val internal_tuple_call_generate_runtime_step1 = SIMP_CONV pure_ss
  [moduleLoweringTheory.compile_generate_runtime_def,
   venomPolicyTypesTheory.dispatch_strategy_case_def,
   optionTheory.option_case_def,
   compileEnvTheory.comp_bind_def,
   compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   internal_tuple_call_fallback_label_eval,
   internal_tuple_call_linear_selectors_eval,
   internal_tuple_call_dispatch_eval,
   internal_tuple_call_external_bodies_eval,
   internal_tuple_call_fallback_block_eval,
   internal_tuple_call_fallback_revert_eval,
   internal_tuple_call_internal_bodies_clean_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl internal_tuple_call_generate_runtime_step0))
val internal_tuple_call_generate_runtime_eval = save_thm
  ("internal_tuple_call_generate_runtime_eval",
   TRANS internal_tuple_call_generate_runtime_step0
     internal_tuple_call_generate_runtime_step1)
val internal_tuple_call_generate_runtime_pair =
  rhs (concl internal_tuple_call_generate_runtime_eval)
val internal_tuple_call_generate_runtime_state =
  #2 (pairSyntax.dest_pair internal_tuple_call_generate_runtime_pair)
val internal_tuple_call_extract_context_eval = save_thm
  ("internal_tuple_call_extract_context_eval",
   EVAL ``extract_context_with_internals "__entry"
           ^internal_tuple_call_internal_fns
           ^internal_tuple_call_generate_runtime_state``)
val internal_tuple_call_context_data = optionSyntax.dest_some
  (rhs (concl internal_tuple_call_extract_context_eval))
val internal_tuple_call_context =
  #1 (pairSyntax.dest_pair internal_tuple_call_context_data)
val internal_tuple_call_lowering_context_ok_eval = save_thm
  ("internal_tuple_call_lowering_context_ok_eval",
   EVAL ``lowering_context_ok ^internal_tuple_call_context``)
val internal_tuple_call_lowering_policy_ok_eval = save_thm
  ("internal_tuple_call_lowering_policy_ok_eval",
   EVAL ``lowering_policy_ok ^internal_tuple_call_rpolicy``)
val internal_tuple_call_run_lowering_eval = save_thm
  ("internal_tuple_call_run_lowering_eval",
   SIMP_CONV pure_ss
     [vyperCompilerTheory.run_lowering_def,
      boolTheory.COND_CLAUSES,
      optionTheory.option_case_def,
      internal_tuple_call_lowering_policy_ok_eval,
      internal_tuple_call_state0_eval,
      internal_tuple_call_generate_runtime_eval,
      internal_tuple_call_extract_context_eval,
      internal_tuple_call_lowering_context_ok_eval,
      LET_THM, pairTheory.FST, pairTheory.SND,
      pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
     ``run_lowering ^internal_tuple_call_selectors
         ^internal_tuple_call_external_fns ^internal_tuple_call_internal_fns
         ^internal_tuple_call_fallback_fn ^internal_tuple_call_rpolicy
         0 0 [] ^internal_tuple_call_entry_info "__entry"``)
val internal_tuple_call_lower_runtime_eval = save_thm
  ("internal_tuple_call_lower_runtime_eval",
   SIMP_CONV pure_ss
     [compileVyperTheory.lower_vyper_runtime_unit_def,
      internal_tuple_call_type_env_eval,
      internal_tuple_call_nkeys_eval,
      internal_tuple_call_classify_eval,
      internal_tuple_call_selectors_eval,
      internal_tuple_call_external_fns_eval,
      internal_tuple_call_internal_fns_eval,
      internal_tuple_call_fallback_fn_eval,
      internal_tuple_call_entry_info_eval,
      internal_tuple_call_run_lowering_eval,
      LET_THM, pairTheory.FST, pairTheory.SND,
      pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
     ``lower_vyper_runtime_unit ^internal_tuple_call_tops
         ^internal_tuple_call_rpolicy``)
