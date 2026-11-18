Theory callCodeEvalPrims
Ancestors
  vyperInterpreter vyperContext vyperState vyperCreate vyperEvmBoundary
  vyperAST exprLowering supportedExprTraverse list pair rich_list sorting

(* Operations below the mutual evaluator inspect the context, but not its code. *)
Theorem storage_backend_code_update[local]:
  get_storage_backend (cx with txn := cx.txn with code := c) tr =
  get_storage_backend cx tr
Proof
  Cases_on `tr` >> simp[get_storage_backend_def]
QED

Theorem resolve_array_code_update[local]:
  !cx tr slot ty path c.
    resolve_array_element (cx with txn := cx.txn with code := c) tr slot ty path =
    resolve_array_element cx tr slot ty path
Proof
  ho_match_mp_tac resolve_array_element_ind >>
  rpt conj_tac >> rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [resolve_array_element_def] >>
  gvs[storage_backend_code_update]
QED

Theorem address_immutables_code_update[local]:
  (get_address_immutables (cx with txn := cx.txn with code := c) =
   get_address_immutables cx) /\
  (set_address_immutables (cx with txn := cx.txn with code := c) imms =
   set_address_immutables cx imms)
Proof
  simp[FUN_EQ_THM,get_address_immutables_def,set_address_immutables_def]
QED

Theorem basic_code_update[local]:
  (get_module_code (cx with txn := cx.txn with code := c) src = get_module_code cx src) /\
  (get_tenv (cx with txn := cx.txn with code := c) = get_tenv cx) /\
  (check_not_static (cx with txn := cx.txn with code := c) = check_not_static cx) /\
  (vyper_to_tx_params (tx with code := c) = vyper_to_tx_params tx) /\
  (get_immutables (cx with txn := cx.txn with code := c) src = get_immutables cx src) /\
  (set_immutable (cx with txn := cx.txn with code := c) src id ty v = set_immutable cx src id ty v) /\
  (lookup_global (cx with txn := cx.txn with code := c) src id = lookup_global cx src id) /\
  (lookup_flag_mem (cx with txn := cx.txn with code := c) nsid id = lookup_flag_mem cx nsid id) /\
  (read_storage_slot (cx with txn := cx.txn with code := c) tr slot ty = read_storage_slot cx tr slot ty) /\
  (write_storage_slot (cx with txn := cx.txn with code := c) tr slot ty v = write_storage_slot cx tr slot ty v) /\
  (subscript_reads_base (cx with txn := cx.txn with code := c) e1 e2 = subscript_reads_base cx e1 e2)
Proof
  simp[get_module_code_def,get_tenv_def,check_not_static_def,vyper_to_tx_params_def,
       get_immutables_def,get_address_immutables_def,set_immutable_def,set_address_immutables_def,
       lookup_global_def,lookup_flag_mem_def,lookup_flag_def,lookup_var_slot_from_layout_def,
       storage_backend_code_update,oneline set_storage_backend_def,
       read_storage_slot_def,write_storage_slot_def,subscript_reads_base_def,
       address_immutables_code_update,oneline lookup_flag_mem_def]
QED

Theorem place_code_update[local]:
  (read_place (cx with txn := cx.txn with code := c) p = read_place cx p) /\
  (place_type_value (cx with txn := cx.txn with code := c) p = place_type_value cx p) /\
  (write_place (cx with txn := cx.txn with code := c) p v = write_place cx p v) /\
  (pop_place (cx with txn := cx.txn with code := c) p = pop_place cx p) /\
  (append_place (cx with txn := cx.txn with code := c) p v = append_place cx p v) /\
  (extend_storage_place (cx with txn := cx.txn with code := c) tr slot ty sb =
   extend_storage_place cx tr slot ty sb)
Proof
  Cases_on `p` >>
  simp[read_place_def,place_type_value_def,write_place_def,oneline pop_place_def,
       oneline append_place_def,oneline extend_storage_place_def,basic_code_update,
       resolve_array_code_update,storage_backend_code_update,oneline read_place_def,
       oneline place_type_value_def,oneline write_place_def]
QED

Theorem result_code_update[local]:
  (read_result (cx with txn := cx.txn with code := c) r = read_result cx r) /\
  (conditional_result (cx with txn := cx.txn with code := c) r = conditional_result cx r) /\
  (result_array_length (cx with txn := cx.txn with code := c) r = result_array_length cx r) /\
  (extend_place (cx with txn := cx.txn with code := c) r sb = extend_place cx r sb) /\
  (select_result (cx with txn := cx.txn with code := c) typ r sb = select_result cx typ r sb)
Proof
  simp[oneline read_result_def,oneline conditional_result_def,oneline result_array_length_def,
       oneline extend_place_def,oneline select_result_def,place_code_update,basic_code_update,
       storage_backend_code_update]
QED

Theorem read_results_code_update[local]:
  !rs. read_results (cx with txn := cx.txn with code := c) rs = read_results cx rs
Proof
  Induct >> simp[read_results_def,result_code_update]
QED

Theorem type_builtin_code_update[local]:
  !cx tb typ ts vs c.
    evaluate_type_builtin (cx with txn := cx.txn with code := c) tb typ ts vs =
    evaluate_type_builtin cx tb typ ts vs
Proof
  ho_match_mp_tac evaluate_type_builtin_ind >>
  simp[evaluate_type_builtin_def,basic_code_update]
QED

Theorem call_code_primitive_updates:
  (get_module_code (cx with txn := cx.txn with code := c) src = get_module_code cx src) /\
  (get_tenv (cx with txn := cx.txn with code := c) = get_tenv cx) /\
  (check_not_static (cx with txn := cx.txn with code := c) = check_not_static cx) /\
  (vyper_to_tx_params (tx with code := c) = vyper_to_tx_params tx) /\
  (get_immutables (cx with txn := cx.txn with code := c) src = get_immutables cx src) /\
  (set_immutable (cx with txn := cx.txn with code := c) src id ty v = set_immutable cx src id ty v) /\
  (lookup_global (cx with txn := cx.txn with code := c) src id = lookup_global cx src id) /\
  (lookup_flag_mem (cx with txn := cx.txn with code := c) nsid id = lookup_flag_mem cx nsid id) /\
  (resolve_array_element (cx with txn := cx.txn with code := c) tr slot ty path =
   resolve_array_element cx tr slot ty path) /\
  (get_storage_backend (cx with txn := cx.txn with code := c) tr = get_storage_backend cx tr) /\
  (read_storage_slot (cx with txn := cx.txn with code := c) tr slot ty = read_storage_slot cx tr slot ty) /\
  (write_storage_slot (cx with txn := cx.txn with code := c) tr slot ty v = write_storage_slot cx tr slot ty v) /\
  (subscript_reads_base (cx with txn := cx.txn with code := c) e1 e2 = subscript_reads_base cx e1 e2) /\
  (read_place (cx with txn := cx.txn with code := c) p = read_place cx p) /\
  (place_type_value (cx with txn := cx.txn with code := c) p = place_type_value cx p) /\
  (write_place (cx with txn := cx.txn with code := c) p v = write_place cx p v) /\
  (pop_place (cx with txn := cx.txn with code := c) p = pop_place cx p) /\
  (append_place (cx with txn := cx.txn with code := c) p v = append_place cx p v) /\
  (extend_storage_place (cx with txn := cx.txn with code := c) tr slot ty sb =
   extend_storage_place cx tr slot ty sb) /\
  (read_result (cx with txn := cx.txn with code := c) r = read_result cx r) /\
  (conditional_result (cx with txn := cx.txn with code := c) r = conditional_result cx r) /\
  (result_array_length (cx with txn := cx.txn with code := c) r = result_array_length cx r) /\
  (extend_place (cx with txn := cx.txn with code := c) r sb = extend_place cx r sb) /\
  (select_result (cx with txn := cx.txn with code := c) typ r sb = select_result cx typ r sb) /\
  (read_results (cx with txn := cx.txn with code := c) rs = read_results cx rs) /\
  (evaluate_builtin (cx with txn := cx.txn with code := c) acc result_ty bt ts vs =
   evaluate_builtin cx acc result_ty bt ts vs) /\
  (switch_BoolV (cx with txn := cx.txn with code := c) r yes no = switch_BoolV cx r yes no) /\
  (array_iterator_results (cx with txn := cx.txn with code := c) typ r = array_iterator_results cx typ r) /\
  (evaluate_type_builtin (cx with txn := cx.txn with code := c) tb typ ts vs =
   evaluate_type_builtin cx tb typ ts vs) /\
  (eval_send (cx with txn := cx.txn with code := c) gas vs = eval_send cx gas vs) /\
  (eval_ext_call (cx with txn := cx.txn with code := c) static skip sig opts vs =
   eval_ext_call cx static skip sig opts vs) /\
  (eval_raw_call (cx with txn := cx.txn with code := c) flags addr data amount g =
   eval_raw_call cx flags addr data amount g) /\
  (eval_create (cx with txn := cx.txn with code := c) kind salt rof ts vs bsize =
   eval_create cx kind salt rof ts vs bsize)
Proof
  simp[basic_code_update,resolve_array_code_update,storage_backend_code_update,
       place_code_update,result_code_update,read_results_code_update,type_builtin_code_update] >>
  conj_tac >- simp[evaluate_builtin_def,evaluate_block_hash_def,evaluate_blob_hash_def,basic_code_update] >>
  simp[switch_BoolV_def,array_iterator_results_def,result_code_update,basic_code_update,
       oneline eval_send_def,oneline eval_ext_call_def,eval_ext_call_effects_def,eval_raw_call_def,
       frame_call_value_def,run_raw_call_def,run_delegate_call_def,make_delegate_call_state_def,
       eval_create_def]
QED

Theorem no_self_code_operands:
  (~supported_exprs_exists is_self_code es ==>
   ~supported_exprs_exists is_self_code (TAKE n es)) /\
  (~supported_exprs_exists is_self_code es ==>
   ~supported_exprs_exists is_self_code (DROP n es)) /\
  (~supported_fields_exists is_self_code kes ==>
   ~supported_exprs_exists is_self_code (MAP SND kes)) /\
  (order_custom_error_args params err = SOME es ==>
   EVERY ($~ o supported_expr_exists is_self_code) (custom_error_exprs err) ==>
   ~supported_exprs_exists is_self_code es)
Proof
  simp[supported_exprs_exists_every,supported_fields_exists_every,EXISTS_MEM,MEM_MAP] >>
  conj_tac >- metis_tac[MEM_TAKE] >>
  conj_tac >- metis_tac[MEM_DROP_IMP] >>
  conj_tac >- metis_tac[] >>
  strip_tac >> drule order_custom_error_args_perm >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[MEM_PERM]
QED
