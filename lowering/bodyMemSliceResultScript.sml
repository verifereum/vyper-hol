(* Full allocated capacity for located slice results. *)
Theory bodyMemSliceResult
Ancestors
  bodyMemSliceData exprSimSliceData exprSimSliceDataPost exprSimMemDefs exprSimVVFrame
  venomState venomExecSemantics
  loweringPosts exprLoweringProps exprLowering context compileEnv
  vyperValue vyperState venomMemDefs valueEncoding finite_map list words

Theorem slice_result_store_bound[local]:
  vv_post ctx func cenv cx e es sa sb s0 ee tv
    (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t /\
  lowered_value_type cenv e = expr_type e /\
  (!ftv. evaluate_type (get_tenv cx) (expr_type e) = SOME ftv ==>
     type_memory_size ftv <= sz) /\
  eval_operand out t = SOME p /\ FLOOKUP t.vs_allocas aid = SOME (w2n p,sz) /\
  alloca_inv t ==>
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv
    (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `w2n p + sz <= t.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)`
  >- simp[vv_store_bound_def] >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_lowered] >>
  gvs[] >> irule vv_store_bound_capacity >> simp[mk_ptr_def] >>
  metis_tac[mk_ptr_def]
QED

Theorem slice_data_bytes_success_post_mem:
 compile_slice_data sl data start len sz sa = (out,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
 eval_operand sl s = SOME (n2w (LENGTH bs)) /\
 eval_operand data s = SOME (n2w src_base) /\
 eval_operand start s = SOME (n2w a) /\ eval_operand len s = SOME (n2w n) /\
 (!op z. MEM op [sl;data;start;len] /\ op = Var z ==> not_fresh_at sa z) /\
 mem_bytes_at src_base (LENGTH bs) s.vs_memory = bs /\
 src_base + LENGTH bs < dimword (:256) /\ a+n <= LENGTH bs /\
 32+n <= sz /\ sz < dimword (:256) /\
 expr_type e = BaseT (BytesT (Dynamic bound)) /\ n <= bound /\
 lowered_value_type cenv e = expr_type e /\
 sz = type_memory_bytes cenv (lowered_value_type cenv e) ==>
 ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
 (!k. vv_post ctx func cenv cx e es sa sb s es
   (Value (BytesV (TAKE n (DROP a bs))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory))
   (t with vs_inst_idx := k) /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es
   (Value (BytesV (TAKE n (DROP a bs))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory))
   (t with vs_inst_idx := k))
Proof
 strip_tac >> drule_all slice_data_success_run >> strip_tac >>
 drule_all slice_data_bytes_success_post >> strip_tac >>
 `t' = t` by fs[] >>
 `vv_post ctx func cenv cx e es sa sb s es
   (Value (BytesV (TAKE n (DROP a bs))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t` by
   metis_tac[vv_post_inst_idx] >>
 `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es
   (Value (BytesV (TAKE n (DROP a bs))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t` by
   (irule slice_result_store_bound >> simp[] >>
    conj_tac >- fs[stmt_state_rel_def] >>
    reverse conj_tac >- metis_tac[] >>
    qexistsl_tac [`aid`, `sz`] >>
    simp[evaluate_type_def, type_memory_size_def, type_memory_bytes_def,
         vfmConstantsTheory.word_size_def]) >>
 qexists_tac `t` >> gvs[] >>
 gvs[vv_store_bound_def, eval_operand_def, lookup_var_def]
QED

Theorem slice_data_string_success_post_mem:
 compile_slice_data sl data start len sz sa = (out,sb) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
 eval_operand sl s = SOME (n2w (LENGTH text)) /\
 eval_operand data s = SOME (n2w src_base) /\
 eval_operand start s = SOME (n2w a) /\ eval_operand len s = SOME (n2w n) /\
 (!op z. MEM op [sl;data;start;len] /\ op = Var z ==> not_fresh_at sa z) /\
 mem_bytes_at src_base (LENGTH text) s.vs_memory = MAP (n2w o ORD) text /\
 src_base + LENGTH text < dimword (:256) /\ a+n <= LENGTH text /\
 32+n <= sz /\ sz < dimword (:256) /\
 expr_type e = BaseT (StringT bound) /\ n <= bound /\
 lowered_value_type cenv e = expr_type e /\
 sz = type_memory_bytes cenv (lowered_value_type cenv e) ==>
 ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
 (!k. vv_post ctx func cenv cx e es sa sb s es
   (Value (StringV (TAKE n (DROP a text))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory))
   (t with vs_inst_idx := k) /\
   vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es
   (Value (StringV (TAKE n (DROP a text))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory))
   (t with vs_inst_idx := k))
Proof
 strip_tac >>
 `mem_bytes_at src_base (LENGTH (MAP (n2w o ORD) text : word8 list))
    s.vs_memory = MAP (n2w o ORD) text` by simp[] >>
 mp_tac (slice_data_success_run |> Q.INST
   [`bs` |-> `MAP (n2w o ORD) text : word8 list`,
    `src_len` |-> `sl`, `src_data` |-> `data`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 drule_all slice_data_string_success_post >> strip_tac >>
 `t' = t` by fs[] >>
 `vv_post ctx func cenv cx e es sa sb s es
   (Value (StringV (TAKE n (DROP a text))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t` by
   metis_tac[vv_post_inst_idx] >>
 `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es
   (Value (StringV (TAKE n (DROP a text))))
   (LocatedValue (expr_type e) (mk_ptr out LocMemory)) t` by
   (irule slice_result_store_bound >> simp[] >>
    conj_tac >- fs[stmt_state_rel_def] >>
    reverse conj_tac >- metis_tac[] >>
    qexistsl_tac [`aid`, `sz`] >>
    simp[evaluate_type_def, type_memory_size_def, type_memory_bytes_def,
         vfmConstantsTheory.word_size_def]) >>
 qexists_tac `t` >> gvs[] >>
 gvs[vv_store_bound_def, eval_operand_def, lookup_var_def]
QED
