(* Concrete request buffer capacities and allocation-site ordering. *)
Theory exprExtRequestWindowSite
Ancestors
  exprExtRequestTupleWindow exprExtRequestTypedCells exprExtRequestAbiFits
  exprExtRequestTupleFold exprLoweringProps loweringHalt compileEnv
  abiEncoderWindowContract valueEncoding list words arithmetic

Theorem extrequest_buffer_site_order:
  compile_alloc_buffer dest_size sd = (db,sd') /\
  sd'.cs_next_id <= ss.cs_next_id /\
  compile_alloc_buffer source_size ss = (sb,ss') /\
  ss'.cs_next_id <= st.cs_next_id ==>
  sd.cs_next_id < st.cs_next_id /\ ss.cs_next_id < st.cs_next_id /\
  sd.cs_next_id <> ss.cs_next_id
Proof
  strip_tac >> imp_res_tac compile_alloc_buffer_parts >> decide_tac
QED

(* The layout sum is the compiler's args_mem_size, not the signature size. *)
Theorem extrequest_cells_source_capacity:
  EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells ==>
  type_memory_size (TupleTV (MAP (\(e,r,vv,ty,tv,v). tv) cells)) =
    SUM (MAP (type_memory_bytes cenv)
      (MAP (\(e,r,vv,ty,tv,v). ty) cells))
Proof
  strip_tac >> drule extrequest_cells_layout >>
  simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem extrequest_buffer_payload_capacity:
  !n argcap b return_size:num. n <= argcap ==>
    b + 32 + n <= b + (MAX argcap return_size + 32)
Proof
  simp[MAX_DEF] >> decide_tac
QED

Theorem extrequest_window_site:
  expr_sim_inv cenv cx env ee /\
  EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells /\
  tys = MAP (\(e,r,vv,ty,tv,v). ty) cells /\
  tvs = MAP (\(e,r,vv,ty,tv,v). tv) cells /\
  vs = MAP (\(e,r,vv,ty,tv,v). v) cells /\
  SUM (MAP (type_memory_bytes cenv) tys) < 2**64 /\
  assignable_type (get_tenv cx) (TupleT tys) /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av /\
  LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <=
    abi_size_bound cenv.ce_struct_fields (TupleT tys) /\
  build_ext_calldata (get_tenv cx) fname ats vs =
    SOME (function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++
      enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) /\
  tuple_in_memory vs tvs source_base s.vs_memory /\
  ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT tys) /\
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx ee s /\
  compile_alloc_buffer
    (MAX (abi_size_bound cenv.ce_struct_fields (TupleT tys)) return_size + 32)
    sd = (db,sd') /\
  sd'.cs_next_id <= ss.cs_next_id /\
  compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys)) ss = (sb,ss') /\
  ss'.cs_next_id <= st.cs_next_id /\
  FLOOKUP s.vs_allocas ss.cs_next_id =
    SOME (source_base,SUM (MAP (type_memory_bytes cenv) tys)) /\
  FLOOKUP s.vs_allocas sd.cs_next_id =
    SOME (dest_base,MAX (abi_size_bound cenv.ce_struct_fields (TupleT tys)) return_size + 32) /\
  eval_operand src s = SOME (n2w source_base) /\
  eval_operand dst s = SOME (n2w (dest_base + 32)) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?at rv.
    build_ext_calldata (get_tenv cx) fname ats vs =
      SOME (function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++ enc at rv) /\
    abi_encoder_window_pre ctx func st en dst src ei at rv source_base
      (type_memory_size (TupleTV tvs)) (dest_base + 32) s
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
   value_has_type (TupleTV tvs) (ArrayV (TupleV vs))` by
    metis_tac[extrequest_cells_tuple] >>
  `type_memory_size (TupleTV tvs) = SUM (MAP (type_memory_bytes cenv) tys)` by
    metis_tac[extrequest_cells_source_capacity] >>
  drule_all extrequest_buffer_site_order >> strip_tac >>
  `dest_base + 32 + LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <=
   dest_base + (MAX (abi_size_bound cenv.ce_struct_fields (TupleT tys)) return_size + 32)` by
    (irule extrequest_buffer_payload_capacity >> simp[]) >>
  `?at rv. enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    abi_encoder_window_pre ctx func st en dst src ei at rv source_base
      (type_memory_size (TupleTV tvs)) (dest_base + 32) s` by
    (irule extrequest_tuple_window_entry >>
     asm_rewrite_tac[] >>
     conj_tac >-
       (qexistsl_tac [`dest_base`, `sd.cs_next_id`,
          `MAX (abi_size_bound cenv.ce_struct_fields (TupleT tys)) return_size + 32`,
          `ss.cs_next_id`, `SUM (MAP (type_memory_bytes cenv) tys)`] >> gvs[]) >>
     metis_tac[]) >>
  qexistsl_tac [`at`, `rv`] >> metis_tac[]
QED
