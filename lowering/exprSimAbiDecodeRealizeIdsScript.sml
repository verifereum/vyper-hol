Theory exprSimAbiDecodeRealizeIds
Ancestors
  exprSimAbiDecodeRealizeStraight exprSimAbiDecodeRealizeFunction
  exprSimAbiDecodeRealizeFootprint exprSimAbiDecodeSizeProbe
  exprSimAbiDecodeRealizeSource exprLowering abiEncoder builtinAbi
  compileEnv emitHelper context vyperCompiler venomInst list arithmetic

Definition abi_decode_realize_ids_def:
  abi_decode_realize_ids f <=>
    !st. ?delta.
      (SND (f st)).cs_current_insts = st.cs_current_insts ++ delta /\
      st.cs_next_id <= (SND (f st)).cs_next_id /\
      ALL_DISTINCT (MAP (\i. i.inst_id) delta) /\
      EVERY (\i. st.cs_next_id <= i.inst_id /\
        i.inst_id < (SND (f st)).cs_next_id) delta
End

Theorem abi_decode_realize_ids_primitives:
  abi_decode_realize_ids (comp_return v) /\
  abi_decode_realize_ids (emit_op opc ops) /\
  abi_decode_realize_ids (emit_void opc ops)
Proof
  simp[abi_decode_realize_ids_def, comp_return_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, mk_inst_def]
QED

Theorem abi_decode_realize_ids_intervals[local]:
  lo <= mid /\ mid <= hi /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) ys) /\
  EVERY (\i. lo <= i.inst_id /\ i.inst_id < mid) xs /\
  EVERY (\i. mid <= i.inst_id /\ i.inst_id < hi) ys ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (xs ++ ys)) /\
  EVERY (\i. lo <= i.inst_id /\ i.inst_id < hi) (xs ++ ys)
Proof
  simp[MAP_APPEND, ALL_DISTINCT_APPEND, EVERY_APPEND, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, NOT_LESS]
QED

Theorem abi_decode_realize_ids_bind:
  abi_decode_realize_ids f /\ (!v. abi_decode_realize_ids (g v)) ==>
  abi_decode_realize_ids (comp_bind f g)
Proof
  simp[abi_decode_realize_ids_def] >> rpt strip_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >>
  rename1 `f st = (v,mid)` >>
  first_x_assum (qspec_then `st` strip_assume_tac) >>
  first_x_assum (qspecl_then [`v`, `mid`] strip_assume_tac) >>
  qexists_tac `delta ++ delta'` >>
  gvs[APPEND_ASSOC] >>
  drule_all abi_decode_realize_ids_intervals >> simp[]
QED

Theorem abi_decode_realize_ids_ignore_bind:
  abi_decode_realize_ids f /\ abi_decode_realize_ids g ==>
  abi_decode_realize_ids (comp_ignore_bind f g)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule abi_decode_realize_ids_bind >> simp[]
QED

Theorem abi_decode_realize_ids_range:
  abi_decode_realize_ids (compile_abi_decode_range_check lo hi lim)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (ho_match_mp_tac abi_decode_realize_ids_bind >>
    conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
  simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_addr:
  abi_decode_realize_ids (compile_abi_dec_addr base_op src)
Proof
  simp[compile_abi_dec_addr_def, abi_decode_realize_ids_primitives] >>
  IF_CASES_TAC >> simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_bytes:
  abi_decode_realize_ids
    (compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n))
Proof
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_ids_primitives] >>
      ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
      >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
      irule abi_decode_realize_ids_ignore_bind >>
      simp[abi_decode_realize_ids_range, abi_decode_realize_ids_primitives]) >>
  gen_tac >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_addr] >> gen_tac >>
  ntac 3 (ho_match_mp_tac abi_decode_realize_ids_bind >>
    conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
  irule abi_decode_realize_ids_ignore_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >>
  irule abi_decode_realize_ids_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_ids_primitives] >>
      ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
      >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
      simp[abi_decode_realize_ids_range]) >>
  IF_CASES_TAC >- simp[abi_decode_realize_ids_primitives] >>
  ntac 4 (ho_match_mp_tac abi_decode_realize_ids_bind >>
    conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
  irule abi_decode_realize_ids_ignore_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
  simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_getelem:
  abi_decode_realize_ids (compile_getelemptr_abi src dyn off MLOAD base_op hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
  IF_CASES_TAC >- simp[abi_decode_realize_ids_primitives] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_addr] >> gen_tac >>
  ntac 2 (ho_match_mp_tac abi_decode_realize_ids_bind >>
    conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
  irule abi_decode_realize_ids_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_ids_primitives] >>
      ntac 2 (ho_match_mp_tac abi_decode_realize_ids_bind >>
        conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
      simp[abi_decode_realize_ids_primitives]) >>
  simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_singleton:
  (!dst src base_op hi. abi_decode_realize_ids
    (compile_abi_decode_to_buf dst src MLOAD base_op hi ei)) ==>
  abi_decode_realize_ids
    (compile_abi_decode_complex_elems dst src MLOAD base_op hi [(ei,asz,msz)] ao vo)
Proof
  strip_tac >> rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_getelem] >> gen_tac >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
  irule abi_decode_realize_ids_ignore_bind >> conj_tac
  >- simp[] >>
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_wrapper:
  (!dst src base_op hi. abi_decode_realize_ids
    (compile_abi_decode_to_buf dst src MLOAD base_op hi ei)) ==>
  abi_decode_realize_ids
    (compile_abi_decode_to_buf dst src MLOAD base_op hi (DecComplex dyn [(ei,asz,msz)]))
Proof
  strip_tac >> rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM, listTheory.FOLDR] >> BETA_TAC >>
  IF_CASES_TAC >- simp[abi_decode_realize_ids_singleton] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
  irule abi_decode_realize_ids_ignore_bind >>
  simp[abi_decode_realize_ids_range, abi_decode_realize_ids_singleton]
QED

Theorem abi_decode_realize_ids_decoder:
  !k dst src base_op hi.
    abi_decode_realize_ids
      (compile_abi_decode_to_buf dst src MLOAD base_op hi
        (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)))
Proof
  Induct
  >- simp[abi_decode_size_probe_type_def, type_to_abi_dec_info_def,
          abi_decode_realize_ids_bytes] >>
  rpt gen_tac >>
  simp[abi_decode_size_probe_type_def, Once type_to_abi_dec_info_def] >>
  irule abi_decode_realize_ids_wrapper >> simp[]
QED

Theorem abi_decode_realize_ids_alloc:
  abi_decode_realize_ids (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >>
  simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_lower:
  abi_decode_realize_ids
    (lower_abi_decode data
      (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)) lo hi sz)
Proof
  rewrite_tac[lower_abi_decode_def] >>
  ntac 2 (ho_match_mp_tac abi_decode_realize_ids_bind >>
    conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
  irule abi_decode_realize_ids_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac abi_decode_realize_ids_bind >>
          simp[abi_decode_realize_ids_primitives]) >>
      ntac 5 (ho_match_mp_tac abi_decode_realize_ids_bind >>
        conj_tac >- simp[abi_decode_realize_ids_primitives] >> gen_tac) >>
      simp[abi_decode_realize_ids_primitives]) >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_alloc] >> gen_tac >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
  irule abi_decode_realize_ids_ignore_bind >>
  simp[abi_decode_realize_ids_decoder, abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_chunks:
  !p bs off. abi_decode_realize_ids (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  rewrite_tac[Once compile_store_byte_chunks_def] >>
  simp_tac (srw_ss()) [LET_THM, abi_decode_realize_ids_primitives] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- simp[abi_decode_realize_ids_primitives] >> gen_tac >>
  irule abi_decode_realize_ids_ignore_bind >>
  simp[abi_decode_realize_ids_primitives] >>
  first_x_assum (mp_tac o SIMP_RULE (srw_ss()) []) >> simp[]
QED

Theorem abi_decode_realize_ids_literal:
  abi_decode_realize_ids
    (compile_literal_vv (BaseT (BytesT (Dynamic 32))) (BytesL (REPLICATE 32 0w)))
Proof
  simp_tac (srw_ss()) [compile_literal_vv_def] >>
  ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
  >- (simp[compile_bytelike_literal_def] >>
      ho_match_mp_tac abi_decode_realize_ids_bind >> conj_tac
      >- simp[abi_decode_realize_ids_alloc] >> gen_tac >>
      irule abi_decode_realize_ids_ignore_bind >> conj_tac
      >- simp[abi_decode_realize_ids_primitives] >>
      irule abi_decode_realize_ids_ignore_bind >>
      simp[abi_decode_realize_ids_chunks, abi_decode_realize_ids_primitives]) >>
  simp[abi_decode_realize_ids_primitives]
QED

Theorem abi_decode_realize_ids_result:
  abi_decode_realize_ids f /\ f st = (v,st') ==>
  ?delta. st'.cs_current_insts = st.cs_current_insts ++ delta /\
    st.cs_next_id <= st'.cs_next_id /\
    ALL_DISTINCT (MAP (\i. i.inst_id) delta) /\
    EVERY (\i. st.cs_next_id <= i.inst_id /\ i.inst_id < st'.cs_next_id) delta
Proof
  simp[abi_decode_realize_ids_def] >> metis_tac[pairTheory.SND]
QED

Theorem abi_decode_realize_expr_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
      (abi_decode_realize_expr k) (initial_compile_state entry))).cs_current_insts)
Proof
  simp_tac (srw_ss()) [abi_decode_realize_expr_def, vyperASTTheory.expr_type_def,
    Once compile_expr_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_component_eq, LET_THM] >>
  simp[abi_decode_realize_arg_compile] >> pairarg_tac >>
  drule abi_decode_realize_literal_unwrap >>
  disch_then (qspec_then `ce` strip_assume_tac) >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def] >>
  qpat_x_assum `Abbrev _` (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at Any abi_decode_realize_ids_result >>
  simp[abi_decode_realize_ids_lower] >> strip_tac >>
  qpat_x_assum `lower_abi_decode _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  drule_at Any abi_decode_realize_ids_result >>
  simp[abi_decode_realize_ids_literal] >> strip_tac >>
  gvs[initial_compile_state_def] >>
  gvs[ALL_DISTINCT_APPEND, EVERY_MEM, MEM_MAP] >>
  metis_tac[NOT_LESS]
QED

Theorem abi_decode_realize_final_ids:
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (abi_decode_realize_code (abi_decode_realize_final ce k entry)))
Proof
  simp[abi_decode_realize_code_def, abi_decode_realize_final_single_block,
       abi_decode_realize_final_def, abi_decode_realize_expr_ids]
QED
