Theory exprSimAbiDecodeRealizeStraight
Ancestors
  exprSimAbiDecodeRealizeFunction exprSimAbiDecodeRealizeFootprint
  exprLowering abiEncoder builtinAbi compileEnv emitHelper list context vyperCompiler
  exprSimAbiDecodeSizeProbe exprSimAbiDecodeRealizeSource

Definition abi_decode_realize_no_switch_def:
  abi_decode_realize_no_switch f <=>
    !st. (SND (f st)).cs_blocks = st.cs_blocks /\
         (SND (f st)).cs_current_bb = st.cs_current_bb
End

Theorem abi_decode_realize_no_switch_primitives:
  abi_decode_realize_no_switch (comp_return v) /\
  abi_decode_realize_no_switch (emit_op opc ops) /\
  abi_decode_realize_no_switch (emit_void opc ops)
Proof
  simp[abi_decode_realize_no_switch_def, comp_return_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def]
QED

Theorem abi_decode_realize_no_switch_bind:
  abi_decode_realize_no_switch f /\
  (!v. abi_decode_realize_no_switch (g v)) ==>
  abi_decode_realize_no_switch (comp_bind f g)
Proof
  rw[abi_decode_realize_no_switch_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> metis_tac[pairTheory.SND]
QED

Theorem abi_decode_realize_no_switch_ignore_bind:
  abi_decode_realize_no_switch f /\ abi_decode_realize_no_switch g ==>
  abi_decode_realize_no_switch (comp_ignore_bind f g)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule abi_decode_realize_no_switch_bind >> simp[]
QED

Theorem abi_decode_realize_no_switch_range:
  abi_decode_realize_no_switch (compile_abi_decode_range_check lo hi lim)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
    conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
  simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_addr:
  abi_decode_realize_no_switch (compile_abi_dec_addr base_op src)
Proof
  simp[compile_abi_dec_addr_def, abi_decode_realize_no_switch_primitives] >>
  IF_CASES_TAC >> simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_bytes:
  abi_decode_realize_no_switch
    (compile_abi_decode_to_buf dst src MLOAD base_op hi (DecBytestring n))
Proof
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_no_switch_primitives] >>
      ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
      >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
      irule abi_decode_realize_no_switch_ignore_bind >>
      simp[abi_decode_realize_no_switch_range,
           abi_decode_realize_no_switch_primitives]) >>
  gen_tac >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_addr] >> gen_tac >>
  ntac 3 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
    conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
  irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >>
  irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_no_switch_primitives] >>
      ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
      >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
      simp[abi_decode_realize_no_switch_range]) >>
  IF_CASES_TAC >- simp[abi_decode_realize_no_switch_primitives] >>
  ntac 4 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
    conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
  irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
  simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_getelem:
  abi_decode_realize_no_switch
    (compile_getelemptr_abi src dyn off MLOAD base_op hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
  IF_CASES_TAC >- simp[abi_decode_realize_no_switch_primitives] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_addr] >> gen_tac >>
  ntac 2 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
    conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
  irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_realize_no_switch_primitives] >>
      ntac 2 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
        conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
      simp[abi_decode_realize_no_switch_primitives]) >>
  simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_singleton:
  (!dst src base_op hi. abi_decode_realize_no_switch
    (compile_abi_decode_to_buf dst src MLOAD base_op hi ei)) ==>
  abi_decode_realize_no_switch
    (compile_abi_decode_complex_elems dst src MLOAD base_op hi [(ei,asz,msz)] ao vo)
Proof
  strip_tac >> rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_getelem] >> gen_tac >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
  irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
  >- simp[] >>
  rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_wrapper:
  (!dst src base_op hi. abi_decode_realize_no_switch
    (compile_abi_decode_to_buf dst src MLOAD base_op hi ei)) ==>
  abi_decode_realize_no_switch
    (compile_abi_decode_to_buf dst src MLOAD base_op hi
      (DecComplex dyn [(ei,asz,msz)]))
Proof
  strip_tac >> rewrite_tac[Once compile_abi_decode_to_buf_def] >>
  simp_tac pure_ss [LET_THM, listTheory.FOLDR] >> BETA_TAC >>
  IF_CASES_TAC >- simp[abi_decode_realize_no_switch_singleton] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
  irule abi_decode_realize_no_switch_ignore_bind >>
  simp[abi_decode_realize_no_switch_range, abi_decode_realize_no_switch_singleton]
QED

Theorem abi_decode_realize_no_switch_decoder:
  !k dst src base_op hi.
    abi_decode_realize_no_switch
      (compile_abi_decode_to_buf dst src MLOAD base_op hi
        (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)))
Proof
  Induct
  >- simp[abi_decode_size_probe_type_def, type_to_abi_dec_info_def,
          abi_decode_realize_no_switch_bytes] >>
  rpt gen_tac >>
  simp[abi_decode_size_probe_type_def, Once type_to_abi_dec_info_def] >>
  irule abi_decode_realize_no_switch_wrapper >> simp[]
QED

Theorem abi_decode_realize_no_switch_alloc:
  abi_decode_realize_no_switch (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >>
  simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_lower:
  abi_decode_realize_no_switch
    (lower_abi_decode data
      (type_to_abi_dec_info sf ce (abi_decode_size_probe_type k)) lo hi sz)
Proof
  rewrite_tac[lower_abi_decode_def] >>
  ntac 2 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
    conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
  irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
          simp[abi_decode_realize_no_switch_primitives]) >>
      ntac 5 (ho_match_mp_tac abi_decode_realize_no_switch_bind >>
        conj_tac >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac) >>
      simp[abi_decode_realize_no_switch_primitives]) >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_alloc] >> gen_tac >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
  irule abi_decode_realize_no_switch_ignore_bind >>
  simp[abi_decode_realize_no_switch_decoder, abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_chunks:
  !p bs off. abi_decode_realize_no_switch (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  rewrite_tac[Once compile_store_byte_chunks_def] >>
  simp_tac (srw_ss()) [LET_THM, abi_decode_realize_no_switch_primitives] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- simp[abi_decode_realize_no_switch_primitives] >> gen_tac >>
  irule abi_decode_realize_no_switch_ignore_bind >>
  simp[abi_decode_realize_no_switch_primitives] >>
  first_x_assum (mp_tac o SIMP_RULE (srw_ss()) []) >> simp[]
QED

Theorem abi_decode_realize_no_switch_literal:
  abi_decode_realize_no_switch
    (compile_literal_vv (BaseT (BytesT (Dynamic 32)))
      (BytesL (REPLICATE 32 0w)))
Proof
  simp_tac (srw_ss()) [compile_literal_vv_def] >>
  ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
  >- (simp[compile_bytelike_literal_def] >>
      ho_match_mp_tac abi_decode_realize_no_switch_bind >> conj_tac
      >- simp[abi_decode_realize_no_switch_alloc] >> gen_tac >>
      irule abi_decode_realize_no_switch_ignore_bind >> conj_tac
      >- simp[abi_decode_realize_no_switch_primitives] >>
      irule abi_decode_realize_no_switch_ignore_bind >>
      simp[abi_decode_realize_no_switch_chunks, abi_decode_realize_no_switch_primitives]) >>
  simp[abi_decode_realize_no_switch_primitives]
QED

Theorem abi_decode_realize_no_switch_result:
  abi_decode_realize_no_switch f /\ f st = (v,st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb
Proof
  simp[abi_decode_realize_no_switch_def] >> metis_tac[pairTheory.SND]
QED

Theorem abi_decode_realize_expr_no_switch:
  (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
    (abi_decode_realize_expr k) st)).cs_blocks = st.cs_blocks /\
  (SND (compile_expr ce (expr_type (abi_decode_realize_expr k))
    (abi_decode_realize_expr k) st)).cs_current_bb = st.cs_current_bb
Proof
  conj_tac >>
  (simp_tac (srw_ss()) [abi_decode_realize_expr_def, vyperASTTheory.expr_type_def,
    Once compile_expr_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  simp_tac (srw_ss()) [Once compile_type_builtin_dispatch_component_eq, LET_THM] >>
  simp[abi_decode_realize_arg_compile] >> pairarg_tac >>
  drule abi_decode_realize_literal_unwrap >>
  disch_then (qspec_then `ce` strip_assume_tac) >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def] >>
  qpat_x_assum `Abbrev _` (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at Any abi_decode_realize_no_switch_result >>
  simp[abi_decode_realize_no_switch_lower] >> strip_tac >>
  qpat_x_assum `lower_abi_decode _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  drule_at Any abi_decode_realize_no_switch_result >>
  simp[abi_decode_realize_no_switch_literal])
QED

Theorem abi_decode_realize_final_single_block:
  (abi_decode_realize_final ce k entry).cs_blocks = [] /\
  (abi_decode_realize_final ce k entry).cs_current_bb = entry
Proof
  mp_tac (Q.INST [`st` |-> `initial_compile_state entry`]
    abi_decode_realize_expr_no_switch) >>
  simp[abi_decode_realize_final_def, initial_compile_state_def]
QED
