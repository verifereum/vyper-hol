(* Structural boundaries for external-call compilation. *)
Theory bodyIntCallExternalLabels
Ancestors
  bodyIntCallExprLabels bodyIntCallAbiLabels bodyIntCallBuiltinLabels
  builtinSimple exprLowering
  bodyIntCallContextLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  compileEnv list pred_set

Theorem compiler_block_tail_select:
  compiler_block_tail (compile_select cond_op then_op else_op)
Proof
  rewrite_tac[compile_select_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_select:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_select cond_op then_op else_op)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_select_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_extcodesize_check:
  compiler_block_tail (compile_extcodesize_check addr)
Proof
  rewrite_tac[compile_extcodesize_check_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_extcodesize_check:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_extcodesize_check addr)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_extcodesize_check_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_return_value_decode:
  compiler_block_tail (compile_return_value_decode buf lo hi)
Proof
  rewrite_tac[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_select] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_return_value_decode:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_return_value_decode buf lo hi)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_return_value_decode_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives, compiler_label_hoare_select] >>
       gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_extcall_store_values:
  !vals off. compiler_block_tail (compile_extcall_store_values cenv vals buf off)
Proof
  Induct >> simp[compile_extcall_store_values_def, compiler_block_tail_primitives] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, LET_THM, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_unwrap_value] >>
       gen_tac >> BETA_TAC) >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, compiler_block_tail_store_bytestring]
QED

Theorem compiler_label_hoare_extcall_store_values:
  !vals off origin pending.
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_extcall_store_values cenv vals buf off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- simp[compile_extcall_store_values_def, compiler_label_hoare_typed_primitives] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, LET_THM, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_unwrap_value] >>
       gen_tac >> BETA_TAC) >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_alloc_buffer:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_alloc_buffer sz) (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_alloc_buffer_label_bounds]
QED

Theorem compiler_block_tail_materialize_vv:
  compiler_block_tail (compile_materialize_vv cenv ty vv)
Proof
  rewrite_tac[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_unwrap_value, compiler_block_tail_store_memory] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_materialize_vv:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_materialize_vv cenv ty vv)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_materialize_vv_def, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_alloc_buffer, compiler_label_hoare_unwrap_value,
               compiler_label_hoare_store_memory] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_ext_call_kwarg:
  (!ty. compiler_block_tail (cfn cenv ty e)) ==>
  compiler_block_tail (compile_ext_call_kwarg cfn cenv return_type k e)
Proof
  strip_tac >> rewrite_tac[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
      gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
      simp[compiler_block_tail_materialize_vv, compiler_block_tail_primitives]) >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_lower_value, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_ext_call_kwarg:
  (!ty origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out)) ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ext_call_kwarg cfn cenv return_type k e)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[compile_ext_call_kwarg_def] >> IF_CASES_TAC
  >- (irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
      gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_materialize_vv, compiler_label_hoare_typed_primitives]) >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_lower_value, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_ext_call_kwargs:
  !es ks. EVERY (\e. !ty. compiler_block_tail (cfn cenv ty e)) es ==>
  compiler_block_tail (compile_ext_call_kwargs cfn cenv return_type ks es)
Proof
  Induct >- (Cases >> simp[compile_ext_call_kwargs_def, compiler_block_tail_primitives]) >>
  gen_tac >> Cases_on `ks` >>
  simp[compile_ext_call_kwargs_def, compiler_block_tail_primitives] >> strip_tac >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_ext_call_kwarg >> simp[]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> PairCases_on `x` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_ext_call_kwargs:
  !es ks. EVERY (\e. !ty origin pending.
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn cenv ty e) (\r out. compiler_label_reservation origin pending out)) es ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_ext_call_kwargs cfn cenv return_type ks es)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct
  >- (Cases >> simp[compile_ext_call_kwargs_def, compiler_label_hoare_typed_primitives]) >>
  gen_tac >> Cases_on `ks` >>
  simp[compile_ext_call_kwargs_def, compiler_label_hoare_typed_primitives] >>
  strip_tac >> rpt gen_tac >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_ext_call_kwarg >> simp[]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> PairCases_on `x` >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_default_return_path:
  compiler_block_tail
    (compile_default_return_path ce rt dt buf result def addr skip lo hi info)
Proof
  rewrite_tac[compile_default_return_path_def, comp_ignore_bind_def] >>
  Cases_on `skip` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_store_memory,
               compiler_block_tail_extcodesize_check,
               compiler_block_tail_return_value_decode,
               compiler_block_tail_abi_decode_to_buf] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_default_return_path:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_default_return_path ce rt dt buf result def addr skip lo hi info)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_default_return_path_def, comp_ignore_bind_def] >>
  ntac 2 (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC) >>
  ntac 3 (irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  gvs[] >> Cases_on `skip` >> simp[] >>
  ntac 3
    (rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- simp[compiler_label_hoare_context_primitives,
              compiler_label_hoare_typed_primitives, compiler_label_hoare_store_memory,
              compiler_label_hoare_extcodesize_check, compiler_label_hoare_return_value_decode,
              compiler_label_hoare_abi_decode_to_buf] >> gen_tac >> BETA_TAC) >>
     ho_match_mp_tac compiler_label_hoare_new_block_bind >> conj_tac >- simp[] >>
     gen_tac >> BETA_TAC >> simp[DELETE_INSERT, DELETE_NON_ELEMENT_RWT]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_external_call_kwargs:
  compiler_block_tail
    (compile_external_call_kwargs ce addr vals tys am aa mid ra lo rm
      static value gas skip has_default def rt dt enc_info dec_info)
Proof
  rewrite_tac[compile_external_call_kwargs_def, LET_THM, comp_ignore_bind_def,
              comp_bind_assoc] >>
  Cases_on `vals = []` >> Cases_on `ra = 0` >> Cases_on `skip` >>
  Cases_on `static` >> Cases_on `has_default` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_extcall_store_values,
               compiler_block_tail_abi_encode_to_buf,
               compiler_block_tail_extcodesize_check,
               compiler_block_tail_default_return_path,
               compiler_block_tail_return_value_decode,
               compiler_block_tail_abi_decode_to_buf] >> gen_tac >> BETA_TAC >>
       simp[comp_bind_assoc]) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_default_return_path]
QED

Theorem compiler_label_hoare_external_call_kwargs:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_external_call_kwargs ce addr vals tys am aa mid ra lo rm
      static value gas skip has_default def rt dt enc_info dec_info)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_external_call_kwargs_def, LET_THM, comp_ignore_bind_def,
              comp_bind_assoc] >>
  Cases_on `vals = []` >> Cases_on `ra = 0` >> Cases_on `skip` >>
  Cases_on `static` >> Cases_on `has_default` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives,
               compiler_label_hoare_alloc_buffer, compiler_label_hoare_extcall_store_values,
               compiler_label_hoare_abi_encode_to_buf, compiler_label_hoare_extcodesize_check] >>
       gen_tac >> BETA_TAC >> simp[comp_bind_assoc]) >>
  ntac 2 (irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  gvs[] >>
  ntac 2
    (rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- simp[compiler_label_hoare_context_primitives,
              compiler_label_hoare_typed_primitives, compiler_label_hoare_alloc_buffer] >>
      gen_tac >> BETA_TAC >> simp[comp_bind_assoc]) >>
     ho_match_mp_tac compiler_label_hoare_new_block_bind >> conj_tac >- simp[] >>
     gen_tac >> BETA_TAC >> simp[DELETE_INSERT, DELETE_NON_ELEMENT_RWT]) >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
    >- simp[compiler_label_hoare_alloc_buffer, compiler_label_hoare_return_value_decode,
            compiler_label_hoare_abi_decode_to_buf] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_default_return_path]
QED

Theorem compile_call_extcall_action[local]:
  compile_call cfn ce rt ty (ExtCall static skip (fn,ats,ret) opts) args dflt =
  (\st. case args of
     [] => let (_,out) = emit_inst INVALID [] [] st in (StackValue rt (Lit 0w),out)
   | addr::rest =>
     let (addr_op,s1) = lower_value cfn ce (BaseT AddressT) addr st in
     let fargs = TAKE (LENGTH ats) rest in
     let kes = DROP (LENGTH ats) rest in
     let (avs,s2) = compile_multi_vvs cfn ce fargs s1 in
     let ((vo,go,do_),s3) = compile_ext_call_kwargs cfn ce ret opts kes s2 in
     let value_op = case vo of SOME v => v | NONE => Lit 0w in
     let cats = ext_call_arg_types ce ats fargs in
     let am = SUM (MAP (type_memory_bytes ce) cats) in
     let aa = abi_size_bound ce.ce_struct_fields (TupleT cats) in
     let ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT cats) in
     let wr = if needs_external_call_wrap ret then TupleT [ret] else ret in
     let ra = abi_size_bound ce.ce_struct_fields wr in
     let lo = abi_static_size ce.ce_struct_fields wr in
     let rm = type_memory_bytes ce ret in
     let mid = ce.ce_method_id fn ats in
     let (hd,def,dt) = case do_ of SOME (d,t) => (T,d,t) | NONE => (F,Lit 0w,ret) in
     let (gas,s4) = case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3 in
     let di = type_to_abi_dec_info ce.ce_struct_fields ce wr in
     let (res,s5) = compile_external_call_kwargs ce addr_op
       (MAP2 ext_call_arg_value cats avs) cats am aa mid ra lo rm static value_op gas
       skip hd def ret dt ei di s4 in
     if ra = 0 then (StackValue rt res,s5)
     else (LocatedValue rt (mk_ptr res LocMemory),s5))
Proof
  simp[FUN_EQ_THM, compile_call_def]
QED

Theorem compiler_uncurried_bind_eq:
  (\s. k (m s)) = comp_bind m (\x s. k (x,s))
Proof
  simp[FUN_EQ_THM, comp_bind_def] >> qx_gen_tac `s` >> Cases_on `m s` >> simp[]
QED

Theorem compiler_block_tail_uncurried_bind:
  compiler_block_tail m /\ (!x. compiler_block_tail (\s. k (x,s))) ==>
  compiler_block_tail (\s. k (m s))
Proof
  strip_tac >> once_rewrite_tac[compiler_uncurried_bind_eq] >>
  irule compiler_block_tail_bind >> simp[]
QED

Theorem compiler_label_hoare_uncurried_bind:
  compiler_label_hoare P m (\x s. P s) /\
  (!x. compiler_label_hoare P (\s. k (x,s)) R) ==>
  compiler_label_hoare P (\s. k (m s)) R
Proof
  simp[compiler_label_hoare_def] >> rpt strip_tac >>
  Cases_on `m s` >> gvs[] >> metis_tac[]
QED

Theorem compiler_block_tail_extcall:
  (!e ce t. MEM e args ==> compiler_block_tail (cfn ce t e)) ==>
  compiler_block_tail (compile_call cfn ce rt ty (ExtCall static skip (fn,ats,ret) opts) args dflt)
Proof
  strip_tac >> rewrite_tac[compile_call_extcall_action] >>
  namedCases_on `args` ["", "addr rest"] >> simp[]
  >- (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
      >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[compiler_block_tail_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_block_tail_def]) >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_multi_vvs >>
      gvs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_block_tail_uncurried_bind >> reverse conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >> irule compiler_block_tail_ext_call_kwargs >>
      gvs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  Cases_on `x2` >> simp[] >>
  TRY (qmatch_goalsub_rename_tac `case p of (d,t) => (T,d,t)` >>
       PairCases_on `p` >> simp[]) >>
  Cases_on `x1` >> simp[] >>
  rpt (ho_match_mp_tac compiler_block_tail_pair_bind >> conj_tac
    >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
        simp[compiler_block_tail_primitives, compiler_block_tail_external_call_kwargs]) >>
    gen_tac >> BETA_TAC) >>
  qmatch_goalsub_abbrev_tac `if test then _ else _` >>
  Cases_on `test` >> simp[compiler_block_tail_def]
QED

Theorem compiler_label_hoare_extcall:
  (!e ce t origin pending. MEM e args ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (cfn ce t e) (\r out. compiler_label_reservation origin pending out)) ==>
  !origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_call cfn ce rt ty (ExtCall static skip (fn,ats,ret) opts) args dflt)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[compile_call_extcall_action] >>
  namedCases_on `args` ["", "addr rest"] >> simp[]
  >- (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
      >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
          simp[compiler_label_hoare_context_primitives]) >>
      gen_tac >> BETA_TAC >> simp[compiler_label_hoare_def]) >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >> irule compiler_label_hoare_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >> irule compiler_label_hoare_multi_vvs >>
      gvs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_uncurried_bind >> reverse conj_tac
  >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >> irule compiler_label_hoare_ext_call_kwargs >>
      gvs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  gen_tac >> PairCases_on `x` >> simp[] >>
  Cases_on `x2` >> simp[] >>
  TRY (qmatch_goalsub_rename_tac `case p of (d,t) => (T,d,t)` >>
       PairCases_on `p` >> simp[]) >>
  Cases_on `x1` >> simp[] >>
  rpt (ho_match_mp_tac compiler_label_hoare_pair_bind >> conj_tac
    >- (CONV_TAC (RATOR_CONV (RAND_CONV (DEPTH_CONV ETA_CONV))) >>
        simp[compiler_label_hoare_context_primitives, compiler_label_hoare_external_call_kwargs]) >>
    gen_tac >> BETA_TAC) >>
  qmatch_goalsub_abbrev_tac `if test then _ else _` >>
  Cases_on `test` >> simp[compiler_label_hoare_def]
QED
