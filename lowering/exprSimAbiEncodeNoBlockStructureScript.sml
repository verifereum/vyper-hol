Theory exprSimAbiEncodeNoBlockStructure
Ancestors
  abiEncoder abiEncoderAppend abiEncoderChildCode abiEncoderAddressReach
  abiDecoderAppend fragExec compileEnv emitHelper emitHelperProps
  exprLoweringProps list rich_list words context arithmetic

Theorem abi_encode_no_block_split:
  cs_extends st mid /\ cs_extends mid en /\ st.cs_blocks = en.cs_blocks ==>
  st.cs_blocks = mid.cs_blocks /\ mid.cs_blocks = en.cs_blocks
Proof
  simp_tac bool_ss [cs_extends_def] >> strip_tac >>
  `LENGTH new = 0 /\ LENGTH new' = 0` by
    (qpat_x_assum `st.cs_blocks = en.cs_blocks` mp_tac >>
     asm_rewrite_tac[] >> disch_then (mp_tac o AP_TERM ``LENGTH:basic_block list -> num``) >>
     simp[] >> strip_tac >>
     `LENGTH new = 0 /\ LENGTH new' = 0` by decide_tac >> fs[]) >> gvs[]
QED

Theorem abi_encode_static_child_no_block:
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  st.cs_blocks = en.cs_blocks ==>
  ?head ready. emit_op ADD [dst;Lit (n2w ho)] st = (head,ready) /\
    compile_abi_encode_to_buf head src ei ready = (out,en) /\
    st.cs_blocks = ready.cs_blocks /\ ready.cs_blocks = en.cs_blocks
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  drule_all abi_encode_no_block_split >> strip_tac >> metis_tac[]
QED

Theorem abi_encode_dynamic_child_no_block:
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  st.cs_blocks = en.cs_blocks ==>
  ?ops ready len mid.
    abi_encode_child_prefix dst ho dp st = (ops,ready) /\
    compile_abi_encode_to_buf (SND (SND ops)) src ei ready = (len,mid) /\
    abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len mid = (out,en) /\
    st.cs_blocks = ready.cs_blocks /\ ready.cs_blocks = mid.cs_blocks /\
    mid.cs_blocks = en.cs_blocks
Proof
  strip_tac >> drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >> metis_tac[]
QED

Theorem abi_encode_member_cons_no_block:
  compile_abi_encode_complex_elems dst src ((ei,az,ms,dyn)::rest) so ho dp st = (out,en) /\
  st.cs_blocks = en.cs_blocks ==>
  ?child_src ready len mid.
    emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
    compile_abi_encode_child dst child_src ei dyn ho dp ready = (len,mid) /\
    compile_abi_encode_complex_elems dst src rest (so+ms) (ho+az) dp mid = (out,en) /\
    st.cs_blocks = ready.cs_blocks /\ ready.cs_blocks = mid.cs_blocks /\
    mid.cs_blocks = en.cs_blocks
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `emit_op ADD _ st = (child_src,ready)` >>
  rename1 `compile_abi_encode_child dst child_src ei dyn ho dp ready = (len,mid)` >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule cs_extends_abi_encode_child >> strip_tac >>
  `cs_extends mid en` by
    metis_tac[cj 3 cs_appends_abi_encode_mutual, cs_appends_def] >>
  `cs_extends st mid` by metis_tac[cs_extends_trans] >>
  drule_all abi_encode_no_block_split >> strip_tac >>
  metis_tac[abi_encode_no_block_split]
QED

Theorem abi_encode_dyn_static_loop_blocks:
  compile_abi_encode_dyn_static_loop dst src ei az ms len st = (out,en) ==>
  LENGTH st.cs_blocks < LENGTH en.cs_blocks
Proof
  simp_tac bool_ss [compile_abi_encode_dyn_static_loop_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `!a b out dst src. compile_abi_encode_static_info dst src ei a = (out,b) ==>
    cs_extends a b` by
    metis_tac[cs_appends_abi_encode_static_info, cs_appends_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, compile_alloc_buffer_def,
    fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  fs[cs_extends_def] >> simp[]
QED

Theorem abi_encode_dyn_loop_blocks:
  compile_abi_encode_dyn_loop dst src ei az ms len st = (out,en) ==>
  LENGTH st.cs_blocks < LENGTH en.cs_blocks
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, compile_alloc_buffer_def,
    fresh_var_def, fresh_id_def, fresh_label_def, emit_def, new_block_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  fs[cs_extends_def] >> simp[]
QED

Theorem abi_encode_dyn_array_has_blocks:
  compile_abi_encode_to_buf dst src (AbiDynArray ei az ms dyn) st = (out,en) ==>
  st.cs_blocks <> en.cs_blocks
Proof
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `dyn` >> gvs[] >>
  imp_res_tac abi_encode_dyn_loop_blocks >>
  imp_res_tac abi_encode_dyn_static_loop_blocks >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, compile_alloc_buffer_def,
    fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> gvs[]
QED

Theorem abi_encode_static_complex_no_block:
  infos <> [] /\ ~EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,en) /\
  st.cs_blocks = en.cs_blocks ==>
  ?ignored. compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st = (ignored,en)
Proof
  Cases_on `infos` >- simp[] >> strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM] >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

Theorem abi_encode_dynamic_complex_no_block:
  infos <> [] /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,en) /\
  st.cs_blocks = en.cs_blocks ==>
  ?alloc allocated ready ignored mid.
    compile_alloc_buffer 32 st = (alloc,allocated) /\
    emit_void MSTORE [alloc.buf_operand;
      Lit (n2w (SUM (MAP (\(_,az,_,_). az) infos)))] allocated = ((),ready) /\
    compile_abi_encode_complex_elems dst src infos 0 0 alloc.buf_operand ready = (ignored,mid) /\
    emit_op MLOAD [alloc.buf_operand] mid = (out,en) /\
    st.cs_blocks = ready.cs_blocks /\ ready.cs_blocks = mid.cs_blocks /\
    mid.cs_blocks = en.cs_blocks
Proof
  Cases_on `infos` >- simp[] >> strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM] >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_alloc_buffer 32 st = (alloc,allocated)` >>
  rename1 `emit_void MSTORE _ allocated = ((),ready)` >>
  rename1 `emit_op MLOAD _ mid = (out,en)` >>

  gvs[emit_op_def, emit_void_def, emit_inst_def, compile_alloc_buffer_def,
    fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM]
QED
