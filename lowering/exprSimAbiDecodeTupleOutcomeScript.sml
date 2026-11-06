(* Heterogeneous tuple traversal.  Member hypotheses are structural recursive
   decoder hypotheses, not an assumption that the tuple has already run. *)
Theory exprSimAbiDecodeTupleOutcome
Ancestors
  exprSimAbiDecodeTupleSource exprSimAbiDecodeChildFrame
  exprSimAbiDecodeMemberReject exprSimAbiDecodeMemberOutcome
  abiDecoderMemberSetup abiDecoderAppend abiDecoderFiniteControl
  abiDecoderSiteEffect abiDecoderCoherence valueEncodingProps fragExec
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  words list rich_list arithmetic pred_set

Theorem abi_decode_complex_elems_nil:
  compile_abi_decode_complex_elems dst src opc base_op hi [] ao vo st = ((),st)
Proof
  simp[Once compile_abi_decode_to_buf_def, comp_return_def]
QED

Theorem abi_decode_complex_elems_cons_split:
  compile_abi_decode_complex_elems dst src opc base_op hi
    ((ei,asz,msz)::rest) ao vo st = ((),end_st) <=>
  ?ops prepared child_end.
    abi_decode_member_setup dst src opc base_op hi
      (dec_info_needs_offset ei) ao vo st = (ops,prepared) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) opc base_op hi ei
      prepared = ((),child_end) /\
    compile_abi_decode_complex_elems dst src opc base_op hi
      rest (ao+asz) (vo+msz) child_end = ((),end_st)
Proof
  rewrite_tac[abi_decode_complex_member_phases] >>
  simp_tac (srw_ss()) [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Definition abi_tuple_row_code_def:
  abi_tuple_row_code (ei,ty,tv,asz,msz) = (ei,asz,msz)
End

Definition abi_tuple_row_accepts_def:
  abi_tuple_row_accepts env bs ao (ei,ty,tv,asz,msz) v <=>
    let at = vyper_to_abi_type env ty;
        slice = abi_decode_member_bytes at bs (DROP ao bs)
    in vyper_decode_valid_enc at slice /\
       abi_to_vyper env ty (dec at slice) = SOME v
End

Definition abi_tuple_row_value_def:
  abi_tuple_row_value d vo (ei,ty,tv,asz,msz) v s <=>
    val_wf tv v /\ val_in_memory tv v (d+vo) s.vs_memory
End

Definition abi_tuple_rows_values_def:
  (abi_tuple_rows_values env bs ao vo d [] vs s <=> vs = []) /\
  (abi_tuple_rows_values env bs ao vo d ((ei,ty,tv,asz,msz)::rows) vs s <=>
    ?v tail. vs = v::tail /\
      abi_tuple_row_accepts env bs ao (ei,ty,tv,asz,msz) v /\
      abi_tuple_row_value d vo (ei,ty,tv,asz,msz) v s /\
      abi_tuple_rows_values env bs (ao+asz) (vo+msz) d rows tail s)
End

Theorem abi_decode_complex_elems_extends:
  compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo st = ((),last) ==>
  cs_extends st last
Proof
  metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def]
QED

Theorem abi_decode_complex_elems_child_context:
  abi_decode_member_setup dst src MLOAD base_op hi
    (dec_info_needs_offset ei) ao vo st = (ops,prepared) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) MLOAD base_op hi ei
    prepared = ((),child_end) /\
  compile_abi_decode_complex_elems dst src MLOAD base_op hi
    rest (ao+asz) (vo+msz) child_end = ((),last) /\
  fn_has_code st last func ==>
  fn_has_code st child_end func /\ fn_has_code child_end last func /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\
  cs_extends st child_end /\ cs_extends child_end last
Proof
  strip_tac >>
  `cs_extends st prepared` by
    (drule abi_decode_member_setup_shape >>
     simp[inst_extends_def, cs_extends_def]) >>
  `cs_extends prepared child_end` by metis_tac[cs_extends_abi_decode] >>
  `cs_extends child_end last` by metis_tac[abi_decode_complex_elems_extends] >>
  `cs_extends st child_end` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  metis_tac[fn_has_code_split]
QED

Theorem abi_tuple_rows_values_length:
  !rows env bs ao vo d vs s.
    abi_tuple_rows_values env bs ao vo d rows vs s ==> LENGTH vs = LENGTH rows
Proof
  Induct >- simp[abi_tuple_rows_values_def] >>
  gen_tac >> PairCases_on `h` >> simp[abi_tuple_rows_values_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Definition abi_tuple_row_abi_width_def:
  abi_tuple_row_abi_width (ei,ty,tv,asz,msz) = asz
End

Definition abi_tuple_row_mem_width_def:
  abi_tuple_row_mem_width (ei,ty,tv,asz,msz) = msz
End

Definition abi_tuple_row_cursor_def:
  abi_tuple_row_cursor width rows off i = off + SUM (MAP width (TAKE i rows))
End

Theorem abi_tuple_row_cursor_zero[simp]:
  abi_tuple_row_cursor width rows off 0 = off
Proof
  simp[abi_tuple_row_cursor_def]
QED

Theorem abi_tuple_row_cursor_cons[simp]:
  abi_tuple_row_cursor width (r::rows) off (SUC i) =
  abi_tuple_row_cursor width rows (off+width r) i
Proof
  `SUC i <> 0` by decide_tac >>
  asm_simp_tac std_ss [abi_tuple_row_cursor_def, TAKE_def, MAP, SUM, ADD_ASSOC]
QED

Theorem abi_tuple_rows_values_indexed:
  !rows env bs ao vo d vs s.
  abi_tuple_rows_values env bs ao vo d rows vs s <=>
    LENGTH vs = LENGTH rows /\
    (!i. i < LENGTH rows ==>
      abi_tuple_row_accepts env bs
        (abi_tuple_row_cursor abi_tuple_row_abi_width rows ao i) (EL i rows) (EL i vs) /\
      abi_tuple_row_value d
        (abi_tuple_row_cursor abi_tuple_row_mem_width rows vo i) (EL i rows) (EL i vs) s)
Proof
  Induct >- simp[abi_tuple_rows_values_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> Cases_on `vs`
  >- simp[abi_tuple_rows_values_def] >>
  simp_tac bool_ss [abi_tuple_rows_values_def] >>
  asm_simp_tac (srw_ss()) [] >>
  eq_tac
  >- (strip_tac >> conj_tac >- simp[] >>
      gen_tac >> strip_tac >> Cases_on `i` >>
      gvs[abi_tuple_row_abi_width_def, abi_tuple_row_mem_width_def]) >>
  strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >> gen_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp[abi_tuple_row_abi_width_def, abi_tuple_row_mem_width_def]
QED

