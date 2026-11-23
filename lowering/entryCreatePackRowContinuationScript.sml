Theory entryCreatePackRowContinuation
Ancestors
  abiEncodeValuesCode abiEncoderChildCode emitHelperProps exprLoweringProps exprLowering
  fragExec compileEnv emitHelper venomInst venomExecSemantics list rich_list pair

(* The compiler's first emission, not the eventual endpoint of the tail,
   determines the installed instruction at the row exit. *)
Theorem pack_row_emit_fetch[local]:
  emit_op opc args en = (v,mid) /\ fn_has_code en mid func /\
  lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
  en.cs_next_id = i.inst_id
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `mid.cs_current_bb = en.cs_current_bb` by
    metis_tac[emit_op_extends,same_blocks_def] >>
  drule_all fn_has_code_same_block >> simp[] >> strip_tac >>
  gvs[mk_inst_def]
QED

Theorem pack_row_child_prefix_first[local]:
  abi_encode_child_prefix dst off cursor en = (ops,prepared) ==>
  ?head mid. emit_op ADD [dst;Lit (n2w off)] en = (head,mid) /\
             ci_mono mid prepared
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def,comp_bind_def,
                    comp_return_def,LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[ci_mono_emit_op,ci_mono_trans,SND]
QED

Theorem pack_row_tail_first[local]:
  rest <> [] /\
  compile_abi_encode_value_rows ce dst cursor off rest en = ((),last) ==>
  ?head mid. emit_op ADD [dst;Lit (n2w off)] en = (head,mid) /\
             ci_mono mid last
Proof
  Cases_on `rest` >> simp[] >> PairCases_on `h` >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields h1`
  >- (drule_all abi_encode_value_rows_dynamic_trace >> strip_tac >>
      drule pack_row_child_prefix_first >> strip_tac >>
      `ci_mono prepared ready /\ ci_mono ready encoded` by
        metis_tac[ci_mono_unwrap_value,cj 2 ci_mono_compile_abi_encode,SND] >>
      `ci_mono encoded advanced` by
        (drule abi_encode_child_suffix_shape >>
         strip_tac >> simp[ci_mono_def] >> irule cs_extends_same_block >>
         simp[] >> fs[inst_extends_def]) >>
      `ci_mono advanced last` by
        metis_tac[ci_mono_compile_abi_encode_value_rows,SND] >>
      rename1 `emit_op ADD [dst;Lit (n2w off)] en = (first,cut)` >>
      qexistsl_tac [`first`,`cut`] >> simp[] >> metis_tac[ci_mono_trans]) >>
  drule_all abi_encode_value_rows_static_trace >> strip_tac >>
  `ci_mono prepared ready /\ ci_mono ready stored /\ ci_mono stored last` by
    metis_tac[ci_mono_unwrap_value,ci_mono_compile_store_memory,
              ci_mono_compile_abi_encode_value_rows,SND] >>
  qexistsl_tac [`head`,`prepared`] >> simp[] >> metis_tac[ci_mono_trans]
QED

(* In abi_encode_values_to_buf_indexed's row callback, en is the
   successor of the singleton row and rest is DROP (SUC i) rows.
   The indexed callback gives both continuation compile equations.
   Row and MLOAD monotonicity give cs_extends en last and
   cs_extends last fin_cs; fn_has_code_split then restricts the enclosing
   encoder installation to en--fin_cs. In the empty case the load itself
   is the first instruction. *)
Theorem pack_row_installed_exit_fetch:
  compile_abi_encode_value_rows ce dst cursor off rest en = ((),last) /\
  emit_op MLOAD [cursor] last = (out,fin_cs) /\
  fn_has_code en fin_cs func ==>
  !bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
         en.cs_next_id <= i.inst_id
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `rest = []`
  >- (gvs[compile_abi_encode_value_rows_def,comp_return_def] >>
      drule_all pack_row_emit_fetch >> simp[]) >>
  drule_all pack_row_tail_first >> strip_tac >>
  `ci_mono en mid /\ ci_mono last fin_cs` by metis_tac[ci_mono_emit_op,SND] >>
  `fn_has_code en mid func` by
    metis_tac[ci_mono_def,ci_mono_trans,fn_has_code_split] >>
  drule_all pack_row_emit_fetch >> simp[]
QED
