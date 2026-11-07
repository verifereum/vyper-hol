Theory exprSimAbiEncodeNoBlockFrame
Ancestors
  exprSimAbiEncodeNoBlockSafety exprSimAbiEncodeObliviousFacts
  exprSimAbiEncodeObliviousCode exprSimAbiEncodeObliviousContext
  exprLoweringProps compileEnv emitHelperProps abiEncoder builtinAbi
  list rich_list sorting venomInst fragExec exprSimAbiGasBridge

Definition abi_encode_straight_ops_def:
  abi_encode_straight_ops P m <=>
    !a x b. m a = (x,b) ==> entry_shape a b /\
      (b.cs_blocks = a.cs_blocks ==> EVERY (\i. P i.inst_opcode) (frag_code a b))
End

Theorem abi_encode_straight_return:
  abi_encode_straight_ops P (comp_return x)
Proof
  simp[abi_encode_straight_ops_def, comp_return_def, entry_shape_refl,
       frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem abi_encode_straight_bind:
  abi_encode_straight_ops P m /\ (!x. abi_encode_straight_ops P (f x)) ==>
  abi_encode_straight_ops P (comp_bind m f)
Proof
  rw[abi_encode_straight_ops_def, comp_bind_def] >>
  Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac
  >- metis_tac[entry_shape_trans] >>
  `LENGTH a.cs_blocks <= LENGTH r.cs_blocks /\
   LENGTH r.cs_blocks <= LENGTH b.cs_blocks` by
    (fs[entry_shape_def] >> gvs[] >> simp[]) >>
  `r.cs_blocks = a.cs_blocks /\ b.cs_blocks = r.cs_blocks` by
    (fs[entry_shape_def] >> gvs[] >> fs[]) >>
  drule_all frag_code_compose_perm >> strip_tac >>
  drule PERM_EVERY >> disch_then (irule o iffRL) >> simp[]
QED

Theorem abi_encode_straight_ignore_bind:
  abi_encode_straight_ops P m /\ abi_encode_straight_ops P n ==>
  abi_encode_straight_ops P (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def, abi_encode_straight_bind]
QED

Theorem abi_encode_straight_code:
  code_action P m ==> abi_encode_straight_ops P m
Proof
  rw[code_action_def, code_step_def, abi_encode_straight_ops_def] >> metis_tac[]
QED

Theorem abi_encode_straight_emit_op:
  P opc ==> abi_encode_straight_ops P (emit_op opc ops)
Proof
  strip_tac >> irule abi_encode_straight_code >> simp[code_action_emit_op]
QED

Theorem abi_encode_straight_emit_void:
  P opc ==> abi_encode_straight_ops P (emit_void opc ops)
Proof
  strip_tac >> irule abi_encode_straight_code >> simp[code_action_emit_void]
QED

Theorem abi_encode_straight_alloc:
  P ALLOCA ==> abi_encode_straight_ops P (compile_alloc_buffer sz)
Proof
  strip_tac >> irule abi_encode_straight_code >> simp[code_action_alloc_buffer]
QED

Theorem abi_encode_straight_grows:
  code_action Q m /\ enc_grows_action m ==> abi_encode_straight_ops P m
Proof
  rw[abi_encode_straight_ops_def, enc_grows_action_def, code_action_def, code_step_def] >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem abi_encode_whitelist_static_loop:
  abi_encode_straight_ops P (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  irule abi_encode_straight_grows >>
  conj_tac >- simp[enc_grows_static_loop] >>
  qexists `enc_safe_opcode` >> simp[code_action_static_loop]
QED

Theorem abi_encode_whitelist_dyn_loop:
  abi_encode_straight_ops P (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  irule abi_encode_straight_grows >>
  conj_tac >- simp[enc_grows_dyn_loop] >>
  qexists `enc_safe_opcode` >> simp[code_action_encoder_mutual]
QED

Definition abi_encode_raw_opcode_def:
  abi_encode_raw_opcode opc <=> MEM opc [ALLOCA;ADD;AND;MLOAD;MSTORE;MCOPY]
End

Theorem abi_encode_whitelist_static:
  abi_encode_straight_ops abi_encode_raw_opcode (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, abi_encode_straight_bind,
    abi_encode_straight_ignore_bind, abi_encode_straight_emit_op,
    abi_encode_straight_emit_void, abi_encode_straight_return, abi_encode_raw_opcode_def]
QED

Theorem abi_encode_whitelist_static_info:
  abi_encode_straight_ops abi_encode_raw_opcode (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    abi_encode_whitelist_static, abi_encode_straight_return, abi_encode_straight_ignore_bind,
    abi_encode_straight_emit_void, abi_encode_raw_opcode_def]
QED

Theorem abi_encode_whitelist_mutual:
  (!dst ptr ei dyn so dp.
    abi_encode_straight_ops abi_encode_raw_opcode (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei.
    abi_encode_straight_ops abi_encode_raw_opcode (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    abi_encode_straight_ops abi_encode_raw_opcode (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    abi_encode_straight_ops abi_encode_raw_opcode (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`abi_encode_straight_ops _ (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- simp[abi_encode_whitelist_dyn_loop] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[] >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      simp[abi_encode_straight_bind, abi_encode_straight_ignore_bind,
           abi_encode_straight_emit_op, abi_encode_straight_emit_void,
           abi_encode_straight_return, abi_encode_raw_opcode_def] >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_bind >> simp[] >> gen_tac >>
      simp[abi_encode_straight_bind, abi_encode_straight_ignore_bind,
           abi_encode_straight_emit_op, abi_encode_straight_emit_void,
           abi_encode_straight_return, abi_encode_raw_opcode_def])
  >- simp[abi_encode_whitelist_static]
  >- (irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_ignore_bind >> simp[abi_encode_straight_emit_void, abi_encode_raw_opcode_def] >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      simp[abi_encode_straight_bind, abi_encode_straight_ignore_bind,
           abi_encode_straight_emit_op, abi_encode_straight_emit_void, abi_encode_raw_opcode_def])
  >- simp[abi_encode_straight_ignore_bind, abi_encode_straight_emit_void,
          abi_encode_straight_return, abi_encode_raw_opcode_def]
  >- (Cases_on `elem_is_dyn` >> gvs[] >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_alloc, abi_encode_raw_opcode_def] >> gen_tac >>
      simp[] >> irule abi_encode_straight_ignore_bind >> simp[abi_encode_straight_emit_void, abi_encode_raw_opcode_def] >>
      irule abi_encode_straight_bind >> simp[abi_encode_straight_emit_op, abi_encode_raw_opcode_def] >> gen_tac >>
      irule abi_encode_straight_ignore_bind >> simp[abi_encode_straight_emit_void, abi_encode_raw_opcode_def] >>
      irule abi_encode_straight_bind >> simp[abi_encode_whitelist_static_loop] >> gen_tac >>
      simp[abi_encode_straight_bind, abi_encode_straight_ignore_bind,
           abi_encode_straight_emit_void, abi_encode_straight_emit_op, abi_encode_raw_opcode_def])
  >- simp[abi_encode_straight_return]
  >- (IF_CASES_TAC >> gvs[] >> simp[abi_encode_straight_bind,
        abi_encode_straight_ignore_bind, abi_encode_straight_alloc,
        abi_encode_straight_emit_void, abi_encode_straight_emit_op,
        abi_encode_straight_return, abi_encode_raw_opcode_def])
  >- simp[abi_encode_straight_return] >>
  simp[abi_encode_straight_bind, abi_encode_straight_ignore_bind,
       abi_encode_straight_emit_op, abi_encode_raw_opcode_def]
QED

Theorem abi_encode_no_block_opcodes:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\ st.cs_blocks = en.cs_blocks ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;AND;MLOAD;MSTORE;MCOPY]) (emitted_insts st en)
Proof
  strip_tac >> mp_tac (cj 2 abi_encode_whitelist_mutual) >>
  simp_tac bool_ss [abi_encode_straight_ops_def] >>
  disch_then drule >> strip_tac >>
  gvs[frag_code_def, emitted_blocks_def, abi_encode_raw_opcode_def]
QED
