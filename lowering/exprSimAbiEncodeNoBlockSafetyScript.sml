Theory exprSimAbiEncodeNoBlockSafety
Ancestors
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousContext exprLoweringProps compileEnv
  emitHelperProps context list rich_list sorting venomInst fragExec exprSimAbiGasBridge
  abiEncoder builtinAbi

Definition enc_straight_action_def:
  enc_straight_action m <=>
    !a x b. m a = (x,b) ==>
      entry_shape a b /\
      (b.cs_blocks = a.cs_blocks ==>
        EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
          (frag_code a b))
End

Theorem enc_entry_blocks_length[local]:
  entry_shape a b ==> LENGTH a.cs_blocks <= LENGTH b.cs_blocks
Proof
  rw[entry_shape_def] >> simp[]
QED

Theorem enc_entry_equal_length[local]:
  entry_shape a b /\ LENGTH a.cs_blocks = LENGTH b.cs_blocks ==>
  b.cs_blocks = a.cs_blocks
Proof
  rw[entry_shape_def] >> gvs[]
QED

Theorem enc_straight_action_return:
  enc_straight_action (comp_return x)
Proof
  simp[enc_straight_action_def, comp_return_def, entry_shape_refl,
       frag_code_def, emitted_blocks_def, emitted_insts_def]
QED

Theorem enc_straight_action_bind:
  enc_straight_action m /\ (!x. enc_straight_action (f x)) ==>
  enc_straight_action (comp_bind m f)
Proof
  rw[enc_straight_action_def, comp_bind_def] >>
  Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- metis_tac[entry_shape_trans] >>
  `LENGTH a.cs_blocks <= LENGTH r.cs_blocks /\
   LENGTH r.cs_blocks <= LENGTH b.cs_blocks` by
    metis_tac[enc_entry_blocks_length] >>
  `r.cs_blocks = a.cs_blocks /\ b.cs_blocks = r.cs_blocks` by
    (conj_tac >> irule enc_entry_equal_length >> simp[] >> gvs[] >> decide_tac) >>
  drule_all frag_code_compose_perm >> strip_tac >>
  drule PERM_EVERY >> disch_then (irule o iffRL) >> simp[]
QED

Theorem enc_straight_action_ignore_bind:
  enc_straight_action m /\ enc_straight_action n ==>
  enc_straight_action (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def, enc_straight_action_bind]
QED

Theorem enc_straight_action_code:
  code_action (\opc. opc <> INVOKE /\ ~is_terminator opc) m ==>
  enc_straight_action m
Proof
  rw[code_action_def, code_step_def, enc_straight_action_def] >> metis_tac[]
QED

Theorem enc_straight_action_fresh_var:
  enc_straight_action fresh_var
Proof
  irule enc_straight_action_code >> simp[code_action_fresh_var]
QED

Theorem enc_straight_action_fresh_label:
  enc_straight_action (fresh_label suffix)
Proof
  irule enc_straight_action_code >> simp[code_action_fresh_label]
QED

Theorem enc_straight_action_emit_inst:
  opc <> INVOKE /\ ~is_terminator opc ==>
  enc_straight_action (emit_inst opc ops outs)
Proof
  strip_tac >> irule enc_straight_action_code >> simp[code_action_emit_inst]
QED

Theorem enc_straight_action_emit_op:
  opc <> INVOKE /\ ~is_terminator opc ==>
  enc_straight_action (emit_op opc ops)
Proof
  strip_tac >> irule enc_straight_action_code >> simp[code_action_emit_op]
QED

Theorem enc_straight_action_emit_void:
  opc <> INVOKE /\ ~is_terminator opc ==>
  enc_straight_action (emit_void opc ops)
Proof
  strip_tac >> irule enc_straight_action_code >> simp[code_action_emit_void]
QED

Theorem enc_straight_action_alloc_buffer:
  enc_straight_action (compile_alloc_buffer sz)
Proof
  irule enc_straight_action_code >> simp[code_action_alloc_buffer, is_terminator_def]
QED

Theorem enc_straight_action_new_block:
  enc_straight_action (new_block l)
Proof
  irule enc_straight_action_code >> simp[code_action_new_block]
QED

Definition enc_grows_action_def:
  enc_grows_action m <=>
    !a x b. m a = (x,b) ==> LENGTH a.cs_blocks < LENGTH b.cs_blocks
End

Theorem enc_code_blocks[local]:
  code_action P m /\ m a = (x,b) ==>
  LENGTH a.cs_blocks <= LENGTH b.cs_blocks
Proof
  rw[code_action_def, code_step_def] >> metis_tac[enc_entry_blocks_length]
QED

Theorem enc_grows_bind_right[local]:
  code_action enc_safe_opcode m /\ (!x. enc_grows_action (f x)) ==>
  enc_grows_action (comp_bind m f)
Proof
  rw[enc_grows_action_def, comp_bind_def] >> Cases_on `m a` >> gvs[] >>
  drule_all enc_code_blocks >> strip_tac >>
  first_x_assum drule >> decide_tac
QED

Theorem enc_grows_bind_left[local]:
  enc_grows_action m /\ (!x. code_action enc_safe_opcode (f x)) ==>
  enc_grows_action (comp_bind m f)
Proof
  rw[enc_grows_action_def, comp_bind_def] >> Cases_on `m a` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspec_then `q` assume_tac) >>
  drule_all enc_code_blocks >> decide_tac
QED

Theorem enc_grows_new_block[local]:
  enc_grows_action (new_block l)
Proof
  simp[enc_grows_action_def, new_block_def]
QED

Theorem enc_grows_static_loop:
  enc_grows_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  irule enc_grows_bind_right >> simp[code_action_alloc_buffer, enc_safe_opcode_def] >>
  gen_tac >> simp[] >>
  irule enc_grows_bind_right >> simp[code_action_emit_void, enc_safe_opcode_def] >>
  irule enc_grows_bind_right >> simp[code_action_fresh_label] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_fresh_label] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_fresh_label] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_emit_inst, enc_safe_opcode_def] >>
  irule enc_grows_bind_left >> simp[enc_grows_new_block] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (rewrite_tac[comp_ignore_bind_def] >> irule code_action_bind >>
       simp[code_action_new_block, code_action_emit_op,
            code_action_emit_inst, code_action_emit_void, code_action_static_info,
            enc_safe_opcode_def] >> rpt gen_tac) >>
  simp[code_action_emit_op, enc_safe_opcode_def]
QED

Theorem enc_grows_dyn_loop:
  enc_grows_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  once_rewrite_tac[compile_abi_encode_child_def] >>
  rewrite_tac[comp_ignore_bind_def] >>
  irule enc_grows_bind_right >> simp[code_action_alloc_buffer, enc_safe_opcode_def] >>
  gen_tac >> simp[] >>
  irule enc_grows_bind_right >> simp[code_action_emit_void, enc_safe_opcode_def] >>
  irule enc_grows_bind_right >> simp[code_action_alloc_buffer, enc_safe_opcode_def] >>
  gen_tac >> simp[] >>
  irule enc_grows_bind_right >> simp[code_action_emit_op, enc_safe_opcode_def] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_emit_void, enc_safe_opcode_def] >>
  irule enc_grows_bind_right >> simp[code_action_fresh_label] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_fresh_label] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_fresh_label] >> gen_tac >>
  irule enc_grows_bind_right >> simp[code_action_emit_inst, enc_safe_opcode_def] >>
  irule enc_grows_bind_left >> simp[enc_grows_new_block] >>
  rpt (rewrite_tac[comp_ignore_bind_def] >> irule code_action_bind >>
       simp[code_action_new_block, code_action_emit_op, code_action_encoder_mutual,
            code_action_emit_inst, code_action_emit_void, enc_safe_opcode_def] >>
       rpt gen_tac) >>
  simp[code_action_emit_op, code_action_emit_void, enc_safe_opcode_def]
QED

Theorem enc_straight_grows[local]:
  code_action enc_safe_opcode m /\ enc_grows_action m ==>
  enc_straight_action m
Proof
  rw[enc_straight_action_def, enc_grows_action_def, code_action_def, code_step_def] >>
  metis_tac[prim_recTheory.LESS_REFL]
QED

Theorem enc_straight_static_loop:
  enc_straight_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  irule enc_straight_grows >> simp[code_action_static_loop, enc_grows_static_loop]
QED

Theorem enc_straight_dyn_loop:
  enc_straight_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  irule enc_straight_grows >> simp[code_action_encoder_mutual, enc_grows_dyn_loop]
QED

Theorem enc_straight_static:
  enc_straight_action (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, enc_straight_action_bind,
       enc_straight_action_ignore_bind, enc_straight_action_emit_op,
       enc_straight_action_emit_void, enc_straight_action_return, is_terminator_def]
QED

Theorem enc_straight_static_info:
  enc_straight_action (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    enc_straight_static, enc_straight_action_return, enc_straight_action_ignore_bind,
    enc_straight_action_emit_void, is_terminator_def]
QED

Theorem enc_straight_encoder_mutual:
  (!dst ptr ei dyn so dp.
    enc_straight_action (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei.
    enc_straight_action (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    enc_straight_action (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    enc_straight_action (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`enc_straight_action (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- simp[enc_straight_dyn_loop] >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[] >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      simp[enc_straight_action_bind, enc_straight_action_ignore_bind,
           enc_straight_action_emit_op, enc_straight_action_emit_void,
           enc_straight_action_return, is_terminator_def] >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_bind >> simp[] >> gen_tac >>
      simp[enc_straight_action_bind, enc_straight_action_ignore_bind,
           enc_straight_action_emit_op, enc_straight_action_emit_void,
           enc_straight_action_return, is_terminator_def])
  >- simp[enc_straight_static]
  >- (irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_ignore_bind >> simp[enc_straight_action_emit_void, is_terminator_def] >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      simp[enc_straight_action_bind, enc_straight_action_ignore_bind,
           enc_straight_action_emit_op, enc_straight_action_emit_void, is_terminator_def])
  >- simp[enc_straight_action_ignore_bind, enc_straight_action_emit_void,
          enc_straight_action_return, is_terminator_def]
  >- (Cases_on `elem_is_dyn` >> gvs[] >>
      irule enc_straight_action_bind >> simp[enc_straight_action_alloc_buffer] >> gen_tac >>
      simp[] >> irule enc_straight_action_ignore_bind >> simp[enc_straight_action_emit_void, is_terminator_def] >>
      irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
      irule enc_straight_action_ignore_bind >> simp[enc_straight_action_emit_void, is_terminator_def] >>
      irule enc_straight_action_bind >> simp[enc_straight_static_loop] >> gen_tac >>
      simp[enc_straight_action_bind, enc_straight_action_ignore_bind,
           enc_straight_action_emit_void, enc_straight_action_emit_op, is_terminator_def])
  >- simp[enc_straight_action_return]
  >- (IF_CASES_TAC >> gvs[] >> simp[enc_straight_action_bind,
        enc_straight_action_ignore_bind, enc_straight_action_alloc_buffer,
        enc_straight_action_emit_void, enc_straight_action_emit_op,
        enc_straight_action_return, is_terminator_def])
  >- simp[enc_straight_action_return] >>
  simp[enc_straight_action_bind, enc_straight_action_ignore_bind,
       enc_straight_action_emit_op, is_terminator_def]
QED

Theorem enc_straight_lower_abi_encode:
  enc_straight_action (lower_abi_encode ensure mid src info maxlen)
Proof
  Cases_on `mid` >> simp[lower_abi_encode_def] >>
  irule enc_straight_action_bind >> simp[enc_straight_action_alloc_buffer] >> gen_tac >>
  irule enc_straight_action_bind >> simp[enc_straight_action_return] >> gen_tac >>
  irule enc_straight_action_bind >> simp[enc_straight_action_emit_op, is_terminator_def] >> gen_tac >>
  simp[enc_straight_action_bind, enc_straight_action_ignore_bind,
       enc_straight_action_return, enc_straight_action_emit_op,
       enc_straight_action_emit_void, enc_straight_encoder_mutual, is_terminator_def] >>
  irule enc_straight_action_ignore_bind >> conj_tac
  >- simp[enc_straight_action_bind, enc_straight_action_emit_op,
          enc_straight_action_emit_void, is_terminator_def] >>
  irule enc_straight_action_bind >> simp[enc_straight_encoder_mutual] >> gen_tac >>
  simp[enc_straight_action_ignore_bind, enc_straight_action_bind,
       enc_straight_action_emit_op, enc_straight_action_emit_void,
       enc_straight_action_return, is_terminator_def]
QED

Theorem lower_abi_encode_no_blocks_safe:
  !ensure mid src info maxlen sa out sb.
    lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
    sa.cs_blocks = sb.cs_blocks ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  mp_tac enc_straight_lower_abi_encode >>
  rewrite_tac[enc_straight_action_def] >>
  disch_then drule >> strip_tac >>
  gvs[frag_code_def, emitted_blocks_def]
QED
