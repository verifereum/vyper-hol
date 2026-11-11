Theory exprSimAbiEncodeObliviousOperands
Ancestors
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousContext exprSimAbiEncodeObliviousLabels
  exprSimAbiGasBridge fragExec compileEnv emitHelper context abiEncoder
  builtinAbi list rich_list sorting venomInst exprLoweringProps
  exprSimAbiEncodeLabelProvenance exprSimAbiEncodeObliviousSimulation

Definition enc_nonlabel_def:
  enc_nonlabel op <=> !l. op <> Label l
End

Definition enc_operand_step_def:
  enc_operand_step a b <=> entry_shape a b /\
    (a.cs_blocks = b.cs_blocks ==>
      EVERY (\i. EVERY enc_nonlabel i.inst_operands) (frag_code a b))
End

Definition enc_operand_action_def:
  enc_operand_action P m <=> !a x b. m a = (x,b) ==>
    enc_operand_step a b /\ P x
End

Theorem enc_operand_step_refl:
  !a. enc_operand_step a a
Proof
  simp[enc_operand_step_def, entry_shape_refl, frag_code_def,
       emitted_blocks_def, emitted_insts_def]
QED

Theorem entry_shape_blocks_between:
  !a b c. entry_shape a b /\ entry_shape b c /\ a.cs_blocks = c.cs_blocks ==>
    a.cs_blocks = b.cs_blocks /\ b.cs_blocks = c.cs_blocks
Proof
  rw[entry_shape_def] >> gvs[]
  >> pop_assum (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``)
  >> simp[]
QED

Theorem enc_operand_step_trans:
  !a b c. enc_operand_step a b /\ enc_operand_step b c ==>
    enc_operand_step a c
Proof
  rw[enc_operand_step_def]
  >- metis_tac[entry_shape_trans]
  >> drule_all entry_shape_blocks_between >> strip_tac
  >> drule_all frag_code_compose_perm >> strip_tac
  >> metis_tac[EVERY_APPEND, PERM_EVERY]
QED

Theorem enc_operand_action_return:
  !P x. enc_operand_action P (comp_return x) <=> P x
Proof
  simp[enc_operand_action_def, comp_return_def, enc_operand_step_refl]
QED

Theorem enc_operand_action_bind:
  !P Q m f. enc_operand_action P m /\
    (!x. P x ==> enc_operand_action Q (f x)) ==>
    enc_operand_action Q (comp_bind m f)
Proof
  rw[enc_operand_action_def, comp_bind_def]
  >> Cases_on `m a` >> gvs[]
  >> metis_tac[enc_operand_step_trans]
QED

Theorem enc_operand_action_ignore_bind:
  !P m n. enc_operand_action (\x. T) m /\ enc_operand_action P n ==>
    enc_operand_action P (comp_ignore_bind m n)
Proof
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def]
  >> irule enc_operand_action_bind >> qexists_tac `\x. T` >> simp[]
QED

Theorem enc_operand_action_weaken:
  !P Q m. enc_operand_action P m /\ (!x. P x ==> Q x) ==>
    enc_operand_action Q m
Proof
  simp[enc_operand_action_def] >> metis_tac[]
QED

Theorem enc_operand_bind_nonlabel:
  !Q m f. enc_operand_action enc_nonlabel m /\
    (!x. enc_nonlabel x ==> enc_operand_action Q (f x)) ==>
    enc_operand_action Q (comp_bind m f)
Proof
  metis_tac[enc_operand_action_bind]
QED

Theorem enc_operand_bind_buffer:
  !Q m f. enc_operand_action (\b. enc_nonlabel b.buf_operand) m /\
    (!x. enc_nonlabel x.buf_operand ==> enc_operand_action Q (f x)) ==>
    enc_operand_action Q (comp_bind m f)
Proof
  rpt strip_tac >> irule enc_operand_action_bind
  >> qexists_tac `\b. enc_nonlabel b.buf_operand` >> simp[]
QED

Theorem enc_operand_ignore_nonlabel:
  !Q m n. enc_operand_action enc_nonlabel m /\ enc_operand_action Q n ==>
    enc_operand_action Q (comp_ignore_bind m n)
Proof
  rpt strip_tac >> irule enc_operand_action_ignore_bind >> simp[]
  >> irule enc_operand_action_weaken >> qexists_tac `enc_nonlabel` >> simp[]
QED

Theorem enc_operand_emit_op:
  !opc ops. EVERY enc_nonlabel ops ==>
    enc_operand_action enc_nonlabel (emit_op opc ops)
Proof
  simp[enc_operand_action_def, enc_operand_step_def, enc_nonlabel_def,
       emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem enc_operand_emit_void:
  !opc ops. EVERY enc_nonlabel ops ==>
    enc_operand_action (\x. T) (emit_void opc ops)
Proof
  simp[enc_operand_action_def, enc_operand_step_def,
       emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem enc_operand_alloc_buffer:
  !n. enc_operand_action (\b. enc_nonlabel b.buf_operand) (compile_alloc_buffer n)
Proof
  simp[compile_alloc_buffer_def, enc_operand_action_def, enc_operand_step_def,
       enc_nonlabel_def, emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, entry_shape_def, frag_code_def,
       emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
QED

Theorem enc_nonlabel_literals[simp]:
  (!w. enc_nonlabel (Lit w)) /\ (!v. enc_nonlabel (Var v))
Proof
  simp[enc_nonlabel_def]
QED

Theorem enc_operand_static:
  !dst src. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action enc_nonlabel (compile_abi_encode_static dst src)
Proof
  rpt strip_tac >> rewrite_tac[compile_abi_encode_static_def]
  >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op]
  >> rpt strip_tac >> irule enc_operand_action_ignore_bind
  >> simp[enc_operand_emit_void, enc_operand_action_return]
QED

Theorem enc_operand_static_info:
  !dst src ei. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action enc_nonlabel (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    enc_operand_static, enc_operand_action_return,
    enc_operand_action_ignore_bind, enc_operand_emit_void]
QED

Theorem enc_operand_static_loop:
  !dst src ei asz msz len.
    enc_operand_action enc_nonlabel
      (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rw[enc_operand_action_def]
  >> `entry_shape a b` by
       metis_tac[entry_action_run_shape, entry_action_static_loop]
  >> simp[enc_operand_step_def]
  >> qpat_x_assum `compile_abi_encode_dyn_static_loop _ _ _ _ _ _ _ = _` mp_tac
  >> simp[compile_abi_encode_dyn_static_loop_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def, fresh_label_def, new_block_def]
  >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule (SRULE[enc_label_flat_def] enc_label_flat_static_info)
  >> strip_tac >> gvs[]
  >> simp[enc_nonlabel_def]
  >> strip_tac
  >> pop_assum (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``)
  >> simp[]
QED

Theorem entry_shape_blocks_length:
  !a b. entry_shape a b ==> LENGTH a.cs_blocks <= LENGTH b.cs_blocks
Proof
  rw[entry_shape_def] >> simp[]
QED

Theorem enc_operand_dyn_loop:
  !dst src ei asz msz len.
    enc_operand_action enc_nonlabel
      (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  rw[enc_operand_action_def]
  >> `entry_shape a b` by
       metis_tac[entry_action_run_shape, entry_action_encoder_mutual]
  >> simp[enc_operand_step_def]
  >> qpat_x_assum `compile_abi_encode_dyn_loop _ _ _ _ _ _ _ = _` mp_tac
  >> once_rewrite_tac[compile_abi_encode_child_def]
  >> simp[compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def, fresh_label_def, new_block_def]
  >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
  >> drule (cj 2 code_action_encoder_mutual |> SRULE [code_action_def, code_step_def])
  >> strip_tac
  >> qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` kall_tac
  >> qpat_x_assum `entry_shape _ cs'` (mp_tac o MATCH_MP entry_shape_blocks_length)
  >> simp_tac pure_ss [compile_state_accfupds, combinTheory.K_THM, LENGTH]
  >> strip_tac >> simp[enc_nonlabel_def]
  >> strip_tac
  >> pop_assum (mp_tac o AP_TERM ``LENGTH : basic_block list -> num``)
  >> simp[]
QED

Theorem enc_operand_encoder_mutual:
  (!dst ptr ei dyn so dp.
    enc_nonlabel dst /\ enc_nonlabel ptr /\ enc_nonlabel dp ==>
    enc_operand_action enc_nonlabel (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei. enc_nonlabel dst /\ enc_nonlabel src ==>
    enc_operand_action enc_nonlabel (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    enc_nonlabel dst /\ enc_nonlabel src /\ enc_nonlabel ptr ==>
    enc_operand_action enc_nonlabel (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    enc_operand_action enc_nonlabel (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac
  >> rpt (disch_then strip_assume_tac)
  >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`enc_operand_action _ (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- simp[enc_operand_dyn_loop]
  >> once_rewrite_tac[compile_abi_encode_child_def]
  >> simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[]
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> simp[enc_operand_bind_nonlabel, enc_operand_action_ignore_bind,
              enc_operand_emit_op, enc_operand_emit_void, enc_operand_action_return]
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_bind_nonlabel >> simp[] >> rpt strip_tac
      >> simp[enc_operand_bind_nonlabel, enc_operand_action_ignore_bind,
              enc_operand_emit_op, enc_operand_emit_void, enc_operand_action_return])
  >- simp[enc_operand_static]
  >- (irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_action_ignore_bind >> simp[enc_operand_emit_void]
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> simp[enc_operand_bind_nonlabel, enc_operand_action_ignore_bind,
              enc_operand_emit_op, enc_operand_emit_void])
  >- simp[enc_operand_action_ignore_bind, enc_operand_emit_void, enc_operand_action_return]
  >- (Cases_on `elem_is_dyn` >> gvs[]
      >> irule enc_operand_bind_buffer >> simp[enc_operand_alloc_buffer] >> rpt strip_tac
      >> simp[] >> irule enc_operand_action_ignore_bind >> simp[enc_operand_emit_void]
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
      >> irule enc_operand_action_ignore_bind >> simp[enc_operand_emit_void]
      >> irule enc_operand_bind_nonlabel >> simp[enc_operand_static_loop, enc_operand_dyn_loop]
      >> rpt strip_tac
      >> simp[enc_operand_bind_nonlabel, enc_operand_action_ignore_bind,
              enc_operand_emit_void, enc_operand_emit_op])
  >- simp[enc_operand_action_return]
  >- (IF_CASES_TAC >> gvs[]
      >> simp[enc_operand_bind_buffer, enc_operand_bind_nonlabel,
          enc_operand_action_ignore_bind, enc_operand_ignore_nonlabel,
          enc_operand_alloc_buffer, enc_operand_emit_void, enc_operand_emit_op,
          enc_operand_action_return])
  >- simp[enc_operand_action_return]
  >> simp[enc_operand_bind_nonlabel, enc_operand_ignore_nonlabel, enc_operand_emit_op]
QED

Theorem enc_operand_lower_abi_encode:
  !ensure mid src info maxlen. enc_nonlabel src ==>
    enc_operand_action enc_nonlabel (lower_abi_encode ensure mid src info maxlen)
Proof
  rpt strip_tac >> Cases_on `mid` >> simp[lower_abi_encode_def]
  >> irule enc_operand_bind_buffer >> simp[enc_operand_alloc_buffer] >> rpt strip_tac
  >> irule enc_operand_bind_nonlabel >> simp[enc_operand_action_return] >> rpt strip_tac
  >> irule enc_operand_bind_nonlabel >> simp[enc_operand_emit_op] >> rpt strip_tac
  >> simp[enc_operand_bind_nonlabel, enc_operand_action_ignore_bind,
          enc_operand_action_return, enc_operand_emit_op, enc_operand_emit_void,
          enc_operand_encoder_mutual]
  >> (irule enc_operand_action_ignore_bind
  >> simp[enc_operand_bind_nonlabel, enc_operand_emit_op,
          enc_operand_emit_void, enc_operand_action_return]
  >> irule enc_operand_bind_nonlabel >> simp[enc_operand_encoder_mutual] >> rpt strip_tac
  >> simp[enc_operand_action_ignore_bind, enc_operand_bind_nonlabel,
          enc_operand_emit_op, enc_operand_emit_void, enc_operand_action_return])
QED

Theorem lower_abi_encode_no_block_gas_free:
  !ensure mid src info maxlen sa out sb.
    lower_abi_encode ensure mid src info maxlen sa = (out,sb) /\
    (!l. src <> Label l) /\ sa.cs_blocks = sb.cs_blocks ==>
    frag_gas_free sa sb
Proof
  rpt strip_tac
  >> `enc_operand_step sa sb` by
       metis_tac[enc_operand_lower_abi_encode, enc_operand_action_def, enc_nonlabel_def]
  >> drule lower_abi_encode_structural_facts >> strip_tac
  >> gvs[enc_operand_step_def, frag_gas_free_def, frag_ops_free_def,
         emitted_blocks_def, EVERY_MEM, enc_nonlabel_def]
  >> metis_tac[]
QED
