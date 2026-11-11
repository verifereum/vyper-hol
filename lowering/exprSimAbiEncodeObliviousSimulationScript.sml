Theory exprSimAbiEncodeObliviousSimulation
Ancestors
  exprSimAbiEncodeObliviousContext abiEncoder compileEnv emitHelper context builtinAbi

Theorem entry_action_static:
  !dst src. entry_action (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, entry_action_bind, entry_action_ignore_bind,
       entry_action_emit_op, entry_action_emit_void, entry_action_return]
QED

Theorem entry_action_static_info:
  !dst src ei. entry_action (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    entry_action_static, entry_action_return, entry_action_ignore_bind,
    entry_action_emit_void]
QED

Theorem entry_action_static_loop:
  !dst src ei asz msz len.
    entry_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_dyn_static_loop_def]
  >> irule entry_action_bind >> simp[entry_action_alloc_buffer]
  >> gen_tac >> simp[]
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_bind >> simp[entry_action_fresh_label] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_fresh_label] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_fresh_label] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_inst]
  >> irule entry_action_new_block
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_inst]
  >> irule entry_action_new_block
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_static_info]
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_inst]
  >> irule entry_action_new_block
  >> simp[entry_action_bind, entry_action_emit_op]
QED

Theorem entry_action_dyn_loop_step:
  !ei. (!dst src. entry_action (compile_abi_encode_to_buf dst src ei)) ==>
  !dst src asz msz len.
    entry_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  rpt strip_tac >> once_rewrite_tac[compile_abi_encode_child_def]
  >> irule entry_action_bind >> simp[entry_action_alloc_buffer]
  >> gen_tac >> simp[]
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_bind >> simp[entry_action_alloc_buffer]
  >> gen_tac >> simp[]
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_bind >> simp[entry_action_fresh_label] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_fresh_label] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_fresh_label] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_inst]
  >> irule entry_action_new_block
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_inst]
  >> irule entry_action_new_block
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_bind >> simp[] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
  >> irule entry_action_ignore_bind >> simp[entry_action_emit_inst]
  >> irule entry_action_new_block
  >> simp[entry_action_bind, entry_action_ignore_bind, entry_action_emit_op]
QED

Theorem entry_action_encoder_mutual:
  (!dst src ei dyn off ptr.
    entry_action (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. entry_action (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    entry_action (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    entry_action (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac
  >> rpt (disch_then strip_assume_tac)
  >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`entry_action (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- (irule entry_action_dyn_loop_step >> simp[])
  >> once_rewrite_tac[compile_abi_encode_child_def]
  >> simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[]
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> simp[entry_action_bind, entry_action_ignore_bind,
              entry_action_emit_op, entry_action_emit_void, entry_action_return]
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_bind >> simp[] >> gen_tac
      >> simp[entry_action_bind, entry_action_ignore_bind,
              entry_action_emit_op, entry_action_emit_void, entry_action_return])
  >- simp[entry_action_static]
  >- (irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> simp[entry_action_bind, entry_action_ignore_bind,
              entry_action_emit_op, entry_action_emit_void])
  >- simp[entry_action_ignore_bind, entry_action_emit_void, entry_action_return]
  >- (Cases_on `elem_is_dyn` >> gvs[]
      >> irule entry_action_bind >> simp[entry_action_alloc_buffer] >> gen_tac
      >> simp[] >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
      >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
      >> irule entry_action_ignore_bind >> simp[entry_action_emit_void]
      >> irule entry_action_bind >> simp[entry_action_static_loop] >> gen_tac
      >> simp[entry_action_bind, entry_action_ignore_bind,
              entry_action_emit_void, entry_action_emit_op])
  >- simp[entry_action_return]
  >- (IF_CASES_TAC >> gvs[] >> simp[entry_action_bind, entry_action_ignore_bind,
        entry_action_alloc_buffer, entry_action_emit_void, entry_action_emit_op,
        entry_action_return])
  >- simp[entry_action_return]
  >> simp[entry_action_bind, entry_action_ignore_bind, entry_action_emit_op]
QED

Theorem entry_action_lower_abi_encode:
  !ensure mid src info maxlen.
    entry_action (lower_abi_encode ensure mid src info maxlen)
Proof
  rpt gen_tac >> Cases_on `mid`
  >> simp[lower_abi_encode_def]
  >> irule entry_action_bind >> simp[entry_action_alloc_buffer] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_return] >> gen_tac
  >> irule entry_action_bind >> simp[entry_action_emit_op] >> gen_tac
  >> simp[entry_action_bind, entry_action_ignore_bind, entry_action_return,
          entry_action_emit_op, entry_action_emit_void, entry_action_encoder_mutual]
QED
