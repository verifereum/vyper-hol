Theory entryCreateCtorEncoderBand
Ancestors
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode abiEncoder

Definition ctor_encoder_safe_def:
  ctor_encoder_safe opc <=> ~MEM opc [GAS; INVOKE; CREATE; CREATE2]
End

Theorem ctor_code_action_dyn_loop_step[local]:
  !ei. (!dst src. code_action ctor_encoder_safe
    (compile_abi_encode_to_buf dst src ei)) ==>
  !dst src asz msz len.
    code_action ctor_encoder_safe
      (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  rpt strip_tac >> once_rewrite_tac[compile_abi_encode_child_def]
  >> irule code_action_bind >> simp[code_action_alloc_buffer, ctor_encoder_safe_def]
  >> gen_tac >> simp[]
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_bind >> simp[code_action_alloc_buffer, ctor_encoder_safe_def]
  >> gen_tac >> simp[]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> simp[code_action_bind, code_action_ignore_bind, code_action_emit_op,
           code_action_emit_void, ctor_encoder_safe_def]
QED

Theorem ctor_code_action_static[local]:
  !dst src. code_action ctor_encoder_safe
    (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, code_action_bind, code_action_ignore_bind,
       code_action_emit_op, code_action_emit_void, code_action_return,
       ctor_encoder_safe_def]
QED

Theorem ctor_code_action_static_info[local]:
  !dst src ei. code_action ctor_encoder_safe
    (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    ctor_code_action_static, code_action_return, code_action_ignore_bind,
    code_action_emit_void, ctor_encoder_safe_def]
QED

Theorem ctor_code_action_static_loop[local]:
  !dst src ei asz msz len. code_action ctor_encoder_safe
    (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_dyn_static_loop_def]
  >> irule code_action_bind >> simp[code_action_alloc_buffer, ctor_encoder_safe_def]
  >> gen_tac >> simp[]
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[ctor_code_action_static_info]
  >> irule code_action_bind >> simp[code_action_emit_op, ctor_encoder_safe_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, ctor_encoder_safe_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> simp[code_action_bind, code_action_emit_op, ctor_encoder_safe_def]
QED

Theorem ctor_abi_window_emitted_band:
  !dst src info.
    code_action ctor_encoder_safe (compile_abi_encode_to_buf dst src info)
Proof
  `(!dst ptr ei dyn so dp.
      code_action ctor_encoder_safe
        (compile_abi_encode_child dst ptr ei dyn so dp)) /\
   (!dst src ei.
      code_action ctor_encoder_safe
        (compile_abi_encode_to_buf dst src ei)) /\
   (!dst src infos so ho ptr.
      code_action ctor_encoder_safe
        (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
   (!dst src ei asz msz len.
      code_action ctor_encoder_safe
        (compile_abi_encode_dyn_loop dst src ei asz msz len))` by
    (ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac
     >> rpt (disch_then strip_assume_tac)
     >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
     >~ [`code_action _ (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
     >- (irule ctor_code_action_dyn_loop_step >> simp[])
     >> once_rewrite_tac[compile_abi_encode_child_def]
     >> simp_tac pure_ss [LET_THM] >> BETA_TAC
     >- (Cases_on `dyn` >> gvs[]
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> simp[code_action_bind, code_action_ignore_bind,
                 code_action_emit_op, code_action_emit_void, code_action_return,
                 ctor_encoder_safe_def]
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[] >> gen_tac
         >> simp[code_action_bind, code_action_ignore_bind,
                 code_action_emit_op, code_action_emit_void, code_action_return,
                 ctor_encoder_safe_def])
     >- simp[ctor_code_action_static]
     >- (irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_ignore_bind >> simp[code_action_emit_void,ctor_encoder_safe_def]
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_ignore_bind >> simp[code_action_emit_void,ctor_encoder_safe_def]
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> simp[code_action_emit_op,ctor_encoder_safe_def])
     >- simp[code_action_ignore_bind, code_action_emit_void, code_action_return,
             ctor_encoder_safe_def]
     >- (Cases_on `elem_is_dyn` >> gvs[]
         >> irule code_action_bind >> simp[code_action_alloc_buffer,ctor_encoder_safe_def] >> gen_tac
         >> simp[] >> irule code_action_ignore_bind >> simp[code_action_emit_void,ctor_encoder_safe_def]
         >> irule code_action_bind >> simp[code_action_emit_op,ctor_encoder_safe_def] >> gen_tac
         >> irule code_action_ignore_bind >> simp[code_action_emit_void,ctor_encoder_safe_def]
         >> irule code_action_bind >> simp[ctor_code_action_static_loop] >> gen_tac
         >> simp[code_action_bind, code_action_ignore_bind,
                 code_action_emit_void, code_action_emit_op, ctor_encoder_safe_def])
     >- simp[code_action_return]
     >- (IF_CASES_TAC >> gvs[] >> simp[code_action_bind, code_action_ignore_bind,
           code_action_alloc_buffer, code_action_emit_void, code_action_emit_op,
           code_action_return, ctor_encoder_safe_def])
     >- simp[code_action_return]
     >> simp[code_action_bind, code_action_ignore_bind, code_action_emit_op,
             ctor_encoder_safe_def]) >>
  qpat_assum `!dst src ei. _` irule
QED
