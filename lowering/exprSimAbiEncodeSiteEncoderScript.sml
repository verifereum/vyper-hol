Theory exprSimAbiEncodeSiteEncoder
Ancestors
  exprSimAbiEncodeSiteSyntax abiEncoder builtinAbi compileEnv emitHelper
  context venomInst list

Theorem site_action_static:
  !dst src. site_action (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, site_action_bind, site_action_ignore_bind,
       site_action_emit_op, site_action_emit_void, site_action_return]
QED

Theorem site_action_static_info:
  !dst src ei. site_action (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    site_action_static, site_action_return, site_action_ignore_bind,
    site_action_emit_void]
QED

Theorem site_action_static_loop:
  !dst src ei asz msz len.
    site_action (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  irule site_action_bind >> simp[site_action_alloc_buffer32] >> gen_tac >> simp[] >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_bind >> simp[site_action_fresh_label] >> gen_tac >>
  irule site_action_bind >> simp[site_action_fresh_label] >> gen_tac >>
  irule site_action_bind >> simp[site_action_fresh_label] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_inst] >>
  irule site_action_ignore_bind >> simp[site_action_new_block] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_inst] >>
  irule site_action_ignore_bind >> simp[site_action_new_block] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_static_info] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_ignore_bind >> simp[site_action_emit_inst] >>
  irule site_action_ignore_bind >> simp[site_action_new_block] >>
  simp[site_action_bind, site_action_emit_op]
QED

Theorem site_action_dyn_loop_step:
  !ei. (!dst src. site_action (compile_abi_encode_to_buf dst src ei)) ==>
  !dst src asz msz len.
    site_action (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  rpt strip_tac >> once_rewrite_tac[compile_abi_encode_child_def] >>
  irule site_action_bind >> simp[site_action_alloc_buffer32] >> gen_tac >> simp[] >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_bind >> simp[site_action_alloc_buffer32] >> gen_tac >> simp[] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_bind >> simp[site_action_fresh_label] >> gen_tac >>
  irule site_action_bind >> simp[site_action_fresh_label] >> gen_tac >>
  irule site_action_bind >> simp[site_action_fresh_label] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_inst] >>
  irule site_action_ignore_bind >> simp[site_action_new_block] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_inst] >>
  irule site_action_ignore_bind >> simp[site_action_new_block] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_bind >> simp[] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
  irule site_action_ignore_bind >> simp[site_action_emit_void] >>
  irule site_action_ignore_bind >> simp[site_action_emit_inst] >>
  irule site_action_ignore_bind >> simp[site_action_new_block] >>
  simp[site_action_bind, site_action_ignore_bind, site_action_emit_op,
       site_action_emit_void]
QED

Theorem site_action_encoder_mutual:
  (!dst ptr ei dyn so dp.
    site_action (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei.
    site_action (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    site_action (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    site_action (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`site_action (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- (irule site_action_dyn_loop_step >> simp[]) >>
  once_rewrite_tac[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[] >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      simp[site_action_bind, site_action_ignore_bind,
           site_action_emit_op, site_action_emit_void, site_action_return] >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_bind >> simp[] >> gen_tac >>
      simp[site_action_bind, site_action_ignore_bind,
           site_action_emit_op, site_action_emit_void, site_action_return])
  >- simp[site_action_static]
  >- (irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_ignore_bind >> simp[site_action_emit_void] >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      simp[site_action_bind, site_action_ignore_bind,
           site_action_emit_op, site_action_emit_void])
  >- simp[site_action_ignore_bind, site_action_emit_void, site_action_return]
  >- (Cases_on `elem_is_dyn` >> gvs[] >>
      irule site_action_bind >> simp[site_action_alloc_buffer32] >> gen_tac >>
      simp[] >> irule site_action_ignore_bind >> simp[site_action_emit_void] >>
      irule site_action_bind >> simp[site_action_emit_op] >> gen_tac >>
      irule site_action_ignore_bind >> simp[site_action_emit_void] >>
      irule site_action_bind >> simp[site_action_static_loop] >> gen_tac >>
      simp[site_action_bind, site_action_ignore_bind,
           site_action_emit_void, site_action_emit_op])
  >- simp[site_action_return]
  >- (IF_CASES_TAC >> gvs[] >> simp[site_action_bind, site_action_ignore_bind,
        site_action_alloc_buffer32, site_action_emit_void, site_action_emit_op,
        site_action_return])
  >- simp[site_action_return] >>
  simp[site_action_bind, site_action_ignore_bind, site_action_emit_op]
QED

Theorem abi_encode_body_site_step:
  compile_abi_encode_to_buf dst src ei a = (r,b) ==> site_step a b
Proof
  metis_tac[site_action_encoder_mutual, site_action_def]
QED
