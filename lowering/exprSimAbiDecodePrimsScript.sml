Theory exprSimAbiDecodePrims
Ancestors
  exprSimAbiDecodeTrace abiEncoder context compileEnv emitHelper venomInst

Theorem decode_history_core_eq:
  decode_core h = decode_core s ==> decode_history s h = h
Proof
  Cases_on `h` >> Cases_on `s` >>
  simp[decode_core_def, decode_history_def, compile_state_component_equality]
QED

Theorem decode_history_history:
  decode_history a (decode_history b h) = decode_history a h
Proof
  simp[decode_history_def]
QED

Theorem decode_certificate_return:
  decode_certificate (comp_return x)
Proof
  rw[decode_certificate_def] >> qexistsl_tac [`x`, `[]`, `s`] >>
  simp[comp_return_def, decode_replay_def] >>
  metis_tac[decode_history_core_eq]
QED

Theorem decode_certificate_bind:
  decode_certificate m /\ (!x. decode_certificate (f x)) ==>
  decode_certificate (comp_bind m f)
Proof
  rw[decode_certificate_def] >>
  first_x_assum (qspec_then `s` strip_assume_tac) >>
  first_x_assum (qspecl_then [`x`, `n`] strip_assume_tac) >>
  qexistsl_tac [`x'`, `es ++ es'`, `n'`] >> rpt strip_tac >>
  simp[comp_bind_def] >>
  first_x_assum (qspec_then `decode_history n (decode_replay es h)` mp_tac) >>
  simp[decode_history_core, decode_replay_history, decode_replay_append,
       decode_history_history]
QED

Theorem decode_certificate_ignore_bind:
  decode_certificate m /\ decode_certificate f ==>
  decode_certificate (comp_ignore_bind m f)
Proof
  simp[comp_ignore_bind_def, decode_certificate_bind]
QED

Theorem decode_certificate_emit:
  decode_certificate (emit i)
Proof
  rw[decode_certificate_def] >> qexistsl_tac [`[DecodeEmit i]`, `s`] >>
  rpt strip_tac >>
  `decode_history s h = h` by metis_tac[decode_history_core_eq] >>
  rewrite_tac[decode_replay_def, GSYM decode_step_history] >>
  simp[emit_def, decode_step_def]
QED

Theorem decode_certificate_switch:
  decode_certificate (comp_ignore_bind (new_block l) (comp_return ()))
Proof
  rw[decode_certificate_def] >> qexistsl_tac [`[DecodeSwitch l]`, `s`] >>
  rpt strip_tac >>
  `decode_history s h = h` by metis_tac[decode_history_core_eq] >>
  rewrite_tac[decode_replay_def, GSYM decode_step_history] >>
  simp[decode_step_def, comp_ignore_bind_def, comp_bind_def,
       new_block_def, comp_return_def]
QED

Theorem decode_certificate_new_block:
  decode_certificate f ==>
  decode_certificate (comp_ignore_bind (new_block l) f)
Proof
  strip_tac >>
  `comp_ignore_bind (new_block l) f =
   comp_ignore_bind (comp_ignore_bind (new_block l) (comp_return ())) f` by
    simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, new_block_def, FUN_EQ_THM] >>
  simp[decode_certificate_ignore_bind, decode_certificate_switch]
QED

Theorem decode_certificate_fresh_id:
  decode_certificate fresh_id
Proof
  rw[decode_certificate_def] >>
  qexistsl_tac [`s.cs_next_id`, `[]`, `s with cs_next_id := s.cs_next_id + 1`] >>
  Cases_on `h` >> Cases_on `s` >>
  simp[decode_core_def, fresh_id_def, decode_replay_def, decode_history_def,
       compile_state_component_equality]
QED

Theorem decode_certificate_fresh_var:
  decode_certificate fresh_var
Proof
  rw[decode_certificate_def] >>
  qexistsl_tac [`"%" ++ toString s.cs_next_var`, `[]`,
    `s with cs_next_var := s.cs_next_var + 1`] >>
  Cases_on `h` >> Cases_on `s` >>
  simp[decode_core_def, fresh_var_def, decode_replay_def, decode_history_def,
       compile_state_component_equality]
QED

Theorem decode_certificate_fresh_label:
  decode_certificate (fresh_label suffix)
Proof
  rw[decode_certificate_def] >>
  qexistsl_tac [`fresh_label_output suffix s.cs_next_label`, `[]`,
    `s with cs_next_label := s.cs_next_label + 1`] >>
  Cases_on `h` >> Cases_on `s` >>
  simp[decode_core_def, fresh_label_def, decode_replay_def, decode_history_def,
       compile_state_component_equality]
QED

Theorem decode_certificate_emit_op:
  decode_certificate (emit_op opc ops)
Proof
  simp[emit_op_def, decode_certificate_bind, decode_certificate_ignore_bind,
       decode_certificate_emit, decode_certificate_fresh_id,
       decode_certificate_fresh_var, decode_certificate_return]
QED

Theorem decode_certificate_emit_void:
  decode_certificate (emit_void opc ops)
Proof
  simp[emit_void_def, decode_certificate_bind, decode_certificate_fresh_id,
       decode_certificate_emit]
QED

Theorem decode_certificate_emit_inst:
  decode_certificate (emit_inst opc ops outs)
Proof
  simp[emit_inst_def, decode_certificate_bind, decode_certificate_fresh_id,
       decode_certificate_emit]
QED

Theorem decode_certificate_alloc_buffer:
  decode_certificate (compile_alloc_buffer sz)
Proof
  simp[compile_alloc_buffer_def, decode_certificate_bind,
       decode_certificate_emit_op, decode_certificate_return]
QED

Theorem decode_certificate_abi_int_clamp:
  decode_certificate (compile_abi_int_clamp v bits signed)
Proof
  Cases_on `signed` >> simp[compile_abi_int_clamp_def, LET_THM,
    decode_certificate_bind, decode_certificate_emit_op,
    decode_certificate_emit_void]
QED

Theorem decode_certificate_abi_bytes_clamp:
  decode_certificate (compile_abi_bytes_clamp v m)
Proof
  simp[compile_abi_bytes_clamp_def, LET_THM, decode_certificate_bind,
       decode_certificate_emit_op, decode_certificate_emit_void]
QED

Theorem decode_certificate_abi_clamp_basetype:
  decode_certificate (compile_abi_clamp_basetype v clamp)
Proof
  Cases_on `clamp` >> simp[compile_abi_clamp_basetype_def,
    decode_certificate_abi_int_clamp, decode_certificate_abi_bytes_clamp,
    decode_certificate_bind, decode_certificate_emit_op,
    decode_certificate_emit_void, decode_certificate_return]
QED

Theorem decode_certificate_abi_decode_static:
  (!v. decode_certificate (f v)) ==>
  decode_certificate (compile_abi_decode_static src dst opc f)
Proof
  strip_tac >> simp[compile_abi_decode_static_def,
    decode_certificate_ignore_bind, decode_certificate_bind,
    decode_certificate_emit_op, decode_certificate_emit_void]
QED

Theorem decode_certificate_abi_dec_addr:
  decode_certificate (compile_abi_dec_addr bop pos)
Proof
  Cases_on `bop = Lit 0w` >>
  simp[compile_abi_dec_addr_def, decode_certificate_emit_op,
       decode_certificate_return]
QED

Theorem decode_certificate_abi_decode_range_check:
  decode_certificate (compile_abi_decode_range_check start end_op hi)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  rpt (match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_emit_op] >> gen_tac >> BETA_TAC) >>
  simp[decode_certificate_emit_void]
QED

Theorem decode_certificate_getelemptr_abi:
  decode_certificate (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, decode_certificate_ignore_bind,
       decode_certificate_bind, decode_certificate_emit_op,
       decode_certificate_emit_void, decode_certificate_abi_dec_addr,
       decode_certificate_return] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_bind, decode_certificate_emit_op,
               decode_certificate_emit_void, decode_certificate_abi_dec_addr,
               decode_certificate_return] >> gen_tac >> BETA_TAC) >>
  simp[decode_certificate_return]
QED

Theorem decode_certificate_abi_decode_dyn_elem_ptr:
  decode_certificate (compile_abi_decode_dyn_elem_ptr opc bop src data_op hi sz)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, decode_certificate_ignore_bind,
       decode_certificate_bind, decode_certificate_emit_op,
       decode_certificate_emit_void, decode_certificate_abi_dec_addr,
       decode_certificate_abi_decode_range_check, decode_certificate_return] >>
  rewrite_tac[comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (match_mp_tac decode_certificate_bind >> conj_tac
       >- simp[decode_certificate_bind, decode_certificate_emit_op,
               decode_certificate_emit_void, decode_certificate_abi_dec_addr,
               decode_certificate_abi_decode_range_check,
               decode_certificate_return] >> gen_tac >> BETA_TAC) >>
  simp[decode_certificate_return]
QED
