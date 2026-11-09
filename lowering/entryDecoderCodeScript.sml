Theory entryDecoderCode
Ancestors
  entryCodePredicate entryContextCodePredicate abiEncoder

Theorem entry_code_int_clamp[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_int_clamp v bits is_signed)
Proof
  Cases_on `is_signed` >> simp[compile_abi_int_clamp_def] >>
  rpt (irule entry_code_bind >>
       simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac)
QED

Theorem entry_code_bytes_clamp[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_bytes_clamp v m)
Proof
  simp[compile_abi_bytes_clamp_def] >>
  rpt (irule entry_code_bind >>
       simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac)
QED

Theorem entry_code_clamp_basetype:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_clamp_basetype v clamp)
Proof
  Cases_on `clamp` >>
  simp[compile_abi_clamp_basetype_def, entry_code_int_clamp,
       entry_code_bytes_clamp, entry_code_return] >>
  rpt (irule entry_code_bind >>
       simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac)
QED

Theorem entry_code_decode_static:
  load_opc <> DALLOCA /\
  (!v. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (clamp_fn v)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_static src dst load_opc clamp_fn)
Proof
  strip_tac >> simp[compile_abi_decode_static_def] >>
  irule entry_code_bind >> simp[entry_code_emit_op] >> gen_tac >>
  irule entry_code_ignore_bind >> simp[entry_code_emit_void]
QED

Theorem entry_code_getelemptr_abi:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_getelemptr_abi src is_dyn abi_offset load_opc (Lit 0w) hi)
Proof
  strip_tac >> Cases_on `is_dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >>
       simp[entry_code_emit_op, entry_code_emit_void, entry_code_return] >>
       rpt gen_tac)
QED

Theorem entry_code_decode_dyn_elem_ptr:
  load_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_decode_dyn_elem_ptr load_opc (Lit 0w) elem_src src_data hi elem_abi_sz)
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >>
       simp[entry_code_emit_op, entry_code_emit_void, entry_code_return] >>
       rpt gen_tac)
QED
