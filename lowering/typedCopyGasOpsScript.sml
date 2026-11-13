(* Opcode-only compiler boundary for layout-changing memory copies. *)
Theory typedCopyGasOps
Ancestors
  exprSimAbiEncodeObliviousCode exprSimAbiGasBridge context compileEnv
  fragExec exprLoweringProps emitHelper list

Theorem typed_copy_primitive_code[local]:
  !P. P ADD /\ P MLOAD /\ P AND /\ P MCOPY /\ P NOT ==>
    (!dst src n. code_action P (compile_copy_memory dst src n)) /\
    (!dst src n. code_action P (compile_copy_memory_dynamic dst src n)) /\
    (!base off. code_action P (compile_with_byte_offset base off)) /\
    (!src dst. code_action P (compile_store_bytestring src dst))
Proof
  rpt strip_tac
  >- (Cases_on `n` >> simp[compile_copy_memory_def, code_action_return,
                         code_action_emit_void])
  >- simp[compile_copy_memory_dynamic_def, code_action_emit_void]
  >- (simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
      simp[code_action_return, code_action_emit_op]) >>
  rewrite_tac[compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
  irule code_action_bind >> simp[code_action_emit_void] >>
  irule code_action_bind >> simp[code_action_emit_op] >> gen_tac >>
  irule code_action_bind >> simp[code_action_emit_op] >> gen_tac >>
  simp[] >> irule code_action_bind >> simp[code_action_emit_op] >> gen_tac >>
  irule code_action_bind >> simp[code_action_emit_op]
QED

Theorem typed_copy_code_family:
  !P. EVERY P [ADD; MLOAD; AND; MCOPY; NOT; MSTORE; INVALID; ASSIGN; JMP;
              LT; ISZERO; JNZ; MUL; GT; ASSERT] ==>
  (!cenv dst dty src sty. code_action P (compile_store_memory_typed cenv dst dty src sty)) /\
  (!cenv dst src dtys stys doff soff.
     code_action P (compile_typed_copy_fields cenv dst src dtys stys doff soff)) /\
  (!cenv dst dty src sty n.
     code_action P (compile_copy_sarray_typed cenv dst dty src sty n)) /\
  (!cenv dst dty cap src sty.
     code_action P (compile_copy_dynarray_typed cenv dst dty cap src sty)) /\
  (!cenv dst src dfs sfs doff soff.
     code_action P (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  gen_tac >> simp[] >> strip_tac >>
  `(!dst src n. code_action P (compile_copy_memory dst src n)) /\
   (!dst src n. code_action P (compile_copy_memory_dynamic dst src n)) /\
   (!base off. code_action P (compile_with_byte_offset base off)) /\
   (!src dst. code_action P (compile_store_bytestring src dst))` by
    (irule typed_copy_primitive_code >> simp[]) >>
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[Once compile_store_memory_typed_def, code_action_return]
  >- simp[Once compile_store_memory_typed_def, code_action_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[Once compile_store_memory_typed_def, code_action_return]
  >> suspend "struct"
QED

Resume typed_copy_code_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >>
  rpt IF_CASES_TAC >> simp[code_action_bind, code_action_emit_op,
    code_action_emit_void] >>
  Cases_on `dty` >> Cases_on `sty` >>
  gvs[code_action_bind, code_action_emit_op, code_action_emit_void] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[]
QED

Resume typed_copy_code_family[fields]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, code_action_bind,
       code_action_ignore_bind]
QED

Resume typed_copy_code_family[sarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def] >> IF_CASES_TAC >>
  simp[code_action_bind, code_action_ignore_bind, code_action_emit_inst,
       code_action_emit_op, code_action_emit_void, code_action_return,
       code_action_fresh_var, code_action_fresh_label, code_action_new_block] >>
  `!d s. code_action P (compile_store_memory_typed cenv d dty s sty)` by
    (rpt gen_tac >> first_x_assum irule >> gvs[]) >>
  rpt (FIRST [irule code_action_bind, irule code_action_ignore_bind] >>
       simp[code_action_emit_inst, code_action_emit_op, code_action_emit_void,
            code_action_return, code_action_fresh_var, code_action_fresh_label,
            code_action_new_block] >> rpt gen_tac) >> simp[]
QED

Resume typed_copy_code_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, code_action_bind,
       code_action_ignore_bind, code_action_emit_inst, code_action_emit_op,
       code_action_emit_void, code_action_return, code_action_fresh_var,
       code_action_fresh_label, code_action_new_block] >>
  Cases_on `type_memory_bytes cenv dty = type_memory_bytes cenv sty /\ dty = sty` >>
  gvs[] >>
  rpt (FIRST [irule code_action_bind, irule code_action_ignore_bind] >>
       simp[code_action_emit_inst, code_action_emit_op, code_action_emit_void,
            code_action_return, code_action_fresh_var, code_action_fresh_label,
            code_action_new_block] >> rpt gen_tac) >>
  `!d s. code_action P (compile_store_memory_typed cenv d dty s sty)` by
    (rpt gen_tac >> first_x_assum irule >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >>
  rpt (FIRST [irule code_action_bind, irule code_action_ignore_bind] >>
       simp[code_action_emit_inst, code_action_emit_op, code_action_emit_void,
            code_action_return, code_action_fresh_var, code_action_fresh_label,
            code_action_new_block] >> rpt gen_tac) >> simp[]
QED

Resume typed_copy_code_family[struct]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, code_action_bind,
       code_action_ignore_bind] >>
  Cases_on `ALOOKUP sfs name` >> gvs[]
  >- simp[code_action_bind, code_action_ignore_bind] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  gvs[code_action_bind, code_action_ignore_bind]
QED

Finalise typed_copy_code_family

Theorem compile_store_memory_typed_ops_free:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) ==>
  frag_ops_free sa sb
Proof
  strip_tac >>
  qspec_then `\opc. opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\
                        opc <> STOP /\ opc <> RETURN` mp_tac typed_copy_code_family >>
  simp[] >> strip_tac >>
  gvs[code_action_def] >> metis_tac[code_step_frag_facts]
QED
