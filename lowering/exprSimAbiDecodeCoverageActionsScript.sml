Theory exprSimAbiDecodeCoverageActions
Ancestors
  exprSimAbiDecodeSiteCoverage exprSimAbiGasBridge abiEncoder abiDecoderCounters abiDecoderAppend
  exprLoweringProps compileEnv emitHelper context fragExec venomInst list rich_list arithmetic pair

Definition abi_decode_id_coverage_def:
  abi_decode_id_coverage (action : 'a compiler) <=>
    !a v b. action a = (v,b) ==>
      cs_extends a b /\ a.cs_next_id <= b.cs_next_id /\
      !id. a.cs_next_id <= id /\ id < b.cs_next_id ==>
        ?i. MEM i (frag_code a b) /\ i.inst_id = id
End

Theorem abi_decode_id_coverage_bind:
  abi_decode_id_coverage action /\
  (!v. abi_decode_id_coverage (next v)) ==>
  abi_decode_id_coverage (comp_bind action next)
Proof
  rewrite_tac[abi_decode_id_coverage_def] >> strip_tac >>
  rpt gen_tac >> simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!a v b. action a = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!v a v' b. next v a = _ ==> _` drule >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- metis_tac[LESS_EQ_TRANS] >>
  rpt strip_tac >>
  metis_tac[abi_decode_frag_code_left_inclusion,
            abi_decode_frag_code_right_inclusion, NOT_LESS]
QED

Theorem abi_decode_id_coverage_ignore_bind:
  abi_decode_id_coverage action /\ abi_decode_id_coverage next ==>
  abi_decode_id_coverage (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule abi_decode_id_coverage_bind >> simp[]
QED

Theorem abi_decode_id_coverage_return:
  abi_decode_id_coverage (comp_return v)
Proof
  simp[abi_decode_id_coverage_def, comp_return_def, cs_extends_refl]
QED

Theorem abi_decode_id_coverage_prims:
  (!opc ops. abi_decode_id_coverage (emit_op opc ops)) /\
  (!opc ops. abi_decode_id_coverage (emit_void opc ops)) /\
  (!opc ops outs. abi_decode_id_coverage (emit_inst opc ops outs)) /\
  abi_decode_id_coverage fresh_var /\
  (!prefix. abi_decode_id_coverage (fresh_label prefix)) /\
  (!lbl. abi_decode_id_coverage (new_block lbl))
Proof
  simp[abi_decode_id_coverage_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM,
    frag_code_def, emitted_blocks_def, emitted_insts_def, mk_inst_def,
    cs_extends_def, DROP_LENGTH_APPEND] >>
  rpt strip_tac >> gvs[]
QED

val coverage_simps = [abi_decode_id_coverage_return, abi_decode_id_coverage_prims];
val COVERAGE_BIND_WITH = fn extra => ho_match_mp_tac abi_decode_id_coverage_bind >> conj_tac
  >- simp (extra @ coverage_simps) >> rpt gen_tac;
val COVERAGE_BIND = COVERAGE_BIND_WITH [];
val COVERAGE_IGNORE = ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- simp coverage_simps;

Theorem abi_decode_id_coverage_clamp:
  !c v. abi_decode_id_coverage (compile_abi_clamp_basetype v c)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, abi_decode_id_coverage_return]
  >- (rpt gen_tac >> IF_CASES_TAC >> simp_tac pure_ss [LET_THM] >>
      ntac 2 COVERAGE_BIND >> simp coverage_simps)
  >- (rpt gen_tac >> ntac 2 COVERAGE_BIND >> simp coverage_simps) >>
  rpt gen_tac >> ntac 2 COVERAGE_BIND >> simp coverage_simps
QED

Theorem abi_decode_id_coverage_static:
  (!v. abi_decode_id_coverage (clamp v)) ==>
  abi_decode_id_coverage (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >> rewrite_tac[compile_abi_decode_static_def] >>
  COVERAGE_BIND >> COVERAGE_IGNORE >> simp coverage_simps
QED

Theorem abi_decode_id_coverage_alloc_buffer:
  abi_decode_id_coverage (compile_alloc_buffer n)
Proof
  rewrite_tac[compile_alloc_buffer_def] >> COVERAGE_BIND >> simp coverage_simps
QED

Theorem abi_decode_id_coverage_addr:
  abi_decode_id_coverage (compile_abi_dec_addr base_op pos)
Proof
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >> simp coverage_simps
QED

Theorem abi_decode_id_coverage_member_pointer:
  abi_decode_id_coverage (compile_getelemptr_abi src dyn off opc base_op hi)
Proof
  rewrite_tac[compile_getelemptr_abi_def] >> COVERAGE_BIND >> Cases_on `dyn` >>
  simp[abi_decode_id_coverage_return] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >> ntac 2 COVERAGE_BIND >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_id_coverage_return] >>
      ntac 2 COVERAGE_BIND >> simp coverage_simps) >>
  simp[abi_decode_id_coverage_return]
QED

Theorem abi_decode_id_coverage_range_check:
  abi_decode_id_coverage (compile_abi_decode_range_check start_op end_op hi_op)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  ntac 5 COVERAGE_BIND >> simp coverage_simps
QED

Theorem abi_decode_id_coverage_head_check:
  abi_decode_id_coverage
    (if hi = Lit 0w then comp_return (Lit 0w)
     else do head_end <- emit_op ADD [src; Lit 32w];
             compile_abi_decode_range_check src head_end hi;
             comp_return head_end
          od)
Proof
  IF_CASES_TAC >> simp[abi_decode_id_coverage_return] >> COVERAGE_BIND >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- simp[abi_decode_id_coverage_range_check] >> simp coverage_simps
QED

Theorem abi_decode_id_coverage_array_pointer:
  abi_decode_id_coverage (compile_abi_decode_dyn_elem_ptr opc base_op src data hi sz)
Proof
  rewrite_tac[compile_abi_decode_dyn_elem_ptr_def] >>
  COVERAGE_BIND_WITH [abi_decode_id_coverage_addr] >> ntac 2 COVERAGE_BIND >>
  ho_match_mp_tac abi_decode_id_coverage_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[abi_decode_id_coverage_return] >>
      ntac 2 COVERAGE_BIND >> COVERAGE_IGNORE >>
      COVERAGE_BIND >> simp[abi_decode_id_coverage_range_check]) >>
  simp[abi_decode_id_coverage_return]
QED
