(* Readonly execution boundary for the extract32 load and clamp. *)
Theory bodyMemTbExtract32Readonly
Ancestors
  bodyMemTbExtract32Load exprSimBopRestWordLoadPath freshWrites
  exprLowering builtinBytes emitHelper emitHelperProps exprLoweringProps compileEnv venomState venomInst
  list rich_list finite_map ASCIInumbers

Theorem extract32_load_output_range[local]:
  compile_extract32_load l d off sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode [ADD; LT; OR; ISZERO; ASSERT; GT; MLOAD] /\
    !x. MEM x i.inst_outputs ==>
      ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
          x = STRING #"%" (toString n)) (emitted_insts sa sb)
Proof
  simp[compile_extract32_load_def, compile_assert_slice_bounds_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_ADD_SUC]
QED

Theorem extract32_clamp_output_range[local]:
  !v ty sa op sb.
  compile_clamp_basetype v ty sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode
      [LT; GT; SLT; SGT; EQ; ISZERO; OR; AND; SHR; SHL; SAR;
       SIGNEXTEND; ASSERT] /\
    !x. MEM x i.inst_outputs ==>
      ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
          x = STRING #"%" (toString n)) (emitted_insts sa sb)
Proof
  recInduct compile_clamp_basetype_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[compile_clamp_basetype_def, clamp_and_return_def, compile_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[type_bounds_def, is_signed_type_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_ADD_SUC]
QED

Theorem extract32_suffix_output_range:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode
      [ADD; LT; GT; SLT; SGT; EQ; ISZERO; OR; AND; SHR; SHL; SAR;
       SIGNEXTEND; ASSERT; MLOAD] /\
    !x. MEM x i.inst_outputs ==>
      ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
          x = STRING #"%" (toString n))
    (emitted_insts sa sc ++ emitted_insts sc sb)
Proof
  strip_tac >> drule extract32_load_output_range >> strip_tac >>
  drule extract32_clamp_output_range >> strip_tac >>
  simp[EVERY_APPEND, EVERY_MEM] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem extract32_suffix_readonly_frame:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. (!n. sa.cs_next_var <= n /\ n < sb.cs_next_var ==>
              x <> STRING #"%" (toString n)) ==>
       FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all extract32_suffix_output_range >> strip_tac >>
  ho_match_mp_tac run_inst_seq_protected_frame >>
  qexists `emitted_insts sa sc ++ emitted_insts sc sb` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `MEM i.inst_opcode
      [ADD; LT; GT; SLT; SGT; EQ; ISZERO; OR; AND; SHR; SHL; SAR;
       SIGNEXTEND; ASSERT; MLOAD] /\
   (!x. MEM x i.inst_outputs ==>
     ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
         x = STRING #"%" (toString n))` by
    (qpat_x_assum `EVERY _ _` mp_tac >> pure_rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  Cases_on `i.inst_opcode = MLOAD`
  >- (`MEM i.inst_opcode [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD]` by simp[] >>
      drule_all rest_word_step_load_frame >> strip_tac >> metis_tac[]) >>
  `MEM i.inst_opcode
      [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
       EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
       SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSERT; ASSERT_UNREACHABLE]` by gvs[] >>
  drule_all step_pure_opcode_frame >> strip_tac >> metis_tac[]
QED

Theorem extract32_suffix_lookup_kept:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t /\
  not_fresh_at sa x ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> drule_all extract32_suffix_readonly_frame >> strip_tac >>
  simp[lookup_var_def] >> first_x_assum irule >>
  gvs[not_fresh_at_def]
QED

Theorem extract32_suffix_fresh:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t /\
  fresh_vars_wrt sa s ==>
  fresh_vars_wrt sb t
Proof
  strip_tac >> drule_all extract32_suffix_output_range >> strip_tac >>
  drule_all extract32_suffix_readonly_frame >> strip_tac >>
  fs[fresh_vars_wrt_def] >> rpt strip_tac >>
  `FLOOKUP t.vs_vars (STRING #"%" (toString n)) =
   FLOOKUP s.vs_vars (STRING #"%" (toString n))` by
    (first_x_assum irule >> rpt strip_tac >>
     gvs[ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `n >= sa.cs_next_var` by decide_tac >>
  `STRING #"%" (toString n) NOTIN FDOM s.vs_vars` by metis_tac[] >>
  qpat_x_assum `!x. _ ==> FLOOKUP _ _ = _` kall_tac >>
  qpat_x_assum `FLOOKUP t.vs_vars _ = _` mp_tac >>
  simp[FLOOKUP_DEF]
QED
