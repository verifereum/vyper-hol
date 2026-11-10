Theory typedNormalizeContinuation
Ancestors
  fragExec loweringHalt exprLoweringProps stmtLowering emitHelper
  venomExecSemantics compileEnv context venomInst exprLowering
  typedArrayLoopControlMem abiDecoderPhi abiEncoderExitPhi stmtLoweringMono

Theorem normalize_alloc_continuation_entry[local]:
  compile_alloc_buffer n sa = (buf,sc) /\ cs_extends sc sb /\
  fn_has_code sa sb fn /\ sa.cs_current_insts = [] ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `cs_extends sa sc` by
    (mp_tac (Q.SPECL [`n`, `sa`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `fn_has_code sa sc fn` mp_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  strip_tac >> goal_assum (drule_at Any) >> simp[phi_prefix_length_def, mk_inst_def]
QED

(* Covers every ABI encoder constructor, including dynamic child CFGs. *)
Theorem normalize_abi_return_entry[local]:
  compile_external_return (SOME op) F F info msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ fn_has_code sa sb fn /\ sa.cs_current_insts = [] ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all compile_external_return_abi_parts >> strip_tac >>
  `cs_extends sa' sb'` by
    (mp_tac (cj 2 ci_mono_compile_abi_encode) >>
     disch_then (qspecl_then [`buf.buf_operand`, `op`, `info`, `sa'`] mp_tac) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sb' sb` by
    (mp_tac (Q.SPECL [`RETURN`, `[buf.buf_operand; len]`, `[]`, `sb'`]
      ci_mono_emit_inst) >> asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sa' sb` by metis_tac[cs_extends_trans] >>
  drule_all normalize_alloc_continuation_entry >> simp[]
QED

Theorem normalize_external_return_entry:
  compile_external_return ret prim raw info msz nr nkey ut iv sa = (x,sb) /\
  (nr ==> iv) /\ fn_has_code sa sb fn /\
  phi_prefix_length sa.cs_current_insts = 0 ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `sa.cs_current_insts = []`
  >- (Cases_on `ret`
  >- (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_external_return_def, optional_unlock_view, emit_inst_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[phi_prefix_length_def, mk_inst_def]) >>
  Cases_on `raw`
  >- (qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_external_return_def, optional_unlock_view, emit_op_def, emit_inst_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[phi_prefix_length_def, mk_inst_def]) >>
  Cases_on `prim`
  >- (drule_all compile_external_return_word_parts >> strip_tac >>
      gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[phi_prefix_length_def, mk_inst_def]) >>
  drule_all normalize_abi_return_entry >> simp[]) >>
  `cs_extends sa sb` by
    metis_tac[cj 3 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  drule_all fn_has_code_start >> strip_tac >> goal_assum (drule_at Any) >>
  irule abi_encoder_nonempty_prefix_phi >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Zero offsets emit no instruction: use the enclosing continuation certificate. *)
Theorem normalize_field_offset_entry:
  compile_with_byte_offset op off sa = (out,sb) /\
  fn_has_code sa sb fn /\ phi_prefix_length sa.cs_current_insts = 0 /\
  (off = 0 ==> ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  Cases_on `off = 0`
  >- simp[compile_with_byte_offset_def, comp_return_def] >>
  simp[compile_with_byte_offset_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  Cases_on `sa.cs_current_insts` >>
  gvs[phi_prefix_length_def, mk_inst_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

Theorem normalize_array_backedge_entry:
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = ec.cs_current_insts ++ typed_sa_backedge_insts id ctr nv hdr /\
  phi_prefix_length ec.cs_current_insts = 0 ==>
  ?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
    phi_prefix_length entry.bb_instructions = 0
Proof
  strip_tac >> qexists_tac `bb` >> simp[] >>
  Cases_on `ec.cs_current_insts` >>
  gvs[typed_sa_backedge_insts_def, phi_prefix_length_def, mk_inst_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

(* Reuse the decoder's generic PHI-free compiler-state invariant.  In
   particular it tracks newly closed blocks as well as the current prefix. *)
Theorem normalize_phi_fresh_var[local]:
  abi_decoder_phi sa (SND (fresh_var sa))
Proof
  simp[fresh_var_def, abi_decoder_phi_def, abi_decoder_phi_safe_def]
QED

Theorem normalize_phi_copy[local]:
  (!dst src sz sa. abi_decoder_phi sa (SND (compile_copy_memory dst src sz sa))) /\
  (!dst src len sa. abi_decoder_phi sa (SND (compile_copy_memory_dynamic dst src len sa))) /\
  (!op off sa. abi_decoder_phi sa (SND (compile_with_byte_offset op off sa)))
Proof
  rpt conj_tac
  >- (rpt gen_tac >> Cases_on `sz` >>
      simp[compile_copy_memory_def, abi_decoder_phi_return, abi_decoder_phi_emit_void])
  >- simp[compile_copy_memory_dynamic_def, abi_decoder_phi_emit_void] >>
  rpt gen_tac >> simp[compile_with_byte_offset_def] >>
  IF_CASES_TAC >> simp[abi_decoder_phi_return, abi_decoder_phi_emit_op]
QED

Theorem normalize_phi_bytes[local]:
  !src dst sa. abi_decoder_phi sa (SND (compile_store_bytestring src dst sa))
Proof
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def, LET_THM] >>
  rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- (rpt gen_tac >>
      ntac 4 (ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
        >- simp[abi_decoder_phi_emit_op] >> rpt gen_tac) >>
      simp[abi_decoder_phi_emit_op]) >>
  simp[abi_decoder_phi_emit_void]
QED

Theorem normalize_phi_typed_family:
  (!cenv dst dt src st sa.
    abi_decoder_phi sa (SND (compile_store_memory_typed cenv dst dt src st sa))) /\
  (!cenv dst src dts sts doff soff sa.
    abi_decoder_phi sa (SND (compile_typed_copy_fields cenv dst src dts sts doff soff sa))) /\
  (!cenv dst dt src st count sa.
    abi_decoder_phi sa (SND (compile_copy_sarray_typed cenv dst dt src st count sa))) /\
  (!cenv dst dt cap src st sa.
    abi_decoder_phi sa (SND (compile_copy_dynarray_typed cenv dst dt cap src st sa))) /\
  (!cenv dst src dfs sfs doff soff sa.
    abi_decoder_phi sa (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff sa)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume normalize_phi_typed_family[dispatch]:
  rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dt`
  >- (simp[Once compile_store_memory_typed_def] >>
      irule abi_decoder_phi_bind >>
      simp[abi_decoder_phi_emit_op, abi_decoder_phi_emit_void]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- simp[Once compile_store_memory_typed_def, normalize_phi_bytes] >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dt` >> Cases_on `st`
      >~ [`compile_store_memory_typed cenv dst (ArrayT a b) src (ArrayT c d)`]
      >- (Cases_on `b` >> Cases_on `d` >> gvs[] >>
           simp[Once compile_store_memory_typed_def, LET_THM, normalize_phi_copy] >>
           metis_tac[]) >>
      gvs[] >>
      simp[Once compile_store_memory_typed_def, LET_THM, normalize_phi_copy] >>
      metis_tac[]) >>
  simp[Once compile_store_memory_typed_def, abi_decoder_phi_emit_void]
QED

Resume normalize_phi_typed_family[fields_nil]:
  simp[Once compile_store_memory_typed_def, abi_decoder_phi_return]
QED
Resume normalize_phi_typed_family[fields_mismatch]:
  simp[Once compile_store_memory_typed_def, abi_decoder_phi_return]
QED
Resume normalize_phi_typed_family[fields_cons]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_store_memory_typed_def, LET_THM] >>
  gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[normalize_phi_copy] >>
  rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
  >- simp[normalize_phi_copy] >>
  rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_ignore_bind >> simp[]
QED

Resume normalize_phi_typed_family[sarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM] >>
  IF_CASES_TAC >- simp[normalize_phi_copy] >>
  gvs[] >>
  rpt (FIRST [ho_match_mp_tac abi_decoder_phi_bind,
              ho_match_mp_tac abi_decoder_phi_ignore_bind,
              conj_tac >- simp[abi_decoder_phi_fresh_label, normalize_phi_fresh_var,
                abi_decoder_phi_emit_inst, abi_decoder_phi_new_block,
                abi_decoder_phi_emit_op, abi_decoder_phi_return], gen_tac]) >>
  simp[abi_decoder_phi_return]
QED

Resume normalize_phi_typed_family[dynarray]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_store_memory_typed_def, LET_THM] >>
  rpt (FIRST [ho_match_mp_tac abi_decoder_phi_bind,
              ho_match_mp_tac abi_decoder_phi_ignore_bind,
              conj_tac >- simp[abi_decoder_phi_emit_op, abi_decoder_phi_emit_void], gen_tac]) >>
  IF_CASES_TAC
  >- (ho_match_mp_tac abi_decoder_phi_bind >>
      simp[abi_decoder_phi_emit_op, normalize_phi_copy]) >>
  gvs[] >>
  rpt (FIRST [ho_match_mp_tac abi_decoder_phi_bind,
              ho_match_mp_tac abi_decoder_phi_ignore_bind,
              conj_tac >- simp[abi_decoder_phi_fresh_label, normalize_phi_fresh_var,
                abi_decoder_phi_emit_inst, abi_decoder_phi_new_block,
                abi_decoder_phi_emit_op, abi_decoder_phi_return], gen_tac]) >>
  simp[abi_decoder_phi_return]
QED

Resume normalize_phi_typed_family[struct_nil]:
  simp[Once compile_store_memory_typed_def, abi_decoder_phi_return]
QED
Resume normalize_phi_typed_family[struct_cons]:
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP sfs name`
  >- (gvs[] >> simp[Once compile_store_memory_typed_def, LET_THM] >>
      gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
      >- simp[normalize_phi_copy] >>
      rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
      >- simp[normalize_phi_copy] >>
      rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_ignore_bind >> simp[]) >>
  rename1 `SOME p` >> PairCases_on `p` >> gvs[] >>
  (simp[Once compile_store_memory_typed_def, LET_THM] >>
   gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
   >- simp[normalize_phi_copy] >>
   rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_bind >> conj_tac
   >- simp[normalize_phi_copy] >>
   rpt gen_tac >> ho_match_mp_tac abi_decoder_phi_ignore_bind >> simp[])
QED
Finalise normalize_phi_typed_family

Theorem normalize_typed_prefix_zero:
  compile_store_memory_typed cenv dst dt src st sa = (x,sb) /\
  phi_prefix_length sa.cs_current_insts = 0 ==>
  phi_prefix_length sb.cs_current_insts = 0
Proof
  strip_tac >>
  mp_tac (cj 1 normalize_phi_typed_family) >>
  disch_then (qspecl_then [`cenv`, `dst`, `dt`, `src`, `st`, `sa`] mp_tac) >>
  simp[abi_decoder_phi_def] >> strip_tac >>
  irule abi_decoder_phi_safe_head >> goal_assum (drule_at Any) >> simp[]
QED

Theorem normalize_fields_prefix_zero:
  compile_typed_copy_fields cenv dst src dts sts doff soff sa = (x,sb) /\
  phi_prefix_length sa.cs_current_insts = 0 ==>
  phi_prefix_length sb.cs_current_insts = 0
Proof
  strip_tac >>
  mp_tac (cj 2 normalize_phi_typed_family) >>
  disch_then (qspecl_then [`cenv`, `dst`, `src`, `dts`, `sts`, `doff`, `soff`, `sa`] mp_tac) >>
  simp[abi_decoder_phi_def] >> strip_tac >>
  irule abi_decoder_phi_safe_head >> goal_assum (drule_at Any) >> simp[]
QED

Theorem normalize_typed_backedge_entry:
  compile_store_memory_typed cenv dst dt src st sa = (x,ec) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  lookup_block ec.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = ec.cs_current_insts ++ typed_sa_backedge_insts id ctr nv hdr ==>
  ?entry. lookup_block ec.cs_current_bb fn.fn_blocks = SOME entry /\
    phi_prefix_length entry.bb_instructions = 0
Proof
  strip_tac >> drule_all normalize_typed_prefix_zero >> strip_tac >>
  metis_tac[normalize_array_backedge_entry]
QED

(* A zero-code field offset needs the enclosing suffix's real entry block.
   Nonzero offsets provide their own non-PHI instruction, even after a child
   that left a nonempty prefix. *)
Theorem normalize_typed_field_offset_entry:
  compile_store_memory_typed cenv dst dt src st sa = (x,ec) /\
  phi_prefix_length sa.cs_current_insts = 0 /\
  compile_with_byte_offset op off ec = (out,sb) /\
  fn_has_code ec sb fn /\
  (off = 0 ==> ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb. lookup_block ec.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule_all normalize_typed_prefix_zero >> strip_tac >>
  drule_all normalize_field_offset_entry >> simp[]
QED

(* A real terminal certificate transports backwards across a PHI-safe suffix,
   including the zero-code case.  Finalized entry blocks are covered by the
   compiler's PHI invariant, not by code containment alone. *)
Theorem normalize_phi_suffix_entry:
  cs_extends sa sb /\ abi_decoder_phi sa sb /\
  phi_prefix_length sa.cs_current_insts = 0 /\ fn_has_code sa sb fn /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `abi_decoder_phi_safe sa.cs_blocks sa` by
    (simp[abi_decoder_phi_safe_def] >> qexists_tac `[]` >> simp[]) >>
  `abi_decoder_phi_safe sa.cs_blocks sb` by
    metis_tac[abi_decoder_phi_def] >>
  qpat_x_assum `cs_extends sa sb` mp_tac >>
  simp_tac bool_ss [cs_extends_def] >> strip_tac >>
  Cases_on `new = []` >- gvs[] >>
  `EVERY (\bb. phi_prefix_length bb.bb_instructions = 0) new` by
    gvs[abi_decoder_phi_safe_def] >>
  `MEM (LAST new) new` by metis_tac[rich_listTheory.MEM_LAST_NOT_NIL] >>
  `phi_prefix_length (LAST new).bb_instructions = 0` by
    (qpat_x_assum `EVERY _ new` mp_tac >>
     simp[ listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `emitted_blocks sa sb = new` by
    simp[emitted_blocks_def, rich_listTheory.TAKE_LENGTH_APPEND] >>
  gvs[fn_has_code_def] >> metis_tac[]
QED

Theorem normalize_fields_suffix_entry:
  compile_typed_copy_fields ce dst src dts sts doff soff sa = (x,sb) /\
  phi_prefix_length sa.cs_current_insts = 0 /\ fn_has_code sa sb fn /\
  (?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> irule normalize_phi_suffix_entry >>
  simp[] >> qexists_tac `sb` >> simp[] >> reverse conj_tac
  >- metis_tac[cj 2 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  mp_tac (cj 2 normalize_phi_typed_family) >>
  disch_then (qspecl_then [`ce`,`dst`,`src`,`dts`,`sts`,`doff`,`soff`,`sa`] mp_tac) >>
  simp[]
QED

Theorem normalize_offset_prefix_zero:
  compile_with_byte_offset op off sa = (out,sb) /\
  phi_prefix_length sa.cs_current_insts = 0 ==>
  phi_prefix_length sb.cs_current_insts = 0
Proof
  strip_tac >>
  mp_tac (cj 3 normalize_phi_copy) >>
  disch_then (qspecl_then [`op`,`off`,`sa`] mp_tac) >> simp[] >>
  strip_tac >> irule abi_decoder_phi_safe_head >>
  metis_tac[abi_decoder_phi_def]
QED
