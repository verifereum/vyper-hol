(* Finite physical recursive decoding, with execution counts on every edge. *)
Theory bodyIntCallDecoderCountedLoopFinite
Ancestors
  bodyIntCallDecoderCountedLoopControl bodyIntCallDecoderCountedArrayBody
  bodyIntCallDecoderCountedContract abiScratchDecoderLoopContext
  abiDecoderRecursiveLoopContext abiScratchDecoderLoopInvariant
  abiScratchEncoderContract abiScratchEffect abiScratchDecoderContract
  abiDecoderValidArrayMemory abiDecoderContract abiDecoderLoop abiDecoderReentry
  compileEnv valueEncoding vyperABI venomState fragGasPath words list arithmetic

val recursive_context_tac =
  qhdtm_assum `abi_decoder_recursive_loop_compiled`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qhdtm_assum `abi_scratch_decoder_loop_data`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_data_def]);

Theorem intcall_scratch_decoder_header_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc base_op hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s ==>
  ?h. abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (if j < LENGTH vs then st.cs_current_bb else exit_lbl) j h /\ gas_path ctx func s 0 (OK h)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_loop_data_facts >> strip_tac >> recursive_context_tac >>
  qhdtm_assum `abi_scratch_decoder_ranges`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  drule_all intcall_scratch_decoder_loop_header >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem intcall_scratch_decoder_body_backedge:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc base_op hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\ intcall_scratch_decoder_counted ce env sf ty tv /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j s /\ j < LENGTH vs ==>
  ?v n. abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr (SUC j) v /\ gas_path ctx func s n (OK v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_loop_data_facts >> strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_scratch_decoder_loop_data_def, abi_scratch_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >> recursive_context_tac >>
  SUBGOAL_THEN ``site < st.cs_next_id \/ end_st.cs_next_id <= site`` assume_tac >- simp[] >>
  drule_all intcall_scratch_decoder_array_iteration >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_budget first last b cap actual` by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  drule_all abi_scratch_decoder_loop_slot_separation >> disch_then assume_tac >>
  `eval_operand (Var (STRING #"%" (toString st.cs_next_var))) actual = SOME (n2w j)` by metis_tac[] >>
  qpat_assum `(_ \/ _) /\ (_ ==> _)` (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\ _` strip_assume_tac >>
  drule_all intcall_scratch_decoder_loop_backedge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [] >> metis_tac[gas_path_then, ADD_CLAUSES]
QED

Theorem intcall_scratch_decoder_loop_iteration:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc base_op hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\ intcall_scratch_decoder_counted ce env sf ty tv /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s /\ j < LENGTH vs ==>
  ?v n. abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr (SUC j) v /\ gas_path ctx func s n (OK v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule_all intcall_scratch_decoder_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j h` by
    (qpat_x_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       (if _ then _ else _) _ _` mp_tac >> simp[]) >>
  drule_all intcall_scratch_decoder_body_backedge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [] >> metis_tac[gas_path_then, ADD_CLAUSES]
QED

Theorem intcall_scratch_decoder_loop_exit:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc base_op hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr (LENGTH vs) s ==>
  ?t. abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial exit_lbl (LENGTH vs) t /\ gas_path ctx func s 0 (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule_all intcall_scratch_decoder_header_reach >> simp[]
QED

Theorem intcall_gas_path_finite_iteration:
  (!i s. i < nmax /\ invp i s ==>
    ?t n. invp (SUC i) t /\ gas_path ctx func s n (OK t)) /\
  (!s. invp nmax s ==> ?t n. Post t /\ gas_path ctx func s n (OK t)) ==>
  !i s. i <= nmax /\ invp i s ==> ?t n. Post t /\ gas_path ctx func s n (OK t)
Proof
  strip_tac >>
  `!remaining i s. i + remaining = nmax /\ invp i s ==>
    ?t n. Post t /\ gas_path ctx func s n (OK t)` suffices_by
    (rpt strip_tac >> first_x_assum (qspecl_then [`nmax-i`, `i`, `s`] mp_tac) >> simp[]) >>
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> first_x_assum drule >> simp[]) >>
  `i < nmax` by decide_tac >>
  qpat_x_assum `!i s. i < nmax /\ _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!i s. i + remaining = nmax /\ _ ==> _`
    (qspecl_then [`SUC i`, `t`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  metis_tac[gas_path_then]
QED

Theorem intcall_scratch_decoder_loop_finite:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc base_op hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\ intcall_scratch_decoder_counted ce env sf ty tv /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr i s ==>
  ?t n. abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial exit_lbl (LENGTH vs) t /\ gas_path ctx func s n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i <= LENGTH vs` by
    fs[abi_scratch_decoder_loop_inv_def, abi_decoder_valid_array_memory_def, Excl "enc_def"] >>
  irule intcall_gas_path_finite_iteration >>
  qexistsl_tac [`i`, `abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr`, `LENGTH vs`] >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >> drule_all intcall_scratch_decoder_loop_iteration >> simp[]) >>
  rpt strip_tac >> drule_all intcall_scratch_decoder_loop_exit >> metis_tac[]
QED

Theorem intcall_scratch_decoder_loop_typed:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc base_op hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc base_op hi_op ip src dst
    B sb d slot first last b cap next initial /\ intcall_scratch_decoder_counted ce env sf ty tv /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr i s ==>
  ?t n. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\ gas_path ctx func s n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule_all intcall_scratch_decoder_loop_finite >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  drule abi_decoder_valid_array_memory_exit >> disch_then (qspec_then `maxn` assume_tac) >>
  qexistsl_tac [`t`, `n`] >> asm_simp_tac bool_ss []
QED
