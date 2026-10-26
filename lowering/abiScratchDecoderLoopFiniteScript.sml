(* Finite execution of the actual recursive body, header and backedge. *)
Theory abiScratchDecoderLoopFinite
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract
  abiDecoderRecursiveLoopContext abiScratchDecoderLoopContext abiScratchDecoderArrayIteration abiDecoderValidArrayMemory
  abiScratchDecoderLoopInvariant abiDecoderEffect abiDecoderTypedContract
  abiDecoderContract abiDecoderValidContract abiDecoderExecution abiDecoderLoop
  abiDecoderReentry compileEnv valueEncoding vyperABI vyperValue venomState words list arithmetic

val recursive_context_tac =
  qpat_assum `abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst
    opc hi_op hdr exit_lbl hid header_var first last lo hi next limit_st site`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_data_def]);

Theorem abi_scratch_decoder_header_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s ==>
  ?h. abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial
    (if j < LENGTH vs then st.cs_current_bb else exit_lbl) j h /\ abi_decode_sim ctx func s h
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_loop_data_facts >> strip_tac >> recursive_context_tac >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  drule_all abi_scratch_decoder_loop_header >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem abi_scratch_decoder_body_backedge:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\ abi_scratch_decoder ce env sf ty tv /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j s /\ j < LENGTH vs ==>
  ?v. abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr (SUC j) v /\ abi_decode_sim ctx func s v
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_loop_data_facts >> strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_scratch_decoder_loop_data_def, abi_scratch_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >> recursive_context_tac >>
  SUBGOAL_THEN ``site < st.cs_next_id \/ end_st.cs_next_id <= site`` assume_tac >- simp[] >>
  drule_all abi_scratch_decoder_array_iteration >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_budget first last b cap actual` by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  drule_all abi_scratch_decoder_loop_slot_separation >> disch_then assume_tac >>
  `eval_operand (Var (STRING #"%" (toString st.cs_next_var))) actual = SOME (n2w j)`
    by metis_tac[] >>
  qpat_assum `(_ \/ _) /\ (_ ==> _)` (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\ _`
    strip_assume_tac >>
  drule_all abi_scratch_decoder_loop_backedge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED

Theorem abi_scratch_decoder_loop_iteration:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\ abi_scratch_decoder ce env sf ty tv /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s /\ j < LENGTH vs ==>
  ?v. abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr (SUC j) v /\ abi_decode_sim ctx func s v
Proof
  strip_tac >> drule_all abi_scratch_decoder_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j h` by
    (qpat_x_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       (if _ then _ else _) _ _` mp_tac >> simp[]) >>
  drule_all abi_scratch_decoder_body_backedge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED

Theorem abi_scratch_decoder_loop_exit:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr (LENGTH vs) s ==>
  ?t. abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial exit_lbl (LENGTH vs) t /\ abi_decode_sim ctx func s t
Proof
  strip_tac >> drule_all abi_scratch_decoder_header_reach >> simp[]
QED

Theorem abi_scratch_decoder_loop_finite:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\ abi_scratch_decoder ce env sf ty tv /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr i s ==>
  ?t. abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial exit_lbl (LENGTH vs) t /\ abi_decode_sim ctx func s t
Proof
  strip_tac >>
  `i <= LENGTH vs` by
    fs[abi_scratch_decoder_loop_inv_def, abi_decoder_valid_array_memory_def, Excl "enc_def"] >>
  mp_tac (Q.SPECL [`LENGTH (vs:vyperValue$value list)`, `i:num`,
    `abi_scratch_decoder_loop_inv opc bs tv vs sb d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
      first last lo hi next limit_st b cap initial hdr`,
    `abi_scratch_decoder_loop_inv opc bs tv vs sb d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
      first last lo hi next limit_st b cap initial exit_lbl (LENGTH vs)`, `ctx`, `func`, `s`]
    abi_decode_finite_iteration) >>
  impl_tac
  >- (conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac
      >- (rpt strip_tac >> drule_all abi_scratch_decoder_loop_iteration >> simp[]) >>
      rpt strip_tac >> drule_all abi_scratch_decoder_loop_exit >> simp[]) >>
  simp[]
QED

Theorem abi_scratch_decoder_loop_typed:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs opc hi_op ip src dst
    sb d slot first last b cap next initial /\ abi_scratch_decoder ce env sf ty tv /\
  abi_scratch_decoder_loop_inv opc bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr i s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w (LENGTH vs) /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\ abi_decode_sim ctx func s t
Proof
  strip_tac >> drule_all abi_scratch_decoder_loop_finite >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  drule abi_decoder_valid_array_memory_exit >> disch_then (qspec_then `maxn` assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_LOOP_FINITE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical finite array loop not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderLoopFinite");

