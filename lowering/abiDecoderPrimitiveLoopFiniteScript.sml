(* A finite primitive-array loop, with the body supplied by actual compilation. *)
Theory abiDecoderPrimitiveLoopFinite
Ancestors
  abiDecoderPrimitiveLoopBackedge abiDecoderPrimitiveLoopReach
  abiDecoderPrimitiveLoopHeader abiDecoderPrimitiveLoopContext
  abiDecoderPrimitiveLoopInvariant abiDecoderArrayInvariant
  abiDecoderExecution abiDecoderLoop abiDecoderReentry
  compileEnv valueEncoding venomState words list arithmetic

Theorem abi_decoder_primitive_loop_header_reach:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr j s ==>
  ?h. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial (if j < LENGTH vs then st0.cs_current_bb else exit_lbl) j h /\
    abi_decode_sim ctx fn s h
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_code_def]) >>
  qpat_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_data_def]) >>
  qpat_assum `abi_decoder_loop_inputs _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_inputs_def]) >>
  drule_all abi_decoder_primitive_loop_header >> simp[]
QED

Theorem abi_decoder_primitive_loop_iteration:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr j s /\ j < LENGTH vs ==>
  ?v. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial hdr (SUC j) v /\ abi_decode_sim ctx fn s v
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial st0.cs_current_bb j h` by
    (qpat_x_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _
       (if _ then _ else _) _ _` mp_tac >> simp[]) >>
  drule_all abi_decoder_primitive_loop_body_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_primitive_loop_backedge_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [] >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem abi_decoder_primitive_loop_exit:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr (LENGTH vs) s ==>
  ?t. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial exit_lbl (LENGTH vs) t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_header_reach >> simp[]
QED

Theorem abi_decoder_primitive_loop_finite:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr i s ==>
  ?t. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial exit_lbl (LENGTH vs) t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `i <= LENGTH vs` by
    fs[abi_decoder_primitive_loop_inv_def, abi_decoder_array_memory_def, Excl "enc_def"] >>
  mp_tac (Q.SPECL [`LENGTH (vs:vyperValue$value list)`, `i:num`,
    `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial hdr`,
    `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial exit_lbl (LENGTH vs)`, `ctx`, `fn`, `s`]
    abi_decode_finite_iteration) >>
  impl_tac
  >- (conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac
      >- (rpt strip_tac >> drule_all abi_decoder_primitive_loop_iteration >> simp[]) >>
      rpt strip_tac >> drule_all abi_decoder_primitive_loop_exit >> simp[]) >>
  simp[]
QED

Theorem abi_decoder_primitive_loop_typed:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr i s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_loop_rel first limit_st fp initial t /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    mload slot t = n2w (LENGTH vs) /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_finite >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> fs[abi_decoder_primitive_loop_inv_def] >>
  drule_all abi_decoder_array_memory_exit >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_FINITE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive finite loop not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopFinite");
