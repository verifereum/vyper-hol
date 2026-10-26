(* Offset-following singleton composition retains the actual parent's initial state.
   The child contract may describe a fragment with arbitrary decoder CFG. *)
Theory abiDecoderSingletonFragment
Ancestors
  abiDecoderSingletonTyped abiDecoderSingletonSetup abiDecoderPointed
  abiDecoderTypedCompose abiDecoderTypedContract abiDecoderCoherence
  abiDecoderDynamic abiDecoderAppend abiDecoderContract
  fragExec exprLoweringProps compileEnv emitHelper valueEncoding
  venomExecSemantics venomState instIdxIndep combin list

Definition abi_decoder_pure_prefix_def:
  abi_decoder_pure_prefix initial mid <=>
    (!op w. eval_operand op initial = SOME w ==> eval_operand op mid = SOME w) /\
    mid.vs_memory = initial.vs_memory /\
    mid.vs_call_ctx = initial.vs_call_ctx /\
    mid.vs_data_section = initial.vs_data_section
End

Theorem abi_decoder_pure_prefix_inst_idx[simp]:
  abi_decoder_pure_prefix initial (mid with vs_inst_idx := ix) <=>
  abi_decoder_pure_prefix initial mid
Proof
  simp[abi_decoder_pure_prefix_def, eval_op_inst_idx]
QED

Theorem abi_decoder_singleton_post_function:
  abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v])) st' d outsz b cap initial =
  abi_decoder_post tv v st' d outsz b cap initial
Proof
  simp[FUN_EQ_THM, abi_decoder_singleton_post]
QED

Theorem abi_decoder_singleton_setup_fragment:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),middle) /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv]) di
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial /\
  is_dynamic (vyper_to_abi_type env ty) ==>
  frag_exec ctx st middle (\s. s = initial)
    (\mid. abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty)
       av v middle last child_src child_dst opc hi (sb + 32) d b cap mid /\
       abi_decoder_pure_prefix initial mid) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_singleton_recursive_setup >> strip_tac >>
  qexists_tac `t` >>
  simp[abi_decoder_recursive_pre_inst_idx, abi_decoder_pure_prefix_def,
       eval_op_inst_idx]
QED

Theorem abi_decoder_singleton_child_fragment:
  frag_exec ctx middle st' (\s. s = mid)
    (abi_decoder_post tv v st' d outsz b cap mid) (K F) /\
  abi_decoder_pure_prefix initial mid ==>
  frag_exec ctx middle st' (\s. s = mid)
    (abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v]))
       st' d outsz b cap initial) (K F)
Proof
  strip_tac >> irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = mid`, `abi_decoder_post tv v st' d outsz b cap mid`, `K F`] >>
  simp[abi_decoder_singleton_post] >> rpt strip_tac >>
  irule abi_decoder_post_pure_prefix >> qexists_tac `mid` >>
  fs[abi_decoder_pure_prefix_def]
QED

Theorem abi_decoder_offset_singleton_child_compile:
  dec_info_needs_offset di /\
  compile_abi_decode_to_buf dst src opc hi (DecComplex T [(di,32,mem_sz)]) st = ((),st') /\
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),middle) ==>
  compile_abi_decode_to_buf child_dst child_src opc hi di middle = ((),st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynamic_singleton_phases, comp_bind_def, LET_THM,
                       pairTheory.FST, pairTheory.SND, pairTheory.UNCURRY_DEF]
QED

Theorem abi_decoder_offset_singleton_fragment:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex T [(type_to_abi_dec_info sf ce ty,32,mem_sz)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex T [(type_to_abi_dec_info sf ce ty,32,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial /\
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) /\
  (!child_src child_dst middle mid.
    abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),middle) /\
    abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty)
      av v middle last child_src child_dst opc hi (sb + 32) d b cap mid ==>
    frag_exec ctx middle st' (\s. s = mid)
      (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap mid) (K F)) ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v]))
       st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule_all abi_decoder_coherent_singleton_dynamic >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_coherent_tuple_iff] >>
  `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    (drule_all abi_decoder_coherent_dynamic >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynamic_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_singleton_setup dst src opc hi st = (child_ops,middle)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),middle)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi
     (type_to_abi_dec_info sf ce ty) middle = ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decoder_singleton_setup_fragment >> strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends middle st'` by (drule_all cs_extends_abi_decode >> simp[]) >>
  irule frag_exec_initial_seq >>
  qexistsl_tac [`\mid. abi_decoder_recursive_pre ce env sf ty tv
     (type_to_abi_dec_info sf ce ty) av v middle last child_src child_dst opc hi
     (sb + 32) d b cap mid /\ abi_decoder_pure_prefix initial mid`, `middle`] >>
  simp[] >> rpt strip_tac >>
  irule abi_decoder_singleton_child_fragment >> conj_tac
  >- (first_x_assum irule >> simp[]) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_SINGLETON_FRAGMENT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI dynamic singleton fragment not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderSingletonFragment");
