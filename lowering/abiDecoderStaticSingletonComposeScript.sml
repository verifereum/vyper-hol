(* Static singleton composition is independent of the child's decoder body. *)
Theory abiDecoderStaticSingletonCompose
Ancestors
  abiDecoderStaticSingletonTyped abiDecoderStaticSingleton abiDecoderSingletonFragment
  abiDecoderPointed abiDecoderTypedContract abiDecoderCoherence abiDecoderAppend
  abiDecoderContract abiDecoderDynamic fragExec exprLoweringProps compileEnv
  emitHelper valueEncoding venomExecSemantics venomState venomInst
  instIdxIndep combin list

Theorem abi_decoder_static_singleton_setup_fragment:
  abi_decode_static_singleton_setup dst src hi head_sz st =
    ((child_src,child_dst),middle) /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st middle (\s. s = initial)
    (\mid. abi_decoder_recursive_pre ce env sf ty tv di av v
       middle last child_src child_dst opc hi sb d b cap mid /\
       abi_decoder_pure_prefix initial mid) (K F)
Proof
  strip_tac >> drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st middle)` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_static_singleton_setup >> strip_tac >>
  qexists_tac `t` >>
  simp[abi_decoder_recursive_pre_inst_idx, abi_decoder_pure_prefix_def,
       eval_op_inst_idx]
QED

Theorem abi_decoder_static_singleton_fragment:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex F [(di,head_sz,mem_sz)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex F [(di,head_sz,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial /\
  (!child_src child_dst middle mid.
    abi_decode_static_singleton_setup dst src hi head_sz st =
      ((child_src,child_dst),middle) /\
    abi_decoder_recursive_pre ce env sf ty tv di av v
      middle last child_src child_dst opc hi sb d b cap mid ==>
    frag_exec ctx middle st' (\s. s = mid)
      (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap mid) (K F)) ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (TupleTV [tv]) (ArrayV (TupleV [v]))
       st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  `~abi_decoder_dynamic di` by
    (drule_all abi_decoder_static_singleton_child >> strip_tac >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_singleton_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_static_singleton_setup dst src hi head_sz st = (child_ops,middle)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_static_singleton_setup dst src hi head_sz st =
    ((child_src,child_dst),middle)` >>
  `compile_abi_decode_to_buf child_dst child_src opc hi di middle = ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decoder_static_singleton_setup_fragment >> strip_tac >>
  drule_all abi_decode_static_singleton_setup_shape >> strip_tac >>
  `cs_extends st middle` by (irule cs_extends_same_block >> simp[]) >>
  `cs_extends middle st'` by (drule_all cs_extends_abi_decode >> simp[]) >>
  irule frag_exec_initial_seq >>
  qexistsl_tac [`\mid. abi_decoder_recursive_pre ce env sf ty tv di av v
     middle last child_src child_dst opc hi sb d b cap mid /\
     abi_decoder_pure_prefix initial mid`, `middle`] >>
  simp[] >> rpt strip_tac >>
  irule abi_decoder_singleton_child_fragment >> conj_tac
  >- (first_x_assum irule >> simp[]) >> simp[]
QED

Theorem abi_decoder_static_singleton_unwrapped_fragment =
  SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    abi_decoder_static_singleton_fragment;

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STATIC_SINGLETON_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static singleton composition not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderStaticSingletonCompose");
