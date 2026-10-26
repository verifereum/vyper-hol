(* Wrapped static-element DynArrays: complete recursive execution, with no
   assumed child execution contract. Aggregate elements use the bulk path. *)
Theory abiDecoderSingletonBulk
Ancestors
  abiDecoderSingletonFragment abiDecoderPointed abiDecoderDynamic
  abiDecoderTypedCompose abiDecoderCoherence abiDecoderTypedContract
  abiEncoder exprLowering compileEnv vyperABI contractABI valueEncoding
  fragExec combin

Theorem abi_decoder_wrapped_bulk_from_state:
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex T [(DecDynArray ei abi_sz mem_sz F maxn,32,outsz)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ArrayT ty (Dynamic maxn)])
    (TupleTV [ArrayTV tv (Dynamic maxn)])
    (DecComplex T [(DecDynArray ei abi_sz mem_sz F maxn,32,outsz)])
    (ListV [ListV avs]) (ArrayV (TupleV [ArrayV (DynArrayV vs)]))
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
       st' d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial) (K F)
Proof
  strip_tac >>
  irule (SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    (Q.INST [`ty` |-> `ArrayT ty (Dynamic maxn)`,
      `tv` |-> `ArrayTV tv (Dynamic maxn)`, `av` |-> `ListV avs`,
      `v` |-> `ArrayV (DynArrayV vs)`, `mem_sz` |-> `outsz`]
      abi_decoder_offset_singleton_fragment)) >>
  qexistsl_tac [`avs`, `dst`, `env`, `hi`, `last`, `opc`, `outsz`, `sb`, `sf`, `src`] >>
  asm_simp_tac (srw_ss()) [vyper_to_abi_type_def, is_dynamic_def, dec_info_needs_offset_def] >>
  rpt strip_tac >>
  `compile_abi_decode_to_buf child_dst child_src opc hi
     (DecDynArray ei abi_sz mem_sz F maxn) middle = ((),st')` by
    (irule abi_decoder_offset_singleton_child_compile >>
     conj_tac >- simp[dec_info_needs_offset_def] >>
     qexistsl_tac [`dst`, `outsz`, `src`, `st`] >>
     simp[abi_decoder_dynamic_def]) >>
  drule_all abi_decoder_typed_bulk_from_state >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_SINGLETON_BULK_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI wrapped bulk decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderSingletonBulk");
