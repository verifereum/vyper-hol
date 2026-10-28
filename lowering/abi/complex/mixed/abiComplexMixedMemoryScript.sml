(* TOP-LEVEL: a complete mixed aggregate arena supplies every smaller
   output separation needed by its static field and following dynamic field. *)
Theory abiComplexMixedMemory
Ancestors
  abiBytesFieldReady abiFieldBytesPath abiFieldLayoutDefs abiMemoryFrame abiEncoderPathProps
  contractABI compileEnv venomState list pair words arithmetic

Theorem abi_complex_mixed_regions:
  !dst_addr dyn_addr payload bs.
    w2n dst_addr + LENGTH payload + 32 + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword(:256) /\
    regions_disjoint (w2n dst_addr)
      (LENGTH payload + 32 + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) (w2n dyn_addr) 32 ==>
    LENGTH payload < dimword(:256) /\
    abi_window_separated (w2n dyn_addr) 32 (w2n dst_addr) (LENGTH payload) /\
    abi_bytes_field_geometry [(F,payload)] (LENGTH payload + 32) dst_addr dyn_addr bs
Proof
  rpt gen_tac >> strip_tac >>
  `w2n dst_addr + LENGTH payload < dimword(:256)` by decide_tac >>
  `w2n dst_addr + (LENGTH payload + 32) < dimword(:256)` by decide_tac >>
  `w2n (dst_addr + n2w (LENGTH payload)) = w2n dst_addr + LENGTH payload` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  `w2n (dst_addr + n2w (LENGTH payload + 32)) = w2n dst_addr + (LENGTH payload + 32)` by
    (irule abi_field_word_address >> first_assum MATCH_ACCEPT_TAC) >>
  fs[abi_bytes_field_geometry_def, abi_field_head_size_def, abi_field_tail_def, LET_THM,
    abi_window_separated_def, regions_disjoint_def] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed mixed aggregate ABI output geometry: " ^ name)
  end) (DB.thms "abiComplexMixedMemory")
