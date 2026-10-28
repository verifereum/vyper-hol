(* TOP-LEVEL: distinct recorded allocations supply the bytestring encoder's
   source/destination separation. This also covers allocations already
   present when a loop executes its allocation instruction again.
   Helper: subwindows of distinct allocations remain disjoint. *)
Theory abiBytestringAllocation
Ancestors
  abiBytestringCorrect abiBytestringMemory memoryReadProps
  venomMemDefs venomState venomExecSemantics finite_map arithmetic words

Theorem allocated_windows_disjoint:
  !ss source_id target_id source_base source_size target_base target_size
      source_offset source_length target_offset target_length.
    allocas_non_overlapping ss /\ source_id <> target_id /\
    FLOOKUP ss.vs_allocas source_id = SOME (source_base,source_size) /\
    FLOOKUP ss.vs_allocas target_id = SOME (target_base,target_size) /\
    source_base <= source_offset /\
    source_offset + source_length <= source_base + source_size /\
    target_base <= target_offset /\
    target_offset + target_length <= target_base + target_size ==>
    source_offset + source_length <= target_offset \/
    target_offset + target_length <= source_offset
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `allocas_non_overlapping ss` mp_tac >>
  rewrite_tac[allocas_non_overlapping_def] >>
  disch_then (qspecl_then [`source_id`, `target_id`, `source_base`, `source_size`,
    `target_base`, `target_size`] mp_tac) >> impl_tac >- simp[] >> decide_tac
QED

Theorem bytestring_abi_pre_allocas:
  !ss source_id target_id source_base source_size target_base target_size
      dst_addr src_addr bs.
    allocas_non_overlapping ss /\ source_id <> target_id /\
    FLOOKUP ss.vs_allocas source_id = SOME (source_base,source_size) /\
    FLOOKUP ss.vs_allocas target_id = SOME (target_base,target_size) /\
    source_base <= w2n src_addr /\
    w2n src_addr + 32 + LENGTH bs <= source_base + source_size /\
    target_base <= w2n dst_addr /\
    w2n dst_addr + 32 + ceil32 (LENGTH bs) <= target_base + target_size /\
    target_base + target_size <= dimword(:256) /\
    32 + ceil32 (LENGTH bs) < dimword(:256) /\
    mload (w2n src_addr) ss = n2w (LENGTH bs) /\
    read_memory (w2n src_addr + 32) (LENGTH bs) ss = bs ==>
    bytestring_abi_pre dst_addr src_addr bs ss /\
    (w2n src_addr + 32 + LENGTH bs <= w2n dst_addr \/
     w2n dst_addr + 32 + ceil32 (LENGTH bs) <= w2n src_addr)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n src_addr + 32 + LENGTH bs <= w2n dst_addr \/
   w2n dst_addr + 32 + ceil32 (LENGTH bs) <= w2n src_addr` by
    (mp_tac (Q.SPECL [`ss`, `source_id`, `target_id`, `source_base`, `source_size`,
       `target_base`, `target_size`, `w2n (src_addr:bytes32)`,
       `32 + LENGTH (bs:word8 list)`, `w2n (dst_addr:bytes32)`,
       `32 + ceil32 (LENGTH (bs:word8 list))`] allocated_windows_disjoint) >>
     impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> decide_tac) >>
  asm_simp_tac bool_ss [bytestring_abi_pre_def] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI bytestring allocation theorem: " ^ name)
  end)
  (DB.thms "abiBytestringAllocation")
