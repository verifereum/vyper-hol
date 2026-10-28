(* TOP-LEVEL: a common output/scratch memory frame preserves every remaining
   field's initial source observation, at its actual source and tail offsets. *)
Theory abiFlatSourcesFrame
Ancestors
  abiFlatFieldsDefs abiComplexMemory abiMemoryFrame abiFieldLayoutDefs
  abiBytestringCorrect compileEnv venomState list words

Theorem abi_flat_source_read_frame:
  !row src_addr tail_addr before after.
    read_memory (w2n src_addr) (abi_flat_source_count row) after =
      read_memory (w2n src_addr) (abi_flat_source_count row) before ==>
    (abi_flat_source row src_addr tail_addr after = abi_flat_source row src_addr tail_addr before)
Proof
  rpt gen_tac >> Cases_on `row`
  >- simp[abi_flat_source_def, abi_flat_source_count_def] >>
  simp_tac bool_ss [abi_flat_source_def, abi_flat_source_count_def] >> DISCH_TAC >>
  irule bytestring_abi_pre_read_frame >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_flat_source_frame:
  !row src_addr tail_addr writes before after.
    abi_flat_source row src_addr tail_addr before /\ abi_memory_frame writes before after /\
    EVERY (\(offset,count). abi_window_separated (w2n src_addr) (abi_flat_source_count row)
      offset count) writes ==>
    abi_flat_source row src_addr tail_addr after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `w2n (src_addr:bytes32)`, `abi_flat_source_count row`]
    abi_memory_frame_read) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`row`, `src_addr`, `tail_addr`, `before`, `after`] abi_flat_source_read_frame) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]
QED

Theorem abi_flat_sources_frame:
  !rows root_addr source_offset dst_addr tail_cursor writes before after.
    abi_flat_sources rows root_addr source_offset dst_addr tail_cursor writes before /\
    abi_memory_frame writes before after ==>
    abi_flat_sources rows root_addr source_offset dst_addr tail_cursor writes after
Proof
  Induct_on `rows` >- simp[abi_flat_sources_def] >>
  rpt gen_tac >> simp_tac bool_ss [abi_flat_sources_def] >> strip_tac >>
  drule_all abi_flat_source_frame >> DISCH_TAC >>
  asm_simp_tac bool_ss [] >> first_x_assum irule >> qexists_tac `before` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed preservation of concrete ABI field source observations: " ^ name)
  end) (DB.thms "abiFlatSourcesFrame")
