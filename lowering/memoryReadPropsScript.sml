(* TOP-LEVEL: total zero-extended memory reads split into adjacent windows.
   Writes preserve disjoint reads, including windows beyond the old memory
   length. This is the footprint frame used by ABI buffer construction. *)
Theory memoryReadProps
Ancestors
  valueEncoding valueEncodingProps valueEncodingProofs venomState
  venomExecSemantics venomMemProps list rich_list arithmetic

Theorem read_memory_eq_mem_bytes_at:
  !offset read_len ss.
    read_memory offset read_len ss = mem_bytes_at offset read_len ss.vs_memory
Proof
  simp[read_memory_def, mem_bytes_at_def]
QED

Theorem LENGTH_read_memory[simp]:
  !offset read_len ss. LENGTH (read_memory offset read_len ss) = read_len
Proof
  simp[read_memory_eq_mem_bytes_at]
QED

Theorem read_memory_split:
  !offset left_count right_count ss.
    read_memory offset (left_count + right_count) ss =
      read_memory offset left_count ss ++
      read_memory (offset + left_count) right_count ss
Proof
  rpt gen_tac >> irule LIST_EQ >>
  simp[read_memory_eq_mem_bytes_at] >> rpt gen_tac >> strip_tac >>
  rename1 `i < left_count + right_count` >> Cases_on `i < left_count`
  >- simp[EL_APPEND1, LENGTH_mem_bytes_at, EL_mem_bytes_at] >>
  `i - left_count < right_count` by decide_tac >>
  simp[EL_APPEND2, LENGTH_mem_bytes_at, EL_mem_bytes_at, ADD_ASSOC]
QED

Theorem read_memory_subwindow:
  !offset whole_len skip read_len ss.
    skip + read_len <= whole_len ==>
    read_memory (offset + skip) read_len ss =
      TAKE read_len (DROP skip (read_memory offset whole_len ss))
Proof
  rpt gen_tac >> strip_tac >>
  `read_len <= whole_len - skip` by decide_tac >>
  irule LIST_EQ >> reverse conj_tac
  >- simp[LENGTH_TAKE_EQ, LENGTH_DROP] >>
  simp[] >> qx_gen_tac `index` >> strip_tac >>
  `index + skip < whole_len` by decide_tac >>
  simp[EL_TAKE, EL_DROP] >>
  PURE_REWRITE_TAC[read_memory_eq_mem_bytes_at] >>
  `offset + skip + index = offset + (index + skip)` by decide_tac >>
  asm_simp_tac bool_ss [EL_mem_bytes_at, ADD_ASSOC]
QED

Theorem read_memory_mstore_disjoint:
  !offset read_len dst value ss.
    offset + read_len <= dst \/ dst + 32 <= offset ==>
    read_memory offset read_len (mstore dst value ss) = read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >> rewrite_tac[read_memory_eq_mem_bytes_at] >>
  irule mstore_mem_bytes_at_disjoint >> first_assum ACCEPT_TAC
QED

Theorem read_memory_write_self:
  !dst bytes ss.
    read_memory dst (LENGTH bytes) (write_memory_with_expansion dst bytes ss) = bytes
Proof
  rpt gen_tac >> simp[read_memory_def] >>
  `LENGTH bytes <=
      LENGTH (DROP dst (write_memory_with_expansion dst bytes ss).vs_memory)` by
    simp[LENGTH_DROP, LENGTH_write_memory_with_expansion, MAX_DEF] >>
  simp[TAKE_APPEND1, write_memory_with_expansion_read_self]
QED

Theorem read_memory_write_disjoint:
  !offset read_len dst bytes ss.
    offset + read_len <= dst \/ dst + LENGTH bytes <= offset ==>
    read_memory offset read_len (write_memory_with_expansion dst bytes ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[read_memory_eq_mem_bytes_at, write_memory_with_expansion_def, LET_THM] >>
  Cases_on `0 < dst + LENGTH bytes - LENGTH ss.vs_memory` >> simp[]
  >- (qmatch_goalsub_abbrev_tac `TAKE dst expanded_mem` >>
      `dst + LENGTH bytes <= LENGTH expanded_mem` by simp[Abbr`expanded_mem`] >>
      `mem_bytes_at offset read_len
         (TAKE dst expanded_mem ++ bytes ++ DROP (dst + LENGTH bytes) expanded_mem) =
       mem_bytes_at offset read_len expanded_mem` by
        (simp[mem_bytes_at_def] >> irule take_drop_splice_disjoint >> simp[]) >>
      simp[Abbr`expanded_mem`, mem_bytes_at_append_zero]) >>
  `dst + LENGTH bytes <= LENGTH ss.vs_memory` by simp[] >>
  simp[mem_bytes_at_def] >> irule take_drop_splice_disjoint >> simp[]
QED

Theorem read_memory_mcopy_self:
  !dst src read_len ss.
    read_memory dst read_len (mcopy dst src read_len ss) = read_memory src read_len ss
Proof
  rpt gen_tac >> rewrite_tac[mcopy_def, LET_THM] >>
  mp_tac (Q.SPECL [`dst`, `read_memory src read_len ss`, `ss`] read_memory_write_self) >>
  simp[read_memory_def]
QED

Theorem read_memory_mcopy_disjoint:
  !offset read_len dst src copied_count ss.
    offset + read_len <= dst \/ dst + copied_count <= offset ==>
    read_memory offset read_len (mcopy dst src copied_count ss) = read_memory offset read_len ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [mcopy_def, LET_THM] >>
  irule read_memory_write_disjoint >> simp[]
QED

(* A zero-byte copy may extend the represented memory list, but every total
   zero-extended read remains equal, including a window containing dst. *)
Theorem read_memory_mcopy_zero:
  !offset read_len dst src ss.
    read_memory offset read_len (mcopy dst src 0 ss) = read_memory offset read_len ss
Proof
  rpt gen_tac >>
  simp[read_memory_eq_mem_bytes_at, mcopy_def, read_memory_def,
    write_memory_with_expansion_def, LET_THM, TAKE_DROP] >>
  rw[] >> simp[mem_bytes_at_append_zero]
QED

Theorem read_memory_mcopy_frame:
  !offset read_len dst src copied_count ss.
    copied_count = 0 \/ offset + read_len <= dst \/ dst + copied_count <= offset ==>
    read_memory offset read_len (mcopy dst src copied_count ss) = read_memory offset read_len ss
Proof
  rpt gen_tac >> strip_tac
  >- simp[read_memory_mcopy_zero] >>
  irule read_memory_mcopy_disjoint >> simp[]
QED

Theorem read_memory_word:
  !offset ss.
    read_memory offset 32 ss = word_to_bytes (mload offset ss) T
Proof
  rpt gen_tac >> rewrite_tac[read_memory_def, mload_def, LET_THM] >>
  BETA_TAC >> sym_tac >> irule word_bytes_roundtrip_256 >> simp[LENGTH_TAKE_EQ]
QED

Theorem mload_read_memory:
  !offset ss.
    mload offset ss = word_of_bytes T 0w (read_memory offset 32 ss)
Proof
  simp[mload_def, read_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed memory-read theorem: " ^ name)
  end)
  (DB.thms "memoryReadProps")
