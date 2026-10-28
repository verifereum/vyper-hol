(* Zero-padded source and expanded assembly reads describe the same bytes.
   TOP-LEVEL: returndata_agree; Helper: bytewise read representations. *)
Theory memoryReadRel
Ancestors
  codegenRel asmSem spillSim strongPrefixSim list rich_list arithmetic

(* Venom RETURN returndata = GENLIST of read_byte *)
Theorem venom_returndata_read_byte:
  !off sz (mem : byte list).
    TAKE sz (DROP off mem ++ REPLICATE sz (0w:byte)) =
    GENLIST (\i. read_byte (off + i) mem) sz
Proof
  rpt gen_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_GENLIST,
       LENGTH_APPEND, LENGTH_DROP] >>
  rpt strip_tac >>
  `x < MIN sz (LENGTH (DROP off mem) + sz)` by simp[MIN_DEF] >>
  simp[EL_TAKE, EL_GENLIST] >>
  simp[read_byte_def] >>
  Cases_on `off + x < LENGTH mem`
  >- (
    `x < LENGTH (DROP off mem)` by (fs[LENGTH_DROP] >> decide_tac) >>
    simp[EL_APPEND1, EL_DROP]
  )
  >- (
    simp[] >>
    `LENGTH (DROP off mem) <= x` by (fs[LENGTH_DROP] >> decide_tac) >>
    `x - LENGTH (DROP off mem) < sz` by decide_tac >>
    simp[EL_APPEND2, EL_REPLICATE]
  )
QED

(* Asm RETURN returndata = GENLIST of read_byte *)
(* Helper: element of asm_expand_memory = read_byte *)
Theorem el_asm_expand:
  !i needed (mem : byte list).
    i < MAX needed (LENGTH mem) ==>
    EL i (asm_expand_memory needed mem) = read_byte i mem
Proof
  rpt strip_tac >> simp[asm_expand_memory_def, LET_THM, read_byte_def] >>
  qabbrev_tac `rounded = 32 * ((needed + 31) DIV 32)` >>
  `needed <= rounded` by
    (simp[Abbr `rounded`] >>
     `(needed + 31) = (needed + 31) DIV 32 * 32 + (needed + 31) MOD 32 /\
      (needed + 31) MOD 32 < 32` by
       (mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[]) >>
     decide_tac) >>
  Cases_on `rounded <= LENGTH mem`
  >- (simp[] >> Cases_on `i < LENGTH mem` >> simp[] >>
      fs[MAX_DEF] >> decide_tac)
  >- (simp[] >> Cases_on `i < LENGTH mem`
      >- simp[EL_APPEND1]
      >- (`i - LENGTH mem < rounded - LENGTH mem` by
            (fs[MAX_DEF] >> decide_tac) >>
          simp[EL_APPEND2, EL_REPLICATE]))
QED

Theorem asm_returndata_read_byte:
  !off sz (mem : byte list).
    TAKE sz (DROP off (asm_expand_memory (off + sz) mem)) =
    GENLIST (\i. read_byte (off + i) mem) sz
Proof
  rpt gen_tac >>
  mp_tac (SPEC ``mem:byte list``
           (SPEC ``off + sz:num`` spillSimTheory.asm_expand_memory_length)) >>
  strip_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_GENLIST, LENGTH_DROP,
       MIN_DEF] >>
  rpt strip_tac >> simp[EL_TAKE, EL_DROP, EL_GENLIST, el_asm_expand, MAX_DEF]
QED

(* Returndata equivalence: when read_byte agrees on [off, off+sz),
   both RETURN formulations produce the same returndata *)
Theorem returndata_agree:
  !off sz (vmem : byte list) (amem : byte list).
    (!i. i < sz ==> read_byte (off + i) vmem = read_byte (off + i) amem) ==>
    TAKE sz (DROP off vmem ++ REPLICATE sz (0w:byte)) =
    TAKE sz (DROP off (asm_expand_memory (off + sz) amem))
Proof
  rpt strip_tac >>
  REWRITE_TAC[venom_returndata_read_byte, asm_returndata_read_byte] >>
  irule LIST_EQ >> simp[LENGTH_GENLIST] >>
  rpt strip_tac >> simp[EL_GENLIST]
QED

(* The same data identity follows from the allocator-masked memory relation
   when the requested range avoids spill bytes. *)
Theorem memory_rel_read_range:
  memory_rel alloc vm am /\
  (!i. off <= i /\ i < off + sz ==>
       ~(alloc.sa_spill_base <= i /\ i < alloc.sa_next_offset)) ==>
  TAKE sz (DROP off vm ++ REPLICATE sz (0w:byte)) =
  TAKE sz (DROP off (asm_expand_memory (off + sz) am))
Proof
  rpt strip_tac >> irule returndata_agree >>
  rpt strip_tac >> fs[memory_rel_def] >>
  first_x_assum irule >> first_x_assum irule >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed memory-read proof: " ^ name)
  end) (DB.thms "memoryReadRel")
