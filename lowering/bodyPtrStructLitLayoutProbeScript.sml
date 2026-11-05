(* Layout arithmetic for the concrete heterogeneous-child probe.
   These facts alone assert nothing about reachability or body correctness. *)
Theory bodyPtrStructLitLayoutProbe
Ancestors bodyPtrDefs valueEncoding valueEncodingProps valueEncodingProofs representationCleanPtr list vyperTypeSystem

Theorem structlit_probe_header_offsets:
  type_memory_size (BaseTV (BytesT (Dynamic 1))) = 64 /\
  type_memory_size (BaseTV (BytesT (Dynamic 33))) = 96 /\
  type_memory_size
    (TupleTV [BaseTV (BytesT (Dynamic 1)); BaseTV (BytesT (Dynamic 1))]) = 128 /\
  type_memory_size
    (TupleTV [BaseTV (BytesT (Dynamic 33)); BaseTV (BytesT (Dynamic 1))]) = 160
Proof
  EVAL_TAC
QED

Theorem structlit_probe_annotated_reads:
  !mem.
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 33)); BaseTV (BytesT (Dynamic 1))])
    (ArrayV (TupleV [BytesV []; BytesV []])) 0 mem <=>
  mem_word_at 0 mem = 0w /\ mem_word_at 96 mem = 0w
Proof
  simp[valueEncodingTheory.val_in_memory_def,
       valueEncodingTheory.type_memory_size_def,
       valueEncodingTheory.mem_bytes_at_def] >> EVAL_TAC >> simp[]
QED

Theorem structlit_probe_word_agrees:
  !a mem m.
  mem_agree_outside {64} mem m /\ (a + 32 <= 64 \/ 65 <= a) ==>
  mem_word_at a mem = mem_word_at a m
Proof
  rpt strip_tac >>
  simp[mem_word_at_def, GSYM mem_bytes_at_def] >>
  AP_TERM_TAC >> irule LIST_EQ >> simp[EL_mem_bytes_at] >>
  rpt strip_tac >>
  `a + x <> 64` by decide_tac >>
  `mem_bytes_at (a+x) 1 mem = mem_bytes_at (a+x) 1 m` by
    (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem structlit_probe_annotated_robust:
  !mem. mem_agree_outside {64} [] mem ==>
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 33)); BaseTV (BytesT (Dynamic 1))])
    (ArrayV (TupleV [BytesV []; BytesV []])) 0 mem
Proof
  rpt strip_tac >> simp[structlit_probe_annotated_reads] >>
  `mem_word_at 0 [] = mem_word_at 0 mem /\
   mem_word_at 96 [] = mem_word_at 96 mem` by
    (conj_tac >> irule structlit_probe_word_agrees >> simp[]) >>
  `mem_word_at 0 [] = 0w /\ mem_word_at 96 [] = 0w` by (EVAL_TAC >> simp[]) >>
  gvs[]
QED

Theorem structlit_probe_lowered_not_robust:
  ~(!mem. mem_agree_outside {64} [] mem ==>
    val_in_memory
      (TupleTV [BaseTV (BytesT (Dynamic 1)); BaseTV (BytesT (Dynamic 1))])
      (ArrayV (TupleV [BytesV []; BytesV []])) 0 mem)
Proof
  strip_tac >>
  `!mem. mem_agree_outside {64} [] mem ==> mem_word_at 64 mem = 0w` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[val_in_memory_def, type_memory_size_def, mem_bytes_at_def] >>
     EVAL_TAC >> simp[]) >>
  drule robust_mem_word_at_clean >>
  disch_then (qspec_then `64` mp_tac) >> simp[]
QED

(* Typing permits the candidate mismatch; this is not call correctness. *)
Theorem structlit_probe_tuple_widening:
  type_widens_to FEMPTY
    (TupleT [BaseT (BytesT (Dynamic 1)); BaseT (BytesT (Dynamic 1))])
    (TupleT [BaseT (BytesT (Dynamic 33)); BaseT (BytesT (Dynamic 1))])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

(* A real widened child's postcondition must also initialize the annotated
   second header.  Abstract cleanliness only at the narrow offsets is not enough. *)
Theorem structlit_probe_annotated_header_clean:
  !m mem.
    (!mem'. mem_agree_outside m mem mem' ==>
      val_in_memory
        (TupleTV [BaseTV (BytesT (Dynamic 33)); BaseTV (BytesT (Dynamic 1))])
        (ArrayV (TupleV [BytesV []; BytesV []])) 0 mem') ==>
    !i. 96 <= i /\ i < 128 ==> i NOTIN m
Proof
  rpt gen_tac >> disch_tac >>
  `!mem'. mem_agree_outside m mem mem' ==> mem_word_at 96 mem' = 0w` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[structlit_probe_annotated_reads]) >>
  drule robust_mem_word_at_clean >> simp[]
QED
