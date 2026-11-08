(* Pure observations on a single bytestring copy endpoint; no execution
   witness is selected by these representation lemmas. *)
Theory bodyPtrMakeArrayBytesTransport
Ancestors
  typedCopyRobustTransportPtr representationCleanPtr valueCopyBytes
  valueEncodingProps valueEncodingProofs bodyPtrDefs venomState
  exprSimDefs exprSimProps loweringPosts

Theorem robust_bytestring_source_live:
  is_bytestring_type sty /\ evaluate_type tenv sty = SOME stv /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside dirty s.vs_memory m ==>
    val_in_memory stv v (w2n a) m) ==>
  mload (w2n a) s = n2w len /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN dirty) /\
  (!i. w2n a + 32 <= i /\ i < w2n a + 32 + len ==> i NOTIN dirty)
Proof
  strip_tac >>
  `val_in_memory stv v (w2n a) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all bytestring_type_value >> strip_tac >> gvs[] >>
  (conj_tac
   >- (gvs[valueEncodingTheory.val_in_memory_def, mload_def,
            valueEncodingTheory.mem_word_at_def] >> metis_tac[]) >>
   FIRST [drule robust_val_in_memory_bytes_clean,
          drule robust_val_in_memory_string_clean] >> simp[])
QED

Theorem robust_bytestring_copied_endpoint:
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  (!m. mem_agree_outside dirty s.vs_memory m ==>
    val_in_memory stv v (w2n a) m) /\
  sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
  (!i. i < n ==> (w2n b+i IN dirty' <=> w2n a+i IN dirty)) /\
  32 <= n /\ 32 + len <= n ==>
  !m. mem_agree_outside dirty' sf.vs_memory m ==>
    val_in_memory dtv v (w2n b) m
Proof
  disch_tac >>
  `mload (w2n a) s = n2w len /\
   (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN dirty) /\
   (!i. w2n a + 32 <= i /\ i < w2n a + 32 + len ==> i NOTIN dirty)` by
    (irule robust_bytestring_source_live >> metis_tac[]) >>
  qpat_x_assum `_ /\ _` strip_assume_tac >> rpt gen_tac >> disch_tac >>
  `mem_bytes_at (w2n b+0) 32 m = mem_bytes_at (w2n a+0) 32 s.vs_memory` by
    (irule clean_copied_window >>
     qexistsl_tac [`n`, `sf`, `dirty`, `dirty'`] >> simp[]) >>
  `mem_bytes_at (w2n b+32) len m = mem_bytes_at (w2n a+32) len s.vs_memory` by
    (irule clean_copied_window >>
     qexistsl_tac [`n`, `sf`, `dirty`, `dirty'`] >> simp[]) >>
  `val_in_memory stv v (w2n a) s.vs_memory` by
    (qpat_assum `!m. mem_agree_outside dirty _ m ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `val_in_memory dtv v (w2n a) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> simp[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> gvs[]) >>
  qpat_x_assum `!m. mem_agree_outside dirty _ m ==> _` kall_tac >>
  qpat_x_assum `val_in_memory stv v _ _` kall_tac >>
  qspecl_then [`tenv`, `dty`, `dtv`] mp_tac bytestring_type_value >>
  simp[] >> strip_tac >>
  gvs[valueEncodingTheory.val_in_memory_def,
      valueEncodingTheory.mem_word_at_def, GSYM valueEncodingTheory.mem_bytes_at_def]
QED
