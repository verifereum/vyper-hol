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
   >- (gvs[valueEncodingDefsTheory.val_in_memory_def, mload_def,
            valueEncodingDefsTheory.mem_word_at_def] >> metis_tac[]) >>
   FIRST [drule robust_val_in_memory_bytes_clean,
          drule robust_val_in_memory_string_clean] >> simp[])
QED
