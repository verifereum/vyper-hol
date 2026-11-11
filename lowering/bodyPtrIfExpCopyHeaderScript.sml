Theory bodyPtrIfExpCopyHeader
Ancestors
  bodyPtrDefs representationCleanPtr valueCopyBytes valueEncoding valueEncodingDefs venomState

Theorem robust_bytestring_header:
  !tenv sty stv v len tn s a.
    evaluate_type tenv sty = SOME stv /\ is_bytestring_type sty /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v a m) ==>
    mload a s = n2w len /\
    (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  `val_in_memory stv v a s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all bytestring_type_value >> strip_tac >>
  (conj_tac
   >- (gvs[val_in_memory_def, mload_def, mem_word_at_def] >> metis_tac[]) >>
   gvs[] >>
   FIRST [drule robust_val_in_memory_bytes_clean,
          drule robust_val_in_memory_string_clean] >> simp[])
QED
