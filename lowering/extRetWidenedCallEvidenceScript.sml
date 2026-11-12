Theory extRetWidenedCallEvidence
Ancestors
  intCallReturnMem valueEncoding vyperValue valueEncodingDefs

(* Conditional layout incompatibility only. The premise still needs a run;
   this is not a counterexample to external_frame_ret_ok_ptr. *)
Theorem nested_call_return_endpoint_incompatible:
  !fn ce cx bw es ir s.
    let word = BaseTV (UintT 256) in
    let sty = ArrayTV (ArrayTV word (Dynamic 1)) (Fixed 2) in
    let aty = ArrayTV (ArrayTV word (Dynamic 2)) (Fixed 2) in
    let v = ArrayV (SArrayV
      [(0,ArrayV (DynArrayV [IntV 11]));
       (1,ArrayV (DynArrayV [IntV 22]))]) in
    intret_mem_q fn ce cx sty bw v es (IntRet ir s) ==>
    ~val_in_memory aty v (w2n bw) s.vs_memory
Proof
  simp[intret_mem_q_def, val_in_memory_def, type_memory_size_def,
       val_to_w256_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `i2w 22 = 1w` mp_tac >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC
QED
