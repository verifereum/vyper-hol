Theory o1CodeEndSsaOwners
Ancestors
  makeSsaCurrentRenameTrace o1MakeSsaOwnership list pair pred_set

(* The static pair relation and runtime token triples can share owners:
   each actual output allocation extends both by the same (name,variable).
   This is the local bridge; it does not identify independently chosen
   existential histories, nor assert protected provenance after cleanup. *)
Theorem code_end_outputs_trace_owner_alignment:
  !anns s rs H E names s' rs' H' E' R.
    current_outputs_trace anns s rs H E names s' rs' H' E' /\
    EVERY (\(token,v,n). R n v) H /\
    LIST_REL (\a n. R n (SND a)) anns names ==>
    EVERY (\(token,v,n). R n v) H'
Proof
  Induct >- simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[current_outputs_trace_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[EVERY_APPEND]
QED
