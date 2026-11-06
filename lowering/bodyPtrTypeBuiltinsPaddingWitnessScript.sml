(* Witness fragments for the padding gate; not a target counterexample. *)
Theory bodyPtrTypeBuiltinsPaddingWitness
Ancestors
  bodyPtrTypeBuiltinsPartialRead valueEncodingProps valueEncodingProofs
  list words bodyPtrDefs valueEncoding

Theorem outside_taint_window_equal:
  mem_agree_outside M mem mem' /\
  (!i. a <= i /\ i < a+n ==> i NOTIN M) ==>
  mem_bytes_at a n mem = mem_bytes_at a n mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  `mem_bytes_at (a+x) 1 mem = mem_bytes_at (a+x) 1 mem'` by
    (gvs[mem_agree_outside_def] >> first_x_assum irule >>
     first_x_assum irule >> decide_tac) >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem padding_robust_bytes:
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [b]) 0 mem /\
  mem_agree_outside {63} mem mem' ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [b]) 0 mem'
Proof
  strip_tac >>
  `mem_bytes_at 0 32 mem = mem_bytes_at 0 32 mem'` by
    (irule outside_taint_window_equal >> qexists_tac `{63}` >> simp[]) >>
  `mem_bytes_at 32 1 mem = mem_bytes_at 32 1 mem'` by
    (gvs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
  gvs[val_in_memory_def, mem_word_at_def, mem_bytes_at_def]
QED

Theorem padding_memory_example:
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [0w:word8]) 0
    (REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w)
Proof
  EVAL_TAC >> simp[wordsTheory.w2n_n2w]
QED

Theorem padding_memory_robust_example:
  !m. mem_agree_outside {63}
    (REPLICATE 31 (0w:word8) ++ [1w;0w] ++ REPLICATE 31 0w) m ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV [0w:word8]) 0 m
Proof
  rpt strip_tac >> irule padding_robust_bytes >>
  goal_assum (drule_at Any) >> ACCEPT_TAC padding_memory_example
QED
