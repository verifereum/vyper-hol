Theory bodyPtrBopInMachineMemory
Ancestors
  bodyPtrDefs valueEncoding valueEncodingDefs valueEncodingProofs venomMemDefs finite_map list

(* A finite joint witness: two separate length-prefixed string buffers.
   This abbreviation keeps the concrete byte computation out of frame proofs. *)
Definition joint_memory_def:
  (joint_memory : byte list) = GENLIST (\i. if i = 95 \/ i = 159 then 1w
                             else if i = 96 \/ i = 160 then 97w else 0w) 192
End

Theorem joint_memory_strings:
  val_in_memory (BaseTV (StringT 1)) (StringV "a") 64 joint_memory /\
  val_in_memory (BaseTV (StringT 1)) (StringV "a") 128 joint_memory
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w,
                   wordsTheory.dimword_def] >> EVAL_TAC (* word widths *) >> simp[]
QED

Theorem mem_agree_outside_window:
  !dead m m' a n.
    mem_agree_outside dead m m' /\
    (!i. a <= i /\ i < a+n ==> i NOTIN dead) ==>
    mem_bytes_at a n m = mem_bytes_at a n m'
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < n` >>
  `mem_bytes_at (a+j) 1 m = mem_bytes_at (a+j) 1 m'` by
    (fs[mem_agree_outside_def] >> metis_tac[]) >>
  qpat_x_assum `mem_bytes_at _ 1 _ = _` mp_tac >>
  simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem joint_memory_robust_strings:
  !m. mem_agree_outside {} joint_memory m ==>
    val_in_memory (BaseTV (StringT 1)) (StringV "a") 64 m /\
    val_in_memory (BaseTV (StringT 1)) (StringV "a") 128 m
Proof
  rpt strip_tac >>
  `!a n. mem_bytes_at a n joint_memory = mem_bytes_at a n m` by
    (rpt gen_tac >> irule mem_agree_outside_window >> simp[] >>
     qexists_tac `{}` >> simp[]) >>
  mp_tac joint_memory_strings >>
  simp[val_in_memory_def, mem_word_at_def, GSYM mem_bytes_at_def]
QED
