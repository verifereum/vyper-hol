(* Robust representation interfaces for recursive field copying. *)
Theory widenedAssignPtrCopyFieldList
Ancestors assignBasePtrFieldsCompose typedCopyRobustTransportPtr typedMemoryCopy
  typedCopyAgreement valueEncodingDefs valueEncodingProps valueEncoding
  fragGasPathPtr fragExec context compileEnv venomState words list arithmetic

Theorem widened_assign_robust_tuple_frame:
  !vs tvs p dst n tn tn' mem mem'.
    tuple_val_wf vs tvs /\
    (p + type_memory_size_list tvs <= dst \/ dst+n <= p) /\
    (!m. mem_agree_outside tn mem m ==> tuple_in_memory vs tvs p m) /\
    typed_copy_frame dst n mem mem' /\
    (!i. ~(dst <= i /\ i < dst+n) ==> (i IN tn' <=> i IN tn)) ==>
    !m. mem_agree_outside tn' mem' m ==> tuple_in_memory vs tvs p m
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `!m. mem_agree_outside tn' mem' m ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p m` suffices_by
      simp[val_in_memory_def] >>
  rpt strip_tac >> irule robust_representation_exterior_frame >>
  conj_tac >- gvs[val_wf_def] >>
  qexistsl_tac [`dst`, `mem`, `mem'`, `n`, `tn`, `tn'`] >>
  gvs[typed_copy_frame_def, val_in_memory_def, val_wf_def, type_memory_size_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem widened_assign_robust_tuple_cons:
  !tv v tvs vs p tn tn' s t.
    val_wf tv v /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v p m) /\
    typed_copy_frame (p + type_memory_size tv) (type_memory_size_list tvs)
      s.vs_memory t.vs_memory /\
    (!i. ~(p + type_memory_size tv <= i /\
            i < p + type_memory_size tv + type_memory_size_list tvs) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      tuple_in_memory vs tvs (p + type_memory_size tv) m) ==>
    !m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      tuple_in_memory (v::vs) (tv::tvs) p m
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
     val_in_memory tv v p m` by
    (rpt strip_tac >> irule robust_representation_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`p + type_memory_size tv`, `s.vs_memory`, `t.vs_memory`,
                   `type_memory_size_list tvs`, `tn.t_mem`, `tn'.t_mem`] >>
     gvs[typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[val_in_memory_def]
QED
