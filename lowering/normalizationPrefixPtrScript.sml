(* Completed semantic prefixes survive a recursive child's exterior frame. *)
Theory normalizationPrefixPtr
Ancestors robustCopyTransportPtr exprSimAggregateEncoding arithmetic list
  bodyPtrDefs valueEncoding valueEncodingProofs venomState venomMemProofs

Theorem robust_array_prefix_extend:
  !tv vs d i tn tn' mem mem'.
    i < LENGTH vs /\
    (!j. j < i ==> val_wf tv (EL j vs) /\
      val_footprint tv (EL j vs) <= type_memory_size tv) /\
    (!j. j < i ==> !m.
      mem_agree_outside tn mem m ==>
      val_in_memory tv (EL j vs) (d + j * type_memory_size tv) m) /\
    (!x. ~(d + i * type_memory_size tv <= x /\
           x < d + (i+1) * type_memory_size tv) ==>
      mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\
      (x IN tn' <=> x IN tn)) /\
    (!m. mem_agree_outside tn' mem' m ==>
      val_in_memory tv (EL i vs) (d + i * type_memory_size tv) m) ==>
    !j. j < SUC i ==> !m.
      mem_agree_outside tn' mem' m ==>
      val_in_memory tv (EL j vs) (d + j * type_memory_size tv) m
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = i` >- gvs[] >>
  `j < i` by decide_tac >> rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`mem`, `mem'`, `tn`, `tn'`,
    `{x | d + i * type_memory_size tv <= x /\
           x < d + (i+1) * type_memory_size tv}`] >>
  simp[] >>
  rpt strip_tac >>
  `val_footprint tv (EL j vs) <= type_memory_size tv` by metis_tac[] >>
  `(j+1) * type_memory_size tv <= i * type_memory_size tv` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  qpat_x_assum `(j+1) * _ <= _` mp_tac >>
  qpat_x_assum `val_footprint _ _ <= _` mp_tac >>
  pure_rewrite_tac[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
  decide_tac
QED

Theorem robust_dynarray_assemble:
  !tv vs capacity d tn mem.
    (!m. mem_agree_outside tn mem m ==>
         mem_word_at d m = n2w (LENGTH vs)) /\
    (!j. j < LENGTH vs ==> !m.
      mem_agree_outside tn mem m ==>
      val_in_memory tv (EL j vs)
        (d + 32 + j * type_memory_size tv) m) ==>
    !m. mem_agree_outside tn mem m ==>
      val_in_memory (ArrayTV tv (Dynamic capacity))
        (ArrayV (DynArrayV vs)) d m
Proof
  rpt strip_tac >> simp[valueEncodingTheory.val_in_memory_def] >>
  irule elems_in_memory_intro >> simp[]
QED

Theorem robust_dynarray_clean_count_assemble:
  !tv vs capacity d tn mem.
    mem_word_at d mem = n2w (LENGTH vs) /\
    DISJOINT {a | d <= a /\ a < d+32} tn /\
    (!j. j < LENGTH vs ==> !m.
      mem_agree_outside tn mem m ==>
      val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) m) ==>
    !m. mem_agree_outside tn mem m ==>
      val_in_memory (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) d m
Proof
  rpt gen_tac >> strip_tac >> match_mp_tac robust_dynarray_assemble >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `mem_bytes_at d 32 m = mem_bytes_at d 32 mem` by
    (irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
     rename1 `i < 32` >>
     `d+i NOTIN tn` by
       (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[DECIDE ``i < 32 ==> d <= d+i /\ d+i < d+32``]) >>
     `mem_bytes_at (d+i) 1 mem = mem_bytes_at (d+i) 1 m` by
       fs[mem_agree_outside_def] >>
     pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
  fs[mem_word_at_def, GSYM mem_bytes_at_def]
QED
