(* Separation of staged memory descriptors from ordered allocation intervals. *)
Theory bodyIntCallStageSeparated
Ancestors
  bodyIntCallStageOwned venomMemDefs compileEnv

Theorem staged_arg_intervals_disjoint:
  staged_arg ce func es a mid t (ty,tv,v,F,op) /\
  staged_arg ce func es mid sn t (ty',tv',v',F,op') /\
  alloca_inv t /\ eval_operand op t = SOME w /\
  eval_operand op' t = SOME w' ==>
  compileEnv$regions_disjoint (w2n w) (type_memory_size tv)
    (w2n w') (type_memory_size tv')
Proof
  simp[staged_arg_def] >> strip_tac >>
  `aid <> aid'` by decide_tac >>
  gvs[venomMemDefsTheory.alloca_inv_def,
      venomMemDefsTheory.allocas_non_overlapping_def,
      compileEnvTheory.regions_disjoint_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
    (qspecl_then [`inst.inst_id`,`inst'.inst_id`] mp_tac) >>
  simp[] >> decide_tac
QED

(* Positional separation preserves multiplicity, unlike set pairwise. *)
Theorem distinct_indices_cons:
  (!i j. i < LENGTH (h::xs) /\ j < LENGTH (h::xs) /\ i <> j ==>
     R (EL i (h::xs)) (EL j (h::xs))) <=>
  ((!i j. i < LENGTH xs /\ j < LENGTH xs /\ i <> j ==>
      R (EL i xs) (EL j xs)) /\
   (!i. i < LENGTH xs ==> R h (EL i xs)) /\
   (!i. i < LENGTH xs ==> R (EL i xs) h))
Proof
  eq_tac
  >- (strip_tac >> rpt conj_tac >> rpt strip_tac
      >- (first_x_assum (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[])
      >- (first_x_assum (qspecl_then [`0`,`SUC i`] mp_tac) >> simp[])
      >> first_x_assum (qspecl_then [`SUC i`,`0`] mp_tac) >> simp[]) >>
  strip_tac >> Cases >> Cases >> simp[]
QED
