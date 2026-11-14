(* Robust indexed representations across one disjoint child write. *)
Theory widenedAssignPtrIndexInvariant
Ancestors typedCopyRobustTransportPtr typedMemoryCopy valueEncodingDefs
  valueEncodingProps venomState ptrDiscipline arithmetic pred_set

Theorem widened_assign_robust_index_step:
  !N k dtv stv vs dp sp sa tn tn' s t.
    k < N /\
    (dp + N * type_memory_size dtv <= sp \/
     sp + N * type_memory_size stv <= dp) /\
    (!i. i < N ==> val_wf dtv (vs i) /\ val_wf stv (vs i)) /\
    (!i m. i < N /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (vs i) (sp + i * type_memory_size stv) m) /\
    (!i m. i < k /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory dtv (vs i) (dp + i * type_memory_size dtv) m) /\
    typed_copy_state_frame sa (dp + k * type_memory_size dtv)
      (type_memory_size dtv) s t /\
    (!a. ~(dp + k * type_memory_size dtv <= a /\
            a < dp + k * type_memory_size dtv + type_memory_size dtv) ==>
       (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory dtv (vs k) (dp + k * type_memory_size dtv) m) ==>
    (!i m. i < N /\ mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory stv (vs i) (sp + i * type_memory_size stv) m) /\
    (!i m. i < SUC k /\ mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory dtv (vs i) (dp + i * type_memory_size dtv) m) /\
    typed_copy_state_frame sa dp (N * type_memory_size dtv) s t /\
    (!a. ~(dp <= a /\ a < dp + N * type_memory_size dtv) ==>
       (a IN tn'.t_mem <=> a IN tn.t_mem))
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `dp <= dp + k * type_memory_size dtv /\
   dp + k * type_memory_size dtv + type_memory_size dtv <=
     dp + N * type_memory_size dtv` by
    (irule typed_copy_array_subinterval >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `sp <= sp + i * type_memory_size stv /\
       sp + i * type_memory_size stv + type_memory_size stv <=
         sp + N * type_memory_size stv` by
        (irule typed_copy_array_subinterval >> simp[]) >>
      irule robust_representation_exterior_frame >> conj_tac >- simp[] >>
      qexistsl_tac [`dp + k * type_memory_size dtv`, `s.vs_memory`,
        `t.vs_memory`, `type_memory_size dtv`, `tn.t_mem`, `tn'.t_mem`] >>
      gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `i = k` >- metis_tac[] >>
      `i < k` by decide_tac >>
      `dp + i * type_memory_size dtv + type_memory_size dtv <=
         dp + k * type_memory_size dtv` by
        (mp_tac (Q.SPECL [`i`, `k`, `dp`, `type_memory_size dtv`]
          typed_copy_array_subinterval) >> simp[]) >>
      irule robust_representation_exterior_frame >> conj_tac >- simp[] >>
      qexistsl_tac [`dp + k * type_memory_size dtv`, `s.vs_memory`,
        `t.vs_memory`, `type_memory_size dtv`, `tn.t_mem`, `tn'.t_mem`] >>
      gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (irule typed_copy_state_frame_subinterval >>
      goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
