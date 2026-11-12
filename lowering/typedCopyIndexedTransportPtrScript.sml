(* One indexed copy preserves its source and extends the copied prefix. *)
Theory typedCopyIndexedTransportPtr
Ancestors typedCopyRobustTransportPtr bodyPtrDefs valueEncoding arithmetic

Theorem indexed_robust_copy_step:
 !N i S B stv dtv V tn tn' mem mem'.
 i < N /\
 (S + N * type_memory_size stv <= B \/ B + N * type_memory_size dtv <= S) /\
 (!j. j < N ==> val_wf stv (V j) /\ val_wf dtv (V j)) /\
 (!x. ~(B + i * type_memory_size dtv <= x /\
         x < B + (i+1) * type_memory_size dtv) ==>
   mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\ (x IN tn' <=> x IN tn)) /\
 (!j. j < N ==> !m. mem_agree_outside tn mem m ==>
   val_in_memory stv (V j) (S + j * type_memory_size stv) m) /\
 (!j. j < i ==> !m. mem_agree_outside tn mem m ==>
   val_in_memory dtv (V j) (B + j * type_memory_size dtv) m) /\
 (!m. mem_agree_outside tn' mem' m ==>
   val_in_memory dtv (V i) (B + i * type_memory_size dtv) m) ==>
 (!j. j < N ==> !m. mem_agree_outside tn' mem' m ==>
   val_in_memory stv (V j) (S + j * type_memory_size stv) m) /\
 (!j. j < i+1 ==> !m. mem_agree_outside tn' mem' m ==>
   val_in_memory dtv (V j) (B + j * type_memory_size dtv) m)
Proof
 rpt gen_tac >> strip_tac >>
 (
 `!x. ~(B + i * type_memory_size dtv <= x /\
         x < B + i * type_memory_size dtv + type_memory_size dtv) ==>
   mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\ (x IN tn' <=> x IN tn)` by
   simp[GSYM LEFT_ADD_DISTRIB] >>
 `!tv v p. val_wf tv v ==>
   (p + type_memory_size tv <= B + i * type_memory_size dtv \/
    B + i * type_memory_size dtv + type_memory_size dtv <= p) ==>
   (!m. mem_agree_outside tn mem m ==> val_in_memory tv v p m) ==>
   !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v p m` by
   (rpt strip_tac >>
    (irule robust_representation_exterior_frame >>
     (conj_tac >- simp[]) >>
     qexistsl_tac [`B + i * type_memory_size dtv`, `mem`, `mem'`,
                   `type_memory_size dtv`, `tn`, `tn'`] >> simp[])) >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum irule >> simp[] >>
     `j * type_memory_size stv + type_memory_size stv <= N * type_memory_size stv` by
       (qspecl_then [`j+1`, `N`, `type_memory_size stv`] mp_tac LESS_MONO_MULT >>
        pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
     qspecl_then [`i+1`, `N`, `type_memory_size dtv`] mp_tac LESS_MONO_MULT >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
 rpt strip_tac >> Cases_on `j = i` >- gvs[] >>
 `j < i` by decide_tac >>
 first_x_assum irule >> simp[] >>
 `j * type_memory_size dtv + type_memory_size dtv <= i * type_memory_size dtv` by
   (qspecl_then [`j+1`, `i`, `type_memory_size dtv`] mp_tac LESS_MONO_MULT >>
    pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
 decide_tac)
QED
