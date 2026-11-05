Theory exprSimAbiDecodeResource
Ancestors
  exprSimAbiDecodeShapeProbe exprSimAbiDecodeShape exprSimAbiDecodeTrace
  exprSimAbiDecodePrims compileEnv emitHelperProps pred_set list arithmetic

Definition decode_label_range_def:
  decode_label_range a b =
    {l | ?suffix k. a <= k /\ k < b /\ l = fresh_label_output suffix k}
End

Definition decode_resource_run_def:
  decode_resource_run excluded P m s x t Q <=>
    m s = (x,t) /\ P SUBSET decode_label_range 0 s.cs_next_label /\
    s.cs_next_label <= t.cs_next_label /\
    ?es. t = decode_history t (decode_replay es s) /\
      decode_trace_safe s.cs_next_id t.cs_next_id (decode_switches es) excluded es /\
      set (decode_switches es) SUBSET
        (P UNION decode_label_range s.cs_next_label t.cs_next_label) /\
      Q = (P UNION decode_label_range s.cs_next_label t.cs_next_label)
            DIFF set (decode_switches es)
End

Theorem decode_label_range_split:
  a <= b /\ b <= c ==>
  decode_label_range a c = decode_label_range a b UNION decode_label_range b c
Proof
  rw[EXTENSION, decode_label_range_def] >> eq_tac
  >- (strip_tac >> Cases_on `k < b` >> metis_tac[NOT_LESS]) >>
  strip_tac >> qexistsl_tac [`suffix`, `k`] >> simp[]
QED

Theorem decode_label_range_disjoint:
  DISJOINT (decode_label_range 0 b) (decode_label_range b c)
Proof
  simp[IN_DISJOINT] >> rpt gen_tac >>
  simp[decode_label_range_def] >>
  spose_not_then strip_assume_tac >>
  `fresh_label_output suffix k = fresh_label_output suffix' k'` by metis_tac[] >>
  drule fresh_label_output_inj >> strip_tac >> gvs[]
QED

Theorem decode_resource_run_pool:
  decode_resource_run excluded P m s x t Q ==>
  Q SUBSET decode_label_range 0 t.cs_next_label
Proof
  rw[decode_resource_run_def] >>
  `decode_label_range 0 t.cs_next_label =
   decode_label_range 0 s.cs_next_label UNION
   decode_label_range s.cs_next_label t.cs_next_label` by
    (irule decode_label_range_split >> simp[]) >>
  ASM_SET_TAC[]
QED

Theorem decode_trace_safe_allowed:
  decode_trace_safe lo hi allowed ex es /\
  (!l. MEM l (decode_switches es) ==> MEM l allowed') ==>
  decode_trace_safe lo hi allowed' ex es
Proof
  simp[decode_trace_safe_def, EVERY_MEM]
QED

Theorem decode_resource_run_trace:
  decode_resource_run ex P m s x t Q ==>
  ?es. m s = (x,t) /\ t = decode_history t (decode_replay es s) /\
    decode_trace_safe s.cs_next_id t.cs_next_id (decode_switches es) ex es /\
    set (decode_switches es) SUBSET
      (P UNION decode_label_range s.cs_next_label t.cs_next_label) /\
    Q = (P UNION decode_label_range s.cs_next_label t.cs_next_label)
          DIFF set (decode_switches es)
Proof
  rw[decode_resource_run_def] >> metis_tac[]
QED

Theorem decode_resource_run_return:
  P SUBSET decode_label_range 0 s.cs_next_label ==>
  decode_resource_run ex P (comp_return x) s x s P
Proof
  rw[decode_resource_run_def, comp_return_def] >> qexists_tac `[]` >>
  simp[decode_replay_def, decode_history_def, decode_trace_safe_def,
       decode_instructions_def, decode_switches_def, decode_label_range_def,
       compile_state_component_equality] >>
  simp[EXTENSION] >> metis_tac[DECIDE ``~(a <= k /\ k < a)``]
QED

Theorem decode_resource_run_bind:
  decode_resource_run ex P m s x u Q /\
  decode_resource_run ex Q (f x) u y t R ==>
  decode_resource_run ex P (comp_bind m f) s y t R
Proof
  rw[decode_resource_run_def] >>
  `decode_label_range 0 u.cs_next_label =
   decode_label_range 0 s.cs_next_label UNION
   decode_label_range s.cs_next_label u.cs_next_label` by
    (irule decode_label_range_split >> simp[]) >>
  `decode_label_range s.cs_next_label t.cs_next_label =
   decode_label_range s.cs_next_label u.cs_next_label UNION
   decode_label_range u.cs_next_label t.cs_next_label` by
    (irule decode_label_range_split >> simp[]) >>
  `DISJOINT (decode_label_range 0 u.cs_next_label)
     (decode_label_range u.cs_next_label t.cs_next_label)` by
    simp[decode_label_range_disjoint] >>
  `DISJOINT (set (decode_switches es)) (set (decode_switches es'))` by
    ASM_SET_TAC[] >>
  simp[comp_bind_def] >>
  qexists_tac `es ++ es'` >>
  conj_tac
  >- (qpat_x_assum `t = _` mp_tac >>
      qpat_x_assum `u = _` (fn th => pure_once_rewrite_tac[th]) >>
      simp[NoAsms, decode_replay_append, decode_replay_history,
           decode_history_history]) >>
  conj_tac
  >- (irule decode_trace_safe_append >>
      conj_tac >- (fs[IN_DISJOINT] >> metis_tac[]) >> qexists_tac `u.cs_next_id` >>
      conj_tac >>
      fs[decode_trace_safe_def, decode_switches_append, EVERY_MEM]) >>
  simp[decode_switches_append, LIST_TO_SET_APPEND] >> ASM_SET_TAC[]
QED

Theorem decode_resource_run_ignore_bind:
  decode_resource_run ex P m s x u Q /\
  decode_resource_run ex Q n u y t R ==>
  decode_resource_run ex P (comp_ignore_bind m n) s y t R
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule decode_resource_run_bind >>
  qexistsl_tac [`Q`, `u`, `x`] >> simp[]
QED
