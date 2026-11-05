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
