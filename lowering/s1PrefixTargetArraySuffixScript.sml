Theory s1PrefixTargetArraySuffix
Ancestors
  s1PrefixFrame bodyFullTargetArraySuffix targetSubscriptSplit vyperStorageTrace

Theorem target_array_suffix_prefix:
  array_tail_packet [(NONE,tops)] [] tops DF lo d ctx func cenv cx env bt e es et bd
    st0 vt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
    mid1 t1 G1 tn1 mid2 t2 G2 tn2 ==>
  gas_prefix_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (extend_place cx pv (ValueSubscript v)) (mid2,t2,G2,tn2)
Proof
  strip_tac >> drule array_tail_packet_finite_source >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  drule_all array_tail_packet_extend_result >> strip_tac >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_extend_place, target_subscript_extend_gas_obs] >>
  fs[array_tail_packet_def]
QED
