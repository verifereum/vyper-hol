Theory exprSimAbiDecodeChildFrame
Ancestors
  abiDecoderSiteEffect valueEncodingProps pred_set

Theorem abi_decode_child_source_window:
  decode_site_effect ctx fn first writes origin s /\
  decode_site_effect ctx fn child V s t /\ first <= child /\ V SUBSET writes /\
  decode_protects writes {(B,H)} /\ off+k <= H ==>
  mem_bytes_at (B+off) k t.vs_memory =
  mem_bytes_at (B+off) k origin.vs_memory
Proof
  strip_tac >> drule_all decode_site_effect_fixed_origin >> strip_tac >>
  `mem_bytes_at B H t.vs_memory = mem_bytes_at B H origin.vs_memory` by
    metis_tac[decode_site_effect_protected, IN_SING] >>
  irule mem_bytes_at_translated_window >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_decode_child_completed_value:
  decode_site_effect ctx fn child V s t /\
  decode_protects V {(d,type_memory_size tv)} /\
  val_in_memory tv v d s.vs_memory /\ val_wf tv v ==>
  val_in_memory tv v d t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at d (type_memory_size tv) t.vs_memory =
   mem_bytes_at d (type_memory_size tv) s.vs_memory` by
    metis_tac[decode_site_effect_protected, IN_SING] >>
  irule val_in_memory_mem_agree >> goal_assum (drule_at Any) >>
  qexists_tac `type_memory_size tv` >> simp[] >>
  qexists_tac `s.vs_memory` >> simp[]
QED

Theorem abi_decode_origin_source_suffix:
  decode_site_effect ctx fn first writes origin s /\
  decode_protects writes {(B,H)} /\ off <= H ==>
  mem_bytes_at (B+off) (H-off) s.vs_memory =
  mem_bytes_at (B+off) (H-off) origin.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at B H s.vs_memory = mem_bytes_at B H origin.vs_memory` by
    metis_tac[decode_site_effect_protected, IN_SING] >>
  irule mem_bytes_at_translated_window >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_decode_protects_interval:
  (!a. a IN V ==> a < d \/ d+len <= a) ==>
  decode_protects V {(d,len)}
Proof
  simp[decode_protects_def] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED
