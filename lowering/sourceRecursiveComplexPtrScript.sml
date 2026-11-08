(* Scratch-aware observation boundaries for recursive calldata decoders. *)
Theory sourceRecursiveComplexPtr
Ancestors sourcePrimitiveComplexPtr robustCopyTransportPtr abiDecoderFrame bodyPtrDefs

Theorem robust_value_footprint_frame:
  val_wf tv v /\ abi_decode_footprint_frame fp s t /\
  abi_footprint_disjoint p (val_footprint tv v) fp /\
  u.t_mem SUBSET tn.t_mem /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) ==>
  val_in_memory tv v p t.vs_memory /\
  (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v p mem)
Proof
  strip_tac >> drule_all abi_decode_footprint_frame_slice >> strip_tac >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v p mem` by
    metis_tac[calldata_member_robust_window_frame] >>
  simp[] >> first_x_assum irule >> simp[mem_agree_outside_def]
QED
