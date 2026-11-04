(* Opcode-independent ambient projections of synchronization. *)
Theory lowerDloadSafetyAmbient
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadDefs words
  o1PassContract venomWf venomInst list

Theorem ld_sync_labels:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  s.vs_labels = t.vs_labels
Proof
  strip_tac >> drule ld_sync_memory >>
  simp[ld_nonghost_def]
QED

Theorem ld_sync_target_headroom:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next < dimword(:256)
Proof
  strip_tac >> drule ld_sync_frontier >>
  gvs[dload_headroom_ok_def]
QED

Theorem ld_sync_fn_shape:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  o1_ctx_shape C ==> o1_fn_shape C fn
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (qhdtm_x_assum `ld_sync` mp_tac >>
     simp[ld_sync_def, EVERY_MEM] >> strip_tac >>
     `MEM (HD frames) frames` by (Cases_on `frames` >> gvs[]) >>
     metis_tac[]) >>
  gvs[o1_ctx_shape_def, EVERY_MEM]
QED

Theorem o1_fn_shape_components:
  o1_fn_shape C fn ==>
  fn_shape_ok fn /\ fn_inst_wf fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)
Proof
  simp[o1_fn_shape_def, wf_function_def, fn_labels_def]
QED
