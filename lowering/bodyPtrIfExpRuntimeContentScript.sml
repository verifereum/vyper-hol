Theory bodyPtrIfExpRuntimeContent
Ancestors exprSimCopy exprSimPtrLiteralBuffer bodyPtrDefs

(* The erased content theorem supplies only representation.  The counted
   copier must separately supply the destination's byte-cleanliness. *)
Theorem ifexp_runtime_copy_robust:
  stmt_state_rel ctx fn ce cx ee u /\ ~ce.ce_is_ctor /\
  immutable_holds ce cx ann (Value v) a ee s /\
  evaluate_type (get_tenv cx) ann = SOME ty /\
  w2n d + type_memory_size ty < dimword (:256) /\
  t.vs_memory = (immutable_transfers F F a d (type_slot_size ty) 0 u).vs_memory /\
  (!i. w2n d <= i /\ i < w2n d+type_memory_size ty ==> i NOTIN tn.t_mem) ==>
  val_wf ty v /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ty v (w2n d) m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all copy_runtime_contents >> strip_tac >>
  `!i. w2n d <= i /\ i < w2n d+val_footprint ty v ==> i NOTIN tn.t_mem` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  conj_tac >- simp[] >>
  rpt strip_tac >> irule literal_clean_representation_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`tn.t_mem`, `t.vs_memory`] >> simp[]
QED
