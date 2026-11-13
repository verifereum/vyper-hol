(* Registered and local windows retain captures during tuple construction. *)
Theory extcallCaptureStoreFrameMemory
Ancestors
  extcallCaptureFrameMemory exprSimIfExpWidenedAdapter exprSimProps
  loweringPosts valueEncodingProofs valueEncoding valueEncodingDefs vyperInterpreter vyperState compileEnv

Theorem extcall_captured_registered_memory_frame:
  vv_at ce cx ty sa sb es (Value v) (LocatedValue tag p) s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\ sb.cs_next_id <= limit /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < limit ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) ==>
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def,read_result_def,return_def] >> strip_tac >> gvs[]
  >- (`aid < limit` by decide_tac >>
      `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        metis_tac[] >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        metis_tac[] >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED
