(* Effect-free operand tails preserve a captured memory value in full,
   including dynamic-array length words. *)
Theory extcallCaptureFrameMemory
Ancestors
  exprSimSubscriptArrayFrame loweringPosts allocaSiteResource
  loweringStateRelDefs venomMemDefs valueEncodingProofs valueEncoding valueEncodingDefs
  compileEnv venomState list

Theorem extcall_captured_memory_pure_frame:
  vv_at ce cx ty sa sb es r (LocatedValue tag p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  pure_frame ce func es st s t /\ sb.cs_next_id <= st.cs_next_id /\
  alloca_inv t /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) ==>
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- suspend "registered"
  >- (qpat_x_assum `pure_frame _ _ _ _ _ _` mp_tac >>
      simp[pure_frame_def] >> strip_tac >>
      `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        metis_tac[] >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED
Resume extcall_captured_memory_pure_frame[registered]:
  `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
  `!inst a n.
     MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     st.cs_next_id <= inst.inst_id /\
     FLOOKUP t.vs_allocas inst.inst_id = SOME (a,n) ==>
     loweringStateRelDefs$regions_disjoint b sz a n` by
    (rpt strip_tac >>
     `aid <> inst.inst_id` by decide_tac >>
     `b+sz <= a \/ a+n <= b` by
       (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[pure_frame_def] >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> simp[]
QED
Finalise extcall_captured_memory_pure_frame
