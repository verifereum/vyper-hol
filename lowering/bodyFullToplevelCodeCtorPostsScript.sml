(* Same-endpoint constructor aggregate contents; no operational witnesses are chosen here. *)
Theory bodyFullToplevelCodeCtorPosts
Ancestors
  exprSimCopy exprSimMemUnwrap robustCopyTransportPtr bodyFullToplevelCodePosts
  bodyFullToplevelCodeWitnessPosts valueEncodingProps valueEncodingDefs exprSimMemorySource
  exprLowering compileEnv venomMemDefs venomState words arithmetic list

Theorem toplevel_code_ctor_contents:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm) /\
  compile_imm_copy_to_memory T imm src dst (type_slot_size rt) 0 mid = ((),sb) /\
  copy_old_operand mid src /\ copy_old_operand mid dst /\
  eval_operand src a = SOME p /\ eval_operand dst a = SOME w /\
  (!region. imm = SOME region ==> eval_operand region a = SOME 0w /\
    copy_old_operand mid region) /\
  copy_runtime_frame mid a sb z /\
  stmt_state_rel H ctx func cenv cx ee a /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) p ee a /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  w2n w + type_memory_size rt < dimword(:256) /\
  regions_disjoint (w2n p) (type_memory_size rt) (w2n w) (type_memory_size rt) ==>
  val_wf rt v /\ val_in_memory rt v (w2n w) z.vs_memory /\
  val_footprint rt v <= type_memory_size rt /\
  LENGTH a.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size rt <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  mem_bytes_at (w2n w) (type_memory_size rt) z.vs_memory =
    mem_bytes_at (w2n p) (type_memory_size rt) a.vs_memory
Proof
  strip_tac >> drule_all copy_ctor_run >> strip_tac >>
  `zz = z` by fs[copy_runtime_frame_def] >>
  qpat_x_assum `zz = z` SUBST_ALL_TAC >>
  drule_all copy_ctor_contents >> strip_tac >>
  reverse (rpt conj_tac)
  >- (Cases_on `type_slot_size rt = 0`
      >- gvs[type_memory_size_slots, mem_bytes_at_def] >>
      `w2n p + type_memory_size rt < dimword(:256)` by
        metis_tac[immutable_holds_bounds] >>
      drule_all copy_ctor_memory_snapshot >> disch_tac >>
      asm_rewrite_tac[] >>
      qspecl_then [`w2n w`, `mem_bytes_at (w2n p) (type_memory_size rt) a.vs_memory`, `a`]
        mp_tac write_memory_mem_bytes_at_same >> simp[]) >>
  metis_tac[]
QED
