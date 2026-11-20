Theory bodyFullUnwrapCodePureFrame
Ancestors
  exprPtrUnwrapAllocation exprSimAlloc exprSimProps loweringStateRelDefs
  compileEnv venomState venomInst finite_map arithmetic words

Theorem unwrap_alloc_copy_pure_frame:
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  buf.buf_operand = Var root /\
  FLOOKUP u.vs_allocas sb.cs_next_id = SOME (dst_addr,nb) /\
  z.vs_allocas = u.vs_allocas /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    b+len <= dst_addr \/ dst_addr+nb <= b) /\
  (!off len. off+len <= dst_addr \/ dst_addr+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  pure_frame cenv func ee sb s z
Proof
  strip_tac >>
  match_mp_tac (Q.SPECL [`cenv`,`func`,`ee`,`sb`,`s`,`z`,`sb.cs_next_id`,
    `[Lit (n2w nb)]`,`[root]`,`dst_addr`,`nb`] exprSimPropsTheory.pure_frame_fresh_alloca) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule exprPtrUnwrapAllocationTheory.unwrap_alloc_generated_code >> strip_tac >>
     drule_all exprSimAllocTheory.buffer_alloc_code >> gvs[]) >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
      qpat_assum `!n b len. local_region cenv ee.scopes s n b len ==> _`
        (drule_then ACCEPT_TAC)) >>
  simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def] >>
  rpt strip_tac >>
  qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
  decide_tac
QED
