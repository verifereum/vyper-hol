Theory bodyPtrIfExpBytesSemantic
Ancestors
  exprSimBufferStore exprSimProps exprSimDefs loweringPosts compileEnv loweringStateRelDefs
  venomState venomInst venomExecSemantics finite_map words exprSimCopy

Theorem ifexp_bytes_mcopy_semantic_state:
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [out]) (fn_insts fn) /\
  not_local_ptr ce es.scopes out /\ n <= capacity /\
  FLOOKUP s.vs_allocas aid = SOME (b,capacity) /\
  (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  sf.vs_memory = (mcopy b a n s).vs_memory /\
  local_ptrs_reserved ce sc /\
  (!p. not_fresh_at sc p ==> lookup_var p sf = lookup_var p s) ==>
  stmt_state_rel ctx fn ce cx es sf
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx es (mcopy b a n s)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`capacity`, `mk_inst aid ALLOCA [Lit (n2w capacity)] [out]`, `out`] >>
     simp[mk_inst_def]) >>
  `sf = (mcopy b a n s) with vs_vars := sf.vs_vars` by
    (gvs[venom_state_component_equality, mcopy_def,
         write_memory_with_expansion_def, write_memory_def, expand_memory_def]) >>
  qpat_x_assum `sf = _` SUBST1_TAC >>
  irule stmt_state_rel_vars_frame >> simp[] >>
  gvs[local_ptrs_reserved_def, mcopy_def, write_memory_with_expansion_def,
      write_memory_def, expand_memory_def, lookup_var_def] >> metis_tac[]
QED

Theorem ifexp_allocated_destination_placement:
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand op q = SOME w /\
  FLOOKUP q.vs_allocas aid = SOME (w2n w,capacity) /\
  sa.cs_next_id <= aid /\ aid < sd.cs_next_id /\ val_footprint tv v <= capacity /\
  (!name p sz. local_region ce ee.scopes q name p sz ==>
    p+sz <= w2n w \/ w2n w+capacity <= p) ==>
  expr_val_at ce cx ty sa sd ee v op q
Proof
  strip_tac >> simp[expr_val_at_def] >> rpt strip_tac >> gvs[] >>
  disj1_tac >> qexistsl_tac [`aid`, `w2n w`, `capacity`] >> simp[] >> metis_tac[]
QED

Theorem ifexp_bytes_original_semantic_frame:
  vv_post ctx fn ce cx arm es sa sc s0 ee raw vv t /\
  sa.cs_next_var <= sc.cs_next_var /\ n <= capacity /\
  (!x. not_fresh_at sc x ==> lookup_var x sf = lookup_var x t) /\
  sf.vs_allocas = t.vs_allocas /\
  (!off len. off+len <= b \/ b+n <= off ==>
    mem_bytes_at off len sf.vs_memory = mem_bytes_at off len t.vs_memory) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= b \/ b+capacity <= off) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+capacity <= p) ==>
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x sf = SOME w) /\
  (!aid site. FLOOKUP s0.vs_allocas aid = SOME site ==> FLOOKUP sf.vs_allocas aid = SOME site) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==> off+sz <= p \/ p+len <= off) ==>
    mem_bytes_at off sz sf.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
  locals_kept ce es ee s0 sf
Proof
  strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x sf = SOME w` by
    (gvs[vv_post_def] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  simp[] >> conj_tac
  >- gvs[vv_post_def] >> conj_tac
  >- (rpt strip_tac >>
      `off+sz <= b \/ b+n <= off` by
        (qpat_x_assum `!aid off sz. _ ==> off+sz <= b \/ b+capacity <= off`
           (qspecl_then [`aid`, `off`, `sz`] mp_tac) >> simp[] >> decide_tac) >>
      `mem_bytes_at off sz sf.vs_memory = mem_bytes_at off sz t.vs_memory` by metis_tac[] >>
      gvs[vv_post_def] >>
      qpat_x_assum `!aid off sz. _ /\ _ /\ _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      simp[] >>
      (impl_tac >- (rpt strip_tac >> first_x_assum drule >>
                    simp[arithmeticTheory.ADD_COMM])) >> simp[]) >>
  `locals_kept ce es ee s0 t` by gvs[vv_post_def] >>
  irule copy_buffer_locals_kept_frame >>
  goal_assum (drule_at (Pat `locals_kept _ _ _ _ _`)) >>
  qexistsl_tac [`b`, `n`] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name p sz. local_region _ _ _ _ _ _ ==> _` drule >>
      strip_tac >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ sf.vs_memory = _` irule >>
  decide_tac
QED
