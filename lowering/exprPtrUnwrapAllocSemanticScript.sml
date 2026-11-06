(* Semantic reconstruction uses the concrete allocation endpoint, not a new run. *)
Theory exprPtrUnwrapAllocSemantic
Ancestors
  exprPtrUnwrapAllocEntry exprPtrUnwrapAllocation exprSimAlloc loweringSlice exprLoweringProps arithmetic
  bufferAllocationExecution loweringPosts compileEnv context venomState venomInst
  venomExecSemantics words finite_map

Theorem unwrap_alloc_semantic_state:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  stmt_state_rel ctx func cenv cx es (u with vs_inst_idx := k) /\
  ?w. lookup_var root u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,nb)
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  `root = STRING #"%" (toString sa.cs_next_var)` by fs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `not_local_ptr cenv es.scopes root` by
    (simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def]) >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  gvs[mk_inst_def] >> disch_then drule_all >>
  simp[stmt_state_rel_inst_idx, w2n_n2w, LESS_MOD]
QED
