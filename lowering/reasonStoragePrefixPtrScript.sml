(* Located storage/transient source frames for the shared reason prefix. *)
Theory reasonStoragePrefixPtr
Ancestors
  storageNormalizationOwnershipPtr reasonPrefixPtr reasonPrefixResourcesPtr
  bodyPtrDefs loweringPosts allocationPtr reasonAllocationFramePtr
  exprSimAlloc exprSimProps exprLoweringProps loweringHalt compileEnv
  context venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  finite_map words

Theorem reason_storage_alloc_buffer_resources:
  !ctx func cenv cx es s cc cd buf n ty tv p t' PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
    local_ptrs_reserved cenv cc /\ fn_inst_ids_distinct func /\
    n < dimword(:256) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ptr_vv_ok cx ty tv (LocatedValue t' p) es G tn s ==>
    ?s1 out w G1 tn1.
      buf.buf_operand = Var out /\
      step_inst_base (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
      stmt_state_rel ctx func cenv cx es s1 /\
      local_ptrs_reserved cenv cd /\
      G1 = step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s1 /\
      tn1 = step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
      FLOOKUP s1.vs_allocas cc.cs_next_id = SOME (w2n w,n) /\
      w2n w+n < dimword(:256) /\ eval_operand (Var out) s1 = SOME w /\
      ptr_covers G1 tn1 out s1 n /\
      (!old k. not_fresh_at cc old /\ ptr_covers G tn old s k ==>
        ptr_covers G1 tn1 old s1 k) /\
      eval_operand p.ptr_operand s1 = eval_operand p.ptr_operand s /\
      ptr_vv_ok cx ty tv (LocatedValue t' p) es G1 tn1 s1 /\
      (!tr sty stv a. storage_holds cx tr sty stv a es s ==>
        storage_holds cx tr sty stv a es s1) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP s1.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < cc.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) n b len) /\
      (!name b len. local_region cenv es.scopes s1 name b len ==>
        regions_disjoint (w2n w) n b len) /\
      MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
      not_local_ptr cenv es.scopes out
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all normalization_alloc_buffer_ownership >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  rename1 `buf.buf_operand = Var out` >>
  `out = STRING #"%" (toString cc.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `!x. p.ptr_operand = Var x ==> x <> out` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `MEM (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts func)` by metis_tac[] >>
  `eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
   ptr_vv_ok cx ty tv (LocatedValue t' p) es
     (step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) t)
     (step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn) t` by
    (irule normalization_alloca_located_storage >> metis_tac[]) >>
  `local_ptrs_reserved cenv cd` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `cc` >>
     drule compile_alloc_buffer_parts >> simp[]) >>
  qexistsl_tac [`t`, `out`, `w`,
    `step_prov PG G (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) t`,
    `step_taint (mk_inst cc.cs_next_id ALLOCA [Lit (n2w n)] [out]) s t tn`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[])
  >- (rpt strip_tac >> irule normalization_alloca_storage_holds >> metis_tac[]) >>
  qspecl_then [`cenv`, `cc`, `es.scopes`, `cc.cs_next_var`] mp_tac
    local_ptrs_reserved_fresh >> simp[]
QED
