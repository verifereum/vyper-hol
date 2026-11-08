(* Allocation ownership boundaries for external slice address evaluation. *)
Theory exprSimSliceExtcodeEntry
Ancestors
  exprSimSliceExtcodeContext exprSimSliceMemory exprSimSliceExtcode
  exprSimHash loweringHalt exprSimProps exprSimPrecompiles loweringPosts
  compileEnv exprLoweringProps fragExec finite_map words pair list venomState

Theorem slice_extcode_out_owner_inst:
  compile_slice_out_buf sz sa = ((out,data),sb) /\ fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule slice_out_buf_decompose >> strip_tac >>
  irule hash_emitted_inst_mem >> qexistsl_tac [`sa`, `sb`] >> simp[] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1]) >> simp[]
QED

Theorem slice_extcode_output_entry:
  compile_slice_out_buf sz sa = ((out,data),sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand out t = SOME p /\ eval_operand data t = SOME (p + 32w) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
    w2n p + sz < dimword (:256) /\ sa.cs_next_id < sb.cs_next_id /\
    (!name off len. local_region cenv es.scopes t name off len ==>
      regions_disjoint (w2n p) sz off len) /\
    (?x. out = Var x /\ not_fresh_at sb x) /\
    (?x. data = Var x /\ not_fresh_at sb x) /\
    stmt_state_rel ctx func cenv cx es t /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!j b len. j < sa.cs_next_id /\ FLOOKUP t.vs_allocas j = SOME (b,len) ==>
      regions_disjoint (w2n p) sz b len) /\
    wb_frame cenv es sa s t
Proof
  strip_tac >> drule_all slice_extcode_out_owner_inst >> strip_tac >>
  drule_all slice_out_buf_run >> strip_tac >>
  qexistsl_tac [`t`, `p`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> irule state_allocations_disjoint >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem slice_extcode_output_post:
  expr_post ctx func cenv cx a es sa sb s ee v addr t /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  eval_operand out s = SOME p /\ eval_operand data s = SOME (p + 32w) /\
  (?x. out = Var x /\ not_fresh_at sa x) /\
  (?x. data = Var x /\ not_fresh_at sa x) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n p,cap) /\
  (!nm off sz. local_region cenv es.scopes s nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  sbase.cs_next_id <= aid ==>
  stmt_state_rel ctx func cenv cx ee t /\
  eval_operand out t = SOME p /\ eval_operand data t = SOME (p + 32w) /\
  FLOOKUP t.vs_allocas aid = SOME (w2n p,cap) /\
  (!nm off sz. local_region cenv ee.scopes t nm off sz ==>
    regions_disjoint (w2n p) cap off sz) /\
  (!j off sz. FLOOKUP t.vs_allocas j = SOME (off,sz) /\ j < sbase.cs_next_id ==>
    regions_disjoint (w2n p) cap off sz)
Proof
  strip_tac >>
  `!op w. MEM op [out;data] /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w` by
    (rpt strip_tac >> gvs[MEM, eval_operand_def] >>
     fs[expr_post_def] >> first_x_assum irule >> simp[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (w2n p,cap)` by fs[expr_post_def] >>
  `stmt_state_rel ctx func cenv cx ee t` by fs[expr_post_def] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes s nm off sz` by
        (irule local_region_frame >> conj_tac
         >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl_tac [`sa`, `ee.scopes`, `t`] >> fs[expr_post_def]) >>
      metis_tac[]) >>
  rpt strip_tac >> irule state_allocations_disjoint >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> decide_tac
QED
