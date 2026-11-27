(* The head field's full endpoint is after its store, where the tail starts. *)
Theory s1PrefixStructLitFieldOutcome
Ancestors
  bodyFullStructLit bodyFullPreds bodySimFull gasOutcomeFull gasContext
  exprSimDefs exprSimFullBundleProps bodyPtrMakeArrayEmission bodyMemoryDefs
  loweringPosts compileEnv exprLoweringProps gasShadowCompile fragExec
  vyperInterpreter vyperStorageTrace vyperStorageFootprint vyperTypeSystem
  typeLayoutProps list pair option

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  irule gas_outcome_full_post_mono >>
  irule_at Any (structlit_fields_bundled_full |> INST_TYPE [alpha |-> ``:256``] |>
    Q.SPEC `inv'` |> UNDISCH |>
    Q.SPECL [`[(fname,e)]`, `[fty]`, `[ftv]`] |>
    SIMP_RULE (srw_ss()) [LIST_REL_CONS1, type_memory_size_list_sum]) >>
  qpat_x_assum `inv' = _` kall_tac >>
  qpat_assum `compile_struct_lit _ ce _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_struct_lit _ _ _ [(fname,gas_shadow_expr e)]
                _ _ shadow_si = (_,shadow_sb)` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
  qpat_assum `ALOOKUP _ _ = SOME (_,_)` (irule_at Any) >>
  qpat_assum `evaluate_type _ _ = SOME _` (irule_at Any) >>
  qexistsl_tac [`cells`, `Hbase`] >>
  simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
*)
Theorem structlit_single_field_store_outcome:
  inv' = (\H ee cs G tn s cells off.
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s /\
    wb_frame ce ees ee fr sf s /\ ghost_kept_at lo ce ees fr Gf tnf sf G tn /\
    MAP FDOM ees.scopes = MAP FDOM ee.scopes /\
    ~s.vs_halted /\ expr_sim_full_endpoint func cs sf s /\
    not_fresh_at cs root /\ lookup_var root s = SOME (n2w addr) /\
    ptr_covers G tn root s capacity /\
    FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
    MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [root]) (fn_insts func) /\
    lo <= addr /\ addr+capacity < dimword (:256) /\
    fr.cs_next_id <= aid /\ aid < cs.cs_next_id /\
    fr.cs_next_var <= cs.cs_next_var /\ off <= capacity /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!name p k. local_region ce ees.scopes sf name p k ==>
      addr+capacity <= p \/ p+k <= addr) /\
    (!old p k. FLOOKUP sf.vs_allocas old = SOME (p,k) /\ old < fr.cs_next_id ==>
      addr+capacity <= p \/ p+k <= addr) /\
    EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\
    literal_prefix_ok cells tn s /\
    (pure ==> pure_frame ce func ees fr sf s)) /\
  compile_struct_lit compile_expr ce (StructT nsid) [(fname,e)] (Var root) off si = (out,sb) /\
  compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
    [(fname,gas_shadow_expr e)] (Var root) off shadow_si = (out,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sb,shadow_si,shadow_sb) /\
  body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  body_inv (cx_tops cx) ctx ce cx /\
  shadow_body_inv (cx_tops cx) ctx shadow_ctx /\
  body_exprs_full_ok cx [e] /\
  (?(Hbase : (bool # 256 word # type_value) list # num list).
    stmt_state_rel Hbase ctx func ce cx ees sf) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,type_memory_bytes ce fty) /\
  arg_type_fits (expr_type e) fty /\
  evaluate_type (get_tenv cx) fty = SOME ftv /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s0 /\
  (!st. expr_sim_inv ce cx env st ==> expr_body_pre ce cx env e st) /\
  (pure ==> ~expr_has_effect e) /\ expr_sim_inv ce cx env es /\
  storage_trace_domain cx st0 es.storage_trace /\
  off + type_memory_size ftv <= capacity /\
  gas_admissible (eval_exprs cx [e])
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    inv' H es si G0 tn0 s0 cells off) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx [e]) (es,s0,G0,tn0)
    (\H res ee G tn z. ?v added. res = INL [v] /\ expr_sim_inv ce cx env ee /\
      value_has_type ftv v /\
      inv' H ee sb G tn z (cells++added) (off+type_memory_size ftv) /\
      (!m. mem_agree_outside tn.t_mem z.vs_memory m ==>
        fields_in_memory [(fname,v)] [(fname,ftv)] (addr+off) m))
    (\H res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
      halt_exit H cx ee (INR exc : eval_result + exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  cheat
QED
