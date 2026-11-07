Theory exprSimAggregateBodyCountedLoops
Ancestors
  exprSimAggregateBodyCountedChildren exprSimAggregateLoops exprLowering
  compileEnv exprLoweringProps emitHelper list exprSimSource exprSimHypsDefs exprSimDefs
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom gasSummary gasContext
  exprSimAggregateChildren emitHelperProps exprSimVVFrame fragGasMode
  exprSimProps loweringPosts stmtSimDefs valueEncodingProofs
  venomExecSemantics venomInstProofs venomInst venomState
Libs
  monadsyntax

Theorem aggregate_tuple_body_cons_compile:
  compile_make_tuple compile_expr ce (e::args) buf off sa = (out,sb) ==>
  ?vv sm dst sn op su st.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e)
      su = ((),st) /\
    compile_make_tuple compile_expr ce args buf
      (off + type_memory_bytes ce (expr_type e)) st = (out,sb)
Proof
  simp[Once compile_make_tuple_def, comp_bind_def] >>
  rpt (pairarg_tac >> fs[]) >> rpt strip_tac >> gvs[] >>
  gvs[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> Cases_on `v'` >> metis_tac[]
QED


Theorem aggregate_body_tuple_marked_child_source:
  expr_body_pre ce cx env e es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK t) ==>
  expr_sim_inv ce cx env (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  immutable_metadata_frame es (mid with gas_obs := []) /\
  ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,mid with gas_obs := []) tv (Type (expr_type e)) /\
    (!v. read_result cx tv (mid with gas_obs := []) =
           (INL v,mid with gas_obs := []) ==> value_has_type tvt v)
Proof
  rpt strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >> gvs[] >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  gvs[expr_sim_inv_gas_obs]
  >- (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  drule eval_expr_immutable_metadata_frame >>
  simp[immutable_metadata_frame_def] >> metis_tac[]
QED

Theorem aggregate_body_tuple_child_outcome:
  exprs_case nocalls ctx func ce cx (e::args) /\
  expr_body_pre ce cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx e es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  rw[exprs_case_def, expr_vv_case_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (rw[gas_admissible_def] >> metis_tac[expr_body_pre_gas_obs,
                                        expr_body_pre_vv_res_ok]) >>
  metis_tac[expr_vv_sim_def]
QED

Theorem aggregate_body_tuple_marked_footprint:
  expr_body_pre ce cx env e es /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) mid (OK t) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b n) ==>
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b n)
Proof
  strip_tac >> drule_all aggregate_body_tuple_marked_child_source >>
  strip_tac >> fs[immutable_metadata_frame_def] >> rpt strip_tac >>
  qpat_x_assum `!addr. IS_SOME _ <=> IS_SOME _`
    (qspec_then `cx.txn.target` assume_tac) >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[] >>
  first_x_assum (drule_all_then (qspecl_then [`ce.ce_module`, `name`] mp_tac)) >>
  Cases_on `FLOOKUP (get_source_immutables ce.ce_module x) name` >>
  simp[] >> Cases_on `x''` >> gvs[] >> metis_tac[]
QED

Theorem aggregate_body_tuple_add_marked:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand buf s = SOME w /\ fn_has_code sm sn func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >> drule_all buffer_emit_add_vv_post >> strip_tac >>
  `!out. step_inst_base (mk_inst sm.cs_next_id ADD [buf; Lit (n2w off)]
       [out]) s = OK (update_var out (w + n2w off) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `gas_path ctx func s 0
    (OK (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_op_zero_path >> simp[is_terminator_def] >>
     goal_assum (drule_at Any) >> simp[is_terminator_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `q = update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s` by
    gvs[run_inst_seq_def] >>
  qexists_tac `q with vs_inst_idx := SUC s.vs_inst_idx` >>
  gvs[gas_marked_path_def, update_var_def, eval_operand_def, lookup_var_def] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def]
QED

Theorem aggregate_body_tuple_local_region_backward:
  !es es1 s0 s1 sa sb ctx func ce cx e tv vv name b sz.
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  rpt strip_tac >> irule local_region_frame >>
  fs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  conj_tac >- (qexists_tac `func` >> simp[]) >>
  qexistsl_tac [`sa`, `es1.scopes`, `s1`] >> simp[]
QED

(* An old nonlocal allocation is preserved as a whole by child evaluation;
   every slice inherits that frame, independently of the child's layout. *)
Theorem aggregate_body_child_slice_frame:
  vv_post ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lo len. local_region ce es.scopes s0 name lo len ==>
    b+sz <= lo \/ lo+len <= b) /\
  b <= p /\ p+n <= b+sz ==>
  mem_bytes_at p n s1.vs_memory = mem_bytes_at p n s0.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory` by
    (fs[vv_post_def] >> first_x_assum irule >>
     conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qexists_tac `aid` >> simp[]) >>
  drule mem_bytes_at_agree_window >> simp[]
QED

(* The aggregate's destination allocation is nonlocal at every source state
   in the loop.  Derive both the whole-allocation and current-slot frames
   at the actual post-child state, not at an intermediate compiler age. *)
Theorem aggregate_body_destination_separation:
  stmt_state_rel ctx func ce cx es r /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\ off+n <= asz ==>
  (!name lo sz. local_region ce es.scopes r name lo sz ==>
    lo+sz <= b \/ b+asz <= lo) /\
  (!name lo sz. local_region ce es.scopes r name lo sz ==>
    lo+sz <= b+off \/ b+off+n <= lo)
Proof
  strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      mp_tac (Q.INST [`off` |-> `0`, `n` |-> `asz`]
        aggregate_alloca_slice_excludes_local) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all aggregate_alloca_slice_excludes_local >> simp[]
QED

(* Compose the child's whole-allocation frame with a store's slice frame.
   The age bound is sa, even though the store starts after child and ADD. *)
Theorem aggregate_body_child_store_frames:
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv r /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  FLOOKUP s0.vs_allocas did = SOME (b,asz) /\ did < sa.cs_next_id /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b) /\
  off+len <= asz /\
  (!aid a k p n.
    FLOOKUP r.vs_allocas aid = SOME (a,k) /\ aid < sa.cs_next_id /\
    (!name lo sz. local_region ce es1.scopes r name lo sz ==>
      a+k <= lo \/ lo+sz <= a) /\
    a <= p /\ p+n <= a+k /\
    (p+n <= b+off \/ b+off+len <= p) ==>
    mem_bytes_at p n q.vs_memory = mem_bytes_at p n r.vs_memory) ==>
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+off \/ b+off+len <= p) ==>
    mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory)
Proof
  strip_tac >>
  `!name lo sz. local_region ce es1.scopes r name lo sz ==>
     local_region ce es.scopes s0 name lo sz` by
    (rpt strip_tac >> irule aggregate_body_tuple_local_region_backward >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
    FLOOKUP r.vs_allocas aid = SOME a` by fs[vv_post_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
           aggregate_body_child_slice_frame >> disch_then irule >>
         qexistsl_tac [`did`, `b`, `asz`] >> simp[] >>
         metis_tac[arithmeticTheory.ADD_COMM]) >>
      `mem_bytes_at p n q.vs_memory = mem_bytes_at p n r.vs_memory` by
        (first_x_assum irule >> reverse conj_tac >- simp[] >>
         qexistsl_tac [`b`, `did`, `asz`] >> simp[] >>
         metis_tac[arithmeticTheory.ADD_COMM]) >> simp[]) >>
  rpt strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
       aggregate_body_child_slice_frame >> disch_then irule >>
     qexistsl_tac [`aid`, `p`, `n`] >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n r.vs_memory` by
    (first_x_assum irule >> reverse conj_tac >- decide_tac >>
     qexistsl_tac [`p`, `aid`, `n`] >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >> simp[]
QED

(* Metadata replay preserves the whole remaining footprint.  A head slot
   can then be selected without replaying the metadata argument again. *)
Theorem aggregate_body_immutable_slice:
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b n) /\
  b <= p /\ p+len <= b+n ==>
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name =
        SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) p len)
Proof
  strip_tac >> rpt strip_tac >>
  first_x_assum drule >> disch_then drule >>
  simp[regions_disjoint_def] >> decide_tac
QED
