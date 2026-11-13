(*
 * The store loops of aggregate literals (#636)
 *
 * compile_make_tuple, compile_struct_lit and compile_make_array emit an
 * ADD, an unwrap and a store per child.  By induction on the children,
 * the source evaluation of each loop is a counted gas_outcome over its
 * code: the code fills the loop's slice of the buffer and keeps the bytes
 * outside it, the older allocations and the locals.
 *
 * TOP-LEVEL:
 *   aggregate_make_tuple_sim — compile_make_tuple
 *   aggregate_struct_fields_sim — compile_struct_lit, by the tuple loop
 *   aggregate_make_array_sim — compile_make_array, with or without a
 *     length word
 *
 * Helpers: aggregate_alloca_slice_excludes_local,
 *   compile_make_array_elems_as_tuple, and the per-step sims.
 *)
Theory exprSimAggregateLoops
Ancestors
  exprSimHashBoundary
  exprBopSimProps
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprSimAggregateSource exprSimAggregateEncoding exprSimAggregateLayout exprLoweringProps
  localPtrsProps compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs valueEncodingProofs
  valueEncodingProps exprLowering vyperInterpreter vyperState
  exprSimHyps  fragExec exprSimAggregateChildren exprSimOps
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom
  exprSimAlloc gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq stmtSimDeclPath stmtSimDeclCompose
  abiStaticAggregateProps venomState exprSimUnwrap
  exprSimBufferStore valueCopyBytes freshWrites
  gasStorage gasExemptCert vyperStorageTrace vyperStorageFootprint


Theorem aggregate_alloca_slice_excludes_local:
  stmt_state_rel H ctx func ce cx es r /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + n <= asz /\ local_region ce es.scopes r name lo sz ==>
  lo + sz <= b + off \/ b + off + n <= lo
Proof
  strip_tac >>
  `alloca_inv r /\ local_ptrs_rel func ce es.scopes r` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[regions_disjoint_def] >> decide_tac
QED

(* An element is stored from its lowered type. That type differs from the
   element's own only for bytestrings, whose store ignores the source type,
   and for an internal call returning a wider layout, which the caller rules
   out. *)
Theorem aggregate_elem_lowered_type:
  !ce e env.
    well_typed_expr env e /\
    (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
    lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, vyperASTTheory.expr_type_def, is_bytestring_type_def,
       vyperTypeSystemTheory.well_typed_expr_def,
       vyperTypeSystemTheory.type_builtin_result_ok_def,
       vyperTypeCallGraphTheory.int_calls_expr_def] >>
  rpt strip_tac >> gvs[is_bytestring_type_def] >>
  (* concat: its typing makes the annotation a bytestring *)
  gvs[vyperTypeSystemTheory.well_typed_builtin_app_def] >>
  rpt (pop_assum mp_tac) >> rw[] >> gvs[is_bytestring_type_def]
QED

Theorem aggregate_store_lowered_elem[local]:
  !ce e src dst.
    lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e) ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
    compile_store_memory ce src dst (expr_type e) (expr_type e)
Proof
  rpt strip_tac >> simp[contextTheory.compile_store_memory_def] >> gvs[]
QED


(* ===== Counted composition of the tuple loop ===== *)

(* The empty source list is a genuine reflexive counted execution. *)
Theorem aggregate_tuple_nil_outcome:
  ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     Q H (INL []) (es with gas_obs := []) s) ==>
  gas_outcome memory tops (ctx,func) cx st0 (eval_exprs cx []) (es,s) Q R
Proof
  strip_tac >> rewrite_tac[gas_outcome_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL []`, `es`, `OK s`] >>
  simp[gas_marked_exec_def, exprSimWordArgsTheory.eval_exprs_nil,
       gas_marked_path_def] >>
  Cases_on `memory` >> simp[cj 1 gas_path_rules, cj 1 gas_path_mem_rules]
QED

Theorem aggregate_tuple_child_outcome[local]:
  exprs_case nocalls ctx func ce cx (e::args) /\
  expr_body_pre ce cx env e es /\ (nocalls ==> int_calls_expr e = []) /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_expr cx e) (es,s0)
    (\H res ee t. ?tv. res = INL tv /\
      vv_post H ctx func ce cx e es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim ctx func ce cx (expr_type e) e es` by
    (fs[exprs_case_def, expr_vv_case_def] >> metis_tac[]) >>
  drule expr_body_pre_vv_gas_admissible >> strip_tac >>
  fs[expr_vv_sim_def]
QED

Theorem aggregate_tuple_marked_child_source[local]:
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
  strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre ce cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
  drule vyperImmutableMetadataFrameTheory.eval_expr_immutable_metadata_frame >>
  simp[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
  metis_tac[]
QED

Theorem aggregate_tuple_marked_footprint[local]:
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
  strip_tac >> drule_all aggregate_tuple_marked_child_source >> strip_tac >>
  rpt strip_tac >>
  Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target`
  >- (fs[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
      qpat_x_assum `!addr. IS_SOME _ <=> IS_SOME _`
        (qspec_then `cx.txn.target` mp_tac) >> simp[]) >>
  gvs[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME old` >>
  qpat_x_assum `!addr imms imms' src id. _`
    (drule_all_then (qspecl_then [`ce.ce_module`, `name`] mp_tac)) >>
  Cases_on `FLOOKUP (get_source_immutables ce.ce_module old) name` >>
  simp[] >>
  rename1 `FLOOKUP (get_source_immutables ce.ce_module old) name = SOME entry` >>
  PairCases_on `entry` >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem aggregate_tuple_store_no_gas[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `is_word_type ty` >>
  Cases_on `is_bytestring_type ty` >>
  Cases_on `type_memory_bytes ce ty` >>
  simp[contextTheory.compile_store_memory_def,
       contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       contextTheory.compile_copy_memory_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def,
       emitted_insts_def, venomInstTheory.mk_inst_def] >>
  strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem aggregate_tuple_add_marked[local]:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  vv_post H ctx func cenv cx e es sa sm s0 es' tv vv s /\
  eval_operand buf s = SOME w /\ fn_has_code sm sn func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post H ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s) /\
    (!H'. vv_post H' ctx func cenv cx e es sa sm s0 es' tv vv s ==>
          vv_post H' ctx func cenv cx e es sa sn s0 es' tv vv q)
Proof
  strip_tac >>
  drule_all exprSimAggregateChildrenTheory.buffer_emit_add_vv_post >>
  strip_tac >>
  `!H'. vv_post H' ctx func cenv cx e es sa sm s0 es' tv vv s ==>
        vv_post H' ctx func cenv cx e es sa sn s0 es' tv vv q` by
    (rpt strip_tac >>
     qpat_x_assum `vv_post H' _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pos (el 5)) mp_tac
          exprSimAggregateChildrenTheory.buffer_emit_add_vv_post) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> gvs[]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  drule exprLoweringPropsTheory.emit_op_same_blocks >>
  simp[exprLoweringPropsTheory.same_blocks_def] >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) exprSimHashBoundaryTheory.hash_run_path >>
  disch_then (qspecl_then [`sn`, `sm`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[venomInstTheory.mk_inst_def,
                      venomInstTheory.is_terminator_def]) >>
  simp[venomInstTheory.mk_inst_def] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[exprSimVVFrameTheory.vv_post_inst_idx,
       exprSimHashTheory.hash_eval_operand_inst_idx, venomStateTheory.lookup_var_def] >>
  gvs[venomStateTheory.lookup_var_def] >>
  qpat_x_assum `q with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
  simp[]
QED

(* An operand keeps its representation when only a bytestring bound changes. *)
Theorem expr_val_rel_compatible:
  !cx sty dty stv dtv v op s.
    (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v /\ expr_val_rel cx sty v op s ==>
    expr_val_rel cx dty v op s
Proof
  rpt strip_tac >- gvs[] >>
  `~is_word_type sty /\ ~is_word_type dty` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  gvs[expr_val_rel_def] >>
  irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
  metis_tac[]
QED

(* A buffer store at a compatible declared type. *)
Theorem buffer_store_memory_compatible_encoding[local]:
  !cenv cx src dst dty sty sa sb dtv stv v s d.
    compile_store_memory cenv src dst dty sty sa = ((),sb) /\
    (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    value_has_type dtv v /\ val_wf dtv v /\ expr_val_rel cx sty v src s /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_size dtv < dimword (:256) /\ eval_operand dst s = SOME d /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
    ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      val_in_memory dtv v (w2n d) q.vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
      (!a k. a + k <= w2n d \/ w2n d + type_memory_size dtv <= a ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH q.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `compile_store_memory cenv src dst dty dty sa = ((),sb)` by
    metis_tac[valueCopyBytesTheory.compile_store_memory_bytestring_src] >>
  `expr_val_rel cx dty v src s` by
    (irule expr_val_rel_compatible >> metis_tac[]) >>
  drule_all (SRULE [] exprSimBufferStoreTheory.buffer_store_memory_encoding) >>
  strip_tac >>
  drule_all (SRULE [] exprSimBufferStoreTheory.buffer_store_memory_capacity) >>
  strip_tac >> qexists_tac `q` >> gvs[] >> first_assum ACCEPT_TAC
QED

(* exprSimAggregateChildren's aggregate_store_rebased_slice_run, storing at a
   compatible declared type dty. *)
Theorem aggregate_store_compatible_rebased_slice_run[local]:
  post_value_type ce e = expr_type e /\
  compile_store_memory ce op (Var x) dty (expr_type e) su = ((),sb) /\
  (dty = expr_type e \/ is_bytestring_type dty /\ is_bytestring_type (expr_type e)) /\
  expr_post H ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  stmt_state_rel H ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size dtv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size dtv)) ==>
  ?q. (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!a k. a + k <= w2n w \/ w2n w + type_memory_size dtv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    run_inst_seq (emitted_insts su sb) s = OK q /\
    val_in_memory dtv v (w2n w) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size dtv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var x s = SOME w` by
    (drule_at (Pos hd) expr_post_rebased_lookup >> simp[]) >>
  `!n b k. local_region ce es'.scopes s n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size dtv <= b` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r n b k` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >>
            gvs[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >>
        gvs[expr_post_def, not_fresh_at_def]) >> metis_tac[]) >>
  `!z. op = Var z \/ Var x = Var z ==> not_fresh_at su z` by
    (rpt strip_tac >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `expr_val_rel cx (expr_type e) v op s /\
   stmt_state_rel H ctx func ce cx es' s` by gvs[expr_post_def] >>
  `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
  drule_all buffer_store_memory_compatible_encoding >> strip_tac >>
  `stmt_state_rel H ctx func ce cx es' q` by
    (irule exprSimBufferStoreTheory.buffer_store_state_frame >>
     qexistsl_tac [`w2n w`, `type_memory_size dtv`, `s`, `su`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `locals_kept ce es' es' r q` by
    (irule locals_kept_regions_tail >> qexists_tac `s` >>
     reverse conj_tac >- gvs[expr_post_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `q.vs_allocas = s.vs_allocas` by
    (qpat_assum `q with <|vs_vars := _; vs_memory := _|> = s`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  qexists_tac `q` >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _` irule >>
      decide_tac) >>
  simp[] >>
  gvs[expr_post_def, not_fresh_at_def] >>
  rpt conj_tac >> rpt strip_tac >>
  `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz r.vs_memory` by
    (qpat_x_assum `!aid off sz. _` irule >>
     conj_tac >- metis_tac[] >> qexists_tac `aid` >> simp[]) >>
  drule valueEncodingProofsTheory.mem_bytes_at_agree_window >> strip_tac >>
  `mem_bytes_at a k r.vs_memory = mem_bytes_at a k s.vs_memory` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[]
QED

(* Split a tuple-literal iteration at its declared member type. *)
Theorem compile_make_tuple_cons:
  compile_make_tuple cfn ce (e::args) (mty::tys) buf off sa = (out,sb) ==>
  ?vv sm dst sn op su st.
    cfn ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst mty (lowered_value_type ce e) su = ((),st) /\
    compile_make_tuple cfn ce args tys buf
      (off + type_memory_bytes ce mty) st = (out,sb)
Proof
  simp[Once compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The head is evaluated at its expression type and stored at its declared
   member type. All exclusion windows below use that destination type. *)
Theorem aggregate_tuple_store_compatible_marked[local]:
  post_value_type ce e = expr_type e /\
  compile_store_memory ce op (Var x) dty (expr_type e) su = ((),sb) /\
  (dty = expr_type e \/ is_bytestring_type dty /\ is_bytestring_type (expr_type e)) /\
  expr_post H ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256) /\
  stmt_state_rel H ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size dtv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size dtv)) /\
  fn_has_code su sb func /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!a k. a + k <= w2n w \/ w2n w + type_memory_size dtv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    gas_marked_path F ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory dtv v (w2n w) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size dtv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q /\
    (!H'. expr_post H' ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
            su r es' v op s /\ stmt_state_rel H' ctx func ce cx es' r ==>
          stmt_state_rel H' ctx func ce cx es' q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all aggregate_store_compatible_rebased_slice_run >> strip_tac >>
  `!H'. expr_post H' ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
          su r es' v op s /\ stmt_state_rel H' ctx func ce cx es' r ==>
        stmt_state_rel H' ctx func ce cx es' q` by
    (rpt strip_tac >>
     qpat_x_assum `expr_post H' _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then (Pos (el 4)) mp_tac aggregate_store_compatible_rebased_slice_run) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> gvs[]) >>
  `compile_store_memory ce op (Var x) dty dty su = ((),sb)` by
    metis_tac[valueCopyBytesTheory.compile_store_memory_bytestring_src] >>
  qpat_x_assum `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> _`
    (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = _`
    (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def]) >>
  drule exprSimBufferStoreTheory.buffer_store_memory_shape >>
  simp[same_blocks_def] >> strip_tac >>
  drule aggregate_store_memory_straight >> strip_tac >>
  drule aggregate_tuple_store_no_gas >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) exprSimHashBoundaryTheory.hash_run_path >>
  disch_then (qspecl_then [`sb`, `su`, `func`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (qpat_x_assum `Abbrev (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> _)`
        (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `Abbrev (!a k. _ ==> mem_bytes_at a k q.vs_memory = _)`
        (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      simp_tac (srw_ss()) [] >> rpt strip_tac >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory`
        irule >> decide_tac) >>
  qpat_x_assum `Abbrev (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> _)` kall_tac >>
  qpat_x_assum `Abbrev (!a k. _ ==> mem_bytes_at a k q.vs_memory = _)` kall_tac >>
  gvs[stmt_state_rel_inst_idx, venomStateTheory.lookup_var_def,
      arithmeticTheory.ADD_COMM] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem aggregate_tuple_exec_end_gas_obs[local]:
  gas_marked_exec memory (ctx,func) source start marks res
    (ee with gas_obs := gs) r =
  gas_marked_exec memory (ctx,func) source start marks res ee r
Proof
  PairCases_on `start` >> simp[gas_marked_exec_def]
QED

Theorem aggregate_tuple_gas_outcome_mono:
  gas_outcome memory tops (ctx,func) cx st0 source start Q R ==>
  (!H res ee r. Q H res ee r ==> Q' H res ee r) ==>
  (!H res ee r. R H res ee r ==> R' H res ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0 source start Q' R'
Proof
  PairCases_on `start` >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

(* The child's value, then the rest of the source under it. *)
Theorem aggregate_tuple_bind_outcome:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> eval_result evaluation_result) (es,s0)
    (\H res ee t. ?v. res = INL v /\ P H v ee t)
    (\H res ee r. ?exc. res = INR exc /\ R H (INR exc) ee r) /\
  (!v. storage_trace_frame (k v)) /\
  (!marks v ee t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) ee (OK t) /\
    ee.gas_obs = [] /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee t) ==>
    gas_outcome memory tops (ctx,func) cx st0
      (k v : evaluation_state -> value list evaluation_result) (ee,t) Q R) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_counted_prefix >>
           qexistsl_tac [`ctx`, `es_end`, `func`, `memory`, `r`, `res`] >>
           simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "normal"
      >> suspend "exit") >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gas_exempt_cert_error_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Resume aggregate_tuple_bind_outcome[normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?v. res = INL v` by
    (first_assum (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!marks v ee t. _`
    (qspecl_then [`marks`, `v`, `es_end with gas_obs := []`, `t`] mp_tac) >>
  (impl_tac >- simp[aggregate_tuple_exec_end_gas_obs]) >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ (k v) _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj1_tac >> irule gas_bad_storage_at_bind_right >> simp[] >>
      metis_tac[])
  >- (qpat_x_assum `gas_summary_at _ _ _ (k _) _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
      disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
      (conj_tac
       >- (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >>
           gvs[])) >>
      fs[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks ++ marks'` >>
  disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gas_exempt_cert_bind_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Resume aggregate_tuple_bind_outcome[exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o BETA_RULE) >>
  first_assum (drule_then strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  gvs[] >> rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC
QED

Finalise aggregate_tuple_bind_outcome

(* A source-only step whose target code reads no gas, then the rest. *)
Theorem aggregate_tuple_value_bind:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0)
    left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func) cx st0
    (k v : evaluation_state -> value list evaluation_result)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `right` strip_assume_tac))
  >- (qexists_tac `left ++ right` >> disj1_tac >>
      irule gas_bad_storage_at_bind_right >> metis_tac[])
  >- (qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_normal])
  >- (qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
      metis_tac[gas_marked_exec_bind_normal]) >>
  qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule_at Any gas_exempt_cert_bind_value >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem aggregate_tuple_ignore_values:
  ignore_bind (bind (eval_exprs cx args) (\vs. return (v::vs))) (return ()) =
  ignore_bind (eval_exprs cx args) (return ())
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >> gen_tac >>
  Cases_on `eval_exprs cx args x` >> Cases_on `q` >> simp[]
QED

(* The rest of the tuple, with the child's value in front. *)
Theorem aggregate_tuple_values_outcome:
  gas_outcome memory tops (ctx,func) cx st0 (eval_exprs cx args) (es,s) Q1 R1 /\
  (!H res ee r. Q1 H res ee r ==>
     Q H (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) /\
  (!H res ee r. R1 H res ee r ==>
     R H (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es,s) Q R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def,
              aggregate_tuple_ignore_values] >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_return])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR exc => INR exc`,
                    `es_end`, `OK t`] >>
      Cases_on `res` >> fs[gas_marked_exec_def, bind_def, return_def] >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL vs => INL (v::vs) | INR exc => INR exc`,
                    `es_end`, `r`] >>
      Cases_on `res` >> fs[gas_marked_exec_def, bind_def, return_def] >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem aggregate_tuple_eval_cons:
  eval_exprs cx (e::args) =
  bind (eval_expr cx e) (\tv. bind (read_result cx tv)
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >> REFL_TAC
QED

(* vv_post_local_region_backward, from the scope domains rather than an
   unmarked evaluation. *)
Theorem aggregate_tuple_local_region_backward[local]:
  !es es1 s0 s1 sa sb ctx func ce cx e tv vv name b sz.
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel H ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post H ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  rpt strip_tac >> irule local_region_frame >>
  conj_tac
  >- (qexists_tac `func` >>
      gvs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`sa`, `es1.scopes`, `s1`] >>
  gvs[vv_post_def]
QED

(* aggregate_make_tuple_sim at the tuple's declared member types tys
   (tuple_literal_types; a struct's field types, an array's element type),
   each of which its element fits (arg_type_fits).  A flat member is its
   element's own type, or a String or Bytes of another bound, which the
   store copies as bytes (compile_store_memory_compatible_run). *)
Theorem aggregate_make_tuple_flat_sim:
  !args tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx nocalls st0.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  LIST_REL (\t e. t = expr_type e \/
    is_bytestring_type t /\ is_bytestring_type (expr_type e)) tys args /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `tys` >> gvs[] >>
      gvs[compile_make_tuple_def, comp_return_def] >>
      irule aggregate_tuple_nil_outcome >>
      simp[val_in_memory_def, exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tys` >- gvs[] >>
  gns[] >>
  rename1 `compile_make_tuple compile_expr ce (h::args) (mty::tys') _ _ _ = _` >>
  `out = Var x` by metis_tac[exprOperandVarTheory.compiler_make_tuple_result] >>
  gnvs[] >>
  `expr_body_pre ce cx env h es /\ (nocalls ==> int_calls_expr h = [])` by
    metis_tac[listTheory.MEM] >>
  `well_typed_expr env h` by metis_tac[expr_body_pre_def] >>
  `post_value_type ce h = expr_type h` by
    (`lowered_value_type ce h = expr_type h \/ is_bytestring_type (expr_type h)` by
       (irule aggregate_elem_lowered_type >> metis_tac[listTheory.MEM]) >>
     metis_tac[post_value_type_lowered, post_value_type_bytestring]) >>
  drule compile_make_tuple_cons >> strip_tac >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `compile_store_memory ce op dst mty _ su = ((),ss)` >>
  `compile_store_memory ce op dst mty (expr_type h) su = ((),ss)` by
    (Cases_on `mty = expr_type h`
     >- (gvs[] >> metis_tac[aggregate_elem_lowered_type,
            aggregate_store_lowered_elem, listTheory.MEM]) >>
     metis_tac[valueCopyBytesTheory.compile_store_memory_bytestring_src]) >>
  qpat_x_assum `compile_store_memory ce op dst mty (lowered_value_type ce h) su = _` kall_tac >>
  `ci_mono sa sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su ss` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono ss sb` by
    metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all aggregate_tuple_child_outcome >> strip_tac >>
  rewrite_tac[aggregate_tuple_eval_cons] >>
  match_mp_tac (Q.SPEC `\H tv ee t.
    vv_post H ctx func ce cx h es sa sm s0 ee tv vv t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts`
    (Q.GEN `P` aggregate_tuple_bind_outcome)) >>
  rpt conj_tac
  >- (qpat_x_assum `gas_outcome _ _ _ _ _ (eval_expr _ _) _ _ _`
        (irule o MATCH_MP aggregate_tuple_gas_outcome_mono) >>
      simp[] >> rpt strip_tac >>
      Cases_on `res` >> gvs[expr_exit_def])
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `gas_marked_exec F _ (eval_expr cx h) _ m1 (INL tv) es1 (OK t1)` >>
  suspend "child_success"
QED

(* Any horizon valid at the child's end works for the per-step facts: the
   steps after it are runs, so the state each one reaches is the same at
   every horizon, and only stmt_state_rel and swf for the tail are needed
   at all of them. *)
Resume aggregate_make_tuple_flat_sim[child_success]:
  `es1 with gas_obs := [] = es1` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  reverse (Cases_on `storage_trace_domain cx st0 es1.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> asm_rewrite_tac[] >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  `?H. valid_horizon cx st0 H es1.storage_trace` by
    (qexists_tac `storage_trace_horizon es1.storage_trace` >>
     fs[storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `~t1.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_expr cx h (es with gas_obs := gas_explicit m1 s0.vs_gas_readings) =
     (INL tv,es1)` by
    (qpat_x_assum `gas_marked_exec F _ (eval_expr cx h) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `?obs. es1.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `eval_expr cx h _ = _`
       (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
     simp[evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es1.storage_trace = _` kall_tac >>
  `stmt_state_rel H ctx func ce cx es s0` by metis_tac[] >>
  `expr_body_pre ce cx env h
     (es with gas_obs := gas_explicit m1 s0.vs_gas_readings)` by simp[] >>
  drule_all aggregate_tuple_marked_child_source >>
  asm_rewrite_tac[] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type h) = SOME stv` >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)
    aggregate_tuple_marked_footprint >>
  disch_then (qpat_assum `expr_body_pre ce cx env h es` o mp_then Any mp_tac) >>
  disch_then (qpat_assum `ce.ce_is_ctor ==> _` o mp_then Any mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `?v. read_result cx tv es1 = (INL v,es1)` by metis_tac[vv_post_materialises] >>
  `value_has_type stv v /\ val_wf stv v` by
    metis_tac[aggregate_materialised_child_typed, aggregate_materialised_child_wf] >>
  qpat_x_assum `?dtv. evaluate_type (get_tenv cx) mty = SOME dtv /\ _`
    (qx_choose_then `dtv` strip_assume_tac) >>
  qpat_x_assum `_ :: _ = tvs` (SUBST_ALL_TAC o SYM) >>
  `value_has_type dtv v` by
    metis_tac[cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type] >>
  `val_wf dtv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `type_memory_bytes ce mty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  suspend "child_steps"
QED

Resume aggregate_make_tuple_flat_sim[child_steps]:
  `cs_extends sa sn /\ cs_extends sn su /\ cs_extends su sb /\
   cs_extends sm sn /\ cs_extends su ss /\ cs_extends ss sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `cs_extends sn sb` by (irule cs_extends_trans >> qexists_tac `su` >> simp[]) >>
  `fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sn su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code su ss func /\ fn_has_code ss sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su /\
   local_ptrs_reserved ce ss` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved,
              ci_mono_def, cs_extends_trans] >>
  `lookup_var x t1 = SOME (n2w b) /\
   FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `eval_operand (Var x) t1 = SOME (n2w b)` by
    simp[venomStateTheory.eval_operand_def] >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  drule_at (Pat `emit_op _ _ _ = _`) aggregate_tuple_add_marked >>
  disch_then (drule_at (Pat `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `eval_operand (Var d) r` >>
  `lookup_var d r = SOME (n2w (b+off))` by
    gvs[venomStateTheory.eval_operand_def, wordsTheory.word_add_n2w] >>
  `not_fresh_at sn d` by
    simp[Abbr `d`, not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    metis_tac[aggregate_child_unwrap_var, ci_mono_def] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> fs[ci_mono_def] >>
     drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `stmt_state_rel H ctx func ce cx es1 r` by fs[vv_post_def] >>
  `off + type_memory_size dtv <= asz /\ b+off+type_memory_size dtv < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `w2n ((n2w (b+off)) : bytes32) = b+off` by
    (`b + off < dimword (:256)` by decide_tac >>
     metis_tac[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `!name lo sz. local_region ce es1.scopes r name lo sz ==>
      lo+sz <= b+off \/ b+off+type_memory_size dtv <= lo` by
    (`not_local_ptr ce es1.scopes x` by simp[] >>
     `FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz)` by simp[] >>
     rpt strip_tac >> drule_all aggregate_alloca_slice_excludes_local >> simp[]) >>
  suspend "unwrap_store"
QED

Resume aggregate_make_tuple_flat_sim[unwrap_store]:
  `type_memory_bytes ce (expr_type h) = type_memory_size stv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `~is_word_type (expr_type h) ==> type_memory_size stv < 2 ** 64` by
    (strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  `vv_post H ctx func ce cx h es1 (sa with cs_next_var := sn.cs_next_var)
     sn r es1 tv vv r` by
    (irule vv_post_rebase >> goal_assum (drule_at Any)) >>
  `local_ptrs_reserved ce (sa with cs_next_var := sn.cs_next_var)` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sn` >> simp[]) >>
  `!H'. valid_horizon cx st0 H' es1.storage_trace ==>
        vv_post H' ctx func ce cx h es1 (sa with cs_next_var := sn.cs_next_var)
          sn r es1 tv vv r` by
    (rpt strip_tac >> irule vv_post_rebase >> metis_tac[]) >>
  qspecl_then [`ctx`, `func`, `ce`, `cx`, `h`, `es1`,
               `sa with cs_next_var := sn.cs_next_var`, `sn`, `su`, `r`,
               `es1`, `tv`, `vv`, `op`, `r`, `st0`, `es1.storage_trace`, `H`]
    mp_tac unwrap_value_marked_read_horizons >>
  (impl_tac >- (asm_rewrite_tac[] >> fs[ci_mono_def] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`v'`, `u`] strip_assume_tac) >>
  `v' = v` by
    (qpat_x_assum `gas_marked_exec F _ (read_result _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[gas_explicit_def]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `expr_post H ctx func ce cx h es1 (sa with cs_next_var := sn.cs_next_var)
     su r es1 v op u` by metis_tac[] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`) aggregate_tuple_store_compatible_marked >>
  disch_then (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` o mp_then Any mp_tac) >>
  disch_then (qpat_assum `lookup_var d r = _` o mp_then Any mp_tac) >>
  disch_then (qpat_assum `evaluate_type _ mty = SOME dtv` o mp_then Any mp_tac) >>
  disch_then (qspec_then `stv` mp_tac) >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  (impl_tac >- (asm_rewrite_tac[] >> fs[ci_mono_def] >> rpt conj_tac >>
     rpt strip_tac >> fs[]
     >>~- ([`regions_disjoint _ _ _ _`],
       (qpat_assum `!n1 i1 v1 o1. _ /\ FLOOKUP (case ALOOKUP es1.immutables _ of NONE => _ | SOME imms => _) _ = _ ==> _`
          (qspecl_then [`name`, `itv`, `iv`, `off'`]
             (mp_tac o REWRITE_RULE [regions_disjoint_def, type_memory_size_def])) >>
        asm_rewrite_tac[] >>
        simp_tac std_ss [regions_disjoint_def, type_memory_size_def] >>
        decide_tac)) >>
     metis_tac[])) >>
  asm_rewrite_tac[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func u 0 (OK t2)` >>
  suspend "rest"
QED

Resume aggregate_make_tuple_flat_sim[rest]:
  `gas_marked_exec F (ctx,func) (read_result cx tv) (es1,t1) [] (INL v) es1 (OK t2)` by
    (qpat_x_assum `gas_marked_exec F _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     `gas_marked_path F ctx func r (0 + 0) (OK t2)` by
       metis_tac[gas_marked_path_then] >>
     `gas_marked_path F ctx func t1 (0 + (0 + 0)) (OK t2)` by
       metis_tac[gas_marked_path_then] >> fs[]) >>
  irule aggregate_tuple_value_bind >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  `not_fresh_at sn x /\ not_fresh_at ss x` by
    (fs[not_fresh_at_def, ci_mono_def] >> decide_tac) >>
  `lookup_var x r = SOME (n2w b)` by (fs[vv_post_def] >> metis_tac[]) >>
  `lookup_var x t2 = SOME (n2w b) /\
   FLOOKUP t2.vs_allocas inst.inst_id = SOME (b,asz)` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `exprs_case nocalls ctx func ce cx args` by
    (qpat_x_assum `exprs_case _ _ _ _ _ (h::args)` mp_tac >>
     simp[Once exprs_case_def] >> metis_tac[]) >>
  `!H'. valid_horizon cx st0 H' es1.storage_trace ==>
        stmt_state_rel H' ctx func ce cx es1 t2 /\
        storage_well_formed_on cx es1 (FST H')` by
    (gen_tac >> strip_tac >>
     `vv_post H' ctx func ce cx h es sa sm s0 es1 tv vv t1` by metis_tac[] >>
     `vv_post H' ctx func ce cx h es sa sn s0 es1 tv vv r` by metis_tac[] >>
     `expr_post H' ctx func ce cx h es1 (sa with cs_next_var := sn.cs_next_var)
        su r es1 v op u` by metis_tac[] >>
     `stmt_state_rel H' ctx func ce cx es1 r /\
      storage_well_formed_on cx es1 (FST H')` by
       (qpat_x_assum `vv_post H' _ _ _ _ _ _ _ sn _ _ _ _ _` mp_tac >>
        simp_tac std_ss [vv_post_def] >> strip_tac >> asm_rewrite_tac[]) >>
     metis_tac[]) >>
  qpat_x_assum `!tys ce':compile_env. _`
    (qspecl_then [`tys'`, `ce`, `cx`, `env`] mp_tac) >>
  disch_then (qpat_assum `compile_make_tuple _ ce args _ _ _ ss = _` o mp_then Any mp_tac) >>
  disch_then (qpat_assum `exprs_case nocalls ctx func ce cx args` o mp_then Any mp_tac) >>
  disch_then (qpat_assum `FLOOKUP t2.vs_allocas inst.inst_id = _` o mp_then Any mp_tac) >>
  disch_then (qspecl_then [`es1`, `t'`, `st0`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    simp[type_memory_size_def] >>
    gnvs[ci_mono_def, type_memory_size_def] >> conj_tac
    >- metis_tac[] >>
    rpt strip_tac >>
    qpat_assum `!n1 i1 v1 o1. ce.ce_is_ctor /\ _ ==> _`
      (qspecl_then [`name`, `itv`, `iv`, `io`]
        (mp_tac o REWRITE_RULE [regions_disjoint_def])) >>
    asm_rewrite_tac[] >> simp_tac std_ss [regions_disjoint_def] >> decide_tac)) >>
  strip_tac >>
  BETA_TAC >> irule aggregate_tuple_values_outcome >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[]) >>
  qx_genl_tac [`H'`, `rr`, `es'`, `s`] >> BETA_TAC >> strip_tac >>
  suspend "tuple_join"
QED

Resume aggregate_make_tuple_flat_sim[tuple_join]:
  gnvs[] >>
  qpat_x_assum `q.vs_memory = t1.vs_memory` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  qpat_x_assum `q.vs_allocas = t1.vs_allocas` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  rpt conj_tac
  >- suspend "head_encoding"
  >- suspend "vars_join"
  >- suspend "allocas_join"
  >- suspend "slice_join"
  >- suspend "exterior_join"
  >- suspend "locals_join"
  >> suspend "pure_join"
QED

Resume aggregate_make_tuple_flat_sim[head_encoding]:
  pure_once_rewrite_tac[val_in_memory_def] >>
  simp_tac std_ss [listTheory.list_case_def, LET_THM] >> conj_tac
  >- (irule (cj 1 val_in_memory_mem_agree_proof) >> simp[] >>
      qexists_tac `t2.vs_memory` >> simp[] >>
      qpat_x_assum `!p n. b <= p /\ _ ==> _`
        (qspecl_then [`b + off`, `type_memory_size dtv`] mp_tac) >>
      fs[type_memory_size_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `tuple_in_memory vs t' _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >>
  simp_tac bool_ss []
QED

Resume aggregate_make_tuple_flat_sim[vars_join]:
  rpt strip_tac >>
  `not_fresh_at sn z /\ not_fresh_at ss z` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q` mp_tac >>
  simp_tac std_ss [vv_post_def] >> strip_tac >> metis_tac[]
QED

Resume aggregate_make_tuple_flat_sim[allocas_join]:
  rpt strip_tac >>
  qpat_x_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q` mp_tac >>
  simp_tac std_ss [vv_post_def] >> strip_tac >> metis_tac[]
QED

Resume aggregate_make_tuple_flat_sim[slice_join]:
  rpt strip_tac >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      b + asz <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es.scopes x` by simp[] >>
     `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0` by
       (qpat_assum `stmt_state_rel H ctx func ce cx es s0` mp_tac >>
        simp_tac std_ss [stmt_state_rel_def, state_rel_def] >>
        strip_tac >> asm_rewrite_tac[]) >>
     rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def]) >>
  `mem_bytes_at b asz q.vs_memory = mem_bytes_at b asz s0.vs_memory` by
    (qpat_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q`
       (mp_then Any irule vv_post_old_buffer) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!name lo sz. local_region ce es1.scopes q name lo sz ==>
      asz + b <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es1.scopes x` by simp[] >>
     `alloca_inv q /\ local_ptrs_rel func ce es1.scopes q` by
       (qpat_assum `stmt_state_rel H ctx func ce cx es1 q` mp_tac >>
        simp_tac std_ss [stmt_state_rel_def, state_rel_def] >>
        strip_tac >> asm_rewrite_tac[]) >>
     rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  `mem_bytes_at p n s.vs_memory = mem_bytes_at p n t2.vs_memory` by
    (qpat_assum `!p n. b <= p /\ _ ==> _` irule >>
     fs[type_memory_size_def] >> decide_tac) >>
  `mem_bytes_at p n t2.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_assum `!aid off sz a k. _` irule >>
     reverse conj_tac >- (fs[type_memory_size_def] >> decide_tac) >>
     qexistsl_tac [`inst.inst_id`, `b`, `asz`] >> asm_rewrite_tac[] >>
     rpt conj_tac >> TRY decide_tac >> rpt strip_tac >> res_tac >> decide_tac) >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_assum `mem_bytes_at b asz _ = _`
       (mp_then Any mp_tac mem_bytes_at_agree_window) >>
     strip_tac >> sym_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Resume aggregate_make_tuple_flat_sim[exterior_join]:
  rpt strip_tac >>
  `!name lo sz. local_region ce es1.scopes q name lo sz ==>
      p + n <= lo \/ lo + sz <= p` by
    (rpt strip_tac >>
     `local_region ce es.scopes s0 name lo sz` by
       (drule_all aggregate_tuple_local_region_backward >> simp[]) >>
     qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _`
       (qspecl_then [`name`, `lo`, `sz`] mp_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `!name lo sz. local_region ce es1.scopes t2 name lo sz ==>
      p + n <= lo \/ lo + sz <= p` by
    (rpt strip_tac >>
     `local_region ce es1.scopes q name lo sz` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sn`, `es1.scopes`, `t2`] >> asm_rewrite_tac[]) >>
     qpat_x_assum `!name lo sz. local_region ce es1.scopes q name lo sz ==> p + n <= lo \/ _`
       (qspecl_then [`name`, `lo`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q`
       (mp_then Any irule vv_post_old_buffer) >> reverse conj_tac
     >- (qexists_tac `aid` >> asm_rewrite_tac[]) >>
     rpt strip_tac >>
     qpat_x_assum `!name lo sz. local_region ce es.scopes s0 name lo sz ==> _`
       (qspecl_then [`n'`, `b'`, `k`] mp_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `FLOOKUP q.vs_allocas aid = SOME (p,n)` by
    (qpat_x_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q` mp_tac >>
     simp_tac std_ss [vv_post_def] >> strip_tac >>
     qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` irule >>
     asm_rewrite_tac[]) >>
  `FLOOKUP t2.vs_allocas aid = SOME (p,n)` by
    (qpat_x_assum `!aid b. FLOOKUP q.vs_allocas aid = SOME b ==> _` irule >>
     asm_rewrite_tac[]) >>
  `mem_bytes_at p n t2.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!aid off sz a k. _` irule >>
     reverse conj_tac >- decide_tac >> qexistsl_tac [`aid`, `p`, `n`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name lo sz. local_region ce es1.scopes q name lo sz ==> p + n <= lo \/ _`
           (qspecl_then [`n'`, `b'`, `len`] mp_tac) >>
         asm_rewrite_tac[] >> decide_tac) >> decide_tac) >>
  `mem_bytes_at p n s.vs_memory = mem_bytes_at p n t2.vs_memory` by
    (qpat_x_assum `!aid p n. _` irule >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name lo sz. local_region ce es1.scopes t2 name lo sz ==> _`
           (qspecl_then [`name`, `lo`, `sz`] mp_tac) >>
         asm_rewrite_tac[] >> decide_tac) >>
     asm_rewrite_tac[] >> qexists_tac `aid` >> asm_rewrite_tac[] >>
     fs[ci_mono_def] >> decide_tac) >> asm_rewrite_tac[]
QED

Resume aggregate_make_tuple_flat_sim[locals_join]:
  `locals_kept ce es1 es' q s` by
    (irule locals_kept_trans >> qexistsl_tac [`es1`, `sn`, `t2`] >>
     asm_rewrite_tac[]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `q`] >>
  qpat_x_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q` mp_tac >>
  simp_tac std_ss [vv_post_def] >> strip_tac >> simp[]
QED

Resume aggregate_make_tuple_flat_sim[pure_join]:
  strip_tac >>
  `~expr_has_effect h /\ ~EXISTS expr_has_effect args` by
    (rpt (qpat_x_assum `~EXISTS _ _` mp_tac) >>
     rpt (qpat_x_assum `EVERY _ args` mp_tac) >>
     rpt (qpat_x_assum `~expr_has_effect _` mp_tac) >>
     simp_tac (srw_ss()) []) >>
  `pure_frame ce func es sa s0 q /\
   (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
      lookup_var z q = SOME w)` by
    (qpat_x_assum `vv_post H ctx func ce cx h es sa sn s0 es1 tv vv q` mp_tac >>
     rewrite_tac[vv_post_def] >> strip_tac >> conj_tac
     >- (qpat_x_assum `~expr_has_effect h ==> _` irule >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post H _ _ _ _ h _ _ _ _ _ _ _ u`
    (mp_then (Pos hd) mp_tac exprSimWordArgsTheory.expr_post_pure_frame) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!aid a. FLOOKUP q.vs_allocas aid = SOME a ==>
     FLOOKUP u.vs_allocas aid = SOME a` by
    (qpat_x_assum `expr_post H _ _ _ _ h _ _ _ _ _ _ _ u` mp_tac >>
     rewrite_tac[expr_post_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `pure_frame ce func es sa s0 u` by
    (match_mp_tac pure_frame_trans >>
     qexistsl_tac [`es1`, `sa with cs_next_var := sn.cs_next_var`, `q`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      b + asz <= lo \/ lo + sz <= b` by
    (`not_local_ptr ce es.scopes x` by simp[] >>
     `alloca_inv s0 /\ local_ptrs_rel func ce es.scopes s0` by
       (qpat_assum `stmt_state_rel H ctx func ce cx es s0` mp_tac >>
        simp_tac std_ss [stmt_state_rel_def, state_rel_def] >>
        strip_tac >> asm_rewrite_tac[]) >>
     rpt strip_tac >> drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def]) >>
  `!a k. a + k <= b + off \/ b + off + type_memory_size dtv <= a ==>
     mem_bytes_at a k t2.vs_memory = mem_bytes_at a k u.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!a k. _ ==> mem_bytes_at a k t2.vs_memory = mem_bytes_at a k u.vs_memory`
       irule >> simp[]) >>
  drule_at (Pat `pure_frame _ _ _ _ _ _`) aggregate_pure_frame_store >>
  disch_then (qpat_assum `!a k. _ ==> mem_bytes_at a k t2.vs_memory = mem_bytes_at a k u.vs_memory` o mp_then Any mp_tac) >>
  disch_then (qspecl_then [`b`, `asz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp[] >> NO_TAC) >> decide_tac)) >>
  strip_tac >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
     lookup_var z t2 = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sn z` by
       (irule freshWritesTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> fs[ci_mono_def] >> decide_tac) >>
     `lookup_var z q = SOME w` by
       (qpat_x_assum `!z w. not_fresh_at sa z /\ _ ==> lookup_var z q = _`
          irule >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `!z a. not_fresh_at sn z /\ _ ==> lookup_var z t2 = _`
       irule >> conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_id <= ss.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `EVERY _ args ==> _` mp_tac >>
  (impl_tac >- (qpat_x_assum `~EXISTS expr_has_effect args` mp_tac >>
                simp_tac (srw_ss()) [])) >> strip_tac >>
  match_mp_tac (SRULE [arithmeticTheory.ADD_COMM] aggregate_pure_frame_trans) >>
  qexistsl_tac [`es1`, `ss`, `t2`] >>
  rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED

Finalise aggregate_make_tuple_flat_sim

(* The equal-type case of aggregate_make_tuple_flat_sim. *)
Theorem aggregate_make_tuple_sim:
  !args ce cx env off sa out sb es tvs func inst x b asz s0 ctx nocalls st0.
  compile_make_tuple compile_expr ce args (MAP expr_type args) (Var x) off sa =
    (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`tys` |-> `MAP expr_type args`] (SPEC_ALL aggregate_make_tuple_flat_sim)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[listTheory.LIST_REL_MAP1] >> irule listTheory.EVERY2_refl >> simp[]) >>
  simp[]
QED

(* HELD: a member whose declared type is an aggregate its element only
   fits (a DynArray[String[5],2] element at DynArray[String[40],2], say)
   is stored by compile_store_memory_typed (compile_store_memory_typed_run),
   which emits INVALID unless acyclic_struct_metadata holds, hence that
   premise.  Unreachable for a supported program: supported_literal_elements and
   supported_struct_elements limit every member to supported_copy_types,
   all of which are flat. *)
Theorem aggregate_make_tuple_nested_sim:
  !args tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx nocalls st0.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  (?t e. MEM (t,e) (ZIP (tys,args)) /\ t <> expr_type e /\
     ~is_bytestring_type t) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  expr_sim_inv ce cx env es /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED

(* A member that is not flat is a nested-narrow one. *)
Theorem aggregate_member_not_flat:
  !tys args.
    LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
    ~LIST_REL (\t e. t = expr_type e \/
       is_bytestring_type t /\ is_bytestring_type (expr_type e)) tys args ==>
    ?t e. MEM (t,e) (ZIP (tys,args)) /\ t <> expr_type e /\
      ~is_bytestring_type t
Proof
  Induct >> rpt gen_tac >> Cases_on `args` >> simp[] >>
  rename1 `LIST_REL _ tys rest` >> rename1 `arg_type_fits (expr_type e0) t0` >>
  rpt strip_tac >>
  (Cases_on `LIST_REL (\t e. t = expr_type e \/
     is_bytestring_type t /\ is_bytestring_type (expr_type e)) tys rest`
   >- (gvs[] >> qexistsl [`t0`, `e0`] >> gvs[] >>
       metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]) >>
   first_x_assum (qspec_then `rest` mp_tac) >> impl_tac >- fs[] >>
   strip_tac >> metis_tac[])
QED

Theorem aggregate_make_tuple_fits_sim:
  !args tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx nocalls st0.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  expr_sim_inv ce cx env es /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `LIST_REL (\t e. t = expr_type e \/
    is_bytestring_type t /\ is_bytestring_type (expr_type e)) tys args`
  >- (mp_tac (SPEC_ALL aggregate_make_tuple_flat_sim) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[]) >>
  mp_tac (SPEC_ALL aggregate_make_tuple_nested_sim) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      irule aggregate_member_not_flat >> simp[]) >>
  simp[]
QED


(* Post transport keeps the counted execution and exemption witnesses intact. *)
Theorem struct_gas_outcome_post:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s0) Q R /\
  (!H res es' r. Q H res es' r ==> Q' H res es' r) ==>
  gas_outcome memory tops (ctx,func) cx st0 source (es,s0) Q' R
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED

Theorem struct_tuple_memory_post:
  !names tvs vs ptr mem.
  LENGTH names = LENGTH tvs /\ tuple_in_memory vs tvs ptr mem ==>
  fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) ptr mem
Proof
  Induct_on `names` >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[listTheory.ZIP_def, valueEncodingDefsTheory.val_in_memory_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem aggregate_struct_fields_sim:
  !fields tys ce cx env ty off sa out sb es tvs func inst x b asz s0 ctx nocalls st0.
  LIST_REL (\t (name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (t,type_memory_bytes ce t)) tys fields /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys (MAP SND fields) /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  expr_sim_inv ce cx env es /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx (MAP SND fields) /\
  (~nocalls ==> !e. MEM e (MAP SND fields) ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx (MAP SND fields)) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      fields_in_memory (ZIP (MAP FST fields,vs))
        (ZIP (MAP FST fields,tvs)) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect (MAP SND fields) ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  drule exprSimAggregateLayoutTheory.compile_struct_lit_as_tuple >>
  disch_then (qspecl_then [`compile_expr`, `Var x`, `off`] assume_tac) >>
  gvs[] >>
  drule aggregate_make_tuple_fits_sim >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `exprs_case _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspecl_then [`es`, `st0`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac >- metis_tac[] >>
    first_assum ACCEPT_TAC)) >>
  strip_tac >> simp[] >>
  imp_res_tac listTheory.LIST_REL_LENGTH >>
  drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[] >> strip_tac >>
  irule struct_gas_outcome_post >>
  goal_assum (drule_at Any) >>
  BETA_TAC >> rpt strip_tac >> qexists_tac `vs` >> gvs[] >> simp[] >>
  conj_tac >- (irule struct_tuple_memory_post >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem compile_make_array_elems_as_tuple:
  !args idx.
  compile_make_array_elems cfn ce args elem_ty (type_memory_bytes ce elem_ty)
    header buf idx =
  compile_make_tuple cfn ce args (REPLICATE (LENGTH args) elem_ty) buf
    ((if header then 32 else 0) + idx * type_memory_bytes ce elem_ty)
Proof
  Induct >> simp[compile_make_array_elems_def, compile_make_tuple_def] >>
  rpt strip_tac >> Cases_on `header` >>
  pure_rewrite_tac[COND_CLAUSES, arithmeticTheory.ADD_CLAUSES,
    arithmeticTheory.RIGHT_ADD_DISTRIB, arithmeticTheory.MULT_CLAUSES,
    GSYM arithmeticTheory.ADD_ASSOC] >> REFL_TAC
QED


Theorem array_header_store_state_rel:
  stmt_state_rel H ctx func ce cx es s /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo) /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel H ctx func ce cx es (mstore b w s)
Proof
  strip_tac >>
  `local_ptrs_rel func ce es.scopes (mstore b w s)` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mstore >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es (mstore b w s)` by
    (irule loweringSliceTheory.immutables_rel_mem_agree >>
     qexists_tac `s` >> conj_tac
     >- (simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
               arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
     conj_tac >- simp[mstore_def] >>
     reverse conj_tac >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> first_x_assum drule_all >>
     simp[regions_disjoint_def] >> strip_tac >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[]) >>
  irule stmt_state_rel_allocas_frame >> conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      gvs[stmt_state_rel_def, mstore_def, lookup_var_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      gvs[stmt_state_rel_def, mstore_def, local_region_def, lookup_var_def] >>
      metis_tac[]) >>
  conj_tac
  >- (irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >>
      gvs[stmt_state_rel_def, mstore_def]) >>
  qexistsl_tac [`es`, `s`] >> simp[mstore_def]
QED

Theorem array_header_store_boundary:
  stmt_state_rel H ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\ 32 <= asz /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel H ctx func ce cx es (mstore b w s) /\
  locals_kept ce es es s (mstore b w s) /\
  mem_word_at b (mstore b w s).vs_memory = w /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n (mstore b w s).vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >>
  `!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `32`]
       aggregate_alloca_slice_excludes_local)) >> simp[]) >>
  conj_tac >- (irule array_header_store_state_rel >> metis_tac[]) >>
  conj_tac
  >- (irule locals_kept_regions >> rpt strip_tac >>
      irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
      first_x_assum drule >> strip_tac >> decide_tac) >>
  conj_tac >- simp[valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  decide_tac
QED


Theorem aggregate_make_array_elems_sim:
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx nocalls st0.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (LENGTH args * type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`args`, `idx`] (Q.INST [`cfn` |-> `compile_expr`,
    `buf` |-> `Var x`] compile_make_array_elems_as_tuple)) >>
  strip_tac >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (REPLICATE (LENGTH args) elem_ty) =
     SOME (REPLICATE (LENGTH args) tv)` by
    (Q.SPEC_TAC (`LENGTH args`, `n`) >> Induct >> gvs[rich_listTheory.REPLICATE]) >>
  `LIST_REL (\t e. arg_type_fits (expr_type e) t)
     (REPLICATE (LENGTH args) elem_ty) args` by
    gvs[listTheory.LIST_REL_EL_EQN, rich_listTheory.EL_REPLICATE, listTheory.EVERY_EL] >>
  `compile_make_tuple compile_expr ce args (REPLICATE (LENGTH args) elem_ty)
     (Var x) off sa = (out,sb)` by
    (gvs[] >> metis_tac[]) >>
  `off + type_memory_size_list (REPLICATE (LENGTH args) tv) <= asz` by
    gvs[type_memory_size_list_replicate] >>
  `ce.ce_is_ctor ==> !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list (REPLICATE (LENGTH args) tv))` by
    (gvs[type_memory_size_list_replicate] >> metis_tac[]) >>
  drule_all aggregate_make_tuple_fits_sim >>
  pure_rewrite_tac [type_memory_size_list_replicate] >>
  disch_then strip_assume_tac >> conj_tac >- asm_rewrite_tac[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac [gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> first_assum ACCEPT_TAC)
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      gvs[] >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac [gas_marked_exec_def] >> strip_tac >>
      first_x_assum (qspec_then `[]` mp_tac) >>
      strip_tac >> drule eval_exprs_length >> strip_tac >>
      metis_tac[tuple_in_memory_replicate_elems]) >>
  metis_tac[]
QED

Theorem aggregate_make_array_start_sim:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx nocalls st0.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty stride header (Var x) 0 sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+(if header then 32 else 0))
       (LENGTH args * type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+(if header then 32 else 0) \/
         b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`args`, `ce`, `cx`, `env`, `elem_ty`, `tv`, `header`, `0`,
    `if header then 32 else 0`, `sa`, `out`, `sb`, `es`, `func`, `inst`, `x`,
    `b`, `asz`, `s0`, `ctx`, `nocalls`] mp_tac aggregate_make_array_elems_sim >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> simp[]
QED

Theorem aggregate_emit_mstore_sim:
  emit_void MSTORE [pop; value] sa = ((),sb) /\
  eval_operand pop s0 = SOME addr /\ eval_operand value s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\r. r = (mstore (w2n addr) w s0 with
      vs_inst_idx := LENGTH sb.cs_current_insts)) R
Proof
  strip_tac >> irule frag_exec_run_inst_seq >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  gvs[cs_extends_def, same_blocks_def, venomInstTheory.mk_inst_def,
      venomInstTheory.is_terminator_def] >>
  rpt strip_tac >> disj1_tac >>
  drule_all exprSimLiteralBufferTheory.literal_emit_mstore_run >>
  strip_tac >> qexists_tac `mstore (w2n addr) w s0` >> gvs[]
QED


Theorem aggregate_make_array_sim:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx nocalls st0.
  EVERY (\e. arg_type_fits (expr_type e) elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
  exprs_case nocalls ctx func ce cx args /\
  (~nocalls ==> !e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) b
       ((if header then 32 else 0) + LENGTH args * type_memory_size tv)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def] >>
      mp_tac (SRULE [] (Q.INST [`header` |-> `F`, `idx` |-> `0`, `off` |-> `0`]
        (SPEC_ALL aggregate_make_array_elems_sim))) >>
      (impl_tac >- (gvs[] >> metis_tac[])) >> simp[]) >>
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def,
      AllCaseEqs()] >>
  Cases_on `emit_void MSTORE [Var x; Lit (n2w (LENGTH args))] sa` >>
  rename1 `emit_void MSTORE _ sa = (u,sm)` >> Cases_on `u` >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`args`, `0`] (Q.INST [`header` |-> `T`,
       `cfn` |-> `compile_expr`, `buf` |-> `Var x`]
       compile_make_array_elems_as_tuple)) >>
     strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome F _ _ _ _ _ _ post exitrel` >>
  qabbrev_tac `sh = mstore b (n2w (LENGTH args)) s0 with
    vs_inst_idx := SUC s0.vs_inst_idx` >>
  `gas_marked_path F ctx func s0 0 (OK sh)` by
    (`b < dimword (:256)` by decide_tac >>
     drule emit_mstore_marked_path >>
     disch_then (qspecl_then [`n2w (LENGTH args)`, `n2w b`, `s0`, `func`, `ctx`] mp_tac) >>
     simp[eval_operand_def, Abbr `sh`]) >>
  `!H. stmt_state_rel H ctx func ce cx es s0 ==>
   stmt_state_rel H ctx func ce cx es (mstore b (n2w (LENGTH args)) s0) /\
   locals_kept ce es es s0 (mstore b (n2w (LENGTH args)) s0) /\
   mem_word_at b (mstore b (n2w (LENGTH args)) s0).vs_memory = n2w (LENGTH args) /\
   (!p n. p+n <= b \/ b+32 <= p ==>
     mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
     mem_bytes_at p n s0.vs_memory)` by
    (gen_tac >> strip_tac >> irule array_header_store_boundary >>
     simp[] >> conj_tac
     >- (rpt strip_tac >> first_x_assum drule_all >>
         simp[regions_disjoint_def] >> decide_tac) >>
     qexistsl_tac [`asz`, `inst`, `x`] >> simp[]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sm.cs_next_id = SUC sa.cs_next_id /\ sm.cs_next_var = sa.cs_next_var` by
    gvs[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es sh /\
       storage_well_formed_on cx es (FST H)` by
    (gen_tac >> strip_tac >>
     `stmt_state_rel H ctx func ce cx es s0 /\
      storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     `stmt_state_rel H ctx func ce cx es (mstore b (n2w (LENGTH args)) s0)` by
       metis_tac[] >>
     asm_simp_tac std_ss [Abbr `sh`, stmt_state_rel_inst_idx]) >>
  `~sh.vs_halted /\ sh.vs_current_bb = sm.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sm.cs_current_insts` by
    simp[Abbr `sh`, mstore_def] >>
  `local_ptrs_reserved ce sm /\ not_fresh_at sm x /\
   inst.inst_id < sm.cs_next_id` by
    (conj_tac
     >- (qpat_x_assum `local_ptrs_reserved ce sa` mp_tac >>
         pure_rewrite_tac[local_ptrs_reserved_def, not_fresh_at_def] >>
         qpat_x_assum `sm.cs_next_var = _` (fn th => rewrite_tac[th])) >>
     conj_tac
     >- (qpat_x_assum `not_fresh_at sa x` mp_tac >>
         pure_rewrite_tac[not_fresh_at_def] >>
         qpat_x_assum `sm.cs_next_var = _` (fn th => rewrite_tac[th])) >>
     decide_tac) >>
  mp_tac (Q.INST [`header` |-> `T`, `idx` |-> `0`, `off` |-> `32`,
     `sa` |-> `sm`, `s0` |-> `sh`] (SPEC_ALL aggregate_make_array_elems_sim)) >>
  (impl_tac >-
    (qpat_x_assum `Abbrev (post = _)` kall_tac >>
     qpat_x_assum `Abbrev (exitrel = _)` kall_tac >>
     `lookup_var x sh = SOME (n2w b) /\
      FLOOKUP sh.vs_allocas inst.inst_id = SOME (b,asz)` by
       (simp[Abbr `sh`, mstore_def, lookup_var_def] >>
        gvs[lookup_var_def]) >>
     simp[] >> reverse conj_tac
     >- (rpt strip_tac >> first_x_assum drule_all >>
         simp[regions_disjoint_def] >> decide_tac) >>
     metis_tac[])) >>
  strip_tac >> conj_tac >- simp[] >>
  irule gas_outcome_zero_prefix >> qexists_tac `sh` >> simp[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> first_assum ACCEPT_TAC)
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      disj1_tac >> suspend "array_post_transport") >>
  metis_tac[]
QED

Resume aggregate_make_array_sim[array_post_transport]:
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `evaluate_type _ _ = _` kall_tac >>
  qpat_x_assum `type_memory_bytes _ _ = _` kall_tac >>
  qpat_x_assum `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!e st. MEM e args /\ expr_sim_inv ce cx env st ==> _` kall_tac >>
  qpat_x_assum `exprs_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `~nocalls ==> _` kall_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` kall_tac >>
  gvs[Abbr `post`] >> rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`?obs. es_end.storage_trace = es.storage_trace ++ obs` by
       (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
        disch_then (qspec_then `[]` assume_tac) >>
        drule_at (Pos last) storage_trace_frame_prefix >>
        simp[evaluate_storage_trace_frame]) >>
     `!H. valid_horizon cx st0 H es_end.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace` by
       simp[valid_horizon_def] >>
     metis_tac[]) >>
  `stmt_state_rel H ctx func ce cx es s0` by metis_tac[] >>
  `locals_kept ce es es s0 (mstore b (n2w (LENGTH args)) s0) /\
   mem_word_at b (mstore b (n2w (LENGTH args)) s0).vs_memory = n2w (LENGTH args) /\
   (!p n. p+n <= b \/ b+32 <= p ==>
     mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
     mem_bytes_at p n s0.vs_memory)` by metis_tac[] >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  gvs[] >>
  conj_tac >- suspend "header_word" >>
  conj_tac >- suspend "variables" >>
  conj_tac >- suspend "allocas" >>
  conj_tac >- suspend "inner_frame" >>
  conj_tac >- suspend "outer_frame" >>
  conj_tac >- suspend "locals" >>
  suspend "pure"
QED

Resume aggregate_make_array_sim[header_word]:
  `mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 sh.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[]) >>
  `mem_word_at b t.vs_memory = mem_word_at b sh.vs_memory` by
    simp[mem_word_at_bytes] >>
  simp[Abbr `sh`]
QED

Resume aggregate_make_array_sim[variables]:
  rpt strip_tac >> qpat_x_assum `!z w. not_fresh_at sm z /\ _ ==> _` irule >>
  simp[not_fresh_at_def, Abbr `sh`, mstore_def, lookup_var_def] >>
  gvs[not_fresh_at_def, lookup_var_def]
QED

Resume aggregate_make_array_sim[allocas]:
  rpt strip_tac >> first_x_assum irule >> simp[Abbr `sh`, mstore_def]
QED

Resume aggregate_make_array_sim[inner_frame]:
  rpt strip_tac >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n sh.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  `mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
   mem_bytes_at p n s0.vs_memory` by
    (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >>
  gvs[Abbr `sh`]
QED

Resume aggregate_make_array_sim[outer_frame]:
  rpt strip_tac >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n sh.vs_memory` by
    (qpat_x_assum `!aid p n. FLOOKUP sh.vs_allocas aid = _ /\ _ ==> _` irule >>
     conj_tac
     >- (simp[Abbr `sh`, mstore_def, local_region_def, lookup_var_def] >>
         gvs[local_region_def, lookup_var_def]) >>
     conj_tac >- (qexists_tac `aid` >> simp[Abbr `sh`, mstore_def]) >>
     simp[]) >>
  `mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
   mem_bytes_at p n s0.vs_memory` by
    (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >>
  gvs[Abbr `sh`]
QED

Resume aggregate_make_array_sim[locals]:
  irule locals_kept_trans >> qexistsl_tac [`es`, `sa`, `sh`] >>
  simp[Abbr `sh`, locals_kept_def, mstore_def, lookup_var_def]
QED

Resume aggregate_make_array_sim[pure]:
  strip_tac >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      b + asz <= lo \/ lo + sz <= b` by
    (rpt strip_tac >>
     `not_local_ptr ce es.scopes x` by simp[] >>
     drule_all (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `asz`, `r` |-> `s0`]
       aggregate_alloca_slice_excludes_local)) >> decide_tac) >>
  qspecl_then [`ce`, `func`, `es`, `sa`, `s0`, `s0`, `sh`, `b`, `asz`, `b`, `32`]
    mp_tac aggregate_pure_frame_store >>
  (impl_tac >-
    (conj_tac >- simp[] >>
     conj_tac >- simp[Abbr `sh`, mstore_def] >>
     conj_tac >- simp[] >>
     conj_tac >- decide_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> simp[Abbr `sh`] >>
     qpat_x_assum `!p n. _ \/ _ ==> _` irule >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_x_assum `EVERY _ args ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
     lookup_var z sh = SOME w` by
    simp[Abbr `sh`, mstore_def, lookup_var_def] >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_x_assum `sm.cs_next_id = _` mp_tac >> rpt (pop_assum kall_tac) >>
     decide_tac) >>
  qpat_x_assum `sm.cs_next_id = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  qspecl_then [`ce`, `func`, `es`, `es`, `sa`, `sm`, `s0`, `sh`, `t`, `b`, `asz`]
    mp_tac aggregate_pure_frame_trans >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (rewrite_tac[] >> NO_TAC) >>
      rpt strip_tac >>
      qpat_x_assum `!p n. (n + p <= b \/ _) /\ _ ==> mem_bytes_at p n t.vs_memory = _`
        irule >>
      conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (qpat_x_assum `p + n <= b` mp_tac) >>
      TRY (qpat_x_assum `b + asz <= p` mp_tac) >>
      rpt (pop_assum kall_tac) >> decide_tac) >>
  simp[]
QED

Finalise aggregate_make_array_sim
