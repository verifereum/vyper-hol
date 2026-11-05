Theory bodyIntCallJointSingleton
Ancestors
  exprSimAggregateSource exprSimWordArgs vyperState
  exprSimSource exprSimHypsDefs vyperTypeSystem
  valueEncoding valueEncodingProps venomState
  bodyIntCallGasPrefix bodyIntCallJointTuple exprSimBuffer exprSimAlloc
  context compileEnv emitHelper exprLowering exprLoweringProps

(* Materialise the sole child on its actual evaluation endpoint. *)
Theorem joint_eval_make_tuple_singleton:
  compatible_bound bnd 1 /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) [e]) es =
    (INL (Value (ArrayV (TupleV [v]))),ee)
Proof
  rpt strip_tac >>
  `eval_exprs cx [e] es = (INL [v],ee)` by
    simp[eval_exprs_cons_action, bind_def, eval_exprs_nil, return_def] >>
  drule_at (Pos last) aggregate_eval_make_tuple >> simp[]
QED

(* The bound is supplied by the parent's typing, not by a new precondition. *)
Theorem joint_typed_eval_make_tuple_singleton:
  expr_sim_pre ce cx env (Builtin ann (MakeArray NONE bnd) [e]) es /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  eval_expr cx (Builtin ann (MakeArray NONE bnd) [e]) es =
    (INL (Value (ArrayV (TupleV [v]))),ee)
Proof
  rpt strip_tac >> irule joint_eval_make_tuple_singleton >>
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  metis_tac[]
QED

(* Representation audit for the allocating MsgGas parent (not a simulation).

   Source: joint_typed_eval_make_tuple_singleton uses only the actual child
   evaluation and read_result at ee.  It is independent of observation tails
   and ctor mode.  expr_sim_pre_body_pre (exprSimSource) supplies the input of
   make_tuple_evaluated_layout; expr_body_pre_builtin_arg supplies child typing.
   For e = Builtin ga (Env MsgGas) args, layout gives ann = TupleT [ga].

   Concrete endpoint from joint_tuple_word_suffix_path:
     r = (mstore (w2n p) w (update_var x p u))
           with vs_inst_idx := LENGTH sb.cs_current_insts.
   Here p MUST be the pointer from literal_alloc_buffer_run, not a new
   existential pointer selected by another simulation.

   Encoding: val_in_memory_def reduces the singleton TupleTV encoding to
   val_in_memory child_tv (IntV (&w2n w)) (w2n p) r.vs_memory.
   mstore_establishes_val_in_memory_prim (valueEncodingProps) establishes this
   once val_to_w256 (IntV (&w2n w)) = w is rewritten.  No tuple-specific local
   helper is required.  Encoding alone is NOT vv_post.

   Exact remaining vv_post sequents at r (loweringPosts):
   1. stmt_state_rel at ee: suffix_frame supplies this once the SAME u has
      its state relation, same allocation and local separation.
   2. vv_holds: buf operand still evaluates to p at r, evaluated parent type
      is TupleTV [child_tv], and source Value reads to itself at ee.
   3. vv_at: val_wf of the tuple, plus SAME allocation id sa.cs_next_id,
      sa.cs_next_id < sb.cs_next_id, its pointer/size at r, footprint bound,
      and disjointness from ALL local_region ce ee.scopes r regions.
      Reused ALLOCA must retain this allocation id; freshness of its address
      is not a premise.  aggregate_alloca_slice_excludes_local is exported.
   4. every not_fresh_at sa variable value is preserved from original s0.
   5. every original allocation map entry is preserved from s0.
   6. every old, nonlocal allocation window is preserved from s0 (exact
      local-separation guard uses es.scopes and s0, not ee and r).
   7. locals_kept ce es s0 r.
   Plus the producer's stronger hs and initialized-immutable byte equalities
   must compose from s0, not merely from u.  Suffix frame already handles
   initialized immutable type_memory_size windows in BOTH ctor modes.

   These are outstanding construction sequents, not assumed consequences of
   the existing existential aggregate simulation.  No ordinary-success proof
   would discharge gas_outcome's exempt alternative; enclosing source outcome
   transport must retain that branch separately. *)

(* Singleton tuple encoding on the actual scalar-store endpoint. *)
Theorem joint_singleton_int_store_encoding:
  val_in_memory (TupleTV [tv]) (ArrayV (TupleV [IntV n])) off
    (mstore off (val_to_w256 (IntV n)) s).vs_memory
Proof
  simp[valueEncodingTheory.val_in_memory_def,
       valueEncodingTheory.val_to_w256_def, mstore_mem_word_at_same]
QED

(* The three register-producing steps use distinct monotonically fresh names. *)
Theorem joint_alloc_gas_add_registers:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_env_var MsgGas sm = (gop,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) ==>
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
  gop = Var (STRING #"%" (toString sm.cs_next_var)) /\
  dst = Var (STRING #"%" (toString sn.cs_next_var)) /\
  sm.cs_next_var = sa.cs_next_var + 1 /\
  sn.cs_next_var = sm.cs_next_var + 1 /\
  sp.cs_next_var = sn.cs_next_var + 1 /\
  sm.cs_next_id = sa.cs_next_id + 1 /\
  sn.cs_next_id = sm.cs_next_id + 1 /\
  sp.cs_next_id = sn.cs_next_id + 1
Proof
  simp[compile_alloc_buffer_def, compile_env_var_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem joint_alloc_gas_add_pointer_kept:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_env_var MsgGas sm = (gop,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  eval_operand buf.buf_operand t = SOME p ==>
  eval_operand buf.buf_operand
    ((mstore (w2n p) w
      (update_var (STRING #"%" (toString sn.cs_next_var)) p
        (update_var (STRING #"%" (toString sm.cs_next_var)) w
          (t with vs_gas_readings := tail))))
       with vs_inst_idx := ix) = SOME p
Proof
  strip_tac >> drule_all joint_alloc_gas_add_registers >> strip_tac >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, mstore_def,
      finite_mapTheory.FLOOKUP_UPDATE, ASCIInumbersTheory.toString_11]
QED

Theorem joint_alloc_gas_add_tuple_holds:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_env_var MsgGas sm = (gop,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  eval_operand buf.buf_operand t = SOME p /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  vv_holds ce cx (TupleT [ty]) (Value (ArrayV (TupleV [IntV (&w2n w)])))
    (LocatedValue (TupleT [ty]) (mk_ptr buf.buf_operand LocMemory)) ee
    ((mstore (w2n p) w
      (update_var (STRING #"%" (toString sn.cs_next_var)) p
        (update_var (STRING #"%" (toString sm.cs_next_var)) w
          (t with vs_gas_readings := tail))))
       with vs_inst_idx := ix)
Proof
  strip_tac >> drule_all joint_alloc_gas_add_pointer_kept >>
  disch_then (qspecl_then [`w`,`tail`,`ix`] assume_tac) >>
  simp[loweringPostsTheory.vv_holds_def, mk_ptr_def, read_result_def,
       return_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def] >>
  qexists_tac `p` >> conj_tac
  >- (qpat_x_assum `eval_operand _ (_ with vs_inst_idx := _) = _` mp_tac >>
      Cases_on `buf.buf_operand` >>
      simp[eval_operand_def, lookup_var_def, update_var_def, mstore_def]) >>
  `val_to_w256 (IntV (&w2n w)) = w` by
    simp[valueEncodingTheory.val_to_w256_def] >>
  metis_tac[joint_singleton_int_store_encoding]
QED

Theorem joint_msg_gas_tuple_typed:
  expr_sim_pre ce cx env
    (Builtin ann (MakeArray NONE bnd) [Builtin ga (Env MsgGas) args]) es ==>
  ann = TupleT [env_item_type MsgGas] /\
  ga = env_item_type MsgGas /\ args = [] /\ compatible_bound bnd 1
Proof
  simp[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[vyperASTTheory.expr_type_def]
QED

(* Both suffix register writes are fresh at the original allocation entry. *)
Theorem joint_alloc_gas_add_old_registers:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_env_var MsgGas sm = (gop,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) ==>
  !x. not_fresh_at sa x ==>
    lookup_var x
      ((mstore (w2n p) w
        (update_var (STRING #"%" (toString sn.cs_next_var)) p
          (update_var (STRING #"%" (toString sm.cs_next_var)) w
            (t with vs_gas_readings := tail))))
        with vs_inst_idx := ix) = lookup_var x s0
Proof
  strip_tac >> drule_all joint_alloc_gas_add_registers >> strip_tac >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sm.cs_next_var) /\
   x <> STRING #"%" (toString sn.cs_next_var)` by
    (gvs[not_fresh_at_def] >> conj_tac >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >>
  gvs[lookup_var_def, update_var_def, mstore_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Allocation-run facts frame the original entry, including its live locals.
   The suffix's register and observation updates do not affect this memory. *)
Theorem joint_allocated_store_entry_frame:
  local_ptrs_reserved ce sa /\ t.vs_memory = s0.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
  (!name lb len. local_region ce es.scopes t name lb len ==>
     regions_disjoint b sz lb len) /\
  (!aid off len. aid < sa.cs_next_id /\
     FLOOKUP s0.vs_allocas aid = SOME (off,len) ==>
     regions_disjoint b sz off len) /\
  b <= a /\ a + 32 <= b + sz /\
  r.vs_memory = (mstore a w t).vs_memory ==>
  locals_kept ce es s0 r /\
  (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
     aid < sa.cs_next_id ==>
     mem_bytes_at off len r.vs_memory = mem_bytes_at off len s0.vs_memory)
Proof
  strip_tac >>
  `!name lb len. local_region ce es.scopes s0 name lb len ==>
     local_region ce es.scopes t name lb len` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[]) >>
  conj_tac
  >- (irule exprSimPropsTheory.locals_kept_regions >> rpt strip_tac >>
      `regions_disjoint b sz b' sz'` by metis_tac[] >>
      qpat_x_assum `r.vs_memory = _` SUBST1_TAC >>
      qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
      irule exprSimHashTheory.mstore_region_frame >>
      qexistsl_tac [`b`, `sz`] >> simp[]) >>
  rpt strip_tac >>
  `regions_disjoint b sz off len` by metis_tac[] >>
  qpat_x_assum `r.vs_memory = _` SUBST1_TAC >>
  qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[GSYM th]) >>
  irule exprSimHashTheory.mstore_region_frame >>
  qexistsl_tac [`b`, `sz`] >> simp[]
QED


(* Symbolic names keep the semantic suffix independent of compiler counters. *)
Theorem joint_gas_store_frame:
  stmt_state_rel ctx func ce cx es t /\
  not_local_ptr ce es.scopes g /\ not_local_ptr ce es.scopes x /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\ 32 <= sz /\
  (!name lb len. local_region ce es.scopes t name lb len ==>
     regions_disjoint b sz lb len) /\
  EVERY (\(off,len). regions_disjoint b sz off len) hs ==>
  let u = update_var g w (t with vs_gas_readings := readings) in
  let r = (mstore b w (update_var x p u)) with vs_inst_idx := ix in
  stmt_state_rel ctx func ce cx (es with gas_obs := gs) r /\
  EVERY (\(off,len). mem_bytes_at off len r.vs_memory =
                     mem_bytes_at off len t.vs_memory) hs /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
      name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) r.vs_memory =
    mem_bytes_at off (type_memory_size tv) t.vs_memory)
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es
     (update_var g w (t with vs_gas_readings := readings))` by
    (irule stmt_state_rel_update_var >>
     simp[exprSimHashTheory.hash_gas_readings_state_rel]) >>
  qabbrev_tac `u = update_var g w (t with vs_gas_readings := readings)` >>
  `(!name lb len. local_region ce es.scopes u name lb len ==>
     regions_disjoint b sz lb len) /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz)` by
    (simp[Abbr `u`, local_region_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[not_local_ptr_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  simp[LET_THM] >>
  qpat_assum `stmt_state_rel _ _ _ _ es u`
    (mp_then (Pos hd) mp_tac joint_tuple_word_suffix_frame) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`w`, `p`, `ix`] mp_tac) >>
  simp[Abbr `u`, update_var_def] >> metis_tac[]
QED

Theorem joint_msg_gas_tuple_layout:
  evaluate_type (get_tenv cx) (TupleT [env_item_type MsgGas]) =
    SOME (TupleTV [BaseTV (UintT 256)]) /\
  val_wf (TupleTV [BaseTV (UintT 256)])
    (ArrayV (TupleV [IntV (&w2n w)])) /\
  val_footprint (TupleTV [BaseTV (UintT 256)])
    (ArrayV (TupleV [IntV (&w2n w)])) = 32
Proof
  simp[env_item_type_def, vyperValueTheory.evaluate_type_def,
       val_wf_def, type_memory_size_def, loweringPostsTheory.val_footprint_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def]
QED

(* A post at the allocation run's actual endpoint, not an independently chosen
   existential aggregate simulation. *)
Theorem joint_singleton_endpoint_post:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  compile_env_var MsgGas sm = (gop,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce gop dst (env_item_type MsgGas) sty sp = ((),sb) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  run_inst_seq (emitted_insts sa sm) s0 = OK t /\
  eval_operand buf.buf_operand t = SOME p ==>
  let r = (mstore (w2n p) w
    (update_var (STRING #"%" (toString sn.cs_next_var)) p
      (update_var (STRING #"%" (toString sm.cs_next_var)) w
        (t with vs_gas_readings := readings)))) with vs_inst_idx := ix in
  vv_post ctx func ce cx
    (Builtin (TupleT [env_item_type MsgGas]) (MakeArray NONE bnd)
      [Builtin (env_item_type MsgGas) (Env MsgGas) []])
    es sa sb s0 (es with gas_obs := gs)
    (Value (ArrayV (TupleV [IntV (&w2n w)])))
    (LocatedValue (TupleT [env_item_type MsgGas])
      (mk_ptr buf.buf_operand LocMemory)) r
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all joint_alloc_gas_add_registers >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `!x. not_fresh_at sa x ==>
    lookup_var x ((mstore (w2n p) w
      (update_var (STRING #"%" (toString sn.cs_next_var)) p
        (update_var (STRING #"%" (toString sm.cs_next_var)) w
          (t with vs_gas_readings := readings)))) with vs_inst_idx := ix) =
    lookup_var x s0` by
    (rpt strip_tac >> irule joint_alloc_gas_add_old_registers >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`buf`, `dst`, `sa`, `sp`, `32`] >>
     gvs[] >> metis_tac[]) >>
  gvs[] >>
  qmatch_goalsub_abbrev_tac `vv_post _ _ _ _ _ _ _ _ _ _ _ _ r` >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString (sa.cs_next_var + 1))) /\
   not_local_ptr ce es.scopes (STRING #"%" (toString (sa.cs_next_var + 2)))` by
    (conj_tac >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func ce cx (es with gas_obs := gs) r` by
    (simp[Abbr `r`] >>
     irule (cj 1 (SRULE [LET_THM, stmt_state_rel_inst_idx]
       joint_gas_store_frame)) >>
     simp[] >>
     qexistsl_tac [`[]`, `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sa.cs_next_var)]`, `32`] >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>

  `locals_kept ce es s0 r /\
   (!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
     aid < sa.cs_next_id ==>
     mem_bytes_at off len r.vs_memory = mem_bytes_at off len s0.vs_memory)` by
    (irule joint_allocated_store_entry_frame >>
     simp[] >>
     qexistsl_tac [`w2n p`, `w2n p`, `32`, `t`, `w`] >>
     simp[Abbr `r`, mstore_def, update_var_def] >> metis_tac[]) >>
  suspend "assemble"
QED

Resume joint_singleton_endpoint_post[assemble]:
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.SPEC `Builtin (TupleT [env_item_type MsgGas]) (MakeArray NONE bnd)
      [Builtin (env_item_type MsgGas) (Env MsgGas) []]`
      (Q.SPECL [`func`, `ce`, `cx`] buffer_memory_vv_post_general))) >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def, mk_ptr_def,
       joint_msg_gas_tuple_layout] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x (r with vs_inst_idx := ix) = _`
      drule >> simp[lookup_var_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (simp[Abbr `r`, mstore_def, update_var_def] >> metis_tac[]) >>
  conj_tac
  >- (`ci_mono sp sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
      gvs[ci_mono_def]) >>
  qexistsl_tac [`32`, `p`] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce es.scopes t n lb lsz` by
        (qpat_x_assum `local_region _ _ r _ _ _` mp_tac >>
         simp[local_region_def, Abbr `r`, lookup_var_def, update_var_def,
              mstore_def, finite_mapTheory.FLOOKUP_UPDATE] >>
         strip_tac >>
         rename1 `FLOOKUP ce.ce_vars n = SOME (PtrVar (Var q) lsz)` >>
         `STRING #"%" (toString (sa.cs_next_var + 1)) <> q /\
          STRING #"%" (toString (sa.cs_next_var + 2)) <> q` by
           (gvs[not_local_ptr_def] >> metis_tac[]) >>
         gvs[] >> metis_tac[]) >>
      gvs[regions_disjoint_def] >> metis_tac[]) >>
  simp[] >>
  conj_tac
  >- (gvs[Abbr `r`, eval_operand_def, lookup_var_def, update_var_def,
          mstore_def, finite_mapTheory.FLOOKUP_UPDATE,
          ASCIInumbersTheory.toString_11]) >>
  conj_tac >- simp[Abbr `r`, mstore_def, update_var_def] >>
  simp[Abbr `r`, valueEncodingTheory.val_in_memory_def,
       mstore_mem_word_at_same, valueEncodingTheory.val_to_w256_def]
QED
Finalise joint_singleton_endpoint_post
