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
  exprBopSimProps
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprSimAggregateSource exprSimAggregateEncoding exprSimAggregateLayout exprLoweringProps
  localPtrsProps compileEnv valueEncoding valueEncodingProofs
  valueEncodingProps exprLowering vyperInterpreter vyperState
  exprSimHyps  fragExec exprSimAggregateChildren exprSimOps
  vyperImmutableMetadataFrame vyperEvalExprPreservesScopesDom
  exprSimAlloc gasOutcome gasSummary gasSummaryCompose gasContext
  fragGasMode fragGasPath fragGasSeq stmtSimDeclPath stmtSimDeclCompose
  abiStaticAggregateProps venomState exprSimUnwrap


Theorem aggregate_alloca_slice_excludes_local:
  stmt_state_rel ctx func ce cx es r /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + n <= asz /\ local_region ce es.scopes r name lo sz ==>
  lo + sz <= b + off \/ b + off + n <= lo
Proof
  cheat
QED

(* An element is stored from its lowered type. That type differs from the
   element's own only for bytestrings, whose store ignores the source type,
   and for an internal call returning a wider layout, which the caller rules
   out. *)
Theorem aggregate_elem_lowered_type[local]:
  !ce e env.
    well_typed_expr env e /\
    (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
    lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)
Proof
  cheat
QED

Theorem aggregate_store_lowered_elem[local]:
  !ce e src dst.
    lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e) ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
    compile_store_memory ce src dst (expr_type e) (expr_type e)
Proof
  cheat
QED


(* ===== Counted composition of the tuple loop ===== *)

(* The empty source list is a genuine reflexive counted execution. *)
Theorem aggregate_tuple_nil_outcome[local]:
  ~s.vs_halted /\ Q (INL []) (es with gas_obs := []) s ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx []) (es,s) Q R
Proof
  cheat
QED

Theorem aggregate_tuple_child_outcome[local]:
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
  cheat
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
  cheat
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
  cheat
QED

Theorem aggregate_tuple_store_no_gas[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  cheat
QED

(* One child's code: its value, the destination ADD, the unwrap and the
   store, then the rest of the tuple. *)
Theorem aggregate_tuple_cons_compile[local]:
  compile_make_tuple compile_expr ce (e::args) buf off sa = (out,sb) /\
  (lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)) ==>
  ?vv sm dst sn op su st.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (op,su) /\
    compile_store_memory ce op dst (expr_type e) (expr_type e) su = ((),st) /\
    compile_make_tuple compile_expr ce args buf
      (off + type_memory_bytes ce (expr_type e)) st = (out,sb)
Proof
  cheat
QED

Theorem aggregate_tuple_add_marked[local]:
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
  cheat
QED

Theorem aggregate_tuple_store_marked[local]:
  post_value_type ce e = expr_type e /\
  compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  fn_has_code su sb func /\ ~s.vs_halted /\
  s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' r q
Proof
  cheat
QED

Theorem aggregate_tuple_exec_end_gas_obs[local]:
  gas_marked_exec memory (ctx,func) source start marks res
    (ee with gas_obs := gs) r =
  gas_marked_exec memory (ctx,func) source start marks res ee r
Proof
  cheat
QED

Theorem aggregate_tuple_gas_outcome_mono[local]:
  gas_outcome memory tops (ctx,func) source start Q R ==>
  (!res ee r. Q res ee r ==> Q' res ee r) ==>
  (!res ee r. R res ee r ==> R' res ee r) ==>
  gas_outcome memory tops (ctx,func) source start Q' R'
Proof
  cheat
QED

(* The child's value, then the rest of the source under it. *)
Theorem aggregate_tuple_bind_outcome[local]:
  gas_outcome F tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) /\
  (!marks v ee t.
    gas_marked_exec F (ctx,func) a (es,s0) marks (INL v) ee (OK t) /\
    ee.gas_obs = [] /\ P v ee t ==>
    gas_outcome F tops (ctx,func)
      (k v : evaluation_state -> value list evaluation_result) (ee,t) Q R) ==>
  gas_outcome F tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  cheat
QED

(* A source-only step whose target code reads no gas, then the rest. *)
Theorem aggregate_tuple_value_bind[local]:
  gas_marked_exec F (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0)
    left (INL v) mid (OK t) /\
  gas_outcome F tops (ctx,func)
    (k v : evaluation_state -> value list evaluation_result)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome F tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  cheat
QED

Theorem aggregate_tuple_ignore_values[local]:
  ignore_bind (bind (eval_exprs cx args) (\vs. return (v::vs))) (return ()) =
  ignore_bind (eval_exprs cx args) (return ())
Proof
  cheat
QED

(* The rest of the tuple, with the child's value in front. *)
Theorem aggregate_tuple_values_outcome[local]:
  gas_outcome F tops (ctx,func) (eval_exprs cx args) (es,s) Q1 R1 /\
  (!res ee r. Q1 res ee r ==>
     Q (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) /\
  (!res ee r. R1 res ee r ==>
     R (case res of INL vs => INL (v::vs) | INR exc => INR exc) ee r) ==>
  gas_outcome F tops (ctx,func)
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es,s) Q R
Proof
  cheat
QED

Theorem aggregate_tuple_eval_cons[local]:
  eval_exprs cx (e::args) =
  bind (eval_expr cx e) (\tv. bind (read_result cx tv)
    (\v. bind (eval_exprs cx args) (\vs. return (v::vs))))
Proof
  cheat
QED

(* vv_post_local_region_backward, from the scope domains rather than an
   unmarked evaluation. *)
Theorem aggregate_tuple_local_region_backward[local]:
  !es es1 s0 s1 sa sb ctx func ce cx e tv vv name b sz.
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  vv_post ctx func ce cx e es sa sb s0 es1 tv vv s1 /\
  local_region ce es1.scopes s1 name b sz ==>
  local_region ce es.scopes s0 name b sz
Proof
  cheat
QED

Theorem aggregate_make_tuple_sim:
  !args ce cx env off sa out sb es tvs func inst x b asz s0 ctx nocalls.
  compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb) /\
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
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
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED














(* Post transport keeps the counted execution and exemption witnesses intact. *)
Theorem struct_gas_outcome_post[local]:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R /\
  (!res es' r. Q res es' r ==> Q' res es' r) ==>
  gas_outcome memory tops (ctx,func) source (es,s0) Q' R
Proof
  cheat
QED

Theorem struct_tuple_memory_post[local]:
  !names tvs vs ptr mem.
  LENGTH names = LENGTH tvs /\ tuple_in_memory vs tvs ptr mem ==>
  fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) ptr mem
Proof
  cheat
QED

Theorem aggregate_struct_fields_sim:
  !fields ce cx env ty off sa out sb es tvs func inst x b asz s0 ctx nocalls.
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (MAP SND fields)) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
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
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED

Theorem compile_make_array_elems_as_tuple:
  !args idx.
  EVERY (\e. expr_type e = elem_ty) args ==>
  compile_make_array_elems cfn ce args elem_ty (type_memory_bytes ce elem_ty)
    header buf idx =
  compile_make_tuple cfn ce args buf
    ((if header then 32 else 0) + idx * type_memory_bytes ce elem_ty)
Proof
  cheat
QED


Theorem array_header_store_state_rel[local]:
  stmt_state_rel ctx func ce cx es s /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo) /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel ctx func ce cx es (mstore b w s)
Proof
  cheat
QED

Theorem array_header_store_boundary[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\ 32 <= asz /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel ctx func ce cx es (mstore b w s) /\
  locals_kept ce es s (mstore b w s) /\
  mem_word_at b (mstore b w s).vs_memory = w /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n (mstore b w s).vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  cheat
QED


Theorem aggregate_make_array_elems_sim:
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx nocalls.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
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
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED

Theorem aggregate_make_array_start_sim:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx nocalls.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty stride header (Var x) 0 sa = (out,sb) /\
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
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
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED

Theorem aggregate_emit_mstore_sim:
  emit_void MSTORE [pop; value] sa = ((),sb) /\
  eval_operand pop s0 = SOME addr /\ eval_operand value s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\r. r = (mstore (w2n addr) w s0 with
      vs_inst_idx := LENGTH sb.cs_current_insts)) R
Proof
  cheat
QED


Theorem aggregate_make_array_sim:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx nocalls.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
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
      locals_kept ce es s0 r)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  cheat
QED








