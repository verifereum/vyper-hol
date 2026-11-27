(* Cut interfaces for the physical suffix of one memory-passed argument. *)
Theory bodyIntCallBufferHeadCutsMods
Ancestors
  bodyIntCallBufferHeadSpecMods bodyIntCallBufferHeadVVMods
  bodyIntCallBufferAllocVVMods bodyIntCallBufferWordInputMods
  bodyIntCallBufferNonwordInputMods bodyIntCallBufferStoreCutMods
  bodyIntCallBufferStoreFrameMods bodyIntCallStagePacketTransportMods
  bodyIntCallStageSnocMods bodyFullPostsMods exprSimMemorySource
  gasExplicitSites gasOutcomeFullMods fragGasOriginPtr
  vyperStorageFootprint vyperInterpreter vyperState venomState
  compileEnv loweringPosts bodyPtrDefs

val _ = Parse.hide "base";

(* These are the representation resources in the successful raw Q clause.
   The constructor witness is needed even when the formal is a word. *)
val vv_bound = ``
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) mid raw vv u``;
val vv_pointer = ``ptr_vv_ok cx (post_value_type cenv e) raw vv mid Gu tu u``;
val vv_ctor = ``
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
             eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)``;
val vv_stack = ``
  !tag x. vv = StackValue tag x /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e x Gu u``;
val vv_memory = ``
  !tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand Gu u``;
val vv_resources = ``^vv_bound /\ ^vv_pointer /\ ^vv_ctor /\ ^vv_stack /\ ^vv_memory``;

val raw_shape = ``
  u.vs_current_bb = ci.cs_current_bb /\
  u.vs_inst_idx = LENGTH ci.cs_current_insts /\
  alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s.vs_alloca_next <= u.vs_alloca_next``;

val raw_eval = ``
  !tail. eval_expr cx e
    (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL raw,mid with gas_obs := tail)``;

Definition intcall_buffer_head_raw_post_mods_def[nocompute]:
  intcall_buffer_head_raw_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (si,esi,s,G,tn) e dty marks raw vv ci mid u Gu tu <=>
    ^raw_eval /\
    eval_expr cx e
      (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ mid.gas_obs) =
      (INL raw,mid) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx func cenv cx e esi si ci s mid raw vv u /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
    ghost_kept_at lo cenv esi si G tn s Gu tu /\
    ^raw_shape /\ ^vv_resources
End

Definition intcall_buffer_head_edge_mods_def[nocompute]:
  intcall_buffer_head_edge_mods cenv (si,esi,s,G,tn) (sj,esj,t,Gj,tj) <=>
    si.cs_next_var <= sj.cs_next_var /\ si.cs_next_id <= sj.cs_next_id /\
    s.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    (!x w. not_fresh_at si x /\ lookup_var x s = SOME w ==>
       lookup_var x t = SOME w) /\
    (!x. not_fresh_at si x ==>
       FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
       FLOOKUP t.vs_allocas aid = SOME row) /\
    (!n lb sz. local_region cenv esi.scopes s n lb sz <=>
       local_region cenv esj.scopes t n lb sz) /\
    (!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < si.cs_next_id /\
       (!nm p k. local_region cenv esi.scopes s nm p k ==> b+n <= p \/ p+k <= b) ==>
       mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
       (!i. b <= i /\ i < b+n /\ i IN tj.t_mem ==> i IN tn.t_mem)) /\
    wb_frame cenv esi esj si s t
End

Definition intcall_buffer_head_alloc_post_mods_def[nocompute]:
  intcall_buffer_head_alloc_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func) mods cenv cx env st0
    (si,esi,s,G,tn) (ci,mid,u,Gu,tu) (ca,mida,a,Ga,ta)
    e dty raw vv buf aid dst base cap v <=>
    mida = mid /\
    read_result cx raw mid = (INL v,mid) /\
    (?rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\ value_has_type rt v) /\
    (?pt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pt /\ value_has_type pt v) /\
    (?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v) /\
    body_const_cells_agree_mods mods cx env mid /\ expr_sim_inv_mods mods cenv cx env mid /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       storage_well_formed_on cx mid (FST H) /\
       vv_post_mods H ctx func cenv cx e esi si ca s mid raw vv a /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid Ga ta a) /\
    ghost_kept_at lo cenv esi si G tn s Ga ta /\
    ^(Q.INST [`u` |-> `a`, `Gu` |-> `Ga`, `tu` |-> `ta`] (REFL vv_resources) |> concl |> rand) /\
    vv_at cenv cx (post_value_type cenv e) si ci mid raw vv u /\
    eval_operand (vv_operand vv) a = eval_operand (vv_operand vv) u /\
    intcall_buffer_head_edge_mods cenv (si,esi,s,G,tn) (ci,mid,u,Gu,tu) /\
    intcall_buffer_head_edge_mods cenv (ci,mid,u,Gu,tu) (ca,mid,a,Ga,ta) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tu) [] (OK a,Ga,ta)) /\
    ~a.vs_halted /\ a.vs_current_bb = ca.cs_current_bb /\
    a.vs_inst_idx = LENGTH ca.cs_current_insts /\ alloca_history func a /\
    alloca_inv a /\ allocas_from lo a /\ lo <= a.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    s.vs_alloca_next <= a.vs_alloca_next /\ return_buf_frame d cenv ca a /\
    aid = ci.cs_next_id /\ aid < ca.cs_next_id /\
    cap = MAX 32 (type_memory_bytes cenv dty) /\
    MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [dst]) (fn_insts func) /\
    buf.buf_operand = Var dst /\ not_fresh_at ca dst /\ not_local_ptr cenv mid.scopes dst /\
    FLOOKUP a.vs_allocas aid = SOME (base,cap) /\
    lookup_var dst a = SOME (n2w base) /\ FLOOKUP Ga dst = SOME (base,cap) /\
    op_taint ta (Var dst) = {} /\ ptr_covers Ga ta dst a cap /\
    lo <= base /\ base + cap < dimword (:256) /\ base + cap <= a.vs_alloca_next /\
    (!i b n. i < aid /\ FLOOKUP u.vs_allocas i = SOME (b,n) ==>
       loweringStateRelDefs$regions_disjoint base cap b n) /\
    (!nm b n. local_region cenv mid.scopes a nm b n ==>
       loweringStateRelDefs$regions_disjoint base cap b n)
End

val store_runtime = ``
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  alloca_history func z /\ alloca_inv z /\ ~z.vs_halted /\
  z.vs_current_bb = cu.cs_current_bb /\ z.vs_inst_idx = LENGTH cu.cs_current_insts``;

(* The compiler code and ambient aggregate invariants are supplied separately.
   Write the destination address as in the normalized store theorem. *)
val store_data = ``
  if is_word_type dty then
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    eval_operand opn z = SOME (typed_val_to_w256 dtv v) /\ op_taint tz opn = {} /\
    lookup_var dst z = SOME (n2w base) /\
    w2n (n2w base : bytes32) + 32 < dimword (:256) /\
    w2n (n2w base : bytes32) + 32 <= z.vs_alloca_next /\ ptr_covers Gz tz dst z 32
  else if is_bytestring_type dty then
    ?src sw len n. opn = Var src /\ is_bytestring_type (vv_type vv) /\
      evaluate_type (get_tenv cx) (vv_type vv) = SOME stv /\
      evaluate_type (get_tenv cx) dty = SOME dtv /\
      value_has_type stv v /\ value_has_type dtv v /\
      ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
       (?str. v = StringV str /\ len = LENGTH str)) /\
      (!m. mem_agree_outside tz.t_mem z.vs_memory m ==>
           val_in_memory stv v (w2n sw) m) /\
      n = 32 + 32 * word_size len /\ n < dimword (:256) /\
      not_fresh_at cu src /\ not_fresh_at cu dst /\
      lookup_var src z = SOME sw /\ lookup_var dst z = SOME (n2w base) /\
      ptr_covers Gz tz src z n /\ ptr_covers Gz tz dst z n /\
      w2n sw + n <= z.vs_alloca_next /\
      w2n (n2w base : bytes32) + n <= z.vs_alloca_next
  else
    struct_operand_mods (cenv,get_tenv cx,vv_type vv,dty,stv,dtv)
      (opn,v) (dst,w2n (n2w base : bytes32)) (cu,Gz,tz,z) /\
    FLOOKUP z.vs_allocas aid = SOME (w2n (n2w base : bytes32),MAX 32 (type_memory_bytes cenv dty))``;

Definition intcall_buffer_head_unwrap_post_mods_def[nocompute]:
  intcall_buffer_head_unwrap_post_mods (DF,lo,d,ctx,shadow_ctx,PG,func) cenv cx st0
    (si,esi,s,G,tn) (ca,mid,a,Ga,ta) (cu,midz,z,Gz,tz)
    e dty raw vv aid dst base cap v opn <=>
    midz = mid /\ read_result cx raw mid = (INL v,mid) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (a,Ga,ta) [] (OK z,Gz,tz)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post_mods H ctx func cenv cx e esi si cu s mid v opn z /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid Gz tz z /\
       storage_well_formed_on cx mid (FST H)) /\
    ghost_kept_at lo cenv esi si G tn s Gz tz /\
    intcall_buffer_head_edge_mods cenv (ca,mid,a,Ga,ta) (cu,mid,z,Gz,tz) /\
    ^store_runtime /\
    aid < ca.cs_next_id /\ cap = MAX 32 (type_memory_bytes cenv dty) /\
    FLOOKUP z.vs_allocas aid = SOME (base,cap) /\
    not_fresh_at cu dst /\ not_local_ptr cenv mid.scopes dst /\
    lookup_var dst z = SOME (n2w base) /\ FLOOKUP Gz dst = SOME (base,cap) /\
    op_taint tz (Var dst) = {} /\ ptr_covers Gz tz dst z cap /\
    lo <= base /\ base + cap < dimword (:256) /\ base + cap <= z.vs_alloca_next /\
    (?stv dtv. ^store_data)
End

Definition intcall_buffer_head_store_post_mods_def[nocompute]:
  intcall_buffer_head_store_post_mods (lo,ctx,shadow_ctx,PG,func) cenv cx
    (cu,mid,z,Gz,tz) (cs,midt,t,Gf,tf) aid dst base cap v dty nw <=>
    midt = mid /\ nw <= cap /\ cap = MAX 32 (type_memory_bytes cenv dty) /\
    cu.cs_next_id <= cs.cs_next_id /\ cu.cs_next_var <= cs.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (z,Gz,tz) [] (OK t,Gf,tf)) /\
    typed_copy_state_frame cu base nw z t /\
    ~t.vs_halted /\ alloca_history func t /\
    t.vs_current_bb = cs.cs_current_bb /\ t.vs_inst_idx = LENGTH cs.cs_current_insts /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    FLOOKUP t.vs_allocas aid = SOME (base,cap) /\ lookup_var dst t = SOME (n2w base) /\
    (!p. not_fresh_at cu p ==> lookup_var p t = lookup_var p z /\
       FLOOKUP Gf p = FLOOKUP Gz p /\ op_taint tf (Var p) = op_taint tz (Var p)) /\
    tf.t_stor = tz.t_stor /\ tf.t_trans = tz.t_trans /\ tf.t_imm = tz.t_imm /\
    (!i. ~(base <= i /\ i < base + nw) ==> (i IN tf.t_mem <=> i IN tz.t_mem)) /\
    (?dtv. evaluate_type (get_tenv cx) dty = SOME dtv /\
       value_has_type dtv v /\ val_wf dtv v /\ type_memory_size dtv <= cap /\
       val_footprint dtv v <= nw /\
       (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory dtv v base m))
End

(* Specialization of the successful Q clause of expr_vv_sim_full_mods_def.
   Only the horizon-independent data are taken from the canonical horizon. *)
Theorem intcall_buffer_head_raw_post_intro_mods:
  ^raw_eval /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     (\res. ?raw. res = INL raw /\
       vv_post_mods H ctx func cenv cx e esi si ci s mid raw vv u /\
       ^vv_bound /\ u.vs_current_bb = ci.cs_current_bb /\
       u.vs_inst_idx = LENGTH ci.cs_current_insts /\ alloca_history func u /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
       ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u /\ ^vv_pointer /\
       (!v. raw = Value v /\ ~is_word_type (post_value_type cenv e) /\
            ~is_bytestring_type (post_value_type cenv e) ==>
            vv_own cenv cx (post_value_type cenv e) si ci mid raw vv u /\
            (!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory)) /\
       ^vv_ctor /\ ^vv_stack /\ ^vv_memory /\
       ghost_kept_at lo cenv esi si G tn s Gu tu) (INL raw) /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,G,tn) marks (OK u,Gu,tu)) ==>
  intcall_buffer_head_raw_post_mods
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods cenv cx env st0 (si,esi,s,G,tn) e dty marks raw vv ci mid u Gu tu
Proof
  simp[intcall_buffer_head_raw_post_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_buffer_head_store_input_mods:
  intcall_buffer_head_unwrap_post_mods (DF,lo,d,ctx,shadow_ctx,PG,func) cenv cx st0
    (si,esi,s,G,tn) (ca,mid,a,Ga,ta) (cu,mid,z,Gz,tz)
    e dty raw vv aid dst base cap v opn ==>
  ^store_runtime /\ (?stv dtv. ^store_data)
Proof
  pure_rewrite_tac[intcall_buffer_head_unwrap_post_mods_def,REFL_CLAUSE] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?stv dtv. _` mp_tac >>
  Cases_on `is_word_type dty` >- simp_tac bool_ss [] >>
  Cases_on `is_bytestring_type dty` >> simp_tac bool_ss []
QED
