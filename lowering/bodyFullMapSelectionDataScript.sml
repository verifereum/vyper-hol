(* Ordinary mapping selection, at the actual returns of the base and key. *)
Theory bodyFullMapSelectionData
Ancestors
  bodyFullMappingRunSeq bodyFullPreds exprSimMapDefs exprSimHypsDefs
  exprSimFullBundleProps exprLowering exprLoweringProps compileEnv context
  gasOutcomeFullCompose gasExplicitSites gasSummary fragGasOriginPtr
  loweringPosts bodyMemoryDefs bodyPtrDefs ptrDiscipline freshWrites allocaHistory
  vyperTypeSystem vyperInterpreter vyperState vyperStorageFootprint
  venomState venomExecSemantics finite_map pred_set list pair

(* The normal post of bodySimFull's mapping judgment (not a VV post). *)
Definition mapping_reference_post_def:
  mapping_reference_post (DF,lo,d,ctx,func) cenv cx e
    (es,sa,sb,s0,vv,G0,tn0) H (res : eval_result + exception) ee G tn t <=>
    ?tr slot kt vt tp p.
      res = INL (HashMapRef tr slot kt vt) /\
      storage_mapping_region cx tr slot (HashMapT kt vt) /\
      vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
      eval_operand p.ptr_operand t = SOME slot /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
         aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                       off + sz <= b \/ b + sz' <= off) ==>
         mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
      locals_kept cenv es ee s0 t /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      return_buf_frame d cenv sa t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
End

Definition mapping_selection_inputs_def:
  mapping_selection_inputs
    (DF,lo,d,ctx,shadow_ctx,PG,func)
    (map_parent,tops,cenv,cx,env,ty,ann,obj,idx,kt,vt)
    (st0,es,sa,sb,vv,s0,G0,tn0)
    (sm,bvv,marks,raw,mid,s,G1,tn1)
    (sn,key,imarks,v,fin,it,Gi,tni) (hashed,sp,outop) <=>
    (if map_parent then expr_map_pre cenv cx env (Subscript ann obj idx) es
     else expr_body_pre cenv cx env (Subscript ann obj idx) es) /\
    body_inv tops ctx cenv cx /\ expr_map_pre cenv cx env obj es /\
    place_type cenv obj = MapPT kt vt /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv (expr_type idx) idx sm = (key,sn) /\
    (if is_bytestring_type kt then compile_keccak256_key key F sn else (key,sn)) =
      (hashed,sp) /\ compile_mapping_subscript (vv_operand bvv) hashed sp = (outop,sb) /\
    vv = LocatedValue ann (mk_ptr outop
      (case vv_location bvv of SOME l => l | NONE => LocMemory)) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    expr_body_pre cenv cx env idx mid /\
    (!tail. eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL raw,mid with gas_obs := tail)) /\
    ~s.vs_halted /\ mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      mapping_reference_post (DF,lo,d,ctx,func) cenv cx obj
        (es,sa,sm,s0,bvv,G0,tn0) H (INL raw) mid G1 tn1 s /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK s,G1,tn1)) /\
    (!tail. bind (eval_expr cx idx) (read_result cx)
      (mid with gas_obs := gas_explicit imarks s.vs_gas_readings ++ tail) =
      (INL v,fin with gas_obs := tail)) /\
    ~it.vs_halted /\ fin.gas_obs = [] /\ storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx idx
        (mid,sm,sn,s,key,G1,tn1) H (INL v : value + exception) fin Gi tni it /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G1,tn1) imarks (OK it,Gi,tni))
End

Definition mapping_selected_slot_def:
  mapping_selected_slot
    (DF,lo,d,ctx,shadow_ctx,PG,func) (cenv,cx,env,obj,idx,kt,vt)
    (st0,es,sa,sb,s0,G0,tn0) (bvv,raw) (sn,v,fin,it,Gi,tni) outop u Gu tnu <=>
    mapping_raw_endpoint sn sb it u /\
    type_place_expr env obj = SOME (HashMapT kt vt) /\
    expr_type idx = kt /\ hashmap_key_type kt /\ expr_sim_inv cenv cx env fin /\
    (?tr base_slot tp p.
      raw = HashMapRef tr base_slot kt vt /\ storage_mapping_region cx tr base_slot (HashMapT kt vt) /\
      bvv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
      eval_operand outop u = SOME (hashmap_slot base_slot (encode_hashmap_key kt v))) /\
    op_taint tnu outop = {} /\ op_prov Gu outop = NONE /\
    (!x. outop = Var x ==> not_fresh_at sb x) /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ allocas_from lo u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (it,Gi,tni) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func cenv cx fin u /\ storage_well_formed_on cx fin (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx fin Gu tnu u) /\
    wb_frame cenv es fin sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
    return_buf_frame d cenv sa u /\
    (~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 u)
End

(* The source state can acquire a new StorageRoot at selection. Only the
   horizons valid for that result are needed, not a proof of its domain. *)
Definition mapping_selection_landing_def:
  mapping_selection_landing (DF,lo,explicit,ctx,func,PG) cx st0 sn sb
    source fin it Gi tni Q <=>
    ?res ee u Gu tnu.
      mapping_raw_endpoint sn sb it u /\
      (!tail. source (fin with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (it,Gi,tni) [] (OK u,Gu,tnu) /\
        Q H res (ee with gas_obs := []) Gu tnu u)
End

Theorem mapping_selection_landing_full:
  ~it.vs_halted /\ mapping_selection_landing (DF,lo,explicit,ctx,func,PG)
    cx st0 sn sb source fin it Gi tni Q ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (fin,it,Gi,tni) Q R
Proof
  rw[mapping_selection_landing_def] >> irule gas_outcome_full_pure >>
  simp[] >> qexistsl_tac [`Gu`,`ee`,`res`,`u`,`tnu`] >> simp[]
QED
