(* The paired compiler/source cuts for traversing a live MakeArray window. *)
Theory bodyMakeElementsContractMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyPtrDefs loweringPosts loweringStateRelDefs exprSimDefs exprSimHypsDefs
  gasOutcomeFullMods gasOutcomeFull fragGasOriginPtr gasSummary gasContext
  gasShadow gasShadowState
  exprLowering compileEnv context venomState venomInst venomWf
  typeLayoutProps valueEncoding valueEncodingDefs exprSimProps exprSimMemDefs
  vyperStorageFootprint vyperInterpreter vyperState vyperTypeSystem vyperAST
  finite_map list pair option words arithmetic

val _ = Parse.hide "base";

Definition make_elements_run_mods_def[nocompute]:
  make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
      source (es,s,G,tn) Q <=>
    gas_outcome_full_mods
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 source (es,s,G,tn) Q
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
End

Definition make_elements_admissible_mods_def[nocompute]:
  make_elements_admissible_mods cx xs ee <=>
    gas_admissible (eval_exprs cx xs)
      (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) ee
End

Definition make_elements_save_mods_def[nocompute]:
  make_elements_save_mods s t <=>
    !a b. FLOOKUP s.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b
End

(* The horizon is universally quantified at each cut, independently of the
   horizon at which a client uses a successful outcome. *)
Definition make_elements_cut_mods_def[nocompute]:
  make_elements_cut_mods DF lo d ctx func cenv cx st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) cs ee z g tt <=>
    (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
    FLOOKUP z.vs_allocas aid = SOME (base,cap) /\
    lookup_var q z = SOME (n2w base) /\
    ptr_covers g tt q z cap /\ not_fresh_at cs q /\
    aid < cs.cs_next_id /\ base + cap < dimword (:256) /\
    base + cap <= z.vs_alloca_next /\
    (!name b n. local_region cenv ee.scopes z name b n ==>
                loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func z /\ sbase.vs_alloca_next <= z.vs_alloca_next /\
    make_elements_save_mods sbase z /\
    MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
    wb_frame cenv ebase ee csbase sbase z /\
    ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase g tt /\
    return_buf_frame d cenv cs z /\ ~z.vs_halted /\
    z.vs_current_bb = cs.cs_current_bb /\
    z.vs_inst_idx = LENGTH cs.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee z /\
      immutable_frame_mods func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee g tt z) /\
    lo <= base /\
    (!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u)
End

Definition make_elements_prefix_mods_def[nocompute]:
  make_elements_prefix_mods base ps off z tt <=>
    EVERY (\(rt,v,p,n). val_wf rt v /\ val_footprint rt v <= n /\
      base <= p /\ p + n <= base + off /\
      (!m. mem_agree_outside tt.t_mem z.vs_memory m ==>
           val_in_memory rt v p m)) ps
End

Definition make_elements_window_mods_def[nocompute]:
  make_elements_window_mods base cap off k s t <=>
    !p n. base + off + k <= p /\ p + n <= base + cap ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory
End

Definition make_elements_frame_mods_def[nocompute]:
  make_elements_frame_mods cenv func base cap sa es s t <=>
    (!name b n. local_region cenv es.scopes s name b n ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!p n. (p + n <= base \/ base + cap <= p) /\
      (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
        sa.cs_next_id <= i.inst_id /\ FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint p n b sz) ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory)
End

Definition make_elements_static_mods_def[nocompute]:
  make_elements_static_mods mods exps src tops cenv cx env
      (DF,lo,ctx,shadow_ctx,func,shadow_func) st0 csbase ebase sbase aid sa <=>
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    expr_sim_inv_mods mods cenv cx env ebase /\
    csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
    csbase.cs_next_var <= sa.cs_next_var /\
    local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
    ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
    gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at csbase x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at csbase x) /\
    (!H. valid_horizon cx st0 H ebase.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ebase sbase)
End

Definition make_elements_entry_mods_def[nocompute]:
  make_elements_entry_mods mods exps src tops cenv cx env
      (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) xs ps off sa (es,s,G,tn) <=>
    make_elements_static_mods mods exps src tops cenv cx env
      (DF,lo,ctx,shadow_ctx,func,shadow_func) st0 csbase ebase sbase aid sa /\
    body_const_cells_agree_mods mods cx env es /\
    body_exprs_full_ok_mods mods exps cx xs /\
    (!e ee. MEM e xs /\ expr_sim_inv_mods mods cenv cx env ee ==>
            expr_body_pre_mods mods cenv cx env e ee) /\
    expr_sim_inv_mods mods cenv cx env es /\
    make_elements_admissible_mods cx xs es /\
    make_elements_cut_mods DF lo d ctx func cenv cx st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sa es s G tn /\
    make_elements_prefix_mods base ps off s tn
End

Definition make_elements_code_mods_def[nocompute]:
  make_elements_code_mods func shadow_func sa sb sha shb <=>
    gas_shadow_state sa sha /\ gas_shadow_state sb shb /\
    fn_has_code sa sb func /\ fn_has_code sha shb shadow_func
End

Definition make_elements_once_mods_def[nocompute]:
  make_elements_once_mods ce e q off dty =
    comp_bind (compile_expr ce (expr_type e) e) (\vv.
      comp_bind (emit_op ADD [Var q; Lit (n2w off)]) (\dst.
        comp_bind (unwrap_value ce vv) (\op.
          compile_store_memory ce op dst dty (lowered_value_type ce e))))
End

Definition make_slot_entry_mods_def[nocompute]:
  make_slot_entry_mods mods exps src tops cenv cx env
      (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
      h xs dty dtv ps off sa sb sha shb (es,s,G,tn) <=>
    make_elements_entry_mods mods exps src tops cenv cx env
      (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) (h::xs) ps off sa (es,s,G,tn) /\
    arg_type_fits (expr_type h) dty /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    off + type_memory_size dtv <= cap /\
    make_elements_once_mods cenv h q off dty sa = ((),sb) /\
    make_elements_once_mods (gas_shadow_env T cenv) (gas_shadow_expr h) q off dty sha = ((),shb) /\
    make_elements_code_mods func shadow_func sa sb sha shb
End

Definition make_slot_post_mods_def[nocompute]:
  make_slot_post_mods mods exps cenv cx env DF lo d ctx func st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
      h xs dtv ps off sa sb es s (H : (bool # 256 word # type_value) list # num list) res ee gf tf t <=>
    ?v. res = INL v /\ value_has_type dtv v /\ val_wf dtv v /\
      expr_sim_inv_mods mods cenv cx env ee /\
      body_const_cells_agree_mods mods cx env ee /\
      body_exprs_full_ok_mods mods exps cx xs /\ make_elements_admissible_mods cx xs ee /\
      make_elements_cut_mods DF lo d ctx func cenv cx st0
        (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sb ee t gf tf /\
      make_elements_save_mods s t /\ make_elements_prefix_mods base ps off t tf /\
      (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory dtv v (base+off) m) /\
      make_elements_window_mods base cap off (type_memory_size dtv) s t /\
      (~expr_has_effect h ==> make_elements_frame_mods cenv func base cap sa es s t)
End

Definition make_elements_post_mods_def[nocompute]:
  make_elements_post_mods mods cenv cx env DF lo d ctx func st0
      (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
      args dtvs ps off sa sb es s (H : (bool # 256 word # type_value) list # num list) res ee gf tf t <=>
    ?vs. res = INL vs /\ LIST_REL value_has_type dtvs vs /\ LIST_REL val_wf dtvs vs /\
      expr_sim_inv_mods mods cenv cx env ee /\
      make_elements_cut_mods DF lo d ctx func cenv cx st0
        (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) sb ee t gf tf /\
      make_elements_save_mods s t /\ make_elements_prefix_mods base ps off t tf /\
      (!m. mem_agree_outside tf.t_mem t.vs_memory m ==> tuple_in_memory vs dtvs (base+off) m) /\
      make_elements_window_mods base cap off (type_memory_size_list dtvs) s t /\
      (~EXISTS expr_has_effect args ==> make_elements_frame_mods cenv func base cap sa es s t)
End

Definition make_elements_contract_mods_def[nocompute]:
  make_elements_contract_mods <=>
    !args tys dtvs off ps sa sb sha shb es s G tn
     mods exps src tops cenv cx env DF lo d ctx shadow_ctx PG func shadow_func st0
     csbase ebase sbase Gbase tnbase aid base cap q.
      make_elements_entry_mods mods exps src tops cenv cx env
        (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
        (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) args ps off sa (es,s,G,tn) /\
      LIST_REL (\ty e. arg_type_fits (expr_type e) ty) tys args /\
      OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME dtvs /\
      LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys dtvs /\
      off + type_memory_size_list dtvs <= cap /\
      compile_make_tuple compile_expr cenv args tys (Var q) off sa = (Var q,sb) /\
      compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args)
        tys (Var q) off sha = (Var q,shb) /\
      make_elements_code_mods func shadow_func sa sb sha shb ==>
      make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
        (eval_exprs cx args) (es,s,G,tn)
        (make_elements_post_mods mods cenv cx env DF lo d ctx func st0
          (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) args dtvs ps off sa sb es s)
End

Definition make_slot_contract_mods_def[nocompute]:
  make_slot_contract_mods <=>
    !h xs dty dtv off ps sa sb sha shb es s G tn
     mods exps src tops cenv cx env DF lo d ctx shadow_ctx PG func shadow_func st0
     csbase ebase sbase Gbase tnbase aid base cap q.
      make_slot_entry_mods mods exps src tops cenv cx env
        (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
        (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
        h xs dty dtv ps off sa sb sha shb (es,s,G,tn) ==>
      make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
        (bind (eval_expr cx h) (read_result cx)) (es,s,G,tn)
        (make_slot_post_mods mods exps cenv cx env DF lo d ctx func st0
          (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) h xs dtv ps off sa sb es s)
End

(* The expr_vv_sim_full_mods success post at the compiler's pre-unwrap cut. *)
Definition make_slot_child_post_mods_def[nocompute]:
  make_slot_child_post_mods DF lo d ctx func cenv cx h es sa sm s G tn vv
      H (res : eval_result + exception) ee gf tf t <=>
    ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx h es sa sm s ee tv vv t /\
      vv_store_bound cx (post_value_type cenv h) (lowered_value_type cenv h)
        ee tv vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee gf tf t /\
      ptr_vv_ok cx (post_value_type cenv h) tv vv ee gf tf t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv h) /\
           ~is_bytestring_type (post_value_type cenv h) ==>
           vv_own cenv cx (post_value_type cenv h) sa sm ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ee = (INL v,ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv h) = SOME rt /\
                  eval_operand (vv_operand vv) t = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
                         val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv h) ==>
               ptr_buf_ok cenv h op gf t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv h p.ptr_operand gf t) /\
      ghost_kept_at lo cenv es sa G tn s gf tf
End

Definition make_slot_landing_mods_def[nocompute]:
  make_slot_landing_mods test <=>
    !h xs dty dtv off ps sa sb sha shb es s G tn
     mods exps src tops cenv cx env DF lo d ctx shadow_ctx PG func shadow_func st0
     csbase ebase sbase Gbase tnbase aid base cap q vv sm shm marks raw mid u g1 tt1.
      test dty /\
      make_slot_entry_mods mods exps src tops cenv cx env
        (DF,lo,d,ctx,shadow_ctx,func,shadow_func) st0
        (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q)
        h xs dty dtv ps off sa sb sha shb (es,s,G,tn) /\
      compile_expr cenv (expr_type h) h sa = (vv,sm) /\
      compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr h))
        (gas_shadow_expr h) sha = (vv,shm) /\
      gas_shadow_state sm shm /\
      (!tail. eval_expr cx h
          (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL raw,mid with gas_obs := tail)) /\
      mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) marks (OK u,g1,tt1) /\
        make_slot_child_post_mods DF lo d ctx func cenv cx h es sa sm s G tn vv
          H (INL raw) mid g1 tt1 u) ==>
      make_elements_run_mods (DF,lo,ctx,shadow_ctx,PG,func) cenv cx st0
        (read_result cx raw) (mid,u,g1,tt1)
        (make_slot_post_mods mods exps cenv cx env DF lo d ctx func st0
          (csbase,ebase,sbase,Gbase,tnbase) (aid,base,cap,q) h xs dtv ps off sa sb es s)
End

Theorem make_elements_prefix_cons_mods:
  make_elements_prefix_mods base ps off u tt /\
  val_wf rt v /\ val_footprint rt v <= type_memory_size rt /\
  (!m. mem_agree_outside tt.t_mem u.vs_memory m ==> val_in_memory rt v (base+off) m) ==>
  make_elements_prefix_mods base ((rt,v,base+off,type_memory_size rt)::ps)
    (off+type_memory_size rt) u tt
Proof
  simp[make_elements_prefix_mods_def, EVERY_MEM, FORALL_PROD] >>
  rpt strip_tac >>
  qpat_assum `!a b p n. MEM (a,b,p,n) ps ==> _`
    (drule_then strip_assume_tac) >>
  simp[] >> decide_tac
QED
