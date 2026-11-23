(* The field's VV was produced at sm; its read starts after the destination
   ADD at sn. Dispatch the shared readers without changing the VV's index. *)
Theory entryCreateStructLitRead
Ancestors
  entryCreateFocusSpec bodyFullUnwrap bodyFullStructLitAdd emitHelperProps
  exprSimUnwrap bodyPtrDefs loweringPosts loweringStateRelDefs
  venomState vyperStorageFootprint ASCIInumbers

(* This is the ordinary unwrap input, apart from the two cursor bounds and
   the constructor frame, which the field ADD supplies separately. *)
Definition structlit_read_pre_def:
  structlit_read_pre (DF,lo,d,ctx,func) (ce,cx,ty,e,rty,st0)
      (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) <=>
    compile_expr ce ty e si = (vv,sm) /\
    unwrap_value ce vv sn = (op,su) /\
    local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id /\
    fn_has_code sn su func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
      ~is_word_type (post_value_type ce e) ==>
      type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
      type_memory_size rt < 2**64) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func ce cx e es si sm s0 ee tv vv t /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t) /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
    (!ann op0. vv = StackValue ann op0 /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op0 G t) /\
    (!ann p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G t) /\
    ghost_kept_at lo ce es si Gi ti s0 G tn /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x)
End

Definition structlit_read_ctor_def:
  structlit_read_ctor ce cx e ee tv vv lo (t,tn) <=>
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) t = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))
End

Definition structlit_read_post_def:
  structlit_read_post (DF,lo,d,explicit,ctx,func,PG) (ce,cx,e,st0)
      (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) (v,z,G',tn') <=>
    create_operand_full_scope sn su explicit ctx func t [] (OK z) /\
    read_result cx tv ee = (INL v,ee) /\
    (!ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
      (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
       p.ptr_location = LocCode) ==>
      vv_own ce cx (post_value_type ce e) sn su ee (Value v)
        (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G,tn) [] (OK z,G',tn') /\
      expr_post H ctx func ce cx e es si su s0 ee v op z /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' z) /\
    (~is_word_type (post_value_type ce e) ==>
     vv_at ce cx (post_value_type ce e) si su ee tv
       (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) z) /\
    (~is_word_type (post_value_type ce e) ==>
     vv_at ce cx (post_value_type ce e) si sm ee tv
       (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) z \/
     vv_at ce cx (post_value_type ce e) sn su ee tv
       (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ t.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type ce e) v op G' tn' z /\
    (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G' z) /\
    (~is_word_type (post_value_type ce e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo ce es si Gi ti s0 G' tn' /\
    (!x. not_fresh_at sn x ==>
      lookup_var x z = lookup_var x t /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame ce ee ee sn t z /\
    ghost_kept_at lo ce ee sn G tn t G' tn'
End

(* Each branch law can be supplied once by the corresponding common unwrap
   site. It is uniform in the compiler cursors and the target/ghost input. *)
Definition structlit_read_site_rule_def:
  structlit_read_site_rule guard (DF,lo,d,explicit,ctx,func,PG)
      (ce,cx,ty,e,rty,st0) (es,s0,Gi,ti,ee,tv) <=>
    !si sm sn su vv op t G tn.
      guard vv /\
      structlit_read_pre (DF,lo,d,ctx,func) (ce,cx,ty,e,rty,st0)
        (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) /\
      sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
      structlit_read_ctor ce cx e ee tv vv lo (t,tn) ==>
      create_operand_cut sn su explicit ctx func (cx_tops cx) cx st0
        (read_result cx tv) (ee,t) /\
      ?v z G' tn'.
        structlit_read_post (DF,lo,d,explicit,ctx,func,PG) (ce,cx,e,st0)
          (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) (v,z,G',tn')
End

Theorem structlit_read_not_calldata[local]:
  structlit_read_pre (DF,lo,d,ctx,func) (ce,cx,ty,e,rty,st0)
    (si,sm,sn,su,LocatedValue ann p,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) ==>
  p.ptr_location <> LocCalldata
Proof
  simp[structlit_read_pre_def] >> strip_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  fs[storage_trace_domain_def, vv_post_calldata]
QED

Theorem structlit_read_ctor_add[local]:
  structlit_read_ctor ce cx e ee tv vv lo (u,un) /\
  (!x. vv_operand vv = Var x ==> lookup_var x t = lookup_var x u) /\
  t.vs_labels = u.vs_labels /\ t.vs_memory = u.vs_memory /\ tn.t_mem = un.t_mem ==>
  structlit_read_ctor ce cx e ee tv vv lo (t,tn)
Proof
  strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) u` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def]) >>
  fs[structlit_read_ctor_def]
QED

Theorem structlit_shifted_read_site:
  structlit_read_site_rule
    (\vv. case vv of StackValue _ _ => T
                 | LocatedValue ann p => is_word_type ann \/ p.ptr_location = LocMemory)
    (DF,lo,d,explicit,ctx,func,PG) (ce,cx,ty,e,rty,st0) (es,s0,Gi,ti,ee,tv) /\
  structlit_read_site_rule
    (\vv. ?ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
       (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient))
    (DF,lo,d,explicit,ctx,func,PG) (ce,cx,ty,e,rty,st0) (es,s0,Gi,ti,ee,tv) /\
  structlit_read_site_rule
    (\vv. ?ann p. vv = LocatedValue ann p /\ ~is_word_type ann /\
       p.ptr_location = LocCode)
    (DF,lo,d,explicit,ctx,func,PG) (ce,cx,ty,e,rty,st0) (es,s0,Gi,ti,ee,tv) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var out,sn) /\
  structlit_read_pre (DF,lo,d,ctx,func) (ce,cx,ty,e,rty,st0)
    (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) /\
  structlit_read_ctor ce cx e ee tv vv lo (u,un) /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u) /\
  t.vs_labels = u.vs_labels /\ t.vs_memory = u.vs_memory /\ tn.t_mem = un.t_mem ==>
  create_operand_cut sn su explicit ctx func (cx_tops cx) cx st0
    (read_result cx tv) (ee,t) /\
  ?v z G' tn'.
    structlit_read_post (DF,lo,d,explicit,ctx,func,PG) (ce,cx,e,st0)
      (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) (v,z,G',tn') /\
    lookup_var out z = lookup_var out t /\
    (!n. ptr_covers G tn out t n ==> ptr_covers G' tn' out z n)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
   not_fresh_at sn out` by
    (gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `structlit_read_ctor ce cx e ee tv vv lo (t,tn)` by
    (irule structlit_read_ctor_add >> simp[] >>
     qexistsl_tac [`u`,`un`] >> simp[] >>
     fs[structlit_read_pre_def] >> metis_tac[]) >>
  `create_operand_cut sn su explicit ctx func (cx_tops cx) cx st0
     (read_result cx tv) (ee,t) /\
   ?v z G' tn'.
     structlit_read_post (DF,lo,d,explicit,ctx,func,PG) (ce,cx,e,st0)
       (si,sm,sn,su,vv,op) (es,s0,Gi,ti,ee,tv) (t,G,tn) (v,z,G',tn')` by
    (Cases_on `vv` >>
     TRY (rename1 `LocatedValue ann p` >>
          `p.ptr_location <> LocCalldata` by metis_tac[structlit_read_not_calldata] >>
          Cases_on `p.ptr_location` >> Cases_on `is_word_type ann`) >>
     fs[structlit_read_site_rule_def] >>
     first_assum (fn law =>
       qpat_assum `structlit_read_pre _ _ _ _ _`
         (mp_then (Pat `structlit_read_pre _ _ _ _ _`) mp_tac law) >>
       simp[] >> NO_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`v`,`z`,`G'`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[structlit_read_post_def] >>
  qpat_assum `!x. not_fresh_at sn x ==> _` (qspec_then `out` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  gvs[ptr_covers_def]
QED
