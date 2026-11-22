(* Request-prefix companion to bodyFullSubscriptCopiedBind. *)
Theory s1PrefixSubscriptCopiedBind
Ancestors
  s1PrefixPreds bodyFullSubscriptCopiedBind s1PrefixDefs

Theorem subscript_copied_bind_caller_frames_prefix:
  !frames cx ann obj idx DF lo d PG tops ctx shadow_ctx func shadow_func ce env ty es et bd.
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_full_ok cx idx) /\
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_prefix_ok cx idx) /\
  body_expr_full_ok cx obj /\
  body_expr_prefix_ok cx obj /\
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  subscript_reads_base cx obj idx /\
  copies_subscript_base ce obj idx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  post_value_type ce obj = expr_type obj /\
  (!st0 sa sm sc bvv cvv shm s0 G0 tn0 gs raw mid saved s G1 tn1.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ gas_shadow_state sm shm /\
       fn_has_code sm sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
       (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s) /\
       vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
       ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G1 tn1 s /\
       (!t op. bvv = StackValue t op ==> ptr_buf_ok ce obj op G1 s) /\
       (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce obj p.ptr_operand G1 s) /\
       (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
         ?v. read_result cx raw mid = (INL v,mid) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
                  eval_operand (vv_operand bvv) s = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             !m. mem_agree_outside tn1.t_mem s.vs_memory m ==> val_in_memory rt v (w2n w) m) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
       ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
       s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
       ?u Gc tnc q w atv.
         cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
         evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\ val_wf atv saved /\
         value_has_type atv saved /\ lookup_var q u = SOME w /\ not_fresh_at sc q /\
         ptr_covers Gc tnc q u (type_memory_size atv) /\
         (!m. mem_agree_outside tnc.t_mem u.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
         vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (s,G1,tn1) [] (OK u,Gc,tnc) /\
           stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
           ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) /\
         ghost_kept_at lo ce es sa G0 tn0 s0 Gc tnc /\ return_buf_frame d ce sc u /\
         local_ptrs_reserved ce sc /\ alloca_history func u /\ allocas_from lo u /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
         (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
             FLOOKUP Gc x = FLOOKUP G1 x /\ op_taint tnc (Var x) = op_taint tn1 (Var x)) /\
         (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
         u.vs_labels = s.vs_labels /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
         u.vs_inst_idx = LENGTH sc.cs_current_insts /\
         (frames ==> wb_frame ce es mid sa s0 u /\
            (~expr_has_effect obj ==> pure_frame ce func es sa s0 u))) /\
  (!st0 sa sm sc si sb bvv cvv vv iop dst s0 G0 tn0 gs raw mid saved s gc ic u
       key fin z Gi tni q w atv.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ic) = (INL key,fin) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
       lower_value compile_expr ce ty idx sc = (iop,si) /\
       compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
       cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
       vv = LocatedValue ann (mk_ptr dst LocMemory) /\
       compile_array_subscript (Var q) iop
         (case bd of Fixed _ => F | Dynamic _ => T)
         (case bd of Fixed n => n | Dynamic _ => 0)
         (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
         (is_signed_type (expr_type idx))
         (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
       fn_has_code si sb func /\ fn_inst_ids_distinct func /\
       cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
       local_ptrs_reserved ce si /\ local_ptrs_reserved ce sa /\
       (frames ==> wb_frame ce es fin sa s0 z /\
          (~expr_has_effect (Subscript ann obj idx) ==> pure_frame ce func es sa s0 z)) /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 fin.storage_trace /\
       fin.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = si.cs_current_bb /\
       z.vs_inst_idx = LENGTH si.cs_current_insts /\ alloca_history func z /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       (!H. valid_horizon cx st0 H fin.storage_trace ==>
          stmt_state_rel H ctx func ce cx es s0 /\
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          expr_post H ctx func ce cx idx mid sc si u fin key iop z /\
          ghost_inv_at (DF H) lo d ce cx fin Gi tni z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gi tni /\
       ptr_val_ok cx (post_value_type ce idx) key iop Gi tni z /\
       evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
       val_wf atv saved /\ value_has_type atv saved /\
       lookup_var q z = SOME w /\ not_fresh_at si q /\ ptr_covers Gi tni q z (type_memory_size atv) /\
       (!m. mem_agree_outside tni.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
       vv_own ce cx (ArrayT et bd) sm sc fin (Value saved) cvv z ==>
       gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
         (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) (fin,z,Gi,tni)
         (\H res ee G tn t. ?tv. res = INL tv /\
           vv_post H ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
           vv_store_bound cx (post_value_type ce (Subscript ann obj idx))
             (lowered_value_type ce (Subscript ann obj idx)) ee tv vv t /\
           t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
           s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
           ptr_vv_ok cx (post_value_type ce (Subscript ann obj idx)) tv vv ee G tn t /\
           (!v. tv = Value v /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
             ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) ==>
             vv_own ce cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv t /\
             (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
           (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?v. read_result cx tv ee = (INL v,ee) /\
              !rt base. evaluate_type (get_tenv cx) (post_value_type ce (Subscript ann obj idx)) = SOME rt /\
                        eval_operand (vv_operand vv) t = SOME base ==>
                w2n base + type_memory_size rt <= lo /\
                (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt v (w2n base) m)) /\
           (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) ==>
             ptr_buf_ok ce (Subscript ann obj idx) op G t) /\
           (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok ce (Subscript ann obj idx) p.ptr_operand G t) /\
           ghost_kept_at lo ce es sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty (Subscript ann obj idx) es
Proof
  cheat
QED

Theorem subscript_copied_bind_prefix:
  !cx ann obj idx DF lo d PG tops ctx shadow_ctx func shadow_func ce env ty es et bd.
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_full_ok cx idx) /\
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_prefix_ok cx idx) /\
  body_expr_full_ok cx obj /\
  body_expr_prefix_ok cx obj /\
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  subscript_reads_base cx obj idx /\
  copies_subscript_base ce obj idx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  post_value_type ce obj = expr_type obj /\
  (!st0 sa sm sc bvv cvv shm s0 G0 tn0 gs raw mid saved s G1 tn1.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ gas_shadow_state sm shm /\
       fn_has_code sm sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
       (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s) /\
       vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
       ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G1 tn1 s /\
       (!t op. bvv = StackValue t op ==> ptr_buf_ok ce obj op G1 s) /\
       (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce obj p.ptr_operand G1 s) /\
       (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
         ?v. read_result cx raw mid = (INL v,mid) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
                  eval_operand (vv_operand bvv) s = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             !m. mem_agree_outside tn1.t_mem s.vs_memory m ==> val_in_memory rt v (w2n w) m) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
       ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
       s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
       ?u Gc tnc q w atv.
         cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
         evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\ val_wf atv saved /\
         value_has_type atv saved /\ lookup_var q u = SOME w /\ not_fresh_at sc q /\
         ptr_covers Gc tnc q u (type_memory_size atv) /\
         (!m. mem_agree_outside tnc.t_mem u.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
         vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (s,G1,tn1) [] (OK u,Gc,tnc) /\
           stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
           ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) /\
         ghost_kept_at lo ce es sa G0 tn0 s0 Gc tnc /\ return_buf_frame d ce sc u /\
         local_ptrs_reserved ce sc /\ alloca_history func u /\ allocas_from lo u /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
         (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
             FLOOKUP Gc x = FLOOKUP G1 x /\ op_taint tnc (Var x) = op_taint tn1 (Var x)) /\
         (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
         u.vs_labels = s.vs_labels /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
         u.vs_inst_idx = LENGTH sc.cs_current_insts) /\
  (!st0 sa sm sc si sb bvv cvv vv iop dst s0 G0 tn0 gs raw mid saved s gc ic u
       key fin z Gi tni q w atv.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ic) = (INL key,fin) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
       lower_value compile_expr ce ty idx sc = (iop,si) /\
       compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
       cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
       vv = LocatedValue ann (mk_ptr dst LocMemory) /\
       compile_array_subscript (Var q) iop
         (case bd of Fixed _ => F | Dynamic _ => T)
         (case bd of Fixed n => n | Dynamic _ => 0)
         (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
         (is_signed_type (expr_type idx))
         (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
       fn_has_code si sb func /\ fn_inst_ids_distinct func /\
       cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
       local_ptrs_reserved ce si /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 fin.storage_trace /\
       fin.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = si.cs_current_bb /\
       z.vs_inst_idx = LENGTH si.cs_current_insts /\ alloca_history func z /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       (!H. valid_horizon cx st0 H fin.storage_trace ==>
          stmt_state_rel H ctx func ce cx es s0 /\
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          expr_post H ctx func ce cx idx mid sc si u fin key iop z /\
          ghost_inv_at (DF H) lo d ce cx fin Gi tni z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gi tni /\
       ptr_val_ok cx (post_value_type ce idx) key iop Gi tni z /\
       evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
       val_wf atv saved /\ value_has_type atv saved /\
       lookup_var q z = SOME w /\ not_fresh_at si q /\ ptr_covers Gi tni q z (type_memory_size atv) /\
       (!m. mem_agree_outside tni.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
       vv_own ce cx (ArrayT et bd) sm sc fin (Value saved) cvv z ==>
       gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
         (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) (fin,z,Gi,tni)
         (\H res ee G tn t. ?tv. res = INL tv /\
           vv_post H ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
           vv_store_bound cx (post_value_type ce (Subscript ann obj idx))
             (lowered_value_type ce (Subscript ann obj idx)) ee tv vv t /\
           t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
           s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
           ptr_vv_ok cx (post_value_type ce (Subscript ann obj idx)) tv vv ee G tn t /\
           (!v. tv = Value v /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
             ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) ==>
             vv_own ce cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv t /\
             (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
           (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?v. read_result cx tv ee = (INL v,ee) /\
              !rt base. evaluate_type (get_tenv cx) (post_value_type ce (Subscript ann obj idx)) = SOME rt /\
                        eval_operand (vv_operand vv) t = SOME base ==>
                w2n base + type_memory_size rt <= lo /\
                (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt v (w2n base) m)) /\
           (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) ==>
             ptr_buf_ok ce (Subscript ann obj idx) op G t) /\
           (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok ce (Subscript ann obj idx) p.ptr_operand G t) /\
           ghost_kept_at lo ce es sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty (Subscript ann obj idx) es
Proof
  cheat
QED
