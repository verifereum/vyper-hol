(* Source-shape and counted suffix boundaries for eager internal arguments. *)
Theory bodyPtrIntCallStageOne
Ancestors
  exprPtrUnwrapStorageShape exprLowering loweringPosts bodyPtrDefs
  exprSimHyps exprSimIfExpWidenedAdapter bodyPtrIntCallConfinement
  aggregateStorePtr bodyPtrIfExpBytesPost rawCallAllocationProofPtr
  gasSummaryComposePtr vyperTypeSystem valueCopyBytes memoryLayoutDefs

(* Shared suffix proposition S (interface only; not a proof certificate).
!d ctx PG func cenv cx env e es sa a vv s0 ee tv s G tn Gi ti
 flag ty op b rty stv dtv P.
 compile_expr cenv (expr_type e) e sa = (vv,a) /\
 expr_body_pre cenv cx env e es /\
 vv_post ctx func cenv cx e es sa a s0 ee tv vv s /\
 ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
 ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
 stmt_state_rel ctx func cenv cx ee s /\
 (~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts) /\
 fn_has_code sa b func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv a /\
 sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id /\
 MAP FDOM es.scopes = MAP FDOM ee.scopes /\
 ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\
 (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
   ptr_buf_ok cenv e op0 G s) /\
 (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
   ptr_buf_ok cenv e p.ptr_operand G s) /\
 evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
 evaluate_type (get_tenv cx) (vv_type vv) = SOME stv /\
 evaluate_type (get_tenv cx) ty = SOME dtv /\
 type_widens_to (get_tenv cx) (vv_type vv) ty /\
 (!v. read_result cx tv ee = (INL v,ee) ==>
   value_has_type rty v /\ value_has_type stv v /\ value_has_type dtv v /\
   val_wf stv v /\ val_wf dtv v) /\
 (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
   ~is_word_type (post_value_type cenv e) ==>
   type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
   type_memory_size rt < 2**64) /\
 type_memory_bytes cenv ty = type_memory_size dtv /\
 MAX 32 (type_memory_bytes cenv ty) < 2**64 /\
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 P SUBSET intcall_protected cenv ee a s /\
 (if flag then unwrap_value cenv vv a = (op,b)
  else ?buf a1 src a2.
   compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) a = (buf,a1) /\
   unwrap_value cenv vv a1 = (src,a2) /\ op = buf.buf_operand /\
   (if is_word_type ty then emit_void MSTORE [op;src] a2 = ((),b)
    else if is_bytestring_type ty then
      comp_ignore_bind (compile_store_bytestring src op) (comp_return ()) a2 = ((),b)
    else compile_store_memory cenv src op ty (vv_type vv) a2 = ((),b))) ==>
 ?v H un z w.
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
    (ee,s,G,tn) [] (INL v) ee H un (OK z) /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  ~z.vs_halted /\ stmt_state_rel ctx func cenv cx ee z /\
  ghost_inv d cenv cx ee H un z /\ ghost_kept cenv es sa Gi ti s0 H un /\
  eval_operand op z = SOME w /\ op_taint un op = {} /\
  (if flag then
    expr_val_rel cx (post_value_type cenv e) v op z /\
    ptr_val_ok cx (post_value_type cenv e) v op H un z
   else ?base cap.
    cap = MAX 32 (type_memory_bytes cenv ty) /\ w = n2w base /\
    op_prov H op = SOME (base,cap) /\ base+cap < dimword(:256) /\
    FLOOKUP z.vs_allocas a.cs_next_id = SOME (base,cap) /\
    a.cs_next_id < b.cs_next_id /\ intcall_site_outside P (base,cap) /\
    (!m. mem_agree_outside un.t_mem z.vs_memory m ==>
      val_in_memory dtv v base m)) /\
  (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
  (!aid site. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP z.vs_allocas aid = SOME site) /\
  (!ft fv p base cap.
    val_wf ft fv /\ base <= p /\ p+type_memory_size ft <= base+cap /\
    ((?aid. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,cap)) \/
     (?name. local_region cenv ee.scopes s name base cap)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside un.t_mem z.vs_memory m ==> val_in_memory ft fv p m)
*)

(* Parse/typecheck the shared proposition only: this creates no HOL constant
   and claims no theorem. Keep the comment above synchronized with this check. *)
val _ = if type_of ``
!d ctx PG func cenv cx env e es sa a vv s0 ee tv s G tn Gi ti
 flag ty op b rty stv dtv P.
 compile_expr cenv (expr_type e) e sa = (vv,a) /\
 expr_body_pre cenv cx env e es /\
 vv_post ctx func cenv cx e es sa a s0 ee tv vv s /\
 ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
 ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
 stmt_state_rel ctx func cenv cx ee s /\
 (~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts) /\
 fn_has_code sa b func /\ fn_inst_ids_distinct func /\
 local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv a /\
 sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= a.cs_next_id /\
 MAP FDOM es.scopes = MAP FDOM ee.scopes /\
 ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\
 (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
   ptr_buf_ok cenv e op0 G s) /\
 (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
   ptr_buf_ok cenv e p.ptr_operand G s) /\
 evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
 evaluate_type (get_tenv cx) (vv_type vv) = SOME stv /\
 evaluate_type (get_tenv cx) ty = SOME dtv /\
 type_widens_to (get_tenv cx) (vv_type vv) ty /\
 (!v. read_result cx tv ee = (INL v,ee) ==>
   value_has_type rty v /\ value_has_type stv v /\ value_has_type dtv v /\
   val_wf stv v /\ val_wf dtv v) /\
 (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
   ~is_word_type (post_value_type cenv e) ==>
   type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
   type_memory_size rt < 2**64) /\
 type_memory_bytes cenv ty = type_memory_size dtv /\
 MAX 32 (type_memory_bytes cenv ty) < 2**64 /\
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
     sz = type_memory_size rt) fields) /\
 P SUBSET intcall_protected cenv ee a s /\
 (if flag then unwrap_value cenv vv a = (op,b)
  else ?buf a1 src a2.
   compile_alloc_buffer (MAX 32 (type_memory_bytes cenv ty)) a = (buf,a1) /\
   unwrap_value cenv vv a1 = (src,a2) /\ op = buf.buf_operand /\
   (if is_word_type ty then emit_void MSTORE [op;src] a2 = ((),b)
    else if is_bytestring_type ty then
      comp_ignore_bind (compile_store_bytestring src op) (comp_return ()) a2 = ((),b)
    else compile_store_memory cenv src op ty (vv_type vv) a2 = ((),b))) ==>
 ?v H un z w.
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
    (ee,s,G,tn) [] (INL v) ee H un (OK z) /\
  z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = LENGTH b.cs_current_insts /\
  ~z.vs_halted /\ stmt_state_rel ctx func cenv cx ee z /\
  ghost_inv d cenv cx ee H un z /\ ghost_kept cenv es sa Gi ti s0 H un /\
  eval_operand op z = SOME w /\ op_taint un op = {} /\
  (if flag then
    expr_val_rel cx (post_value_type cenv e) v op z /\
    ptr_val_ok cx (post_value_type cenv e) v op H un z
   else ?base cap.
    cap = MAX 32 (type_memory_bytes cenv ty) /\ w = n2w base /\
    op_prov H op = SOME (base,cap) /\ base+cap < dimword(:256) /\
    FLOOKUP z.vs_allocas a.cs_next_id = SOME (base,cap) /\
    a.cs_next_id < b.cs_next_id /\ intcall_site_outside P (base,cap) /\
    (!m. mem_agree_outside un.t_mem z.vs_memory m ==>
      val_in_memory dtv v base m)) /\
  (!x. not_fresh_at a x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint un (Var x) = op_taint tn (Var x)) /\
  (!aid site. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME site ==>
    FLOOKUP z.vs_allocas aid = SOME site) /\
  (!ft fv p base cap.
    val_wf ft fv /\ base <= p /\ p+type_memory_size ft <= base+cap /\
    ((?aid. aid < a.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (base,cap)) \/
     (?name. local_region cenv ee.scopes s name base cap)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside un.t_mem z.vs_memory m ==> val_in_memory ft fv p m)
`` = bool then () else raise Fail "suffix interface is not boolean";
