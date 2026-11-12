(* unwrap_value on one joint path: the GAS provenance, the memory check
   and the pointer ghosts of forcing a compiled expression's value, at any
   dead set D and fixed region [0, lo), constructors included.

   TOP-LEVEL:
     unwrap_value_origin_ptr -- forcing started at sb, at or after the
       state sm where the expression's value was produced
     unwrap_value_origin_ptr_here -- forcing started where the value's
       post holds; one case per lemma of the bodyFullUnwrap* theories *)
Theory bodyFullUnwrap
Ancestors
  bodyFullUnwrapIdentity bodyFullUnwrapWord bodyFullUnwrapSlot
  bodyFullUnwrapCodeCopy exprPtrUnwrapMarked exprSimCalldataSlice
  fragGasOriginPtr bodyPtrDefs loweringPosts exprSimMemDefs exprLowering
  exprLoweringProps freshWrites compileEnv context

Theorem vv_at_end_mono:
  sm.cs_next_id <= sb.cs_next_id /  vv_at cenv cx ty sa sm es tv vv u ==>
  vv_at cenv cx ty sa sb es tv vv u
Proof
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP u.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[])
  >>~- ([`local_region cenv es.scopes u n b sz`],
        disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

Theorem vv_own_end_mono:
  sm.cs_next_id <= sb.cs_next_id /  vv_own cenv cx ty sa sm es tv vv u ==>
  vv_own cenv cx ty sa sb es tv vv u
Proof
  Cases_on `vv` >> simp[vv_own_def, expr_val_own_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP u.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

(* A value's post at sm holds at any later compile state: the allocations
   it may sit in were made before sm's next id. *)
Theorem vv_post_end_mono:
  sm.cs_next_id <= sb.cs_next_id /  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s ==>
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s
Proof
  simp[vv_post_def] >> metis_tac[vv_at_end_mono, vv_own_end_mono]
QED

Theorem unwrap_value_origin_ptr_here:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    read_result cx tv ee = (INL v, ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (OK z, H, tf) /\
    expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z /\
    ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s H tf
Proof
  strip_tac >>
  `(?t0 op0. vv = StackValue t0 op0) \/ (?t p. vv = LocatedValue t p)` by
    (Cases_on `vv` >> simp[])
  >- (pop_assum strip_assume_tac >>
      drule_all unwrap_stack_origin_ptr >> disch_then ACCEPT_TAC) >>
  pop_assum strip_assume_tac >>
  `p.ptr_location = LocMemory \/
   (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) \/
   p.ptr_location = LocCode` by
    (`p.ptr_location <> LocCalldata` by
       (strip_tac >> gvs[] >> metis_tac[vv_post_not_calldata]) >>
     Cases_on `p.ptr_location` >> fs[]) >>
  qpat_x_assum `p.ptr_location = LocMemory \/ _`
    (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 assume_tac assume_tac)) >>
  Cases_on `is_word_type t`
  >~ [`p.ptr_location = LocMemory`, `~is_word_type t`]
  >- (drule_all unwrap_memory_origin_ptr >> disch_then ACCEPT_TAC)
  >~ [`p.ptr_location = LocMemory`]
  >- (drule_all unwrap_memory_word_origin_ptr >> disch_then ACCEPT_TAC)
  >~ [`p.ptr_location = LocCode`, `~is_word_type t`]
  >- (drule_all unwrap_code_copy_origin_ptr >> disch_then ACCEPT_TAC)
  >~ [`p.ptr_location = LocCode`]
  >- (drule_all unwrap_code_word_origin_ptr >> disch_then ACCEPT_TAC)
  >~ [`~is_word_type t`]
  >- (drule_all unwrap_slot_copy_origin_ptr >> disch_then ACCEPT_TAC)
  >> drule_all unwrap_slot_word_origin_ptr >> disch_then ACCEPT_TAC
QED

(* Forcing may start after allocations made since the value was produced
   (an IfExp arm's), so at any sb after sm. *)
Theorem unwrap_value_origin_ptr:
  compile_expr cenv ty e sa = (vv,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    read_result cx tv ee = (INL v, ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (OK z, H, tf) /\
    expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z /\
    ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s H tf
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e es sa sb s0 ee tv vv s` by
    metis_tac[vv_post_end_mono] >>
  `local_ptrs_reserved cenv sb` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[not_fresh_at_mono] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    simp[] >>
  drule_all unwrap_value_origin_ptr_here >> disch_then ACCEPT_TAC
QED
