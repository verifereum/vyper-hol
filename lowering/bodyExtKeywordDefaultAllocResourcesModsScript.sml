(* Resources for unwrapping the original value after destination allocation. *)
Theory bodyExtKeywordDefaultAllocResourcesMods
Ancestors
  bodyFullPostsMods bodyExtKeywordDefaultAllocPtrVVMods
  bodyExtKeywordDefaultAllocCtorMods exprSimMemDefs exprSimCopy
  logValueFramePtr ptrDiscipline venomState context

Theorem ext_kw_default_alloc_unwrap_resources_mods:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
  ~is_word_type (post_value_type ce e) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  value_has_type ptv v /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?a. read_result cx raw ee = (INL a,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt a (w2n w) mem)) /\
  local_ptrs_reserved ce sm /\ lo <= s.vs_alloca_next /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s) /\
  u.vs_memory = s.vs_memory /\ ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  (!x. not_fresh_at sm x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint ta (Var x) = op_taint tn (Var x)) ==>
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv u /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee Ga ta u /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x Ga u) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand Ga u) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?a. read_result cx raw ee = (INL a,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
          val_in_memory rt a (w2n w) mem)) /\
  (!name b len. local_region ce ee.scopes u name b len <=>
                local_region ce ee.scopes s name b len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- (drule_all vv_store_bound_frame_mem_src >> simp[]) >>
  conj_tac >-
   (`u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
     u.vs_call_ctx = s.vs_call_ctx` by
      (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
                             vs_alloca_next := _; vs_inst_idx := _|> = s`
         (SUBST1_TAC o SYM) >> simp[]) >>
    qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
    drule_all ext_kw_default_alloc_ptr_vv_mods >> simp[]) >>
  `(ptr_buf_ok ce e (vv_operand vv) G s ==>
    ptr_buf_ok ce e (vv_operand vv) Ga u)` by
   (strip_tac >> irule ptr_buf_ok_frame >> qexistsl [`G`,`s`] >>
    asm_rewrite_tac[] >> rpt strip_tac >> fs[op_prov_def]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> fs[vv_operand_def]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> fs[vv_operand_def]) >>
  conj_tac >-
    (match_mp_tac (Q.INST [`pt` |-> `ptv`] ext_kw_default_alloc_ctor_payload_mods) >>
     asm_rewrite_tac[]) >>
  rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `sm` >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED
