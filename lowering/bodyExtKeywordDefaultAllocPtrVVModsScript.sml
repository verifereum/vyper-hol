Theory bodyExtKeywordDefaultAllocPtrVVMods
Ancestors
  bodyPtrIfExpAllocSource bodyPtrBopRepresentationFrame revertReasonPrefixPtr
  bodyPtrDefs valueTypingMemoryProps ptrDiscipline venomState context

(* The allocation may add taint at its destination, but not on any byte
   occupied by the reached stack or memory value below the old frontier. *)
Theorem ext_kw_default_alloc_ptr_vv_mods:
  ptr_vv_ok cx ty raw vv ee G tn s /\
  stmt_state_rel H ctx func ce cx ee s /\ vv_at ce cx ty sa sm ee raw vv s /\
  ~is_word_type ty /\ read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME pt /\ value_has_type pt v /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty raw vv ee Ga ta u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!tag p. vv = LocatedValue tag p ==> p.ptr_location = LocMemory) ==>
    ptr_mem_ok cx ty v (vv_operand vv) Ga ta u` by
    (strip_tac >>
     `ptr_mem_ok cx ty v (vv_operand vv) G tn s` by
       (Cases_on `vv` >> gvs[ptr_vv_ok_def,ptr_val_ok_def,vv_operand_def]) >>
     `!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x` by
       (rpt strip_tac >> fs[op_prov_def]) >>
     `val_wf pt v` by metis_tac[value_has_type_memory_wf] >>
     `!w i. eval_operand (vv_operand vv) s = SOME w /\ w2n w <= i /\
             i < w2n w + val_footprint pt v ==> i < s.vs_alloca_next` by
       (rpt strip_tac >> drule_all vv_at_memory_footprint >> simp[]) >>
     irule bop_ptr_mem_ok_frame >> qexistsl_tac [`G`,`s`,`tn`,`pt`] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     `i < s.vs_alloca_next` by (first_x_assum irule >> metis_tac[]) >>
     metis_tac[]) >>
  Cases_on `vv`
  >- gvs[ptr_vv_ok_def,ptr_val_ok_def,vv_operand_def] >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- gvs[ptr_vv_ok_def,vv_operand_def] >>
  gvs[vv_operand_def] >> irule ptr_vv_ok_nonmemory_frame >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`s`,`tn`] >> asm_rewrite_tac[]
QED
