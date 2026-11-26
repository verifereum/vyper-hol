(* A constructor code pointer reads from the old memory footprint even
   after ALLOCA taints the new destination. *)
Theory bodyExtKeywordDefaultAllocCtorMods
Ancestors
  logValueFramePtr valueTypingMemoryProps exprSimProps loweringPosts
  vyperStorageFootprint venomMemDefs context venomState words arithmetic

Theorem ext_kw_default_alloc_ctor_payload_mods:
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?a. read_result cx tv ee = (INL a,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt a (w2n w) mem)) /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  value_has_type pt v /\ lo <= s.vs_alloca_next /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  u.vs_memory = s.vs_memory /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?a. read_result cx tv ee = (INL a,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
          val_in_memory rt a (w2n w) mem))
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> ?a. read_result _ _ _ = _ /\ _` mp_tac >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `a` strip_assume_tac) >>
  `a = v` by fs[] >>
  qpat_x_assum `a = v` SUBST_ALL_TAC >>
  qexists `v` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `rt = pt` by fs[] >>
  qpat_x_assum `rt = pt` SUBST_ALL_TAC >>
  qpat_x_assum `!rt w. _ /\ _ ==> _` (qspecl_then [`pt`,`w`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule_then assume_tac value_has_type_memory_wf >>
  drule_then assume_tac val_footprint_le >>
  rpt strip_tac >>
  irule robust_val_in_memory_footprint_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`s.vs_memory`, `u.vs_memory`, `tn.t_mem`, `ta.t_mem`] >>
  simp[] >> rpt strip_tac >>
  `i < s.vs_alloca_next` by decide_tac >>
  qpat_assum `!i. i < _ ==> (i IN ta.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]
QED
