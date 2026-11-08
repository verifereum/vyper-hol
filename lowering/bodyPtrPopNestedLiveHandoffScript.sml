Theory bodyPtrPopNestedLiveHandoff
Ancestors
  bodyPtrPopNestedLiveSource bodyPtrPopTargetDefs exprSimPopNestedLocalMemory
  bodyPtrPopMemoryHeader bodyPtrDefs valueEncoding venomState
  exprSimPopNestedLocalHandoff ptrDiscipline
  words finite_map

(* Restrict robust encoding to a current mutable subvalue. *)
Theorem pop_mutable_path_robust:
  !path tv a b k ct child s tm.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ val_wf tv a /\
    mem_path_offset tv path = SOME (k,ct) /\
    evaluate_subscripts tv a path = INL child /\
    (!mem. mem_agree_outside tm s.vs_memory mem ==>
           val_in_memory tv a b mem) ==>
    !mem. mem_agree_outside tm s.vs_memory mem ==>
          val_in_memory ct child (b+k) mem
Proof
  rpt strip_tac >>
  `val_in_memory tv a b mem` by metis_tac[] >>
  qabbrev_tac `ms = s with vs_memory := mem` >>
  `val_in_memory tv a b ms.vs_memory` by simp[Abbr `ms`] >>
  drule_all val_in_memory_mutable_path >> simp[Abbr `ms`]
QED

Theorem pop_local_path_robust:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\
  mutable_place_path entry.type path /\
  value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ val_wf entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,ct) /\
  evaluate_subscripts entry.type entry.value path = INL child ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory ct child (w2n b+k) mem
Proof
  rpt strip_tac >> irule pop_mutable_path_robust >>
  qexistsl_tac [`entry.value`, `path`, `s`, `tn.t_mem`, `entry.type`] >>
  simp[] >> fs[ghost_inv_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem pop_local_path_header_clean:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\
  mutable_place_path entry.type path /\
  value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ val_wf entry.type entry.value /\
  mem_path_offset entry.type path = SOME (k,ArrayTV tv (Dynamic cap)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  w2n a = w2n b+k ==>
  !i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem` by
    (metis_tac[pop_local_path_robust]) >>
  drule pop_robust_dynarray_header_clean >> simp[]
QED

Theorem pop_memory_target_ptr_handoff:
  target_post ctx func cenv cx es sa sb s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) (hdr,loc,pt) s /\
  ghost_inv d cenv cx mid G tn s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path)) (hdr,loc,pt) G tn s /\
  lookup_scopes id mid.scopes = SOME entry /\
  cenv.ce_var_type id = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME entry.type ==>
  ?p b sz k tv w out.
    loc = SOME LocMemory /\ pt = SOME (value_type_place (Type ty)) /\
    hdr = Var out /\ not_fresh_at sb out /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME b /\ lookup_var out s = SOME w /\
    w = b + n2w k /\ w2n w = w2n b+k /\
    mem_path_offset entry.type path = SOME (k,tv) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    val_wf entry.type entry.value /\
    type_memory_size entry.type <= sz /\
    k + type_memory_size tv <= sz /\ w2n b+sz < dimword (:256) /\
    ptr_covers G tn out s (type_memory_size tv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory entry.type entry.value (w2n b) mem)
Proof
  strip_tac >> drule_all memory_target_encoding_handoff >> strip_tac >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n b) mem` by
    (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  `op_taint tn hdr = {} /\ op_prov G hdr = FLOOKUP G p` by
    (fs[target_ptr_ok_def] >> metis_tac[]) >>
  `?out. hdr = Var out` by
    (Cases_on `hdr` >> gvs[ptr_covers_def, op_prov_def]) >>
  gvs[] >>
  `ptr_covers G tn out s (type_memory_size tv)` by
    (gvs[ptr_covers_def, op_prov_def, eval_operand_def] >>
     rename1 `FLOOKUP G p = SOME (site,capacity)` >>
     qexistsl_tac [`site`, `capacity`] >> simp[] >> decide_tac) >>
  gvs[eval_operand_def]
QED
