(* A typed memory-path write reconstructs the locals' robust ghost. *)
Theory placeMemoryGhostPtr
Ancestors
  placeMemoryRobustPtr bodyPtrPopNestedLiveGhost bodyPtrDefs
  compileEnv loweringStateRelDefs venomState vyperState vyperTyping finite_map

Theorem memory_place_write_ghost_ptr:
  !d ce cx es ff G tn s fn id path v old root cap bw k ptv
    H tm t sa.
    ghost_inv d ce cx es G tn s /\ local_ptrs_rel fn ce es.scopes s /\
    lookup_scopes id es.scopes = SOME old /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) cap) /\
    lookup_var root s = SOME bw /\
    value_has_type old.type old.value /\ well_formed_type_value old.type /\
    mem_path_offset old.type path = SOME (k,ptv) /\ value_has_type ptv v /\
    write_place cx (MemoryPlace id path) v es = (INL (),ff) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory ptv v (w2n bw+k) m) /\
    (!i. ~(w2n bw+k <= i /\ i < w2n bw+k+type_memory_size ptv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    local_ptrs_reserved ce sa /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    stor_taint_ok cx tm t ==>
    ghost_inv d ce cx ff H tm t
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`d`, `ce`, `cx`, `es`, `ff`, `G`, `tn`, `s`,
    `fn`, `id`, `path`, `v`, `old`, `root`, `cap`, `bw`, `k`, `ptv`,
    `tm`, `t.vs_memory`] memory_place_write_locals_robust_ptr) >>
  impl_tac >- simp[] >> strip_tac >>
  irule pop_header_ghost_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >> simp[] >>
  first_assum ACCEPT_TAC
QED
