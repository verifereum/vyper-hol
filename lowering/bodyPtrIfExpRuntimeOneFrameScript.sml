Theory bodyPtrIfExpRuntimeOneFrame
Ancestors bodyPtrIfExpRuntimeOne bodyPtrIfExpMaterializeWord
  bodyPtrAttributeAdd exprSimPtrProps exprSimCopy exprSimStorageCopy
  bodyPtrDefs venomState ptrDiscipline finite_map pred_set words arithmetic
  ghostPcTransportPtr compileEnv venomInst valueEncoding bodyPtrIfExpBytesEndpoint

(* The producer's restored-cursor runtime frame hides all instruction details. *)
Theorem ifexp_runtime_fresh_inv:
  ghost_inv rty ce cx ee G tn s /\ local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  copy_runtime_frame ca s cb (r with vs_inst_idx := s.vs_inst_idx) /\
  r.vs_memory = s.vs_memory /\ tr.t_mem = tn.t_mem /\
  tr.t_stor = tn.t_stor /\ tr.t_trans = tn.t_trans /\ tr.t_imm = tn.t_imm /\
  (!x. not_fresh_at ca x ==> lookup_var x r = lookup_var x s /\
    FLOOKUP J x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x)) ==>
  ghost_inv rty ce cx ee J tr r
Proof
  strip_tac >>
  `r.vs_call_ctx = s.vs_call_ctx /\ r.vs_accounts = s.vs_accounts /\
   r.vs_transient = s.vs_transient` by
    (qpat_x_assum `copy_runtime_frame _ _ _ _` mp_tac >>
     simp[copy_runtime_frame_def] >> strip_tac >>
     qpat_x_assum `copy_static _ = _` mp_tac >>
     simp[copy_static_def, venom_state_component_equality]) >>
  irule ghost_inv_fresh_frame >>
  qexistsl_tac [`G`, `ee`, `s`, `ca`, `tn`] >> simp[]
QED

(* Clean DLOAD stores only remove taint, so ghost_kept needs no protected
   interval disjointness premise; current local values still need separation. *)
Theorem ifexp_runtime_one_ptr:
  immutable_copy_one F imm src (Var root) off ca = ((),cb) /\
  fn_has_code ca cb fn /\ copy_old_operand ca src /\
  copy_old_operand ca (Var root) /\ eval_operand src s = SOME a /\
  lookup_var root s = SOME d /\ op_taint tn src = {} /\
  ptr_covers G tn root s capacity /\ off+32 <= capacity /\
  w2n d+capacity < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa0 G0 tn0 s0 G tn /\
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x. not_fresh_at sa0 x ==> not_fresh_at ca x) /\
  (!name entry p sz v. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME v ==>
    val_wf entry.type entry.value /\
    (w2n v+type_memory_size entry.type <= w2n d \/ w2n d+capacity <= w2n v)) ==>
  ?t H tt.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    copy_runtime_frame ca s cb (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_memory = (immutable_word_transfer F F a d off s).vs_memory /\
    t.vs_current_bb = cb.cs_current_bb /\
    t.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers H tt root t capacity /\ eval_operand src t = SOME a /\
    op_taint tt src = {} /\
    tt.t_mem = tn.t_mem DIFF {i | w2n d+off <= i /\ i < w2n d+off+32} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!x. not_fresh_at ca x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    ghost_inv rty ce cx ee H tt t /\ ghost_kept ce es sa0 G0 tn0 s0 H tt
Proof
  strip_tac >> drule_all ifexp_runtime_one_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame ca s cc (r with vs_inst_idx := s.vs_inst_idx)` >>
  `ghost_inv rty ce cx ee J tr r` by
    (irule ifexp_runtime_fresh_inv >> metis_tac[]) >>
  suspend "one_store_inv"
QED

Resume ifexp_runtime_one_ptr[one_store_inv]:
  `w2n (d+n2w off) = w2n d+off` by
    (simp[w2n_add_2] >> decide_tac) >>
  `!name entry p sz v. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p r = SOME v ==>
    val_wf entry.type entry.value /\
    (w2n v+type_memory_size entry.type <= w2n (d+n2w off) \/
     w2n (d+n2w off)+32 <= w2n v)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at ca p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var p s = SOME v` by metis_tac[] >>
     qpat_x_assum `!name entry p sz v. _` drule_all >>
     simp[] >> decide_tac) >>
  `ghost_inv rty ce cx ee H tt t` by
    (qpat_x_assum `t = _` SUBST1_TAC >>
     pure_rewrite_tac[ifexp_ghost_inv_inst_idx] >>
     qpat_x_assum `H = _` SUBST1_TAC >> qpat_x_assum `tt = _` SUBST1_TAC >>
     irule ifexp_materialize_store_inv >> simp[] >>
     conj_tac >- (qpat_x_assum `!name entry p sz v. _` mp_tac >> simp[]) >>
     qexists_tac `ca` >> simp[]) >>
  qexistsl_tac [`t`, `H`, `tt`] >> simp[] >>
  simp[ghost_kept_def] >>
  conj_tac >- (rpt strip_tac >> gvs[ghost_kept_def] >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >> gvs[ghost_kept_def] >> metis_tac[]
QED

Finalise ifexp_runtime_one_ptr
