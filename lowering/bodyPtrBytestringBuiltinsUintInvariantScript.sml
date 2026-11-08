Theory bodyPtrBytestringBuiltinsUintInvariant
Ancestors
  bodyPtrBytestringBuiltinsUintGhost exprSimPtrProps bodyPtrAttributeAdd
  bodyPtrDefs exprSimUint2Str codegenRel contextCodegenRel
  ptrDiscipline venomState finite_map words venomExecSemantics
  typedCopyPtr stmtFragPtr

(* This abbreviation packages the repeated loop-boundary ghost conjunction.
   Transient registers and allocated padding are deliberately unconstrained;
   S1's u2s_safe and u2s_digits remain separate semantic predicates. *)
Definition u2s_ptr_state_def:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s <=>
    ghost_inv d cenv cx es G tn s /\
    ghost_kept cenv es a G0 tn0 s0 G tn /\
    FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
    op_taint tn (Var p) = {} /\
    (!k. k < 2 ==> FLOOKUP G (u2s_var a k) = NONE /\
                     op_taint tn (Var (u2s_var a k)) = {}) /\
    i <= n /\
    (!j. b+n+32-i <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem)
End

Theorem u2s_ptr_state_ambient:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s ==>
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn
Proof
  simp[u2s_ptr_state_def]
QED

Theorem u2s_ptr_state_buffer:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s ==>
  FLOOKUP G p = SOME (b,sz) /\ lookup_var p s = SOME (n2w b) /\
  op_taint tn (Var p) = {}
Proof
  simp[u2s_ptr_state_def]
QED

Theorem u2s_ptr_state_scalar:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\ k < 2 ==>
  FLOOKUP G (u2s_var a k) = NONE /\ op_taint tn (Var (u2s_var a k)) = {}
Proof
  simp[u2s_ptr_state_def]
QED

Theorem u2s_ptr_state_suffix:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s ==>
  i <= n /\ (!j. b+n+32-i <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem)
Proof
  simp[u2s_ptr_state_def]
QED

(* Fresh outputs may be pointers. Only agreement on older variables and
   unchanged non-variable taint is required for the ambient frame. *)
Theorem u2s_fresh_update_frame:
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es a G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!p. p <> u2s_var a k ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d cenv cx es G' tn'
    (update_var (u2s_var a k) w s with vs_inst_idx := idx) /\
  ghost_kept cenv es a G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `!p. not_fresh_at a p ==> p <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  conj_tac
  >- (irule ghost_inv_fresh_frame >> goal_assum (drule_at Any) >>
      simp[update_var_def] >> qexistsl_tac [`G`, `es`, `s`, `a`] >>
      simp[] >> rpt strip_tac >>
      simp[lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  irule attribute_ghost_kept_frame >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem u2s_ptr_state_update:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\
  not_fresh_at a p /\ local_ptrs_reserved cenv a /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at a p) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!q. q <> u2s_var a k ==> FLOOKUP G' q = FLOOKUP G q /\
     op_taint tn' (Var q) = op_taint tn (Var q)) /\
  (k < 2 ==> FLOOKUP G' (u2s_var a k) = NONE /\
             op_taint tn' (Var (u2s_var a k)) = {}) ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G' tn'
    (update_var (u2s_var a k) w s with vs_inst_idx := idx)
Proof
  strip_tac >>
  drule u2s_ptr_state_ambient >> strip_tac >>
  `ghost_inv d cenv cx es G' tn'
      (update_var (u2s_var a k) w s with vs_inst_idx := idx) /\
   ghost_kept cenv es a G0 tn0 s0 G' tn'` by
    (irule u2s_fresh_update_frame >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`G`, `tn`] >> simp[]) >>
  `p <> u2s_var a k` by metis_tac[u2s_var_fresh] >>
  gvs[u2s_ptr_state_def] >>
  conj_tac >- gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `k' = k` >> gvs[] >>
  metis_tac[u2s_var_injective]
QED

Theorem u2s_ptr_state_jump:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn (jump_to lbl s)
Proof
  simp[u2s_ptr_state_def] >> strip_tac >>
  gvs[ghost_inv_jump_to, lookup_var_def, jump_to_def]
QED

Theorem u2s_ptr_state_store:
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n i G tn s /\ i < n /\
  local_ptrs_rel func cenv es.scopes s /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= b+n-i /\ b+n-i+32 <= b+sz /\ b+n-i < dimword(:256) /\
  lookup_var dst s = SOME (n2w (b+n-i)) /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  u2s_ptr_state d cenv cx es a G0 tn0 s0 p b sz n (i+1) G
    (tn with t_mem := tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
    (mstore (b+n-i) w s)
Proof
  strip_tac >> drule u2s_ptr_state_ambient >> strip_tac >>
  `b <= w2n (n2w (b+n-i):bytes32) /\
   w2n (n2w (b+n-i):bytes32)+32 <= b+sz` by simp[w2n_n2w] >>
  `step_prov [] G (mk_inst 0 MSTORE [Var dst;value] [])
      (mstore (b+n-i) w s) = G` by
    (drule_all mstore_ghost_frame >>
     disch_then (qspecl_then [`[]`, `G`, `0`] mp_tac) >> simp[w2n_n2w]) >>
  drule_all clean_mstore_ghost_inv >>
  disch_then (qspecl_then [`[]`, `0`] mp_tac) >>
  simp[w2n_n2w, clean_mstore_taint_state, mstore_ghost_frame] >> strip_tac >>
  drule_all clean_mstore_ghost_kept >>
  disch_then (qspecl_then [`[]`, `0`] mp_tac) >>
  simp[w2n_n2w, clean_mstore_taint_state, mstore_ghost_frame] >> strip_tac >>
  drule u2s_ptr_state_suffix >> strip_tac >>
  qspecl_then [`tn`, `b`, `n`, `i`] mp_tac digit_store_suffix_clean >>
  simp[] >> strip_tac >>
  gvs[u2s_ptr_state_def, op_taint_def]
QED
