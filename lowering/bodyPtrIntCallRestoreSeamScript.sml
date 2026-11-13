(* Return-side framing at the internal-call boundary. *)
Theory bodyPtrIntCallRestoreSeam
Ancestors
  bodyIntCallSeams bodyPtrDefs bodyPtrIntCallConfinement
  bodyPtrBytestringBuiltinsWindowGhost exprSimDefs exprSimProps
  loweringPosts compileEnv venomState venomExecSemantics
  finite_map pred_set list

(* Concrete and ghost confinement have different jobs: the exit seam
   preserves the bytes; the protected-set frame prevents new taint there. *)
Theorem intcall_callee_exit_local_windows:
  !func cenv cx rtv rc rb first t v ee ir s P tn tm es.
  intcall_callee_exit func cenv cx rtv (rc:num) rb (first:num) t
    (INL v) ee (IntRet ir s) /\
  intcall_mem_frame P tn tm /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      first <= aid ==> regions_disjoint b sz off asz) /\
    (!i. b <= i /\ i < b + sz ==> i IN P)) ==>
  !name b sz. local_region cenv es.scopes t name b sz ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory /\
    (!i. b <= i /\ i < b + sz /\ i IN tm.t_mem ==> i IN tn.t_mem)
Proof
  simp[intcall_callee_exit_def, expr_exit_def] >>
  rpt strip_tac
  >- metis_tac[] >>
  fs[intcall_mem_frame_def, SUBSET_DEF, IN_INTER] >> metis_tac[]
QED

Theorem intcall_callee_exit_restore_ghost:
  !func cenv cx rtv rc rb first t v ee ir s d es G tn sa u H tm P.
  intcall_callee_exit func cenv cx rtv (rc:num) rb (first:num) t
    (INL v) ee (IntRet ir s) /\
  ghost_inv d cenv cx es G tn t /\
  local_ptrs_rel func cenv es.scopes t /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==>
    lookup_var x u = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  u.vs_memory = s.vs_memory /\ stor_taint_ok cx tm u /\
  intcall_mem_frame P tn tm /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      first <= aid ==> regions_disjoint b sz off asz) /\
    (!i. b <= i /\ i < b + sz ==> i IN P)) ==>
  ghost_inv d cenv cx es H tm u
Proof
  rpt gen_tac >> strip_tac >> irule ghost_inv_local_window_transport >>
  simp[] >> qexistsl_tac [`G`, `func`, `t`, `sa`, `tn`] >> simp[] >>
  drule intcall_callee_exit_local_windows >>
  disch_then (qspecl_then [`P`, `tn`, `tm`, `es`] assume_tac) >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> goal_assum (drule_at Any)
QED
