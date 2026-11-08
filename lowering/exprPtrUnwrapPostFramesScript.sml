(* Projection boundaries for allocation/copy reconstruction. *)
Theory exprPtrUnwrapPostFrames
Ancestors
  bodyPtrDefs ptrDiscipline venomState finite_map

Theorem copy_stor_taint_frame:
  stor_taint_ok cx tn s /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm ==>
  stor_taint_ok cx tm t
Proof
  simp[stor_taint_ok_def]
QED

(* Fresh destination bytes are absent: only retained bytes require
   a no-new-taint implication. *)
Theorem copy_ghost_kept_transport:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
  (!n b sz i.
    local_region cenv es.scopes s0 n b sz /\ b <= i /\ i < b+sz /\
    (!k. dynarray_len_at cenv n k ==> i < b+k \/ b+k+32 <= i) /\
    i IN tm.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept cenv es sa G0 tn0 s0 H tm
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED
