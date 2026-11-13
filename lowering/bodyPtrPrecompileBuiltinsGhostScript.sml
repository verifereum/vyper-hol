(* Ghost frames preserve provenance, but runtime address stability is separate. *)
Theory bodyPtrPrecompileBuiltinsGhost
Ancestors bodyPtrDefs ptrDiscipline venomState freshWrites

Theorem ghost_kept_operand_taint:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_taint tn op = op_taint tn0 op
Proof
  strip_tac >> Cases_on `op` >> gvs[op_taint_def, ghost_kept_def]
QED

Theorem ghost_kept_provenance:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p ==>
  FLOOKUP G p = FLOOKUP G0 p
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_ptr_covers:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p /\
  eval_operand (Var p) s0 = SOME w /\ eval_operand (Var p) s = SOME w /\
  ptr_covers G0 tn0 p s0 m ==>
  ptr_covers G tn p s m
Proof
  rw[ghost_kept_def, ptr_covers_def, eval_operand_def] >> gvs[] >>
  metis_tac[]
QED

Theorem ghost_kept_alloca_clean:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
  (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
             off + sz <= b \/ b + sz' <= off) /\
  off <= a /\ a + m <= off + sz /\
  (!i. a <= i /\ i < a + m ==> i NOTIN tn0.t_mem) ==>
  !i. a <= i /\ i < a + m ==> i NOTIN tn.t_mem
Proof
  rw[ghost_kept_def] >> spose_not_then assume_tac >>
  `off <= i /\ i < off + sz` by decide_tac >> metis_tac[]
QED

Theorem ghost_kept_local_clean:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_region cenv es.scopes s0 n b sz /\
  b <= a /\ a + m <= b + sz /\
  (!k. dynarray_len_at cenv n k ==> a + m <= b + k \/ b + k + 32 <= a) /\
  (!i. a <= i /\ i < a + m ==> i NOTIN tn0.t_mem) ==>
  !i. a <= i /\ i < a + m ==> i NOTIN tn.t_mem
Proof
  rw[ghost_kept_def] >> spose_not_then assume_tac >>
  `b <= i /\ i < b + sz` by decide_tac >>
  `!k. dynarray_len_at cenv n k ==> i < b + k \/ b + (k + 32) <= i` by
    (rpt strip_tac >>
     qpat_x_assum `!k. dynarray_len_at _ _ _ ==> _` drule >> decide_tac) >>
  qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _`
    (qspecl_then [`n`, `b`, `sz`, `i`] mp_tac) >>
  metis_tac[]
QED
