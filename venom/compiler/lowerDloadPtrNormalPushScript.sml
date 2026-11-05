Theory lowerDloadPtrNormalPush
Ancestors lowerDloadPtrInvoke lowerDloadPtrAggregate pred_set

(* Interface probe for the active set delivered by actual invoke. *)
Theorem dload_invoke_active_set_probe[local]:
  dload_boundary_core lo fs {a | ~retpc_var callee a} Ws
    PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs
    (set (fn_ir_vars callee) DIFF {a | retpc_var callee a}) Ws
    PG PH G H tn un s t cs ds
Proof
  strip_tac >> irule dload_boundary_vars_restrict >>
  goal_assum (drule_at Any) >> simp[SUBSET_DEF]
QED

Theorem dload_scratch_stack_push:
  LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
  (!k. k < LENGTH fs ==>
    (EL k fs).dr_scratch =
      FDOM (EL k (t::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                i.inst_id = id}) /\
  v.vs_allocas = FEMPTY /\ fr.dr_scratch = {} /\
  c.cf_fn = f /\ d.cf_state = t ==>
  LENGTH (fr::fs) = SUC (LENGTH (c::cs)) /\
  LENGTH (c::cs) = LENGTH (d::ds) /\
  (!k. k < LENGTH (fr::fs) ==>
    (EL k (fr::fs)).dr_scratch =
      FDOM (EL k (v::MAP (\d. d.cf_state) (d::ds))).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (callee::MAP (\c. c.cf_fn) (c::cs)))) /\
                i.inst_id = id})
Proof
  strip_tac >> simp[] >> Cases >> simp[]
QED

(* The saved suffix contains no observation of the active frame except the
   address parameter. Abstract the rest once for both push and head change. *)
Theorem dload_saved_suffix_push:
  (!k. k < LENGTH cs ==> R (DROP (SUC k) fs) (EL k cs) (EL k ds)) ==>
  !k. k < LENGTH cs ==>
    R (DROP (SUC (SUC k)) (fr::fs))
      (EL (SUC k) (c::cs)) (EL (SUC k) (d::ds))
Proof
  simp[]
QED

Theorem dload_saved_suffix_head_change:
  (!k. k < LENGTH cs ==> R addr (DROP (SUC k) (fr::fs)) (EL k cs) (EL k ds)) /\
  addr' = addr ==>
  !k. k < LENGTH cs ==>
    R addr' (DROP (SUC k) (fr'::fs)) (EL k cs) (EL k ds)
Proof
  simp[]
QED
