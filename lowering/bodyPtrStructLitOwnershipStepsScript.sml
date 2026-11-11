Theory bodyPtrStructLitOwnershipSteps
Ancestors bodyPtrStructLitCompilerOwnership compileEnv loweringStateRelDefs pair
  loweringShapeDefs loweringShapeRules list exprCallBounds venomInst

(* These two interfaces keep reserved old registers distinct from readable
   allocation pointers and avoid repeating frame quantifiers in callbacks. *)
Definition alloc_frame_def:
  alloc_frame st st' <=>
    (!x. not_fresh_at st x ==> not_fresh_at st' x) /\
    (!x. not_fresh_at st x /\ ~alloc_owned st x ==> ~alloc_owned st' x)
End

Definition alloc_run_def:
  alloc_run P f Q <=>
    !st v st'. P st /\ alloc_writers_unique st /\ f st = (v,st') ==>
      alloc_writers_unique st' /\ alloc_frame st st' /\ Q v st'
End

Theorem alloc_frame_refl:
  alloc_frame st st
Proof simp[alloc_frame_def]
QED

Theorem alloc_frame_trans:
  alloc_frame st st' /\ alloc_frame st' st'' ==> alloc_frame st st''
Proof rw[alloc_frame_def] >> metis_tac[]
QED

Theorem alloc_run_return:
  (!st. P st ==> Q v st) ==> alloc_run P (\st. (v,st)) Q
Proof simp[alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_conseq:
  alloc_run P f Q /\ (!st. P' st ==> P st) /\
  (!v st. Q v st ==> Q' v st) ==> alloc_run P' f Q'
Proof rw[alloc_run_def] >> metis_tac[]
QED

Theorem alloc_run_bind:
  alloc_run P f R /\ (!v. alloc_run (R v) (g v) Q) ==>
  alloc_run P (comp_bind f g) Q
Proof
  rw[alloc_run_def, comp_bind_def] >> Cases_on `f st` >> gvs[] >>
  qpat_x_assum `!st v st'. _` drule_all >> strip_tac >>
  qpat_x_assum `!v st v' st'. _` drule_all >> strip_tac >>
  metis_tac[alloc_frame_trans]
QED

Theorem alloc_frame_same_insts:
  state_insts st' = state_insts st /\ st.cs_next_var <= st'.cs_next_var ==>
  alloc_frame st st'
Proof
  rw[alloc_frame_def, alloc_owned_def] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem alloc_writers_unique_same_insts:
  state_insts st' = state_insts st /\ alloc_writers_unique st ==>
  alloc_writers_unique st'
Proof rw[alloc_writers_unique_def] >> metis_tac[]
QED

Theorem alloc_run_fresh_label:
  alloc_run (\st. T) (fresh_label suffix) (\v st. T)
Proof
  rw[alloc_run_def, fresh_label_def] >>
  `state_insts (st with cs_next_label := st.cs_next_label + 1) = state_insts st`
    by simp[state_insts_def, all_blocks_def]
  >- metis_tac[alloc_writers_unique_same_insts] >>
  irule alloc_frame_same_insts >> simp[]
QED

Theorem alloc_run_new_block:
  alloc_run (\st. T) (new_block lbl) (\v st. T)
Proof
  rw[alloc_run_def, new_block_def] >>
  fs[alloc_writers_unique_def, alloc_frame_def, alloc_owned_def,
     state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
     APPEND_ASSOC, not_fresh_at_def] >> metis_tac[]
QED

Theorem alloc_run_fresh_var:
  alloc_run (\st. T) fresh_var (\v st. T)
Proof
  rw[alloc_run_def, fresh_var_def] >>
  `state_insts (st with cs_next_var := st.cs_next_var + 1) = state_insts st`
    by simp[state_insts_def, all_blocks_def]
  >- metis_tac[alloc_writers_unique_same_insts] >>
  irule alloc_frame_same_insts >> simp[]
QED

Theorem alloc_run_emit_void:
  alloc_run (\st. T) (emit_void opc ops) (\v st. T)
Proof
  rw[alloc_run_def]
  >- (drule_all alloc_writers_unique_emit_void >> simp[]) >>
  drule emit_void_owned >> strip_tac >>
  gvs[alloc_frame_def, alloc_owned_def, emit_void_eq, not_fresh_at_def]
QED

Theorem alloc_run_emit_inst:
  opc <> ALLOCA ==>
  alloc_run (\st. EVERY (\x. ~alloc_owned st x) outs)
    (emit_inst opc ops outs) (\v st. T)
Proof
  rw[alloc_run_def]
  >- (irule alloc_writers_unique_emit_inst >>
      goal_assum (drule_at Any) >> fs[alloc_owned_def]) >>
  drule_all emit_inst_nonalloc_owned >> strip_tac >>
  gvs[alloc_frame_def, alloc_owned_def, emit_inst_eq, not_fresh_at_def]
QED

Theorem alloc_run_emit_op:
  alloc_run shape_base_state (emit_op opc ops) (\v st. T)
Proof
  rw[alloc_run_def]
  >- (drule_all alloc_writers_unique_emit_op >> simp[]) >>
  drule emit_op_facts >> strip_tac >>
  rw[alloc_frame_def]
  >- (irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
  pure_rewrite_tac[alloc_owned_def] >>
  irule emit_op_preserves_nonowned >> goal_assum (drule_at Any) >>
  fs[shape_base_state_def, alloc_owned_def] >> metis_tac[]
QED

Theorem fresh_var_nonowned:
  shape_base_state st /\ fresh_var st = (x,st') ==>
  not_fresh_at st' x /\ ~alloc_owned st' x
Proof
  rw[fresh_var_def] >>
  mp_tac (Q.SPECL [`st`, `st with cs_next_var := st.cs_next_var + 1`]
    fresh_output_props) >>
  simp[] >> strip_tac >>
  fs[alloc_owned_def, opaque_out_def, state_insts_def, all_blocks_def,
     shape_base_state_def] >> metis_tac[]
QED

Theorem alloc_run_invalid_expr_call:
  alloc_run (\st. T) (invalid_expr_call ty)
    (\v st. v = StackValue ty (Lit 0w))
Proof
  mp_tac (Q.INST [`opc` |-> `INVALID`, `ops` |-> `[]`, `outs` |-> `[]`]
    alloc_run_emit_inst) >>
  simp[alloc_run_def, invalid_expr_call_def, emit_inst_eq]
QED

(* Monadic bind in its uncurried and pair-let forms; formerly in theories
   trunk removed (gasShadowCompileBase,). *)
Theorem comp_bind_uncurry:
  (\s. UNCURRY h (f s)) = comp_bind f h
Proof
  simp[FUN_EQ_THM, comp_bind_def] >> gen_tac >>
  Cases_on `f s` >> simp[]
QED

Theorem state_pair_let_bind:
  pair$UNCURRY k (m a) = comp_bind m k a
Proof
  Cases_on `m a` >> simp[comp_bind_def]
QED
