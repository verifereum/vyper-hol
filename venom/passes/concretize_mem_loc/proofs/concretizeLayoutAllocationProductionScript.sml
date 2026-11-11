Theory concretizeLayoutAllocationProduction
Ancestors
  frameRelocationBinding frameAllocationEffects frameRelocationGuardedValues
  frameRelocationGhostCopy
  frameActivationLookup frameResolvedTrace frameRelocationMemory
  frameJointDemand frameOriginUpdates ptrDiscipline finite_map words list pred_set

(* ALLOCA has no byte writes.  The trace-wide retained-demand boundary
   therefore applies to both cached and fresh executions. *)
Theorem layout_alloca_demand_retained:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  EL n (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL n es = SOME (OriginOrdinary fuel post) /\ inst.inst_opcode = ALLOCA /\
  joint_relocation_demand lo positions q0 es qs (SUC n) a z ==>
  joint_relocation_demand lo positions q0 es qs n a z
Proof
  strip_tac >> irule joint_relocation_demand_retained >>
  simp[joint_writes_def, alloca_step_writes, range_bytes_def] >>
  metis_tac[]
QED

(* A resolved local output is a pointer even for a zero-sized site.
   No byte-agreement obligation is imposed on pointer-valued outputs. *)
Theorem layout_alloca_output_guarded:
  inst.inst_opcode = ALLOCA /\
  FLOOKUP post.vs_allocas inst.inst_id = SOME (b,sz) ==>
  guarded_ptr Opaque
    (activation_lookup default positions (birth::ids) (fn::owners))
    (origin_set rv [v]
      (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
    v (n2w b) (n2w (positions fn inst.inst_id)) /\
  guarded_bytes Opaque
    (origin_set rv [v]
      (resolved_out birth post.vs_allocas rp (origin_out PG om inst post)))
    tn' v (n2w b) (n2w (positions fn inst.inst_id))
Proof
  strip_tac >>
  simp[origin_out_def, resolved_out_def, resolved_cache_local,
       guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, activation_lookup_def, WORD_SUB_REFL]
QED

(* The other bindings use the same activation lookup; only the variable
   component of taint matters here, not fresh-allocation memory taint. *)
Theorem layout_single_output_guarded_other:
  inst.inst_outputs = [v] /\ u <> v ==>
  (guarded_ptr Opaque L (origin_set rv [v] p) u x y <=>
     guarded_ptr Opaque L rv u x y) /\
  (guarded_bytes Opaque (origin_set rv [v] p)
     (step_taint inst s post tn) u x y <=>
     guarded_bytes Opaque rv tn u x y)
Proof
  strip_tac >> simp[guarded_ptr_other] >>
  simp[guarded_bytes_def, copy_bytes_def, origin_set_lookup,
       step_taint_def, set_var_taint_def, op_taint_def, FLOOKUP_UPDATE]
QED

