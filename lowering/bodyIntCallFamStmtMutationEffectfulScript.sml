(* Held leaves of the internal-call mutation step: Assign and AugAssign to
   a base target whose indices have effects.  The body-level twins of these
   cases (stmtSimAssignPlace's assign_place_effectful_index_case and
   bodyAugAssignOther's augassign_place_effectful_index_case) are false as
   stated: an index call can reassign the nested array.  Both leaves carve
   out exactly the targets those twins cover and are held until the twins
   are restated after the target-overlap and RHS-first turns. *)
Theory bodyIntCallFamStmtMutationEffectful
Ancestors
  bodyIntCallJointContract supportedTargets targetPlaceSim

(* Held: twin of assign_place_effectful_index_case; waits on the
   target-overlap turn and the RHS-first turn. *)
Theorem intcall_assign_effectful_index_step:
  !fp bt e.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\
    ~supported_target_pure fp.jc_tops bt ==>
    intcall_stmts_producer fp [Assign (BaseTarget bt) e]
Proof
  cheat
QED

(* Held: twin of augassign_place_effectful_index_case; waits on the
   target-overlap turn and the RHS-first turn. *)
Theorem intcall_augassign_effectful_index_step:
  !fp ty bt bop e.
    (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
         intcall_map_producer fp e) /\
    (!id. target_root bt <> NameTarget id) /\
    ~supported_target_pure fp.jc_tops bt /\
    ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) ==>
    intcall_stmts_producer fp [AugAssign ty bt bop e]
Proof
  cheat
QED
