(* Concrete representation frames and counted membership iteration. *)
Theory exprSimBopRestWordIterate
Ancestors
  exprSimBopRestWordLoopPath exprSimBopRestWordLoadSafety exprSimVVFrame
  freshWrites

(* All arithmetic temporaries are fresh at the operand compiler endpoint.
   Keep that endpoint fixed while framing each write, rather than rebasing
   the operand post to a later endpoint which would make temporaries old. *)
Theorem rest_word_vv_address_frame:
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  ~not_fresh_at sm mulvar /\ ~not_fresh_at sm totalvar /\
  ~not_fresh_at sm addrvar /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) ==>
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv
    (update_var addrvar (baseword + n2w (off + i * stride))
      (if 0 < off then update_var totalvar (n2w (off + i * stride))
          (update_var mulvar (n2w (i * stride)) s)
       else update_var mulvar (n2w (i * stride)) s))
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e es sa sm s0 es' tv vv
     (update_var mulvar (n2w (i * stride)) s)` by
    (irule vv_post_update_var >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `0 < off` >> simp[] >>
  irule vv_post_update_var >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  irule vv_post_update_var >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_vv_post_jump:
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv (jump_to lbl s) <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s
Proof
  `!op. eval_operand op (jump_to lbl s) = eval_operand op s` by
    (Cases >> simp[venomStateTheory.eval_operand_def,
                   venomStateTheory.lookup_var_def, venomStateTheory.jump_to_def]) >>
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_post_def,
       exprLoweringPropsTheory.stmt_state_rel_jump_to,
       loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
       loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
       venomStateTheory.lookup_var_def, compileEnvTheory.local_region_def,
       loweringPostsTheory.storage_holds_def, loweringPostsTheory.immutable_holds_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomStateTheory.jump_to_def, venomStateTheory.eval_operand_def,
       loweringPostsTheory.locals_kept_def]
QED
