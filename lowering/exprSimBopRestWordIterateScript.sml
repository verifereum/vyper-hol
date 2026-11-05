(* Concrete representation frames and counted membership iteration. *)
Theory exprSimBopRestWordIterate
Ancestors
  exprSimBopRestWordLoopPath exprSimBopRestWordLoadSafety exprSimVVFrame
  freshWrites exprSimBopRestWordLoop venomExecSemantics

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

(* Finite-search composition consumes the four local marked block contracts.
   Its premises are instantiated by the layout and concrete representation;
   in particular they do not assert preservation for an arbitrary R. *)
Theorem rest_word_search_iteration:
  (!i s. rest_word_membership_inv idx result len needle elem R i s /\
     s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
     ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
       t.vs_current_bb = (if i = len then exit else body_lbl) /\
       t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       rest_word_membership_inv idx result len needle elem R i t) /\
  (!i s. rest_word_membership_inv idx result len needle elem R i s /\
     i < len /\ s.vs_current_bb = body_lbl /\
     s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
     ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
       t.vs_current_bb = (if elem i = needle then found else incr) /\
       t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       rest_word_membership_inv idx result len needle elem R i t) /\
  (!s. R s /\ s.vs_current_bb = found /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
     ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       eval_operand (Var result) t = SOME 1w /\ R t) /\
  (!i s. rest_word_membership_inv idx result len needle elem R i s /\
     i < len /\ elem i <> needle /\ s.vs_current_bb = incr /\
     s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
     ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
       t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       rest_word_membership_inv idx result len needle elem R (i+1) t) ==>
  !i s. rest_word_membership_inv idx result len needle elem R i s /\
    s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      eval_operand (Var result) t =
        SOME (bool_to_word (?j. j < len /\ elem j = needle)) /\ R t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "cond")
    (CONJUNCTS_THEN2 (mk_asm "body")
      (CONJUNCTS_THEN2 (mk_asm "found")
                      (mk_asm "incr")))) >>
  measureInduct_on `len - i` >> rpt strip_tac >>
  asm "cond" drule_all >> disch_then (qx_choose_then `c` strip_assume_tac) >>
  Cases_on `i = len`
  >- (`~(?j. j < len /\ elem j = needle)` by
        metis_tac[rest_word_membership_exhausted] >>
      qexists_tac `c` >> simp[] >>
      qpat_x_assum `rest_word_membership_inv _ _ _ _ _ _ _ c` mp_tac >>
      simp[rest_word_membership_inv_def, venomExecSemanticsTheory.bool_to_word_def]) >>
  `i < len` by fs[rest_word_membership_inv_def] >>
  fs[] >> asm "body" drule_all >> simp[] >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  `gas_marked_path memory ctx fn s 0 (OK b)` by
    metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  Cases_on `elem i = needle`
  >- (`R b` by fs[rest_word_membership_inv_def] >> fs[] >>
      asm "found" drule_all >> disch_then (qx_choose_then `f` strip_assume_tac) >>
      `?j. j < len /\ elem j = needle` by metis_tac[] >>
      qexists_tac `f` >> simp[] >> conj_tac
      >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
             fragGasModeTheory.gas_marked_path_then)) >>
          qexists_tac `b` >> simp[]) >>
      `(?j. j < len /\ elem j = needle) = T` by metis_tac[] >>
      simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  fs[] >> asm "incr" drule_all >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qpat_x_assum `!y. _ ==> !s. _` (qspec_then `i+1` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `u` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED
