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
       loweringPostsTheory.vv_own_def, loweringPostsTheory.expr_val_own_def,
       loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
       venomStateTheory.lookup_var_def, loweringStateRelDefsTheory.local_region_def,
       loweringPostsTheory.storage_holds_def, loweringPostsTheory.immutable_holds_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomStateTheory.jump_to_def, venomStateTheory.eval_operand_def,
       loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def]
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

(* The concrete persistent part of the search invariant.  The operand
   compiler endpoint sm stays fixed throughout the loop. *)
Definition rest_word_search_rep_def:
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop needle lenop len s <=>
    vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
    eval_operand needleop s = SOME needle /\
    eval_operand lenop s = SOME (n2w len)
End

Theorem rest_word_search_rep_update:
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  ~not_fresh_at sm x /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  needleop <> Var x /\ lenop <> Var x ==>
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len (update_var x w s)
Proof
  simp[rest_word_search_rep_def] >> strip_tac >> conj_tac
  >- (irule vv_post_update_var >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `needleop` >> Cases_on `lenop` >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem rest_word_search_rep_control:
  (rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
     needleop needle lenop len (jump_to lbl s) <=>
   rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
     needleop needle lenop len s) /\
  (rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
     needleop needle lenop len (s with vs_inst_idx := k) <=>
   rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
     needleop needle lenop len s)
Proof
  simp[rest_word_search_rep_def, rest_word_vv_post_jump] >>
  Cases_on `needleop` >> Cases_on `lenop` >>
  simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       venomStateTheory.jump_to_def]
QED

Theorem rest_word_search_rep_load:
  context$compile_ptr_load ctor imm loc addr cl = (op,cm) /\
  loc <> LocCalldata /\ sm.cs_next_var <= cl.cs_next_var /\
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z. needleop = Var z ==> not_fresh_at cl z) /\
  (!z. lenop = Var z ==> not_fresh_at cl z) /\
  run_inst_seq (emitted_insts cl cm) s = OK t ==>
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len t
Proof
  Cases_on `loc` >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_def,
       emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def] >> strip_tac >> gvs[] >>
  `!n. cl.cs_next_var <= n ==>
       needleop <> Var (STRING #"%" (toString n)) /\
       lenop <> Var (STRING #"%" (toString n))` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, exprLoweringPropsTheory.run_inst_seq_def,
       venomInstTheory.mk_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  irule rest_word_search_rep_update >>
  simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  irule rest_word_search_rep_update >>
  simp[loweringStateRelDefsTheory.not_fresh_at_def]
QED

(* Boundary check: freshness and the tested register come from the SAME
   compiler certificate, without reconciling independent layout witnesses. *)
Theorem rest_word_safe_cond_probe[local]:
  rest_word_loop_layout_safe cs ct fn needleop arrop lenop stride off bound_opt is_in out h code cl cm valueop /\
  rest_word_membership_inv h.rw_idx h.rw_result len needle elem R i s /\
  s.vs_current_bb = h.rw_cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand lenop s = SOME (n2w len) /\
  (!u x w. R u /\ ~not_fresh_at cs x ==> R (update_var x w u)) /\
  (!u lbl. R u ==> R (jump_to lbl u)) ==>
  ?t. gas_marked_path memory ctx fn s 0 (OK t) /\
      t.vs_current_bb = (if i = len then h.rw_exit else h.rw_body) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      rest_word_membership_inv h.rw_idx h.rw_result len needle elem R i t
Proof
  strip_tac >> drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_safe_cond >> strip_tac >>
  `~not_fresh_at cs done /\ done <> h.rw_idx /\ done <> h.rw_result` by
    metis_tac[] >>
  `R s` by fs[rest_word_membership_inv_def] >>
  irule rest_word_cond_path >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`a`, `b`, `lenop`] >> simp[]
QED

(* The only semantic oracle in this compiled-loop boundary is the located
   element load.  In particular it does not assume any loop transitions. *)
Theorem rest_word_compiled_search:
  compile_array_membership_loop needleop arrop lenop stride off
    (context$compile_ptr_load ctor imm loc) bound_opt is_in cs = (out,ct) /\
  fn_has_code cs ct fn /\ loc <> LocCalldata /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_var <= cs.cs_next_var /\
  (!z. vv_operand vv = Var z ==> not_fresh_at sm z) /\
  (!z. needleop = Var z \/ arrop = Var z \/ lenop = Var z ==> not_fresh_at cs z) /\
  len < dimword (:256) /\
  (case bound_opt of NONE => T | SOME cap => len <= cap /\ cap < dimword (:256)) /\
  (!h cl cm v i p.
    rest_word_loop_prefix needleop arrop lenop stride off bound_opt cs = (h,cl) /\
    context$compile_ptr_load ctor imm loc h.rw_addr cl = (v,cm) /\ i < len /\
    rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop needle lenop len p /\
    eval_operand arrop p = SOME baseword /\
    eval_operand h.rw_addr p = SOME (baseword + n2w (off + i * stride)) ==>
    ?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
        eval_operand v q = SOME (elem i) /\
        (memory ==> run_inst_seq_mem_ok (emitted_insts cl cm) p)) /\
  rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len s /\ eval_operand arrop s = SOME baseword /\
  s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_marked_path memory execctx fn s 0 (OK t) /\
    t.vs_current_bb = ct.cs_current_bb /\
    t.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~t.vs_halted /\
    rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop needle lenop len t /\ eval_operand arrop t = SOME baseword /\
    eval_operand out t = SOME (bool_to_word
      (if is_in then (?j. j < len /\ elem j = needle)
       else ~(?j. j < len /\ elem j = needle)))
Proof
  strip_tac >> drule_all exprSimBopRestWordLayoutTheory.rest_word_ptr_loop_layout_safe >>
  disch_then (qx_choose_then `h` (qx_choose_then `cl`
    (qx_choose_then `cm` (qx_choose_then `v` strip_assume_tac)))) >>
  qabbrev_tac `R = \u. rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
    needleop needle lenop len u /\ eval_operand arrop u = SOME baseword` >>
  `!u x w. R u /\ ~not_fresh_at cs x ==> R (update_var x w u)` by
    (rpt gen_tac >> simp[Abbr `R`] >> strip_tac >> conj_tac
     >- (irule rest_word_search_rep_update >> simp[] >>
         metis_tac[not_fresh_at_mono]) >>
     Cases_on `arrop` >>
     gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `!u lbl. R u ==> R (jump_to lbl u)` by
    (simp[Abbr `R`, rest_word_search_rep_control] >>
     Cases_on `arrop` >> simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, venomStateTheory.jump_to_def]) >>
  `!u k. R u ==> R (u with vs_inst_idx := k)` by
    (simp[Abbr `R`, rest_word_search_rep_control] >>
     Cases_on `arrop` >> simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_allocation >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_idx_result >> strip_tac >>
  drule_all exprSimBopRestWordLayoutTheory.rest_word_loop_ptr_protected >> strip_tac >>
  `cs.cs_next_var <= cl.cs_next_var /\ cl.cs_next_var <= cm.cs_next_var` by
    (qspec_then `cl` mp_tac (Q.SPECL [`ctor`, `imm`, `loc`, `h.rw_addr`]
       exprLoweringPropsTheory.ci_mono_compile_ptr_load) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     Cases_on `bound_opt` >> simp[]) >>
  `!z. not_fresh_at cs z ==> not_fresh_at cl z` by metis_tac[not_fresh_at_mono] >>
  `~not_fresh_at cs h.rw_idx /\ ~not_fresh_at cs h.rw_result` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  qpat_x_assum `h.rw_idx = _` kall_tac >>
  qpat_x_assum `h.rw_result = _` kall_tac >>
  qpat_x_assum `h.rw_entry = _` kall_tac >>
  qpat_x_assum `h.rw_cond = _` kall_tac >>
  qpat_x_assum `h.rw_body = _` kall_tac >>
  qpat_x_assum `h.rw_found = _` kall_tac >>
  qpat_x_assum `h.rw_incr = _` kall_tac >>
  qpat_x_assum `h.rw_exit = _` kall_tac >>
  qpat_x_assum `cl.cs_next_var = _` kall_tac >>
  qpat_x_assum `cl.cs_next_label = _` kall_tac >>
  qpat_x_assum `cl.cs_next_id = _` kall_tac >>
  `!i u. rest_word_membership_inv h.rw_idx h.rw_result len needle elem R i u /\
    u.vs_current_bb = h.rw_cond /\ u.vs_inst_idx = 0 /\ ~u.vs_halted ==>
    ?t. gas_marked_path memory execctx fn u 0 (OK t) /\
      t.vs_current_bb = h.rw_exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      eval_operand (Var h.rw_result) t =
        SOME (bool_to_word (?j. j < len /\ elem j = needle)) /\ R t` by
    (ho_match_mp_tac (Q.INST [`body_lbl` |-> `h.rw_body`,
       `found` |-> `h.rw_found`, `incr` |-> `h.rw_incr`] rest_word_search_iteration) >> rpt conj_tac
     >- suspend "cond"
     >- suspend "body"
     >- suspend "found"
     >- suspend "incr") >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_safe_forget >> strip_tac >>
  `R s` by simp[Abbr `R`] >>
  `gas_marked_path memory execctx fn s 0 (OK (jump_to h.rw_entry s))` by
    (drule_all rest_word_layout_caller_path >> simp[]) >>
  `?u. gas_marked_path memory execctx fn (jump_to h.rw_entry s) 0 (OK u) /\
    u.vs_current_bb = h.rw_cond /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    rest_word_membership_inv h.rw_idx h.rw_result len needle elem R 0 u` by
    (irule rest_word_layout_entry_path >>
     qpat_assum `rest_word_loop_layout_safe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >>
     simp[venomStateTheory.jump_to_def] >>
     Cases_on `lenop` >>
     gvs[rest_word_search_rep_def, venomStateTheory.eval_operand_def,
         venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  qpat_x_assum `!i u. _` drule_all >> strip_tac >>
  `?w. gas_marked_path memory execctx fn t 0 (OK w) /\
    w.vs_current_bb = ct.cs_current_bb /\
    w.vs_inst_idx = LENGTH ct.cs_current_insts /\ ~w.vs_halted /\
    eval_operand out w = SOME (bool_to_word
      (if is_in then (?j. j < len /\ elem j = needle)
       else ~(?j. j < len /\ elem j = needle))) /\ R w` by
    (irule rest_word_layout_exit_path >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >>
     drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_safe_exit >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  qexists `w` >> simp[GSYM CONJ_ASSOC] >>
  `gas_marked_path memory execctx fn s 0 (OK w)` by
    metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  fs[Abbr `R`]
QED

Resume rest_word_compiled_search[cond]:
  rpt gen_tac >> strip_tac >>
  `eval_operand lenop u = SOME (n2w len)` by
    fs[rest_word_membership_inv_def, Abbr `R`, rest_word_search_rep_def] >>
  drule_all rest_word_safe_cond_probe >> simp[]
QED

Resume rest_word_compiled_search[found]:
  rpt gen_tac >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_safe_forget >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_found >> strip_tac >>
  `R (update_var h.rw_result 1w u)` by metis_tac[] >>
  irule rest_word_found_path >> simp[] >> qexistsl [`a`, `b`] >> simp[]
QED

Resume rest_word_compiled_search[incr]:
  rpt gen_tac >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_safe_incr >> strip_tac >>
  `~not_fresh_at cs next /\ next <> h.rw_result` by metis_tac[] >>
  `R u` by fs[rest_word_membership_inv_def] >>
  `R (update_var h.rw_idx (n2w (i+1)) (update_var next (n2w (i+1)) u))` by
    metis_tac[] >>
  irule rest_word_incr_path >> simp[] >> qexistsl [`a`, `b`, `c`, `next`] >> simp[]
QED

Resume rest_word_compiled_search[body]:
  rpt gen_tac >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_loop_layout_safe_body >> strip_tac >>
  `R u` by fs[rest_word_membership_inv_def] >>
  `~not_fresh_at cs mulvar /\ ~not_fresh_at cs totalvar /\
   ~not_fresh_at cs addr /\ ~not_fresh_at cs matched /\
   matched <> h.rw_idx /\ matched <> h.rw_result` by metis_tac[] >>
  qabbrev_tac `p = update_var addr (baseword + n2w (off + i * stride))
    (if 0 < off then update_var totalvar (n2w (off + i * stride))
      (update_var mulvar (n2w (i * stride)) u)
     else update_var mulvar (n2w (i * stride)) u)` >>
  `R p` by (Cases_on `0 < off` >> simp[Abbr `p`] >> metis_tac[]) >>
  `eval_operand h.rw_addr p = SOME (baseword + n2w (off + i * stride))` by
    simp[Abbr `p`, venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `?q. run_inst_seq (emitted_insts cl cm) p = OK q /\
       eval_operand v q = SOME (elem i) /\
       (memory ==> run_inst_seq_mem_ok (emitted_insts cl cm) p)` by
    (`rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
        needleop needle lenop len p` by fs[Abbr `R`] >>
     `eval_operand arrop p = SOME baseword` by fs[Abbr `R`] >>
     qpat_x_assum `!h cl cm v i p. _` drule_all >> simp[]) >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop needle lenop len p` by fs[Abbr `R`] >>
  `rest_word_search_rep ctx func cenv cx e es sa sm s0 es' tv vv
      needleop needle lenop len q` by
    (`sm.cs_next_var <= cl.cs_next_var` by decide_tac >>
     `(!z. needleop = Var z ==> not_fresh_at cl z) /\
      (!z. lenop = Var z ==> not_fresh_at cl z)` by metis_tac[] >>
     drule_all rest_word_search_rep_load >> simp[]) >>
  drule_all exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_run_frame >> strip_tac >>
  drule exprSimBopRestWordLayoutTheory.rest_word_ptr_load_fresh >> strip_tac >>
  `not_fresh_at cl h.rw_idx /\ not_fresh_at cl h.rw_result` by
    metis_tac[exprSimBopRestWordLayoutTheory.rest_word_loop_prefix_handles_old] >>
  `FLOOKUP q.vs_vars h.rw_idx = FLOOKUP p.vs_vars h.rw_idx /\
   FLOOKUP q.vs_vars h.rw_result = FLOOKUP p.vs_vars h.rw_result` by
    (conj_tac >>
     qpat_assum `!x. (!i. _) ==> FLOOKUP _ _ = _` irule >>
     fs[listTheory.EVERY_MEM]) >>
  `!z. arrop = Var z ==> FLOOKUP q.vs_vars z = FLOOKUP p.vs_vars z` by
    (rpt strip_tac >>
     qpat_assum `!x. (!i. _) ==> FLOOKUP _ _ = _` irule >>
     `not_fresh_at cl z` by metis_tac[] >> fs[listTheory.EVERY_MEM]) >>
  `eval_operand arrop p = SOME baseword` by fs[Abbr `R`] >>
  `eval_operand arrop q = SOME baseword` by
    (`q.vs_labels = p.vs_labels` by
       (qpat_assum `q = p with vs_vars := _`
          (mp_tac o AP_TERM ``\(st:venom_state). st.vs_labels``) >> simp[]) >>
     Cases_on `arrop` >> fs[venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def]) >>
  `R q` by simp[Abbr `R`] >>
  `R (update_var matched (bool_to_word (elem i = needle)) q)` by metis_tac[] >>
  drule_all exprSimBopRestWordLoadPathTheory.rest_word_ptr_load_code >> strip_tac >>
  `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\
          j.inst_opcode <> GAS) (emitted_insts cl cm)` by
    (qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _` mp_tac >>
     pure_rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (fn th => gen_tac >> strip_tac >> drule th) >>
     simp[] >> strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  irule rest_word_body_loaded_path >> simp[] >>
  qexistsl [`a`, `addr`, `arrop`, `b`, `baseword`, `c`, `d`, `e'`,
    `emitted_insts cl cm`, `matched`, `mulvar`, `needleop`, `off`, `q`, `stride`, `totalvar`, `v`] >>
  simp[] >>
  `arrop <> Var mulvar /\ arrop <> Var totalvar` by
    (rpt strip_tac >> metis_tac[]) >>
  `~q.vs_halted /\ q.vs_current_bb = p.vs_current_bb` by
    (qpat_assum `q = p with vs_vars := _` SUBST1_TAC >>
     Cases_on `0 < off` >> simp[Abbr `p`, venomStateTheory.update_var_def]) >>
  fs[Abbr `R`, rest_word_search_rep_def]
QED

Finalise rest_word_compiled_search
