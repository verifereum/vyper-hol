(* Simulation transport at the very same local-write endpoint as the
   pointer path. No independent execution is selected. *)
Theory assignBasePtrLocalSemantic
Ancestors typedMemoryCopy stmtSimAssignStore localMemoryStorePath
  exprLoweringProps stmtSimDefs compileEnv loweringStateRelDefs localPtrsProps venomState
  valueEncoding finite_map vyperState

Theorem assign_base_local_write_state_post:
  !ctx fn cenv cx es s t sa id p sz dst pre sc entry rest v n.
    stmt_state_rel ctx fn cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME dst /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\
    n <= sz /\ n <= type_memory_size entry.type /\
    typed_copy_state_frame sa (w2n dst) n s t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
    val_wf entry.type v /\ val_in_memory entry.type v (w2n dst) t.vs_memory ==>
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx` >>
  `u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` by
    fs[Abbr `u`, typed_copy_state_frame_def, venom_state_component_equality] >>
  `!q. ~not_local_ptr cenv es.scopes q ==> lookup_var q u = lookup_var q s` by
    (rpt strip_tac >> fs[not_local_ptr_def, local_ptrs_reserved_def,
       typed_copy_state_frame_def, Abbr `u`, lookup_var_def] >> metis_tac[]) >>
  `!b k. b+k <= w2n dst \/ w2n dst + type_memory_size entry.type <= b ==>
    mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory` by
    (rpt strip_tac >> fs[typed_copy_state_frame_def, typed_copy_frame_def, Abbr `u`] >>
     first_x_assum irule >> decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es u` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >> qexists_tac `n` >>
     fs[Abbr `u`, typed_copy_state_frame_def, typed_copy_frame_def,
        venom_state_component_equality] >> metis_tac[]) >>
  `val_in_memory entry.type v (w2n dst) u.vs_memory` by simp[Abbr `u`] >>
  drule_all stmt_state_rel_write_local >> simp[Abbr `u`, stmt_state_rel_inst_idx]
QED
