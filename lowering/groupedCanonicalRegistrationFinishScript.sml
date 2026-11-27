(* Convert the canonical registration fold's terminal witnesses to body inputs. *)
Theory groupedCanonicalRegistrationFinish
Ancestors
  groupedDefaultState groupedDefaultHorizon externalEntryBound selectedAcceptedFold
  defaultConcreteRegistrationDefs entryStateRel allocaFrontierBound loweringPosts
  fragFuel fragGasOriginPtr fragGasOrigin fragGasMode fragGasPathFrameMem
  vyperCall vyperInterpreter vyperState vyperStorageFootprint
  loweringStateRelDefs compileEnv ptrDiscipline venomExecSemantics venomState venomInst
  finite_map list words

Theorem grouped_canonical_registration_finish:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  initial_venom_state_rel tops am tx vs /\
  send_call_value mut cx (initial_state am [FEMPTY] with
    <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),ev) /\
  bind_arguments (type_env tops) args tx.args = SOME envb /\
  ALL_DISTINCT (MAP FST args) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (MAP SND args) tvs /\
  (!k. ~MEM k (MAP FST args) ==> FLOOKUP cf.ce_vars k = NONE) /\
  local_ptrs_reserved cf sa /\
  cf.ce_modules = [(NONE,tops)] /\ cf.ce_module = NONE /\ ~cf.ce_is_ctor /\ cf.ce_imm_alloca = NONE /\
  cf.ce_return_pc = NONE /\ cf.ce_return_buf = NONE /\
  storage_vars_rel (cf with ce_vars := FEMPTY) cx /\
  transient_vars_rel (cf with ce_vars := FEMPTY) cx /\
  immutable_section_layout (cf with ce_vars := FEMPTY) tops /\
  fn_inst_ids_distinct fn /\
  selected_registration_frame vs entry_taint u tn /\
  selected_registration_resources ctx fn site 0 reg u /\
  default_registration_resources ctx fn site 0 reg u (tn with t_mem := {}) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (s,FEMPTY,entry_taint) [] (OK u,G,tn)) /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (u,G,tn) [] (OK t,J,tz)) /\
  t.vs_data_section = u.vs_data_section /\
  ((!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) ==>
   (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w)) /\
  (!j. j < LENGTH args ==> ?aid q p n.
    MEM (mk_inst aid ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
    aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (p,n) /\
    FLOOKUP cf.ce_vars (FST (EL j args)) = SOME (PtrVar (Var q) n) /\
    lookup_var q t = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
    ptr_covers J tz q t n /\ val_wf (EL j tvs) (EL j tx.args) /\
    val_footprint (EL j tvs) (EL j tx.args) <= n /\
    (!mem. mem_agree_outside tz.t_mem t.vs_memory mem ==>
      val_in_memory (EL j tvs) (EL j tx.args) p mem)) /\
  (!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < sa.cs_next_id) /\
  alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from 0 t /\
  fresh_vars_wrt sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts /\
  tz.t_stor = tn.t_stor /\ tz.t_trans = tn.t_trans /\ tz.t_imm = tn.t_imm /\
  t.vs_call_ctx = u.vs_call_ctx /\
  t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
  t.vs_logs = u.vs_logs /\ t.vs_outcomes = u.vs_outcomes /\
  t.vs_requests = u.vs_requests /\
  t.vs_pending_deletions = u.vs_pending_deletions /\ t.vs_tx_ctx = u.vs_tx_ctx /\
  t.vs_block_ctx = u.vs_block_ctx /\ t.vs_fmp = u.vs_fmp /\
  t.vs_gas_readings = u.vs_gas_readings ==>
  ?es.
    (!gx. external_entry_bound tops am tx vs.vs_outcomes gx mut args [] (es with gas_obs := gx)) /\
    es.gas_obs = [] /\ storage_trace_domain cx (initial_state am []) es.storage_trace /\
    at_point sa t /\ fresh_vars_wrt sa t /\ return_buf_frame NONE cf sa t /\
    (!H:(bool # bytes32 # type_value) list # num list.
      stmt_state_rel H ctx fn cf cx es t /\ ghost_inv_at (cx_dead H cx) 0 NONE cf cx es J tz t) /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,FEMPTY,entry_taint) [] (OK t,J,tz)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `send_call_value mut cx (initial_state am [envb] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
      (INL (),ev with scopes := [envb])` by
    (drule send_call_value_with_scopes >>
     simp[initial_state_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!gx. external_entry_bound tops am tx vs.vs_outcomes gx mut args []
      ((ev with scopes := [envb]) with gas_obs := gx)` by
    (qpat_assum `cx = _` SUBST_ALL_TAC >> drule_all external_entry_bound_no_defaults >> simp[]) >>
  `ev.gas_obs = [] /\ ev.storage_trace = []` by
    (qpat_assum `send_call_value _ _ _ = (INL (),ev)`
       (mp_tac o MATCH_MP send_call_value_accounts) >> simp[initial_state_def]) >>
  `storage_trace_domain cx (initial_state am []) ev.storage_trace` by
    simp[storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
         storage_observations_ok_def, storage_trace_regions_def,
         storage_trace_locks_def, regions_consistent_def, storage_locks_separated_def,
         storage_well_formed_on_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def] >>
  suspend "entry_state"
QED

Resume grouped_canonical_registration_finish[entry_state]:
  `cx.txn = tx` by simp[initial_evaluation_context_def] >>
  `stmt_state_rel (([],[]):(bool # bytes32 # type_value) list # num list)
     ctx fn (cf with ce_vars := FEMPTY) cx ev u` by
    (drule_all (SIMP_RULE (srw_ss()) []
       (Q.INST [`ce` |-> `cf with ce_vars := FEMPTY`]
         (SPEC_ALL grouped_empty_registration_state))) >>
     simp[]) >>
  `selected_registration_owners fn (MAP FST args) tvs tx.args (LENGTH args) cf sa t J tz` by
    (qpat_x_assum `!j. j < LENGTH args ==> ?aid q p n. _` mp_tac >>
     simp[selected_registration_owners_def, EL_MAP]) >>
  `selected_registration_resources ctx fn site 0 sa t` by
    (fs[selected_registration_resources_def] >> metis_tac[]) >>
  `t.vs_alloca_next < dimword (:256)` by
    drule_all_then ACCEPT_TAC alloca_frontier_inv_bound >>
  `gas_origin_ptr_path (cx_dead ([],[]) cx,0,K F,ctx,fn,[]) (u,G,tn) [] (OK t,J,tz)` by simp[] >>
  `t.vs_code = u.vs_code` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >>
     disch_then (assume_tac o MATCH_MP gas_marked_path_exec) >>
     drule gas_path_code_labels >> simp[]) >>
  `selected_registration_frame u tn t tz` by simp[selected_registration_frame_def] >>
  `tz.t_stor = {} /\ tz.t_trans = {} /\ tz.t_imm = {}` by
    fs[selected_registration_frame_def, entry_taint_def] >>
  suspend "body_inputs"
QED

Resume grouped_canonical_registration_finish[body_inputs]:
  `LENGTH tx.args = LENGTH args` by metis_tac[bind_arguments_length] >>
  `local_ptrs_rel fn cf [envb] t` by
    drule_all_then ACCEPT_TAC selected_registration_terminal_locals >>
  `stmt_state_rel (([],[]):(bool # bytes32 # type_value) list # num list)
      ctx fn cf cx (ev with scopes := [envb]) t` by
    drule_all_then ACCEPT_TAC grouped_positional_state_frame >>
  `!H:(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx fn cf cx (ev with scopes := [envb]) t /\
     ghost_inv_at (cx_dead H cx) 0 NONE cf cx (ev with scopes := [envb]) J tz t` by
    (qx_gen_tac `H` >> conj_tac
     >- metis_tac[grouped_default_empty_mask_state] >>
     irule grouped_registered_owners_ghost >> simp[] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,FEMPTY,entry_taint) [] (OK t,J,tz)` by
    metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  qexists_tac `ev with scopes := [envb]` >>
  gvs[at_point_def, return_buf_frame_def]
QED

Finalise grouped_canonical_registration_finish
