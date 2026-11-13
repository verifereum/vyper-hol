Theory lowerDloadReturnRestore
Ancestors
  lowerDloadSharedState o1LowerDloadJointRestore venomExecSemantics
  venomState ptrDiscipline finite_map pred_set list
  o1LowerDloadRunnerBoundary lowerDloadOperationalClosure o1PassLift
  lowerDloadReachability lowerDloadOwnership lowerDloadOwnerTransport
  lowerDloadTableSupport lowerDloadFrameRepresentation
  lowerDloadFrameCertificate lowerDloadCoverageInvariant lowerDloadPairedBoundary
  lowerDloadOpaqueExecution lowerDloadTargetGeometry lowerDloadLifetime

(* Retained environment comes from the caller; global observations and masks
   come from the current callee, never from the saved memory snapshot. *)
Theorem ld_shared_state_return_slice:
  callerS.vs_call_ctx = callerT.vs_call_ctx /\
  callerS.vs_tx_ctx = callerT.vs_tx_ctx /\
  callerS.vs_block_ctx = callerT.vs_block_ctx /\
  callerS.vs_prev_hashes = callerT.vs_prev_hashes /\
  callerS.vs_code = callerT.vs_code /\
  callerS.vs_data_section = callerT.vs_data_section /\
  callerS.vs_fmp = callerT.vs_fmp /\
  callerS.vs_call_entry_fmp = callerT.vs_call_entry_fmp /\
  callerS.vs_initial_fmp = callerT.vs_initial_fmp /\
  ld_shared_state tn un endS endT /\
  bind_outputs os xs (merge_callee_state callerS endS) = SOME s' /\
  bind_outputs ot xt (merge_callee_state callerT endT) = SOME t' ==>
  ld_shared_state (tn with t_var := ms) (un with t_var := mt) s' t'
Proof
  strip_tac >>
  dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
  dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
  fs[ld_shared_state_def, merge_callee_state_def]
QED

Theorem ld_shared_state_return_restore:
  ld_shared_state savedS savedT callerS callerT /\
  ld_shared_state tn un endS endT /\
  bind_outputs os xs (merge_callee_state callerS endS) = SOME s' /\
  bind_outputs ot xt (merge_callee_state callerT endT) = SOME t' ==>
  ld_shared_state (tn with t_var := ms) (un with t_var := mt) s' t'
Proof
  strip_tac >> irule ld_shared_state_return_slice >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  fs[ld_shared_state_def]
QED

(* Definedness is weaker than value agreement and needs no distinct outputs:
   overwriting a variable with the same word makes it defined on both sides. *)
Theorem ld_bind_fold_definedness[local]:
  !kvs s t.
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
    !v. v IN V ==>
      (lookup_var v (FOLDL (\st (k,w). update_var k w st) s kvs) = NONE <=>
       lookup_var v (FOLDL (\st (k,w). update_var k w st) t kvs) = NONE)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> fs[lookup_var_def]
QED

Theorem ld_bind_outputs_definedness:
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  bind_outputs outs vals s = SOME s' /\
  bind_outputs outs vals t = SOME t' ==>
  !v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)
Proof
  simp[bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> irule ld_bind_fold_definedness >> qexists_tac `V` >> simp[]
QED

Theorem ld_return_definedness:
  (!v. v IN V ==>
    (lookup_var v callerS = NONE <=> lookup_var v callerT = NONE)) /\
  bind_outputs outs vals (merge_callee_state callerS endS) = SOME s' /\
  bind_outputs outs vals (merge_callee_state callerT endT) = SOME t' ==>
  !v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)
Proof
  rpt strip_tac >> irule ld_bind_outputs_definedness >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexists_tac `merge_callee_state callerS endS` >>
  fs[lookup_var_def, merge_callee_state_def]
QED

Theorem ld_frame_reach_call_ctx:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
    s.vs_call_ctx = s0.vs_call_ctx
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >> rpt strip_tac >>
  simp[] >> metis_tac[ld_step_ok_call_ctx, ld_enters_block_call_ctx]
QED

Theorem ld_callee_prefix_call_ctx:
  setup_callee fn args caller = SOME s0 /\ frame_reach C fn s0 i s ==>
  s.vs_call_ctx = caller.vs_call_ctx
Proof
  metis_tac[ld_frame_reach_call_ctx, ld_setup_callee_call_ctx]
QED

Theorem ld_annotated_return_call_ctx:
  o1_ctx_shape C /\
  ld_annotated_reachable vs0 C (sf::astk) k L AP AG tn fn i s /\
  ld_stack_origin vs0 C (MAP ld_erase_frame (sf::astk)) fn s0 ==>
  s.vs_call_ctx = sf.lf_state.vs_call_ctx
Proof
  strip_tac >> drule_all ld_annotated_prefix_at_origin >> strip_tac >>
  qpat_x_assum `ld_stack_origin _ _ _ _ _` mp_tac >>
  simp[ld_stack_origin_cons, ld_erase_frame_def] >> rpt strip_tac >>
  drule_all ld_callee_prefix_call_ctx >> simp[]
QED

(* A return only deletes head provenance roots and pops the saved head. *)
Theorem ld_return_owner_subset:
  (!owner bs sz. ld_live (sf::astail) L AP AG (owner,(bs,sz)) ==>
    owner IN live) ==>
  {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} SUBSET live
Proof
  strip_tac >> simp[SUBSET_DEF] >> rpt strip_tac >>
  drule ld_live_restrict_shape >> strip_tac >>
  first_x_assum irule >> qexistsl [`bs`, `sz`] >>
  irule ld_live_saved_projection >> qexistsl [`sf`, `astail`] >>
  simp[]
QED

(* The same table is retained for all roots, including parameters and older
   saved frames. Consumers need not choose a fresh restriction witness. *)
Theorem ld_return_owner_lookup:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} ==>
  !owner bs sz.
    ld_live astail sf.lf_local sf.lf_params
      (DRESTRICT sf.lf_prov keep) (owner,(bs,sz)) ==>
    FLOOKUP (DRESTRICT E owners) owner = FLOOKUP E owner
Proof
  rpt strip_tac >> simp[FLOOKUP_DRESTRICT] >> metis_tac[IN_GSPEC_IFF]
QED

Theorem ld_return_head_table:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  ld_frame_embedding E sf.lf_local H s t /\
  LIST_REL (ld_owned_selection E) sf.lf_params BP /\
  (!v. ld_owned_selection E (FLOOKUP (DRESTRICT sf.lf_prov keep) v)
    (FLOOKUP BH v)) ==>
  ld_frame_embedding (DRESTRICT E owners) sf.lf_local H s t /\
  LIST_REL (ld_owned_selection (DRESTRICT E owners)) sf.lf_params BP /\
  (!v. ld_owned_selection (DRESTRICT E owners)
    (FLOOKUP (DRESTRICT sf.lf_prov keep) v) (FLOOKUP BH v))
Proof
  strip_tac >>
  `!owner bs sz.
    ld_live astail sf.lf_local sf.lf_params (DRESTRICT sf.lf_prov keep)
      (owner,(bs,sz)) ==>
    FLOOKUP (DRESTRICT E owners) owner = FLOOKUP E owner` by
    (rpt strip_tac >> simp[FLOOKUP_DRESTRICT] >> metis_tac[IN_GSPEC_IFF]) >> gvs[] >>
  conj_tac
  >- (irule ld_frame_embedding_support >> qexists_tac `E` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  conj_tac
  >- (irule ld_owned_params_support >> qexists_tac `E` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  gen_tac >> irule ld_owned_selection_support >> qexists_tac `E` >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[ld_live_def, ld_selected_def] >> metis_tac[]
QED

Theorem ld_return_tail_table:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  MEM f astail /\ ld_saved_embedded V E keys d A f g ==>
  ld_saved_embedded V (DRESTRICT E owners) keys d A f g
Proof
  strip_tac >> irule ld_saved_embedded_restrict >> simp[] >>
  rpt strip_tac >> gvs[] >> simp[] >>
  qexistsl [`bs`, `sz`] >> simp[ld_live_def] >> metis_tac[]
QED

Theorem ld_return_stack_table:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g)
    astail gtail ==>
  LIST_REL (\f g. ?V keys d A.
    ld_saved_embedded V (DRESTRICT E owners) keys d A f g) astail gtail
Proof
  strip_tac >> irule ld_saved_stack_restrict >> simp[] >>
  rpt strip_tac >> gvs[] >> simp[] >>
  qexistsl [`bs`, `sz`] >> simp[ld_live_def] >> metis_tac[]
QED

(* This transports actual parameter words, not merely parameter provenance.
   One interface covers the resumed caller and every retained saved frame. *)
Theorem ld_return_parameter_values:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  (ps = sf.lf_params \/ ?f. MEM f astail /\ ps = f.lf_params) /\
  LENGTH ps = LENGTH xs /\
  (!q. q < LENGTH xs ==>
    ld_owned_value E (EL q ps) (EL q pt) Ms Mt (EL q xs) (EL q ys)) ==>
  !q. q < LENGTH xs ==>
    ld_owned_value (DRESTRICT E owners) (EL q ps) (EL q pt)
      Ms Mt (EL q xs) (EL q ys)
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  irule ld_owned_value_support >> qexists_tac `E` >> simp[] >>
  rpt strip_tac >>
  `MEM (SOME (owner,(bs,sz))) ps` by metis_tac[EL_MEM] >>
  `owner IN owners` by
    (gvs[] >> simp[] >> qexistsl [`bs`, `sz`] >>
     simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  gvs[] >> simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_return_owned_vars_table:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  ld_owned_vars V E (DRESTRICT sf.lf_prov keep) BH tn un s t ==>
  ld_owned_vars V (DRESTRICT E owners) (DRESTRICT sf.lf_prov keep)
    BH tn un s t
Proof
  strip_tac >> irule ld_owned_vars_support >> qexists_tac `E` >> simp[] >>
  rpt strip_tac >>
  `owner IN owners` by
    (gvs[] >> simp[] >> qexistsl [`bs`, `sz`] >>
     simp[ld_live_def, ld_selected_def] >> metis_tac[]) >>
  gvs[] >> simp[FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ld_return_mask_bounds:
  (!v. (case FLOOKUP ms v of NONE => {} | SOME m => m) SUBSET count 32) /\
  (!v. (case FLOOKUP mt v of NONE => {} | SOME m => m) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm ==>
  (!v. op_taint (tn with t_var := DRESTRICT ms keepS) (Var v) SUBSET count 32) /\
  (!v. op_taint (un with t_var := DRESTRICT mt keepT) (Var v) SUBSET count 32) /\
  (un with t_var := DRESTRICT mt keepT).t_stor SUBSET
    (tn with t_var := DRESTRICT ms keepS).t_stor /\
  (un with t_var := DRESTRICT mt keepT).t_trans SUBSET
    (tn with t_var := DRESTRICT ms keepS).t_trans /\
  (un with t_var := DRESTRICT mt keepT).t_imm SUBSET
    (tn with t_var := DRESTRICT ms keepS).t_imm
Proof
  simp[op_taint_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  Cases_on `v IN keepS` >> Cases_on `v IN keepT` >> simp[]
QED

Theorem ld_return_global_companions:
  callerS.vs_call_ctx = endS.vs_call_ctx /\
  endS.vs_gas_readings = endT.vs_gas_readings /\
  (!a. a <> endS.vs_call_ctx.cc_address ==>
    (endS.vs_accounts a).storage = (endT.vs_accounts a).storage) /\
  (!a. a <> endS.vs_call_ctx.cc_address ==>
    endS.vs_transient a = endT.vs_transient a) /\
  bind_outputs os xs (merge_callee_state callerS endS) = SOME s' /\
  bind_outputs ot xt (merge_callee_state callerT endT) = SOME t' ==>
  s'.vs_gas_readings = t'.vs_gas_readings /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    s'.vs_transient a = t'.vs_transient a)
Proof
  strip_tac >>
  dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
  dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
  fs[merge_callee_state_def]
QED

Theorem ld_return_frame_data:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  ld_saved_embedded U E keys d A sf tf /\
  (!v. v IN V ==> (lookup_var v sf.lf_state = NONE <=>
                    lookup_var v tf.lf_state = NONE)) /\
  bind_outputs sf.lf_inst.inst_outputs vals
    (merge_callee_state sf.lf_state endS) = SOME s' /\
  bind_outputs sf.lf_inst.inst_outputs vals
    (merge_callee_state tf.lf_state endT) = SOME t' /\
  ld_owned_vars U E (DRESTRICT sf.lf_prov keep) (DRESTRICT tf.lf_prov keep)
    (entry_taint with t_var := DRESTRICT sf.lf_tvar keep)
    (entry_taint with t_var := DRESTRICT tf.lf_tvar keep) s' t' /\
  sf.lf_state.vs_call_ctx = tf.lf_state.vs_call_ctx /\
  sf.lf_state.vs_tx_ctx = tf.lf_state.vs_tx_ctx /\
  sf.lf_state.vs_block_ctx = tf.lf_state.vs_block_ctx /\
  sf.lf_state.vs_prev_hashes = tf.lf_state.vs_prev_hashes /\
  sf.lf_state.vs_code = tf.lf_state.vs_code /\
  sf.lf_state.vs_data_section = tf.lf_state.vs_data_section /\
  sf.lf_state.vs_fmp = tf.lf_state.vs_fmp /\
  sf.lf_state.vs_call_entry_fmp = tf.lf_state.vs_call_entry_fmp /\
  sf.lf_state.vs_initial_fmp = tf.lf_state.vs_initial_fmp /\
  ld_shared_state tn un endS endT ==>
  ld_frame_data V U (DRESTRICT E owners) sf.lf_local tf.lf_local
    sf.lf_params tf.lf_params (DRESTRICT sf.lf_prov keep)
    (DRESTRICT tf.lf_prov keep)
    (tn with t_var := DRESTRICT sf.lf_tvar keep)
    (un with t_var := DRESTRICT tf.lf_tvar keep) s' t'
Proof
  strip_tac >>
  `ld_frame_embedding E sf.lf_local tf.lf_local s' t'` by
    (drule ld_saved_embedded_layout >>
     dxrule ld_bind_outputs_allocas >>
     dxrule ld_bind_outputs_allocas >>
     simp[ld_frame_embedding_def, merge_callee_state_def]) >>
  `!v. ld_owned_selection E (FLOOKUP (DRESTRICT sf.lf_prov keep) v)
    (FLOOKUP (DRESTRICT tf.lf_prov keep) v)` by
    (gen_tac >> Cases_on `v IN keep` >>
     simp[FLOOKUP_DRESTRICT, ld_owned_selection_def] >>
     metis_tac[ld_saved_embedded_prov, ld_owned_selection_def]) >>
  drule ld_saved_embedded_params >> strip_tac >>
  drule_all ld_return_head_table >> strip_tac >>
  simp[ld_frame_data_def] >> conj_tac
  >- (irule ld_return_owned_vars_table >>
      conj_tac >- (qexists_tac `astail` >> simp[]) >>
      fs[ld_owned_vars_def, op_taint_def]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all ld_return_definedness >> simp[]) >>
  irule ld_shared_state_return_slice >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_return_parameter_envelope:
  owners = {owner | ?bs sz. ld_live astail sf.lf_local sf.lf_params
    (DRESTRICT sf.lf_prov keep) (owner,(bs,sz))} /\
  bind_outputs os xs (merge_callee_state sf.lf_state endS) = SOME s' /\
  bind_outputs ot xt (merge_callee_state tf.lf_state endT) = SOME t' /\
  ((CS.ctx_entry = SOME sf.lf_fn.fn_name /\ sf.lf_params = [] /\
      tf.lf_params = [] /\ entry_fn_no_params sf.lf_fn) \/
   (LENGTH sf.lf_params = LENGTH sf.lf_state.vs_params /\
    LENGTH tf.lf_params = LENGTH tf.lf_state.vs_params /\
    LENGTH sf.lf_state.vs_params = LENGTH tf.lf_state.vs_params /\
    (!q. q < LENGTH sf.lf_state.vs_params ==>
      ld_owned_value E (EL q sf.lf_params) (EL q tf.lf_params) {} {}
        (EL q sf.lf_state.vs_params) (EL q tf.lf_state.vs_params)))) ==>
  ((CS.ctx_entry = SOME sf.lf_fn.fn_name /\ sf.lf_params = [] /\
      tf.lf_params = [] /\ entry_fn_no_params sf.lf_fn) \/
   (LENGTH sf.lf_params = LENGTH s'.vs_params /\
    LENGTH tf.lf_params = LENGTH t'.vs_params /\
    LENGTH s'.vs_params = LENGTH t'.vs_params /\
    (!q. q < LENGTH s'.vs_params ==>
      ld_owned_value (DRESTRICT E owners)
        (EL q sf.lf_params) (EL q tf.lf_params) {} {}
        (EL q s'.vs_params) (EL q t'.vs_params))))
Proof
  strip_tac >>
  `s'.vs_params = sf.lf_state.vs_params /\
   t'.vs_params = tf.lf_state.vs_params` by
    (dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
     dxrule ld_bind_outputs_vars_only >> disch_then SUBST1_TAC >>
     simp[merge_callee_state_def]) >>
  simp[] >> disj2_tac >> rpt strip_tac >>
  irule ld_return_parameter_values >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`astail`, `keep`, `sf`] >> simp[]
QED

(* Selection certificates pin the source base and size in the unique table
   entry. An owner alone is not a certificate for an arbitrary source base. *)
Theorem ld_selected_source_entry:
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_selected L AP AG (owner,(bs,sz)) ==>
  ?bt. ld_site_entry E owner bs bt sz
Proof
  strip_tac >>
  `!ps. MEM ps AP ==> ?pt. MEM pt BP /\ ld_owned_selection E ps pt` by
    (gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `ld_selected _ _ _ _` mp_tac >>
  simp[ld_selected_def] >> strip_tac
  >- (drule ld_frame_embedding_selection >>
      disch_then (qspec_then `id` mp_tac) >>
      fs[ld_owned_selection_def] >> metis_tac[]) 
  >- (first_x_assum drule >> simp[ld_owned_selection_def] >> metis_tac[]) >>
  qpat_x_assum `!v. ld_owned_selection _ _ _`
    (qspec_then `v` mp_tac) >> simp[ld_owned_selection_def] >> metis_tac[]
QED

Theorem ld_live_source_entry:
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) astk gstk /\
  ld_live astk L AP AG (owner,(bs,sz)) ==>
  ?bt. ld_site_entry E owner bs bt sz
Proof
  strip_tac >>
  `!f. MEM f astk ==> ?g. MEM g gstk /\
    (?V keys d A. ld_saved_embedded V E keys d A f g)` by
    (gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  qpat_x_assum `ld_live _ _ _ _ _` mp_tac >>
  simp[ld_live_def] >> strip_tac
  >- (irule ld_selected_source_entry >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  irule ld_selected_source_entry >> goal_assum (drule_at Any) >>
  metis_tac[ld_saved_embedded_layout, ld_saved_embedded_params,
    ld_saved_embedded_prov]
QED

Theorem ld_annotated_owner_endpoints:
  ld_annotated_reachable vs0 C astk k L AP AG tn fn i s /\
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) astk gstk /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\
  owner IN {owner | ?bs sz. ld_live astk L AP AG (owner,(bs,sz))} /\
  ld_site_entry E owner bs bt sz ==>
  bs+sz <= s.vs_alloca_next /\ bt+sz <= t.vs_alloca_next
Proof
  simp[] >> strip_tac >>
  drule_all ld_live_source_entry >> strip_tac >>
  `bs' = bs /\ sz' = sz` by
    (fs[ld_site_entry_def] >> metis_tac[]) >> gvs[] >>
  conj_tac
  >- (drule_all ld_annotated_live_endpoint >> simp[]) >>
  irule ld_paired_live_endpoints >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

(* Return boundaries must be unconditional kernel theorems. *)
val _ = List.app (fn (name,th) =>
  if null (hyp th) then print ("KERNEL_HYP_EMPTY " ^ name ^ "\n")
  else raise Fail ("unexpected kernel hypothesis: " ^ name))
  [("ld_return_owner_lookup",ld_return_owner_lookup),
   ("ld_return_head_table",ld_return_head_table),
   ("ld_return_owned_vars_table",ld_return_owned_vars_table),
   ("ld_return_frame_data",ld_return_frame_data)];
