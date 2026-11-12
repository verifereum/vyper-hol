Theory exprSimAbiDecodeQuantifiedLift
Ancestors
  exprSimAbiDecodeFreshProbe exprSimAbiDecodeBuiltin abiDecoderReentry
  exprSimAbiDecodeStepLift abiDecoderSiteEffect actualDecoderSites
  exprSimAbiDecodeOutcomeAllocation exprSimAbiDecodeEndpointFrame
  exprSimAbiDecodeObserverReject
  exprSimAbiDecodePathReconstruct exprSimAbiDecodePathLift
  abiEncoderVarTransport exprSimAbiGasBridge abiEncoderObserver
  abiDecoderVarExtend abiDecoderLoop fragExec venomExecSemantics venomState
  venomInst relation

Theorem abi_decode_observer_success_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t) /\
  (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut sb /\
  abi_decoder_vars_extend extras s s' ==>
  ?u u'. stop_view u = stop_view t /\
    abi_decoder_vars_extend extras u u' /\
    local_prefix ctx fn (frag_observer_cut sb) s' u' /\
    abi_decode_sim ctx fn s' u'
Proof
  strip_tac >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[] >>
     conj_tac >- (qexists_tac `fuel` >> simp[]) >>
     simp[stop_view_def, halt_state_def]) >>
  drule_all abi_encoder_local_prefix_extend >> strip_tac >>
  `local_prefix ctx fn (frag_observer_cut sb) s' t'` by
    (qpat_assum `abi_decoder_vars_extend extras s s'`
       (mp_then Any strip_assume_tac abi_encoder_vars_extend_control) >>
     qpat_assum `local_prefix _ _ _ s' t'`
       (mp_then Any mp_tac frag_observer_prefix_transfer) >>
     disch_then (qspecl_then [`sa`, `sb`, `fn`, `id`] mp_tac) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u`, `t'`] >> simp[] >>
  metis_tac[local_prefix_sim]
QED

Theorem abi_decode_observer_rtc_transfer:
  !s t. RTC (abi_observer_step ctx (frag_observer sa sb fn id)
                    (frag_observer_cut sb)) s t ==>
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
  RTC (abi_observer_step ctx fn (frag_observer_cut sb)) s t
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `abi_observer_step _ _ _ s middle` >>
  irule (cj 2 RTC_RULES) >> qexists_tac `middle` >>
  conj_tac
  >- (irule frag_observer_step_transfer >> metis_tac[]) >>
  drule_all frag_observer_region_closed >>
  simp[observer_region_closed_def] >> strip_tac >>
  `(middle.vs_current_bb,middle.vs_inst_idx) IN frag_observer_region sa sb` by
    (qpat_x_assum `!id' ctx' s t. _`
       (qspecl_then [`id`, `ctx`, `s`, `middle`] mp_tac) >> simp[]) >>
  qpat_x_assum `cs_extends _ _ /\ _ ==> _` mp_tac >> simp[]
QED

Theorem abi_decode_observer_reject_transfer_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v /\
  abi_decoder_vars_extend extras s s' ==>
  ?v' fuel'. abi_decoder_vars_extend extras v v' /\
    run_from fuel' ctx fn s' = Abort Revert_abort v'
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_decode_frag_observer_reject_lift >> strip_tac >>
  `RTC (abi_observer_step ctx fn (frag_observer_cut sb)) s' u'` by
    (irule abi_decode_observer_rtc_transfer >>
     qexistsl_tac [`id`, `sa`] >> simp[] >>
     qpat_assum `abi_decoder_vars_extend extras s s'`
       (mp_then Any strip_assume_tac abi_encoder_vars_extend_control) >>
     drule frag_observer_start_region >> gvs[] >> metis_tac[]) >>
  drule_all frag_observer_entry_code_agrees >>
  disch_then (qspec_then `id` mp_tac) >>
  simp[frag_entry_code_agrees_def] >> strip_tac >>
  qpat_x_assum `!lbl idx bb inst. _`
    (qspecl_then [`u'.vs_current_bb`, `u'.vs_inst_idx`, `bb`, `inst`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `v'` >> simp[] >>
  irule abi_decode_observer_rtc_reject >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem abi_decode_observer_continuation_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!fuel r. run_from fuel ctx (frag_observer sa sb fn id) t = r /\
    (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx (frag_observer sa sb fn id) s = r) /\
  abi_decoder_vars_extend extras s s' ==>
  ?u u'. stop_view u = stop_view t /\
    abi_decoder_vars_extend extras u u' /\
    local_prefix ctx fn (frag_observer_cut sb) s' u' /\
    abi_decode_sim ctx fn s' u'
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `run_from 0 ctx (frag_observer sa sb fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
     qexists_tac `id` >> simp[]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule abi_decode_observer_success_extend >>
  simp[frag_observer_cut_def] >>
  qexistsl_tac [`fuel`, `id`, `s`, `sa`] >> simp[] >>
  drule frag_observer_start_region >> simp[] >> metis_tac[]
QED

(* One run function at a time: the caller keeps fn universally quantified.
   Success consumes a freshly reconstructed continuation, never the pruned one. *)
Theorem abi_decode_observer_outcome_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  abi_decoder_vars_extend extras s s' /\
  (!t u u'. post t /\ stop_view u = stop_view t /\
    abi_decoder_vars_extend extras u u' /\
    local_prefix ctx fn (frag_observer_cut sb) s' u' ==> post' u') /\
  ((?t. post t /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx (frag_observer sa sb fn id) t = r /\
        (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx (frag_observer sa sb fn id) s = r) \/
   (reject /\ ?fuel v.
      run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v)) ==>
  (?t'. post' t' /\ abi_decode_sim ctx fn s' t') \/
  (reject /\ ?fuel v'. run_from fuel ctx fn s' = Abort Revert_abort v')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `(?t. _) \/ _` strip_assume_tac
  >- (drule_all abi_decode_observer_continuation_extend >> strip_tac >>
      disj1_tac >> qexists_tac `u'` >> simp[] >>
      first_x_assum irule >> simp[] >> qexistsl_tac [`t`, `u`] >> simp[]) >>
  drule_all abi_decode_observer_reject_transfer_extend >> strip_tac >>
  disj2_tac >> simp[] >> metis_tac[]
QED

(* Keep the semantic/frame part of the protected outcome separate from its
   continuation. Freshness belongs to the pruned execution, not the caller. *)
Definition abi_decode_success_post_def:
  abi_decode_success_post ce env ty tv bs out d start final ctx func s t <=>
    ?v. evaluate_abi_decode env ty bs = INL v /\
      eval_operand out t = SOME (n2w d) /\ val_in_memory tv v d t.vs_memory /\
      decode_site_effect ctx func start.cs_next_var
        ({a | d <= a /\ a < d + type_memory_bytes ce ty} UNION
         {a | s.vs_alloca_next <= a} UNION
         {a | ?id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
                FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz})
        s t /\
      (!id. id < start.cs_next_id \/ final.cs_next_id <= id ==>
            FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\ ~t.vs_halted
End

Theorem abi_decode_pruned_observer_outcome:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts fn) ==> i.inst_id <> id) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  let pruned = abi_decoder_prune_vars start.cs_next_var s in
  (?t. abi_decode_success_post ce env ty tv bs out d start final ctx func pruned t /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    !fuel r. run_from fuel ctx (frag_observer start final fn id) t = r /\
      (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx (frag_observer start final fn id) pruned = r) \/
  ((?e. evaluate_abi_decode env ty bs = INR e) /\
    ?fuel u. run_from fuel ctx (frag_observer start final fn id) pruned =
      Abort Revert_abort u)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `fn_has_code start final (frag_observer start final fn id)` by
    (irule frag_observer_has_code >> simp[]) >>
  `fn_inst_ids_distinct (frag_observer start final fn id)` by
    (irule frag_observer_ids_distinct >> simp[]) >>
  `!i. MEM i (fn_insts (frag_observer start final fn id)) /\
       i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     irule frag_observer_nonstop_inclusion >> metis_tac[]) >>
  drule_all frag_observer_end_phi_zero >>
  disch_then (qspecl_then [`id`, `fn`] assume_tac) >>
  `eval_operand data (abi_decoder_prune_vars start.cs_next_var s) = SOME (n2w p)` by
    simp[abi_decoder_prune_eval] >>
  `fresh_vars_wrt limit_st (abi_decoder_prune_vars start.cs_next_var s)` by
    (irule abi_decode_pruned_limit_fresh >> simp[]) >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p
     (abi_decoder_prune_vars start.cs_next_var s).vs_memory` by
    simp[abi_decoder_prune_vars_def] >>
  `abi_builtin_decode_site_resources ctx func start final.cs_next_id
     (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
     (type_memory_bytes ce ty) (LENGTH bs) p d
     (abi_decoder_prune_vars start.cs_next_var s)` by
    simp[abi_decode_pruned_resources] >>
  `~(abi_decoder_prune_vars start.cs_next_var s).vs_halted /\
   (abi_decoder_prune_vars start.cs_next_var s).vs_current_bb = start.cs_current_bb /\
   (abi_decoder_prune_vars start.cs_next_var s).vs_inst_idx = LENGTH start.cs_current_insts` by
    simp[abi_decoder_prune_vars_def] >>
  `final.cs_current_insts = [] ==>
    start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb (frag_observer start final fn id).fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  mp_tac lower_abi_decode_outcome >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `abi_decoder_prune_vars start.cs_next_var s` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `frag_observer start final fn id` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  simp[abi_decode_success_post_def] >> metis_tac[]
QED

Theorem abi_decode_success_post_extend:
  abi_decode_success_post ce env ty tv bs out d start final ctx func
    (abi_decoder_prune_vars start.cs_next_var s) t /\
  stop_view u = stop_view t /\
  abi_decoder_vars_extend s.vs_vars u u' /\ ~u'.vs_halted ==>
  abi_decode_success_post ce env ty tv bs out d start final ctx func s
    (u' with vs_returndata := t.vs_returndata)
Proof
  simp_tac bool_ss [abi_decode_success_post_def] >> strip_tac >>
  `eval_operand out u' = SOME (n2w d)` by
    (irule abi_decoder_vars_extend_eval >> qexistsl_tac [`s.vs_vars`, `u`] >>
     simp[] >> drule stop_view_operand >> simp[]) >>
  `u' with vs_returndata := t.vs_returndata = t with vs_vars := u'.vs_vars` by
    (drule abi_decoder_vars_extend_restore >>
     gvs[stop_view_def, halt_state_def, venom_state_component_equality]) >>
  `!op w. abi_decoder_operand_live start.cs_next_var op /\
      eval_operand op s = SOME w ==> eval_operand op u' = SOME w` by
    (rpt strip_tac >> irule abi_decoder_vars_extend_eval >>
     qexistsl_tac [`s.vs_vars`, `u`] >> simp[] >>
     drule stop_view_operand >> disch_then (qspec_then `op` mp_tac) >>
     metis_tac[decode_site_effect_live, abi_decoder_prune_eval]) >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  drule stop_view_fields >> strip_tac >>
  qexists_tac `v` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `eval_operand out u' = _` mp_tac >>
      Cases_on `out` >> simp[eval_operand_def, lookup_var_def]) >>
  gvs[decode_site_effect_def, abi_decoder_prune_vars_def,
      decode_memory_frame_def, decode_static_frame_def, decode_upper_frame_def] >>
  reverse conj_tac >- metis_tac[] >>
  conj_tac
  >- (irule decode_site_resources_fields >> qexists_tac `t` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op w. abi_decoder_operand_live _ op /\ eval_operand op s = _ ==> _`
        (drule_then mp_tac) >> simp[] >>
      Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `t = _`
    (mp_tac o AP_TERM ``\r:venom_state. r with vs_vars := u'.vs_vars``) >> simp[]
QED

Definition abi_decode_success_closed_def:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t <=>
    abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t /\
    FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)) =
      SOME (d,type_memory_bytes ce ty) /\
    ?u rd prev. abi_decode_success_post ce env ty tv bs out d start final ctx func s u /\
      t = u with <|vs_returndata := rd; vs_prev_bb := prev|>
End

Theorem abi_decode_success_closed_transport:
  abi_decode_success_post ce env ty tv bs out d start final ctx func
    (abi_decoder_prune_vars start.cs_next_var s) t /\
  stop_view u = stop_view t /\ abi_decoder_vars_extend s.vs_vars u u' /\
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t /\
  FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)) =
    SOME (d,type_memory_bytes ce ty) /\
  local_prefix ctx fn (frag_observer_cut final) s u' ==>
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s u' /\
  ~u'.vs_halted /\ u'.vs_current_bb = final.cs_current_bb /\
  u'.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  strip_tac >> drule local_prefix_endpoint >>
  simp[frag_observer_cut_def] >> strip_tac >> simp[] >>
  drule_all abi_decode_endpoint_allocation_transport >> strip_tac >>
  drule_all abi_decode_success_post_extend >> strip_tac >>
  simp[abi_decode_success_closed_def] >>
  qexistsl_tac [`u' with vs_returndata := t.vs_returndata`,
                `u'.vs_returndata`, `u'.vs_prev_bb`] >> simp[]
QED

(* fn is arbitrary. Its end-PHI disjunction is the one supplied per run
   function by the gas bridges; no premise is imposed on the counted func. *)
Theorem abi_decode_original_entry_outcome:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  (?t. abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn s t) \/
  ((?e. evaluate_abi_decode env ty bs = INR e) /\
    ?fuel u. run_from fuel ctx fn s = Abort Revert_abort u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  strip_assume_tac frag_observer_fresh_id >>
  mp_tac abi_decode_pruned_observer_outcome >>
  (impl_tac >- simp[]) >> simp_tac bool_ss [LET_THM] >> strip_tac
  >- (`abi_decoder_vars_extend s.vs_vars
         (abi_decoder_prune_vars start.cs_next_var s) s` by
        simp[abi_decoder_prune_extension] >>
      `?u u'. stop_view u = stop_view t /\
        abi_decoder_vars_extend s.vs_vars u u' /\
        local_prefix ctx fn (frag_observer_cut final) s u' /\
        abi_decode_sim ctx fn s u'` by
        (irule abi_decode_observer_continuation_extend >> simp[] >>
         qexistsl_tac [`id`, `abi_decoder_prune_vars start.cs_next_var s`, `start`] >>
         gvs[abi_decoder_prune_vars_def] >> metis_tac[]) >>
      `abi_decode_allocation_floor
         (abi_decoder_prune_vars start.cs_next_var s).vs_alloca_next
         (abi_decoder_prune_vars start.cs_next_var s).vs_allocas t` by
        (irule abi_decode_observer_continuation_floor >>
         simp[abi_decoder_prune_vars_def] >>
         goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >> simp[] >>
         qexistsl_tac [`ctx`, `id`] >> fs[abi_decoder_prune_vars_def]) >>
      `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t` by
        fs[abi_decoder_prune_vars_def] >>
      `FLOOKUP t.vs_allocas (abi_builtin_decode_output_site start
         (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)) =
         SOME (d,type_memory_bytes ce ty)` by
        (irule (cj 2 abi_decode_outcome_allocation) >>
         conj_tac >- (fs[abi_builtin_decode_site_resources_def] >> decide_tac) >>
         goal_assum (drule_at (Pat `lower_abi_decode _ _ _ _ _ _ = _`)) >>
         simp[] >> qexistsl_tac [`ctx`, `fn`, `id`,
           `abi_decoder_prune_vars start.cs_next_var s`] >>
         fs[abi_builtin_decode_site_resources_def, abi_decoder_prune_vars_def]) >>
      drule_all abi_decode_success_closed_transport >> strip_tac >>
      disj1_tac >> qexists_tac `u'` >> simp[]) >>
  `abi_decoder_vars_extend s.vs_vars
     (abi_decoder_prune_vars start.cs_next_var s) s` by
    simp[abi_decoder_prune_extension] >>
  disj2_tac >> simp[] >>
  `?u' fuel'. abi_decoder_vars_extend s.vs_vars u u' /\
     run_from fuel' ctx fn s = Abort Revert_abort u'` by
    (irule abi_decode_observer_reject_transfer_extend >>
     qexistsl_tac [`fuel`, `id`, `abi_decoder_prune_vars start.cs_next_var s`,
                   `start`, `final`] >>
     gvs[abi_decoder_prune_vars_def] >> metis_tac[]) >> metis_tac[]
QED

Theorem abi_decode_success_closed_updates:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s
    (t with <|vs_returndata := rd; vs_prev_bb := prev|>)
Proof
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >>
  gvs[abi_decode_allocation_floor_def] >>
  qexistsl_tac [`u`, `rd`, `prev`] >> gvs[]
QED

Theorem abi_decode_success_closed_returndata:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s
    (t with vs_returndata := rd)
Proof
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >>
  gvs[abi_decode_allocation_floor_def] >>
  qexistsl_tac [`u`, `rd`, `prev`] >> gvs[]
QED

Theorem abi_decode_success_closed_prev_bb:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s
    (t with vs_prev_bb := prev)
Proof
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >>
  gvs[abi_decode_allocation_floor_def] >>
  qexistsl_tac [`u`, `rd`, `prev`] >> gvs[]
QED
