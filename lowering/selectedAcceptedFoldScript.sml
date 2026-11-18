(* Positional registration on the fixed source calldata. *)
Theory selectedAcceptedFold
Ancestors
  selectedAcceptedInterfaces calldataRegistrationExec calldataSourceSize
  calldataSourceCorrespondence calldataRegistrationTerminalBindings
  defaultConcreteRegistrationCompiler fragGasPathFrameMem
  entryPtrSeamRegister entryStateRel allocaFrontierBound rich_list
  compileVyper calldataRegistration ctorRegisterArgs

Definition selected_registration_resources_def:
  selected_registration_resources ctx fn site lo st s <=>
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
    (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit w] /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==> n = w2n w) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ allocas_from lo s /\
    lo <= s.vs_alloca_next /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition selected_registration_frame_def:
  selected_registration_frame s Gtn t Utn <=>
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_code = s.vs_code /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_logs = s.vs_logs /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
    Utn.t_stor = Gtn.t_stor /\ Utn.t_trans = Gtn.t_trans /\ Utn.t_imm = Gtn.t_imm
End

Definition selected_registration_owners_def:
  selected_registration_owners fn names tvs vals i ce st s G tn <=>
    !j. j < i ==> ?aid q p n.
      MEM (mk_inst aid ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
      aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,n) /\
      FLOOKUP ce.ce_vars (EL j names) = SOME (PtrVar (Var q) n) /\
      lookup_var q s = SOME (n2w p) /\ n = type_memory_size (EL j tvs) /\
      ptr_covers G tn q s n /\ val_wf (EL j tvs) (EL j vals) /\
      val_footprint (EL j tvs) (EL j vals) <= n /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory (EL j tvs) (EL j vals) p mem)
End

Theorem selected_registration_frame_trans[local]:
  selected_registration_frame s tn t u /\ selected_registration_frame t u v z ==>
  selected_registration_frame s tn v z
Proof
  rw[selected_registration_frame_def]
QED

Theorem selected_registration_head[local]:
  selected_slot_accepts ce env ce.ce_struct_fields ty (EL i tvs) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty (EL i tvs) /\
  (?loc. FLOOKUP ce.ce_vars (EL i names) = SOME loc /\
    var_location_memory_size loc = SOME (type_memory_size (EL i tvs))) /\
  type_memory_size (EL i tvs) < dimword (:256) /\
  ALL_DISTINCT names /\ i < LENGTH names /\
  compile_register_positional_args ce [build_positional_arg ce (EL i names,ty)]
    (4+ofs) st = (ce1,st1) /\
  cd = s.vs_call_ctx.cc_calldata /\ 4+ofs < dimword (:256) /\
  calldata_decode_args cd (EL i tvs::more) ofs = SOME (EL i vals::xs) /\
  selected_registration_owners fn names tvs vals i ce st s G tn /\
  selected_registration_resources ctx fn site lo st s /\
  fn_has_code st st1 fn /\ fn_inst_ids_distinct fn /\
  (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  st1.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  unit_alloca_budget ctx < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
  ?t H u.
    selected_registration_owners fn names tvs vals (SUC i) ce1 st1 t H u /\
    selected_registration_resources ctx fn site lo st1 t /\
    fresh_vars_wrt limit t /\ selected_registration_frame s tn t u /\
    calldata_decode_args cd more (ofs + tv_abi_size (EL i tvs)) = SOME xs /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,H,u)
Proof
  strip_tac >>
  qabbrev_tac `tv = EL i tvs` >>
  qabbrev_tac `dyn = tv_abi_dynamic tv` >>
  qabbrev_tac `delta = w2n (cd_word cd (4+ofs))` >>
  qabbrev_tac `srcpos = if dyn then (4+delta) MOD dimword (:256) else 4+ofs` >>
  `dyn = tv_abi_dynamic tv /\ delta = w2n (cd_word cd (4+ofs)) /\
   srcpos = (if dyn then (4+delta) MOD dimword (:256) else 4+ofs)` by
    metis_tac[markerTheory.Abbrev_def] >>
  drule_all selected_slot_source_input >> strip_tac >>
  `is_abi_dynamic ce.ce_struct_fields ty = dyn` by metis_tac[calldata_coherent_dynamic] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv` by
    metis_tac[calldata_coherent_embedded_size] >>
  `is_word_type ty ==> ~dyn /\ ?clamp.
      type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp` by
    (strip_tac >> conj_tac
     >- (qpat_assum `is_abi_dynamic _ _ <=> dyn`
           (once_rewrite_tac o single o GSYM) >>
         irule ctor_word_type_static >> first_assum ACCEPT_TAC) >>
     irule word_type_decoder_primitive >> first_assum ACCEPT_TAC) >>
  `delta = w2n (cd_word s.vs_call_ctx.cc_calldata (4+ofs))` by metis_tac[] >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _`
    (mp_tac o BETA_RULE o REWRITE_RULE [build_positional_arg_def, LET_THM]) >>
  qpat_assum `is_abi_dynamic _ _ <=> dyn` (once_rewrite_tac o single) >>
  qpat_assum `abi_embedded_static_size _ _ = _` (once_rewrite_tac o single) >>
  strip_tac >>
  qpat_x_assum `selected_registration_resources _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [selected_registration_resources_def]) >>
  `!bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  qpat_x_assum `selected_slot_accepts _ _ _ _ _`
    (drule o REWRITE_RULE [selected_slot_accepts_def]) >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `cd_decode _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_decode_load _ _ _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `_ <= limit.cs_next_var`)) >>
  disch_then (qspecl_then [`PG`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))) >>
  strip_tac >>
  qexistsl [`t`,`H`,`u`] >> simp[selected_registration_resources_def,
    selected_registration_frame_def] >>
  conj_tac
  >- (qpat_x_assum `selected_registration_owners _ _ _ _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[selected_registration_owners_def] >> strip_tac >>
      gen_tac >> strip_tac >>
      irule (BETA_RULE (Q.INST
        [`R` |-> `\aid q n. MEM (mk_inst aid ALLOCA [Lit (n2w n)] [q]) (fn_insts fn)`]
        registration_owned_prefix_invariant_update)) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G`,`ce`,`i`,`p`,`q`,`s`,`st`,`tn`] >>
      qpat_assum `Abbrev (tv = _)`
        (fn th => pure_once_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))
  >- (qpat_assum `(!inst w b k. _ ==> _) ==> !inst w b k. _ ==> _` mp_tac >>
      impl_tac >- first_assum ACCEPT_TAC >> simp[]) >>
  decide_tac
QED
