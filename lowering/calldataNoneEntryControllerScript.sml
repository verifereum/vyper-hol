(* The entry controller needs only the installed local decoder alternative. *)
Theory calldataNoneEntryController
Ancestors
  allocaFrontierRoom
  calldataNoneEntryAssembly calldataNoneSelectedPrefix calldataNoneRegisterInit
  calldataNoneRegisterFold calldataNoneRegisterOne venomInstIdsProps
  defaultConcreteRegistrationDefs ctorDeployMemoryFrontier allocaFrontierBound
  vyperLoweringCorrect vyperCalldata e2eDefs compileVyper fragExec
  fragGasOriginPtr fragGasPathMem fragGasPathPtr ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words list arithmetic

Theorem none_entry_reject_from_decoder:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    (!fn site ce ty tv last.
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
      abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
      fn_inst_ids_distinct fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
      unit_alloca_budget unit.cu_context < dimword (:256) /\
      ~ctx_has_dalloca unit.cu_context ==>
      !first t src q p d oid H u.
        compile_abi_decode_to_buf (Var q) src CALLDATALOAD (Lit 0w) (Lit 0w)
          (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
        fn_has_code first last fn /\ eval_operand src t = SOME p /\
        eval_operand (Var q) t = SOME (n2w d) /\
        abi_decoder_operand_live first.cs_next_var src /\
        abi_decoder_operand_live first.cs_next_var (Var q) /\
        alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
        (!id. first.cs_next_id <= id ==> FLOOKUP t.vs_allocas id = NONE) /\
        FLOOKUP t.vs_allocas oid = SOME (d,type_memory_size tv) /\
        oid < first.cs_next_id /\ d+type_memory_size tv < dimword (:256) /\
        ptr_covers H u q t (type_memory_size tv) /\
        op_taint u src = {} /\ op_prov H src = NONE /\
        fresh_vars_wrt last t /\ ~t.vs_halted /\
        t.vs_current_bb = first.cs_current_bb /\
        t.vs_inst_idx = LENGTH first.cs_current_insts ==>
          (?z K w. z.vs_returndata = [] /\
            !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
              (t,H,u) [] (Abort Revert_abort z,K,w)) \/
          (?v K w. IS_SOME (cd_decode F t.vs_call_ctx.cc_calldata tv (w2n p)) /\
            v.vs_call_ctx = t.vs_call_ctx /\ alloca_inv v /\
            alloca_frontier_inv unit.cu_context fn site v /\
            (!id. last.cs_next_id <= id ==>
              FLOOKUP v.vs_allocas id = FLOOKUP t.vs_allocas id) /\
            fresh_vars_wrt last v /\ ~v.vs_halted /\
            v.vs_current_bb = last.cs_current_bb /\
            v.vs_inst_idx = LENGTH last.cs_current_insts /\
            !D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
              (t,H,u) [] (OK v,K,w)))
    ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!fn site ce ty tv last. _` (mk_asm "decoder") >>
  drule lower_vyper_runtime_unit_context_entry >>
  disch_then (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (qx_choose_then `func` ASSUME_TAC))) >>
  drule none_entry_reject_from_selected >>
  disch_then (drule_at (Pat `source_typing_ok _ _ _`)) >>
  disch_then (drule_at (Pat `venomInst$lookup_function _ _ = _`)) >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >> drule_all none_selected_check_prefix >>
      disch_then (qx_choosel_then
        [`mut`,`nr`,`rr`,`args`,`ret`,`fbody`,`tvs`,`ce`,`pos`,`mincd`,`pay`,
         `key`,`ut`,`iv`,`rt`,`opened`,`checked`,`ce'`,`last`,`fn`,`p`,`G`,`tn`]
        strip_assume_tac) >>
      `fn = func` by fs[] >> qpat_x_assum `fn = func` SUBST_ALL_TAC >>
      qexistsl [`tvs`,`mincd`,`pay`,`opened`,`checked`,`p`,`G`,`tn`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[] >> suspend "registration")
  >> disch_then (CONJUNCTS_THEN2 ASSUME_TAC
      (qx_choosel_then [`s`,`G'`,`tn'`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`func`,`s`,`G'`,`tn'`] >> simp[]
QED

Resume none_entry_reject_from_decoder[registration]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `site = ARB:instruction` >>
  drule_all none_selected_registration_inputs >>
  disch_then (qspec_then `site` (map_every assume_tac o CONJUNCTS)) >>
  drule fn_inst_ids_distinct_all_distinct >> strip_tac >>
  qabbrev_tac `R = \a v (K:(string,num # num) fmap) (w:taint).
    alloca_inv v /\ alloca_frontier_inv unit.cu_context func site v /\
    (!id e. FLOOKUP v.vs_allocas id = SOME e ==> id < a.cs_next_id) /\
    fresh_vars_wrt a v /\ ~v.vs_halted /\ v.vs_current_bb = a.cs_current_bb /\
    v.vs_inst_idx = LENGTH a.cs_current_insts` >>
  `unit_alloca_budget unit.cu_context < dimword (:256) /\ R checked t H u` by
    fs[Abbr `R`, default_registration_resources_def,
       alloca_frontier_inv_from_def, alloca_frontier_inv_def] >>
  mp_tac (Q.INST [`ctx` |-> `unit.cu_context`, `fn` |-> `func`,
                  `env` |-> `type_env tops`, `cd` |-> `vs.vs_call_ctx.cc_calldata`,
                  `R` |-> `R`] none_registration_suffix_reject) >>
  impl_tac >- suspend "singleton" >>
  disch_then (drule_at (Pat `R _ _ _ _`)) >>
  disch_then (drule_at (Pat `calldata_decode_args _ _ _ = NONE`)) >>
  disch_then (drule_at (Pat `compile_register_positional_args _ _ _ _ = _`) o
    REWRITE_RULE [ADD_CLAUSES]) >> simp[]
QED

Resume none_entry_reject_from_decoder[singleton]:
  ntac 8 gen_tac >>
  map_every qx_gen_tac [`s0`,`G0`,`tn0`] >>
  qunabbrev_tac `R` >> BETA_TAC >> strip_tac >>
  rename1 `compile_register_positional_args c [build_positional_arg c (n,ty)]
    _ st = (c1,st1)` >>
  asm "decoder" (qspecl_then [`func`,`site`,`c`,`ty`,`tv`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all none_registration_singleton_paths >>
  disch_then (qspecl_then [`tn0`,`G0`] (fn th =>
    simp[NoAsms, GSYM CONJ_ASSOC, th]))
QED

Finalise none_entry_reject_from_decoder
