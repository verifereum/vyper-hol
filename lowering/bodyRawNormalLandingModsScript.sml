(* The reached CALL-family edge, before transport of the linked frame. *)
Theory bodyRawNormalLandingMods
Ancestors
  exprSimRawCall bodyFullRawCallCallOrigin bodyFullRawCallCallStorage
  exprLoweringProps allocaHistory decoderGhostFramePtr
  emitHelperProps loweringStateRelDefs words finite_map pred_set
  venomInst venomState exprSafeOperand venomExecSemantics ptrDiscipline bodyPtrDefs
  fragExec list arithmetic lowerDloadOracleCallAssembly
Libs stepInstBaseLib

Theorem raw_call_normal_landing_mods:
  emit_op (case call_ty of RegularCall => CALL | StaticCall => STATICCALL
                         | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)]) s7 = (ok,sc) /\
  inst = mk_inst s7.cs_next_id
    (case call_ty of RegularCall => CALL | StaticCall => STATICCALL
                   | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)])
    [STRING #"%" (toString s7.cs_next_var)] /\
  emitted_insts s7 sc = [inst] /\
  lookup_block t7.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t7.vs_inst_idx = SOME inst /\
  sc.cs_current_bb = t7.vs_current_bb /\
  LENGTH sc.cs_current_insts = SUC t7.vs_inst_idx /\
  ~t7.vs_halted /\ alloca_history func t7 /\
  stmt_state_rel H ctx func cenv cx esK t7 /\ local_ptrs_reserved cenv s7 /\
  eval_operand gas_op t7 = SOME gas /\ eval_operand to_op t7 = SOME aw /\
  eval_operand dp t7 = SOME ao /\ eval_operand dl t7 = SOME az /\
  eval_operand op t7 = SOME rw /\ eval_operand val_op t7 = SOME val_word /\
  w2w aw = target /\ ro = w2n rw /\ cap < dimword (:256) /\
  w2n (if call_ty = RegularCall then val_word else 0w) =
    (case value_opt of NONE => 0 | SOME n => n) /\
  (call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
    gas_cap target (read_memory (w2n ao) (w2n az) t7) value_opt esK =
    (INL (rq,outcome),es1) /\
  es2 = SND (adopt_call_outcome rq outcome es1) /\
  (!name b sz. local_region cenv esK.scopes t7 name b sz ==>
     regions_disjoint ro cap b sz) /\
  (cenv.ce_is_ctor ==> ?tops. ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
     ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) ro cap) /\
  source_memory_write_ranges inst t7 = [(ro,cap)] /\
  mem_safe_step 0 ctx inst t7 /\ allocas_from lo t7 /\ stor_taint_ok_at D tn7 t7 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t7) /\
  EVERY (\p. op_taint tn7 p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn7.t_mem) /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (w2n az)) /\
  (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap) ==>
  ?u. run_inst_seq (emitted_insts s7 sc) t7 = OK u /\ step_inst_base inst t7 = OK u /\
      let q = u with vs_inst_idx := LENGTH sc.cs_current_insts in
      let Gq = step_prov PG G7 inst u in
      let tnq = step_taint inst t7 u tn7 in
        gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t7,G7,tn7) [] (OK q,Gq,tnq) /\
        stmt_state_rel H ctx func cenv cx es2 q /\
        ~q.vs_halted /\ q.vs_current_bb = sc.cs_current_bb /\
        q.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func q /\
        q.vs_returndata = outcome.co_returnData /\
        q.vs_memory = (write_memory_with_expansion ro (TAKE cap outcome.co_returnData) t7).vs_memory /\
        q.vs_allocas = t7.vs_allocas /\ q.vs_alloca_next = t7.vs_alloca_next /\
        q.vs_fmp = t7.vs_fmp /\ q.vs_initial_fmp = t7.vs_initial_fmp /\
        q.vs_immutables = t7.vs_immutables /\ q.vs_data_section = t7.vs_data_section /\
        (!p. safe_operand s7 p ==> eval_operand p q = eval_operand p t7) /\
        eval_operand ok q = SOME (bool_to_word outcome.co_success) /\
        op_taint tnq ok = {} /\ op_prov Gq ok = NONE /\
        tnq.t_mem = tn7.t_mem DIFF {j | ro <= j /\ j < ro + LENGTH (TAKE cap outcome.co_returnData)} /\
        stor_taint_ok_at D tnq q /\
        (!x. ~MEM x inst.inst_outputs ==>
             FLOOKUP Gq x = FLOOKUP G7 x /\ op_taint tnq (Var x) = op_taint tn7 (Var x) /\
             lookup_var x q = lookup_var x t7)
Proof
  strip_tac >>
  `w2n (n2w cap : bytes32) = cap` by simp[w2n_n2w] >>
  `!name b sz. local_region cenv esK.scopes t7 name b sz ==>
     b + sz <= w2n rw \/ w2n rw + cap <= b` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  `cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     off + type_memory_size tv <= w2n rw \/ w2n rw + cap <= off` by
    (rpt strip_tac >>
     qpat_assum `cenv.ce_is_ctor ==> ?tops. _` (drule_then strip_assume_tac) >>
     qpat_assum `cenv.ce_is_ctor ==> !src tops name tv v off. _`
       (drule_then (drule_all_then mp_tac)) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  qpat_x_assum `inst = _` (mk_asm "encoded_call") >>
  qpat_x_assum `w2w aw = target` (SUBST_ALL_TAC o SYM) >>
  drule raw_call_kind_oracle_emit_run_aged >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand gas_op t7 = _`)) >>
  disch_then (drule_at (Pat `eval_operand val_op t7 = _`)) >>
  disch_then (qspecl_then [`gas`,`aw`] mp_tac) >>
  simp[] >>
  (impl_tac >-
    (qpat_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     qpat_assum `cenv.ce_is_ctor ==> !name tv v off. FLOOKUP _ (_,_) = _ /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >>
     ntac 2 disch_tac >> conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [inst] t7 = OK u` >>
  `step_inst_base inst t7 = OK u` by
    (qpat_x_assum `run_inst_seq [inst] t7 = _` mp_tac >>
     pure_rewrite_tac[run_inst_seq_def] >> Cases_on `step_inst_base inst t7` >> simp[]) >>
  asm_x "encoded_call" assume_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  suspend "endpoint"
QED

Resume raw_call_normal_landing_mods[endpoint]:
  `u.vs_allocas = t7.vs_allocas /\ u.vs_alloca_next = t7.vs_alloca_next /\
   u.vs_fmp = t7.vs_fmp /\ u.vs_initial_fmp = t7.vs_initial_fmp /\
   u.vs_immutables = t7.vs_immutables /\ u.vs_data_section = t7.vs_data_section /\
   ~u.vs_halted /\ u.vs_current_bb = t7.vs_current_bb /\ t.vs_vars = t7.vs_vars` by
    (simp[Abbr `u`,update_var_def] >>
     qpat_assum `t = _ with <|vs_memory := _; vs_transient := _; vs_returndata := _;
       vs_accounts := _; vs_logs := _; vs_outcomes := _; vs_requests := _;
       vs_pending_deletions := _|>` (fn th => pure_once_rewrite_tac[th]) >> simp[]) >>
  `inst.inst_outputs = [STRING #"%" (toString s7.cs_next_var)]` by simp[mk_inst_def] >>
  `inst.inst_opcode <> ALLOCA` by (Cases_on `call_ty` >> simp[mk_inst_def]) >>
  `!x. ~MEM x inst.inst_outputs ==> lookup_var x u = lookup_var x t7` by
    (gen_tac >> simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> simp[]) >>
  `!p. safe_operand s7 p ==> eval_operand p u = eval_operand p t7` by
    (Cases >> simp[safe_operand_def, eval_operand_def] >> rpt strip_tac >>
     first_x_assum irule >> fs[not_fresh_at_def]) >>
  `alloca_history func (u with vs_inst_idx := SUC t7.vs_inst_idx)` by
    (irule alloca_history_frame >> qexists `t7 with vs_inst_idx := SUC t7.vs_inst_idx` >>
     simp[] >> irule history_nonalloca_advance >> metis_tac[]) >>
  `u.vs_returndata = outcome.co_returnData /\
   u.vs_memory = (write_memory_with_expansion (w2n rw) (TAKE cap outcome.co_returnData) t7).vs_memory` by
    simp[Abbr `u`,update_var_def] >>
  qpat_x_assum `inst = _` (mk_asm "encoded_call") >>
  qexists `u` >>
  simp[stmt_state_rel_inst_idx] >>
  rpt conj_tac
  >- suspend "origin"
  >- suspend "out_taint"
  >- suspend "out_prov"
  >- suspend "mem_taint"
  >- suspend "storage_taint"
  >> suspend "other_output"
QED

Resume raw_call_normal_landing_mods[origin]:
  asm_x "encoded_call" assume_tac >>
  Cases_on `call_ty`
  >- (irule raw_call_step_mem_safe_origin_full >> simp[eval_operand_def, w2n_n2w])
  >- (irule raw_delegate_call_step_mem_safe_origin_full >> simp[eval_operand_def, w2n_n2w])
  >> irule raw_call_step_mem_safe_origin_full >> simp[eval_operand_def, w2n_n2w]
QED

Resume raw_call_normal_landing_mods[out_taint]:
  asm "encoded_call" (fn th => rewrite_tac[th]) >>
  Cases_on `call_ty` >>
  simp[step_taint_def, op_taint_def, set_var_taint_def,
       out_taint_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Resume raw_call_normal_landing_mods[out_prov]:
  irule step_prov_out_none >>
  asm "encoded_call" (fn th => rewrite_tac[th]) >>
  Cases_on `call_ty` >> simp[out_prov_def, mk_inst_def]
QED

Resume raw_call_normal_landing_mods[mem_taint]:
  `source_memory_write_ranges inst t7 = [(w2n rw,w2n (n2w cap : bytes32))]` by simp[] >>
  `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/ inst.inst_opcode = DELEGATECALL` by
    (asm_x "encoded_call" assume_tac >> Cases_on `call_ty` >> simp[mk_inst_def]) >>
  `3 < LENGTH inst.inst_operands` by
    (asm_x "encoded_call" assume_tac >> Cases_on `call_ty` >> simp[mk_inst_def]) >>
  dxrule_at (Pat `source_memory_write_ranges _ _ = _`) ld_oracle_call_taint >>
  disch_then (drule_at (Pat `_.vs_allocas = _`)) >>
  simp[] >> disch_then (qspec_then `tn7` (fn th => simp[th])) >>
  `!b n. {j+b | j < n} = {j | b <= j /\ j < n+b}` by
    (rpt gen_tac >> simp[EXTENSION] >> gen_tac >> eq_tac
     >- (strip_tac >> gvs[] >> decide_tac)
     >> disch_then strip_assume_tac >> qexists `x - b` >> decide_tac) >>
  simp[]
QED

Resume raw_call_normal_landing_mods[storage_taint]:
  `stor_taint_ok_at D (step_taint inst t7 u tn7) (u with vs_inst_idx := SUC t7.vs_inst_idx) <=>
   stor_taint_ok_at D (step_taint inst t7 u tn7) u` by simp[stor_taint_ok_at_def] >>
  asm_rewrite_tac[] >>
  asm_x "encoded_call" assume_tac >> Cases_on `call_ty`
  >- (`inst.inst_opcode = CALL` by simp[mk_inst_def] >>
      `exec_ext_call inst t7 gas aw val_word ao az rw (n2w cap : bytes32)
         t7.vs_call_ctx.cc_static = OK u` by
        (qpat_x_assum `step_inst_base inst t7 = _` mp_tac >>
         drule (stepInstBaseLib.opcode_clause ``CALL``) >>
         disch_then (fn th => pure_once_rewrite_tac[th]) >>
         `inst.inst_operands = [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]` by
           simp[mk_inst_def] >>
         qpat_assum `inst.inst_operands = _`
           (fn th => simp_tac bool_ss [th,list_case_def]) >>
         asm_simp_tac bool_ss [optionTheory.option_case_def,
                               pairTheory.pair_case_thm, eval_operand_lit] >>
         IF_CASES_TAC >> simp[]) >>
      drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`) raw_call_exec_stor_taint_at >> simp[])
  >- (`inst.inst_opcode = DELEGATECALL` by simp[mk_inst_def] >>
      `exec_delegatecall inst t7 gas aw ao az rw (n2w cap : bytes32) = OK u` by
        (qpat_x_assum `step_inst_base inst t7 = _` mp_tac >>
         drule (stepInstBaseLib.opcode_clause ``DELEGATECALL``) >>
         disch_then (fn th => pure_once_rewrite_tac[th]) >>
         `inst.inst_operands = [gas_op;to_op;dp;dl;op;Lit (n2w cap)]` by
           simp[mk_inst_def] >>
         qpat_assum `inst.inst_operands = _`
           (fn th => simp_tac bool_ss [th,list_case_def]) >>
         asm_simp_tac bool_ss [optionTheory.option_case_def,
                               pairTheory.pair_case_thm, eval_operand_lit]) >>
      drule_at (Pat `exec_delegatecall _ _ _ _ _ _ _ _ = _`) raw_delegate_call_exec_stor_taint_at >> simp[])
  >> `inst.inst_opcode = STATICCALL` by simp[mk_inst_def] >>
  `exec_ext_call inst t7 gas aw (0w:bytes32) ao az rw (n2w cap : bytes32) T = OK u` by
    (qpat_x_assum `step_inst_base inst t7 = _` mp_tac >>
     drule (stepInstBaseLib.opcode_clause ``STATICCALL``) >>
     disch_then (fn th => pure_once_rewrite_tac[th]) >>
     `inst.inst_operands = [gas_op;to_op;dp;dl;op;Lit (n2w cap)]` by
       simp[mk_inst_def] >>
     qpat_assum `inst.inst_operands = _`
       (fn th => simp_tac bool_ss [th,list_case_def]) >>
     asm_simp_tac bool_ss [optionTheory.option_case_def,
                           pairTheory.pair_case_thm, eval_operand_lit]) >>
  drule_at (Pat `exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`) raw_call_exec_stor_taint_at >> simp[]
QED

Resume raw_call_normal_landing_mods[other_output]:
  rpt strip_tac
  >- (irule step_prov_other_output >> simp[])
  >- (irule step_taint_other_output >> simp[])
  >> first_x_assum (qspec_then `x` mp_tac) >> simp[lookup_var_def]
QED

Finalise raw_call_normal_landing_mods
