Theory gasFocusFmpCutPureEffect
Ancestors
  fmpStageRel o1LowerDloadShared venomExecSemantics venomState venomInst
  vfmState finite_map list ptrDiscipline pred_set arithmetic words
  fmpStagePointRanges o1LowerDloadRelocationKernel o1LowerDloadAddressArithmetic
  frameRelocationGuardedValues o1LowerDloadJointRead0
  ptrStaticDiscipline pointerConfinedDefs memLocDefs o1PassContract venomWf
  deadStoreElimPureSteps deadStoreElimFrameReadSteps

val reads = ``[CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
  COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
  CALLDATASIZE; CODESIZE; RETURNDATASIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
  BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD]``;

Theorem cut_context_read[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^reads /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x) /\
  step_inst_base inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out x t)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
   s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
   s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section` by
    gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `!a. (lookup_account a s.vs_accounts).balance =
          (lookup_account a t.vs_accounts).balance /\
        (lookup_account a s.vs_accounts).nonce =
          (lookup_account a t.vs_accounts).nonce /\
        (lookup_account a s.vs_accounts).code =
          (lookup_account a t.vs_accounts).code` by
    (fs[fmp_stage_rel_def] >> drule ld_shared_accounts_fields >>
     simp[lookup_account_def] >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a` mp_tac) >>
     simp[account_state_component_equality]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  fs[MEM] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_read0_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM, account_empty_def] >> metis_tac[]
QED

val clean_scalars = ``[Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
  SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]``;
val dedicated = ``[ADD; SUB; MUL; EQ; LT; GT; SHL; SHR; SAR; PARAM; ASSIGN]``;
val idle = ``[NOP; ASSERT; ASSERT_UNREACHABLE]``;
val pure_ops = ``^reads ++ ^clean_scalars ++ ^dedicated ++ ^idle``;

(* An update to the variable map is the only state effect of an OK pure
   instruction. In the ghost state, only the variable taint is updated. *)
Theorem cut_pure_taint[local]:
  MEM inst.inst_opcode ^pure_ops /\ s1 = (s with vs_vars := s1.vs_vars) ==>
  step_taint inst s s1 tn =
    tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  qpat_x_assum `s1 = (s with vs_vars := s1.vs_vars)` (once_rewrite_tac o single) >>
  `source_memory_write_ranges inst s = [] /\
   inst.inst_opcode <> MSTORE /\ inst.inst_opcode <> ISTORE /\
   inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> SSTORE /\
   inst.inst_opcode <> TSTORE /\ inst.inst_opcode <> CALL /\
   inst.inst_opcode <> STATICCALL /\ inst.inst_opcode <> DELEGATECALL` by
    gvs[MEM, codegenRelTheory.source_memory_write_ranges_def] >>
  `written_taint tn inst s = {}` by
    (simp[written_taint_def] >> rpt (CASE_TAC >> simp[])) >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, range_bytes_def, store_taint_def, adopt_reset_def,
       imm_taint_def, taint_component_equality, FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem cut_param_step[local]:
  fmp_params_rel sm PG s t /\ inst.inst_opcode = PARAM /\
  step_inst_base inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out y t) /\
    fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s) x y
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[fmp_params_rel_def] >>
  `w2n idx < LENGTH t.vs_params` by decide_tac >>
  simp[out_prov_def, out_taint_def, eval_operand_def] >> metis_tac[]
QED

Theorem cut_assign_step[local]:
  inst.inst_opcode = ASSIGN /\
  (!op x out. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
     eval_operand op s = SOME x ==>
     ?y. eval_operand op t = SOME y /\
       (~retpc_var fn out ==> fmp_value_rel sm (op_prov G op) (op_taint tn op) x y)) /\
  step_inst_base inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out y t) /\
    (~retpc_var fn out ==> fmp_value_rel sm
      (out_prov PG G inst s1) (out_taint tn inst s) x y)
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl [`v`,`y`] >>
  simp[out_prov_def, first_prov_def, out_taint_def] >>
  Cases_on `op_prov G op1` >> gvs[]
QED

Theorem cut_idle_step[local]:
  MEM inst.inst_opcode ^idle /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x) /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  ?r'. step_inst_base inst t = r' /\
    ((r = OK s /\ r' = OK t) \/ (?ab s1 t1. r = Abort ab s1 /\ r' = Abort ab t1))
Proof
  strip_tac >> fs[MEM] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
  strip_tac >> gvs[passSimulationDefsTheory.terminates_def, MEM] >>
  metis_tac[]
QED

val cut_data = ``
  (!v. ~MEM v inst.inst_outputs ==>
       FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
       FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
     ?y. FLOOKUP t1.vs_vars v = SOME y /\
         (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
           (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1``;

Theorem cut_pure_data[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^pure_ops /\
  ((inst.inst_outputs = [] /\ s1 = s /\ t1 = t) \/
   (?out x y. inst.inst_outputs = [out] /\
       s1 = update_var out x s /\ t1 = update_var out y t /\
       (~retpc_var fn out ==> fmp_value_rel sm (out_prov PG G inst s1)
         (out_taint tn inst s) x y))) ==>
  ^cut_data
Proof
  strip_tac >>
  `step_taint inst s s1 tn = tn with t_var :=
     set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)` by
    (irule cut_pure_taint >> gvs[update_var_def]) >>
  fs[fmp_stage_rel_def] >>
  gvs[update_var_def, ld_shared_agree_def, FLOOKUP_UPDATE, step_prov_def,
      set_var_taint_def, op_taint_def] >>
  Cases_on `out_prov PG G inst (s with vs_vars := s.vs_vars |+ (out,x))` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem cut_clean_step[local]:
  MEM inst.inst_opcode ^clean_scalars /\
  (!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x) /\
  step_inst_base inst s = OK s1 ==>
  ?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out x t)
Proof
  strip_tac >> fs[MEM] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >> gvs[MEM] >> metis_tac[]
QED

Theorem cut_clean_output[local]:
  MEM inst.inst_opcode (^reads ++ ^clean_scalars ++ [EQ;LT;GT]) ==>
  fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s) x x
Proof
  strip_tac >> fs[MEM] >>
  simp[out_prov_def, fmp_value_rel_def,
       o1LowerDloadRelocationKernelTheory.ld_value_agree_def, word_agree_except_def]
QED

val affine = ``[ADD;SUB]``;
val comparisons = ``[EQ;LT;GT]``;
val shifts = ``[SHL;SHR;SAR]``;
val binops = ``^affine ++ ^comparisons ++ ^shifts ++ [MUL]``;
val bin_eval = ``case inst.inst_opcode of
      ADD => word_add | SUB => word_sub | MUL => word_mul
    | EQ => (\x y. bool_to_word (x = y))
    | LT => (\x y. bool_to_word (w2n x < w2n y))
    | GT => (\x y. bool_to_word (w2n y < w2n x))
    | SHL => (\n w. word_lsl w (w2n n))
    | SHR => (\n w. word_lsr w (w2n n))
    | SAR => (\n w. word_asr w (w2n n))
    | _ => word_add``;

Theorem cut_bin_eval[local]:
  MEM inst.inst_opcode ^binops ==>
  step_inst_base inst s = exec_pure2 (^bin_eval) inst s
Proof
  simp[MEM] >> strip_tac >> simp[step_inst_base_opcode_eqs, GREATER_DEF]
QED

Theorem cut_affine_value[local]:
  MEM inst.inst_opcode ^affine /\ inst.inst_operands = [p;q] /\
  fmp_value_rel sm (op_prov G p) {} x x' /\
  fmp_value_rel sm (op_prov G q) {} y y' /\
  (op_prov G p = NONE \/ op_prov G q = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov G q = NONE) ==>
  fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s)
    ((^bin_eval) x y) ((^bin_eval) x' y')
Proof
  strip_tac >>
  `out_taint tn inst s = {}` by gvs[MEM, ld_out_taint_default] >>
  Cases_on `op_prov G p` >> Cases_on `op_prov G q` >>
  gvs[MEM, out_prov_def, first_prov_def] >>
  imp_res_tac fmp_mem_value_clean >> gvs[] >>
  gvs[fmp_value_rel_def, ld_value_agree_pointer, ld_value_agree_scalar,
      word_agree_except_def] >>
  qexistsl [`b`,`c`,`z`] >> simp[] >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem cut_cmp_site[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  0 < z /\ b <= w2n x /\ w2n x <= b+z /\ b <= w2n y /\ w2n y <= b+z /\
  fmp_value_rel sm (SOME (b,z)) {} x x' /\
  fmp_value_rel sm (SOME (b,z)) {} y y' ==>
  (w2n x < w2n y <=> w2n x' < w2n y') /\
  (w2n y < w2n x <=> w2n y' < w2n x') /\ (x = y <=> x' = y')
Proof
  strip_tac >> `z <> 0` by decide_tac >>
  gvs[fmp_value_rel_def, ld_value_agree_pointer] >>
  drule_all fmp_mem_sites_bounds >> strip_tac >> gvs[] >>
  `w2n (x + n2w c - n2w b) = c + (w2n x-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >> qexists `z` >> simp[]) >>
  `w2n (y + n2w c - n2w b) = c + (w2n y-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >> qexists `z` >> simp[]) >>
  pure_once_rewrite_tac[GSYM w2n_11] >>
  gvs[] >> decide_tac
QED

Theorem cut_shift_value[local]:
  MEM inst.inst_opcode ^shifts /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ op_taint tn p = {} /\
  fmp_value_rel sm NONE {} x x' /\
  fmp_value_rel sm NONE (op_taint tn q) y y' ==>
  fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s)
    ((^bin_eval) x y) ((^bin_eval) x' y')
Proof
  strip_tac >> imp_res_tac fmp_mem_value_clean >> gvs[MEM] >>
  gvs[out_prov_def, out_taint_def, fmp_value_rel_def, ld_value_agree_scalar] >>
  metis_tac[word_agree_except_shl, word_agree_except_shr, word_agree_except_sar]
QED

Theorem cut_mul_value[local]:
  inst.inst_opcode = MUL /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ eval_operand q s = SOME y /\
  taint_ok fn tn inst s /\
  fmp_value_rel sm NONE (op_taint tn p) x x' /\
  fmp_value_rel sm NONE (op_taint tn q) y y' ==>
  fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s) (x*y) (x'*y')
Proof
  strip_tac >>
  `!a b. (p = a /\ q = b \/ q = a /\ p = b) /\ op_taint tn a <> {} ==>
      op_taint tn b = {} /\ (eval_operand b s = SOME 0w \/ eval_operand b s = SOME 1w)` by
    (fs[taint_ok_def] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!op. MEM op inst.inst_operands /\ _ ==> _` (qspec_then `a` mp_tac) >>
     gvs[MEM] >>
     disch_then (qx_choose_then `sel` strip_assume_tac) >> gvs[]) >>
  gvs[out_prov_def, out_taint_def, fmp_value_rel_def, ld_value_agree_scalar] >>
  irule word_agree_except_selector_mul >> simp[] >> conj_tac
  >- (qpat_x_assum `!a b. _` (qspecl_then [`p`,`q`] mp_tac) >> simp[] >> metis_tac[])
  >> qpat_x_assum `!a b. _` (qspecl_then [`q`,`p`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem cut_affine_prov[local]:
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM inst.inst_opcode ^affine /\
  inst.inst_operands = [p;q] ==>
  (op_prov G p = NONE \/ op_prov G q = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov G q = NONE)
Proof
  strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (fs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `affine_pointer_ops fn (ptr_roots P fn)` by gvs[fn_static_ptr_ok_def] >>
  qpat_x_assum `affine_pointer_ops _ _`
    (mp_tac o SRULE [affine_pointer_ops_def, LET_THM]) >>
  disch_then (qspecl_then [`bb`,`inst`,`p`,`q`] mp_tac) >>
  fs[MEM] >> strip_tac >>
  Cases_on `p` >> Cases_on `q` >>
  gvs[op_prov_def, fn_pv_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem cut_cmp_vars[local]:
  FDOM G SUBSET pv /\ ptr_use_static_ok P pv inst /\
  MEM inst.inst_opcode ^comparisons /\ inst.inst_operands = [p;q] /\
  (op_prov G p <> NONE \/ op_prov G q <> NONE) ==>
  ?u w. p = Var u /\ q = Var w /\ (u IN FDOM G \/ w IN FDOM G)
Proof
  strip_tac >> Cases_on `p` >> Cases_on `q` >>
  gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def,
      mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def, MEM] >>
  metis_tac[]
QED

Theorem cut_cmp_value[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FDOM G SUBSET pv /\ ptr_use_static_ok P pv inst /\ access_ok lo G fn inst s /\
  MEM inst.inst_opcode ^comparisons /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ eval_operand q s = SOME y /\
  fmp_value_rel sm (op_prov G p) {} x x' /\
  fmp_value_rel sm (op_prov G q) {} y y' ==>
  (^bin_eval) x y = (^bin_eval) x' y'
Proof
  strip_tac >>
  Cases_on `op_prov G p = NONE /\ op_prov G q = NONE`
  >- (fs[] >> imp_res_tac fmp_mem_value_clean >> gvs[]) >>
  `?u w. p = Var u /\ q = Var w /\ (u IN FDOM G \/ w IN FDOM G)` by
    metis_tac[cut_cmp_vars] >>
  gvs[] >>
  `?b z. FLOOKUP G u = SOME (b,z) /\ FLOOKUP G w = SOME (b,z) /\
     0 < z /\ b <= w2n x /\ w2n x <= b+z /\ b <= w2n y /\ w2n y <= b+z` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, MEM] >> metis_tac[]) >>
  fs[op_prov_def] >>
  `(w2n x < w2n y <=> w2n x' < w2n y') /\
   (w2n y < w2n x <=> w2n y' < w2n x') /\ (x = y <=> x' = y')` by
    (irule cut_cmp_site >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[MEM] >> simp[] >> metis_tac[]
QED

val clean_in = ``^reads ++ ^clean_scalars ++ ^idle``;
val scalar_in = ``^clean_in ++ ^shifts ++ [MUL]``;

Theorem cut_scalar_prov[local]:
  MEM inst.inst_opcode ^scalar_in /\ ptr_use_static_ok P pv inst /\
  FDOM G SUBSET pv /\ MEM op inst.inst_operands ==> op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >>> NTH_GOAL (simp[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def, mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def, MEM]) 1 >>
  gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_static_ok_def,
      mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def, MEM] >>
  metis_tac[]
QED

Theorem cut_plain_taint[local]:
  MEM inst.inst_opcode (^clean_in ++ ^affine ++ ^comparisons) /\
  taint_ok fn tn inst s /\ MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> fs[taint_ok_def] >>
  qpat_x_assum `!op. MEM op inst.inst_operands /\ _ ==> _` (qspec_then `op` mp_tac) >>
  gvs[MEM]
QED

Theorem cut_shift_amount[local]:
  MEM inst.inst_opcode ^shifts /\ inst.inst_operands = [p;q] /\
  taint_ok fn tn inst s ==> op_taint tn p = {}
Proof
  strip_tac >> fs[taint_ok_def] >>
  qpat_x_assum `!op. MEM op inst.inst_operands /\ _ ==> _` (qspec_then `p` mp_tac) >>
  gvs[MEM]
QED

val operands_related = ``!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    ?y. eval_operand op t = SOME y /\ fmp_value_rel sm (op_prov G op) (op_taint tn op) x y``;
val operands_equal = ``!op x. MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x``;

Theorem cut_scalar_operands_equal[local]:
  MEM inst.inst_opcode ^clean_in /\ ptr_use_static_ok P pv inst /\
  FDOM G SUBSET pv /\ taint_ok fn tn inst s /\ ^operands_related /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `op_prov G op = NONE` by (irule cut_scalar_prov >> qexistsl [`P`,`inst`,`pv`] >> simp[]) >>
  `op_taint tn op = {}` by (irule cut_plain_taint >> qexistsl [`fn`,`inst`,`s`] >> simp[]) >>
  qpat_x_assum `!op x. _` (qspecl_then [`op`,`x`] mp_tac) >>
  simp[] >> strip_tac >> imp_res_tac fmp_mem_value_clean >> gvs[]
QED

Theorem cut_binary_value[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode ^binops /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ eval_operand q s = SOME y /\
  fmp_value_rel sm (op_prov G p) (op_taint tn p) x x' /\
  fmp_value_rel sm (op_prov G q) (op_taint tn q) y y' ==>
  fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s)
    ((^bin_eval) x y) ((^bin_eval) x' y')
Proof
  strip_tac >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by metis_tac[fn_static_ptr_ok_def] >>
  Cases_on `MEM inst.inst_opcode ^affine \/ MEM inst.inst_opcode ^comparisons`
  >- (`op_taint tn p = {} /\ op_taint tn q = {}` by
        (conj_tac >> irule cut_plain_taint >> qexistsl [`fn`,`inst`,`s`] >> simp[MEM] >> fs[MEM]) >>
      Cases_on `MEM inst.inst_opcode ^affine`
      >- (drule_all cut_affine_prov >> strip_tac >> irule cut_affine_value >>
          simp[] >> (gvs[])) >>
      `MEM inst.inst_opcode ^comparisons` by fs[] >>
      `(^bin_eval) x y = (^bin_eval) x' y'` by (irule cut_cmp_value >> metis_tac[]) >>
      pop_assum SUBST1_TAC >> irule cut_clean_output >> simp[]) >>
  `MEM inst.inst_opcode ^scalar_in` by gvs[MEM] >>
  `op_prov G p = NONE /\ op_prov G q = NONE` by
    (conj_tac >> irule cut_scalar_prov >> qexistsl [`P`,`inst`,`fn_pv P fn`] >> simp[]) >>
  Cases_on `inst.inst_opcode = MUL`
  >- (simp[] >> irule cut_mul_value >> metis_tac[]) >>
  `MEM inst.inst_opcode ^shifts` by gvs[MEM] >>
  `op_taint tn p = {}` by (irule cut_shift_amount >> metis_tac[]) >>
  irule cut_shift_value >> simp[] >> metis_tac[]
QED

Theorem cut_exec_binary_ok[local]:
  exec_pure2 f inst s = OK s1 ==>
  ?p q out x y. inst.inst_operands = [p;q] /\ inst.inst_outputs = [out] /\
    eval_operand p s = SOME x /\ eval_operand q s = SOME y /\
    s1 = update_var out (f x y) s
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem cut_binary_step[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode ^binops /\ ^operands_related /\ step_inst_base inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out y t) /\
    fmp_value_rel sm (out_prov PG G inst s1) (out_taint tn inst s) x y
Proof
  strip_tac >>
  `exec_pure2 (^bin_eval) inst s = OK s1` by metis_tac[cut_bin_eval] >>
  drule cut_exec_binary_ok >>
  disch_then (qx_choose_then `p` (qx_choose_then `q` (qx_choose_then `out`
    (qx_choose_then `x` (qx_choose_then `y` strip_assume_tac))))) >>
  `?x'. eval_operand p t = SOME x' /\ fmp_value_rel sm (op_prov G p) (op_taint tn p) x x'` by
    metis_tac[MEM] >>
  `?y'. eval_operand q t = SOME y' /\ fmp_value_rel sm (op_prov G q) (op_taint tn q) y y'` by
    metis_tac[MEM] >>
  qexistsl [`out`,`(^bin_eval) x y`,`(^bin_eval) x' y'`] >>
  simp[cut_bin_eval, exec_pure2_def] >> irule cut_binary_value >> metis_tac[]
QED

(* Apart from assertions, these instructions either update a register or
   fail with Error. Classify the source result before transporting values. *)
Theorem cut_update_terminates[local]:
  MEM inst.inst_opcode (^reads ++ ^clean_scalars ++ ^dedicated) /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  ?s1. r = OK s1
Proof
  strip_tac >>
  `(?s1. step_inst_base inst s = OK s1) \/ (?e. step_inst_base inst s = Error e)` by
    (qpat_x_assum `step_inst_base _ _ = r` kall_tac >> fs[MEM] >>
     simp[step_inst_base_opcode_eqs, exec_pure1_result_cases, exec_pure2_result_cases,
          exec_pure3_result_cases, exec_read0_result_cases, exec_read1_result_cases] >>
     rpt (CASE_TAC >> simp[])) >>
  gvs[passSimulationDefsTheory.terminates_def]
QED

val assign_operands = ``!op x out. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
  eval_operand op s = SOME x ==> ?y. eval_operand op t = SOME y /\
    (~retpc_var fn out ==> fmp_value_rel sm (op_prov G op) (op_taint tn op) x y)``;

Theorem cut_pure_update[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode (^reads ++ ^clean_scalars ++ ^dedicated) /\
  (inst.inst_opcode <> ASSIGN ==> ^operands_related) /\
  (inst.inst_opcode = ASSIGN ==> ^assign_operands) /\
  step_inst_base inst s = OK s1 ==>
  ?out x y. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
    step_inst_base inst t = OK (update_var out y t) /\
    (~retpc_var fn out ==> fmp_value_rel sm (out_prov PG G inst s1)
      (out_taint tn inst s) x y)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ASSIGN`
  >- (irule cut_assign_step >> simp[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (`fmp_params_rel sm PG s t` by gvs[fmp_stage_rel_def, fmp_frame_rel_def] >>
      drule_all cut_param_step >> metis_tac[]) >>
  `^operands_related` by fs[] >>
  Cases_on `MEM inst.inst_opcode ^binops`
  >- (drule_all cut_binary_step >> metis_tac[]) >>
  `MEM inst.inst_opcode (^reads ++ ^clean_scalars)` by gvs[MEM] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by metis_tac[fn_static_ptr_ok_def] >>
  `^operands_equal` by
    (`MEM inst.inst_opcode ^clean_in` by simp[MEM_APPEND] >>
     rpt gen_tac >> strip_tac >> drule_all cut_scalar_operands_equal >> simp[]) >>
  `?out x. inst.inst_outputs = [out] /\ s1 = update_var out x s /\
     step_inst_base inst t = OK (update_var out x t)` by
    (Cases_on `MEM inst.inst_opcode ^reads`
     >- (drule_all cut_context_read >> simp[]) >>
     `MEM inst.inst_opcode ^clean_scalars` by fs[MEM_APPEND] >>
     drule_all cut_clean_step >> simp[]) >>
  qexistsl [`out`,`x`,`x`] >> simp[] >>
  strip_tac >> irule cut_clean_output >> simp[MEM_APPEND]
QED

(* This is the local effect only: advancing the instruction index and
   rebuilding the frame relation are responsibilities of the segment step. *)
Theorem focus_fmp_cut_pure_effect:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  FDOM G SUBSET fn_pv P fn /\ fn_static_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst_wf inst /\ access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode ^pure_ops /\
  (inst.inst_opcode <> ASSIGN ==> ^operands_related) /\
  (inst.inst_opcode = ASSIGN ==> ^assign_operands) /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  ?r'. step_inst_base inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\ ^cut_data
    | Abort ab s1 => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode ^idle`
  >- (`ptr_use_static_ok P (fn_pv P fn) inst` by metis_tac[fn_static_ptr_ok_def] >>
      `inst.inst_opcode <> ASSIGN` by gvs[MEM] >>
      `^operands_related` by fs[] >>
      `^operands_equal` by
        (`MEM inst.inst_opcode ^clean_in` by simp[MEM_APPEND] >>
         rpt gen_tac >> strip_tac >> drule_all cut_scalar_operands_equal >> simp[]) >>
      drule_all cut_idle_step >> strip_tac
      >- (`inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
          qexists `OK t` >> conj_tac >- metis_tac[] >>
          qpat_x_assum `r = OK s` SUBST_ALL_TAC >>
          pure_rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
          qexists `t` >> conj_tac >- simp[] >>
          irule cut_pure_data >> metis_tac[]) >>
      qexists `Abort ab t1` >> gvs[dead_result_rel_def]) >>
  `MEM inst.inst_opcode (^reads ++ ^clean_scalars ++ ^dedicated)` by fs[MEM_APPEND] >>
  drule_all cut_update_terminates >> strip_tac >>
  qpat_x_assum `r = OK s1` SUBST_ALL_TAC >>
  drule_all cut_pure_update >> strip_tac >>
  qexists `OK (update_var out y t)` >> conj_tac >- simp[] >>
  pure_rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  qexists `update_var out y t` >> conj_tac >- simp[] >>
  irule cut_pure_data >> metis_tac[]
QED
