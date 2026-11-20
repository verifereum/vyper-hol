Theory bodyFullAbiDecodeClampObserved
Ancestors
  bodyFullAbiDecodeScalarObserved calldataWordLive calldataClampPtr
  bodyPtrBopScalarOutcome ghostPcTransportPtr stateFrame loweringStateRelDefs
  ptrDiscipline emitHelperProps exprLoweringProps abiDecoderReentry venomState

(* Select the clamp's raw result first, then lift it to the joint path and
   to every compatible observer without changing the cut state. *)
Theorem abi_decode_clamp_joint_observed:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand value s = SOME w /\ op_prov G value = NONE /\
  op_taint tn value = {} /\ abi_decoder_operand_live sa.cs_next_var value /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       eval_operand value t = SOME w /\
       op_prov Gf value = NONE /\ op_taint tnf value = {} /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
       tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
       tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
       (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tnf (Var x) = op_taint tn (Var x))))
Proof
  strip_tac >>
  drule calldataClampPtrTheory.abi_decode_clamp_scalar >>
  disch_then (qspecl_then [`{x | not_fresh_at sa x}`, `{value} UNION {Lit w | T}`] mp_tac) >>
  simp[] >> strip_tac >>
  `!op. op IN {value} UNION {Lit w | T} ==>
        op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb` by
    gs[inst_extends_def, same_blocks_def] >>
  drule_all calldataWordLiveTheory.calldata_clamp_repeat >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  reverse (Cases_on `abi_clamp_ok clamp w` >> asm_rewrite_tac[] >> strip_tac)
  >- (drule_all bodyFullAbiDecodeScalarObservedTheory.member_scalar_revert_observed >>
      disch_then (qspecl_then [`explicit`, `PG`]
        (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)))) >>
      qexistsl_tac [`Abort Revert_abort u`, `Gf`, `tnf`] >> simp[]) >>
  drule_all bodyFullAbiDecodeScalarObservedTheory.member_scalar_success_observed >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `eval_operand value t = SOME w` by simp[] >>
  `op_prov Gf value = NONE /\ op_taint tnf value = {}` by
    (qpat_assum `op_prov G value = NONE` mp_tac >>
     qpat_assum `op_taint tn value = {}` mp_tac >>
     Cases_on `value` >>
     gs[op_prov_def, op_taint_def, abi_decoder_operand_live_def,
        abi_decoder_older_vars_def, GSYM not_fresh_at_def]) >>
  qexistsl_tac [`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`, `Gf`, `tnf`] >>
  simp[lookup_var_def, op_taint_def] >>
  qpat_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]
QED
