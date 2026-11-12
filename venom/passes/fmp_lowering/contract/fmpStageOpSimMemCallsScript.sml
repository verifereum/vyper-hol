(* External calls at the FMP boundary. *)
Theory fmpStageOpSimMemCalls
Ancestors
  fmpStageOpSimMemSupport fmpStageOpSimMemReads fmpStageOpBase fmpStageRel
  o1LowerDloadExternalOracle o1LowerDloadExternalEffects o1LowerDloadShared
  o1LowerDloadRangeTransport o1LowerDloadRelocationKernel o1PassContract
  ptrDiscipline ptrStaticDiscipline contextCodegenRel codegenRel unitShapeDefs
  venomExecSemantics venomCallOracleDefs extCallOracle venomState venomInst
  memLocDefs pointerConfinedDefs words finite_map pred_set list

Theorem fmp_mem_external_scalar_clean:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM op inst.inst_operands /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   (?P. EVERY (fn_static_ptr_ok P) C.ctx_functions) /\ taint_ok fn tn inst s` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    fs[EVERY_MEM, fn_static_ptr_ok_def] >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
     `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def] >> metis_tac[]) >>
  simp[] >> fs[taint_ok_def] >> gvs[] >> metis_tac[]
QED

Theorem fmp_mem_external_scalar:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    metis_tac[fmp_mem_external_scalar_clean] >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by
    gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_operand_clean >> simp[]
QED

Theorem fmp_mem_external_input:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    read_memory (w2n x) len s = read_memory (w2n y) len t
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn op = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_read_operand_range >> strip_tac >>
  qexists_tac `y` >> simp[] >>
  irule LIST_EQ >> simp[ld_read_memory_length] >> rpt strip_tac >>
  `w2n x+x' NOTIN tn.t_mem` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, about_to_revert_def] >> strip_tac >>
     qpat_x_assum `!off len i. _` (qspecl_then [`w2n x`,`len`,`w2n x+x'`] mp_tac) >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[fmp_stage_rel_def] >> metis_tac[]
QED

Theorem fmp_mem_external_world:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> INVOKE /\ step_inst k C inst s = OK s1 /\
  LENGTH s.vs_requests < LENGTH s1.vs_requests ==>
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient
Proof
  strip_tac >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def, taint_within_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe]
QED

Theorem fmp_mem_call_operands[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop])) /\
  inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
  (!op. MEM op prefix ==> ?w. eval_operand op s = SOME w) /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs ==>
  (!op x. MEM op (prefix ++ [szop;rsop]) /\ eval_operand op s = SOME x ==>
     eval_operand op t = SOME x) /\
  ?off' ro'. eval_operand offop t = SOME off' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  strip_tac >> (
  conj_tac
  >- (rpt strip_tac >> irule fmp_mem_external_scalar >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >> simp[Excl "FILTER"] >>
      reverse conj_tac >- (gvs[] >> metis_tac[]) >>
      gvs[Excl "FILTER", mem_read_ops_def, mem_write_ops_def] >>
      rpt strip_tac >> gvs[Excl "FILTER"] >>
      qpat_x_assum `FILTER _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [FILTER] >> rpt IF_CASES_TAC >> simp[]) >>
  `(?w. eval_operand gop s = SOME w) /\ (?w. eval_operand adop s = SOME w) /\
   (inst.inst_opcode = CALL ==> ?w. eval_operand vop s = SOME w)` by
    (gvs[] >> metis_tac[]) >>
  `?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (irule fmp_mem_external_input >> conj_tac >- simp[] >> goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     gvs[mem_read_ops_def, source_memory_read_ranges_def, memory_range_of_operands_def] >>
     `?w. eval_operand vop s = SOME w` by metis_tac[] >> simp[]) >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn rop = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `!v. rop = Var v ==> ~retpc_var fn v` by
    (`!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
     `MEM rop inst.inst_operands` by simp[] >> metis_tac[fmp_mem_operand_non_retpc]) >>
  `?ro'. eval_operand rop t = SOME ro' /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (irule fmp_mem_write_operand_range >> goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     gvs[mem_write_ops_def, source_memory_write_ranges_def,
         fixed_source_write_range_def] >>
     `?w. eval_operand vop s = SOME w` by metis_tac[] >> simp[]) >>
  gvs[] >> metis_tac[])
QED
