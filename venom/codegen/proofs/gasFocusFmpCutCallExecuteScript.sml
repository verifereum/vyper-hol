(* Execute the two calls at the selected FMP point without comparing outcomes. *)
Theory gasFocusFmpCutCallExecute
Ancestors
  fmpStagePointRanges fmpStageOpBase fmpStageRel
  lowerDloadExternalInputs lowerDloadOpaqueExecution
  o1LowerDloadRangeTransport o1LowerDloadRelocationKernel o1LowerDloadJointRelation
  ptrDiscipline ptrStaticDiscipline pointerConfinedDefs contextCodegenRel
  codegenRel o1PassContract memLocDefs venomWf
  venomExecSemantics venomCallOracleDefs extCallOracle venomState venomInst
  arithmetic finite_map pred_set words list pair

Theorem cut_call_decode[local]:
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL] /\
  step_inst_base inst s = OK s1 ==>
  ?gop adop vop offop szop rop rsop gas addr value off sz ro rs prefix out.
    eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
    eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
    eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
    ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
      eval_operand vop s = SOME value /\ ~(s.vs_call_ctx.cc_static /\ value <> 0w)) \/
     (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\
      value = 0w)) /\
    inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
    inst.inst_outputs = [out]
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def,
      Excl "consume_call_outcome_eq", pairTheory.UNCURRY, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem cut_call_dispatch[local]:
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
    eval_operand vop s = SOME value /\ ~(s.vs_call_ctx.cc_static /\ value <> 0w)) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\ value = 0w)) /\
  inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
  eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
  inst.inst_outputs = [out] /\
  kind = (if inst.inst_opcode = DELEGATECALL then DelegateMessageCall else MessageCall) /\
  static = (if inst.inst_opcode = CALL then s.vs_call_ctx.cc_static
            else inst.inst_opcode = STATICCALL) /\
  rq = (venom_call_request s addr value off sz static with cr_kind := kind) /\
  consume_call_outcome rq (w2n ro) (w2n rs) s = (w,r) ==>
  step_inst_base inst s = OK (update_var out w r)
Proof
  strip_tac >> gvs[MEM, Excl "consume_call_outcome_eq"] >>
  gvs[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
  simp[step_inst_base_opcode_eqs, exec_ext_call_def, exec_delegatecall_def,
       venom_call_request_def, Excl "consume_call_outcome_eq"]
QED

Theorem cut_call_scalar_prov[local]:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  MEM op inst.inst_operands /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `MEM (Var v) inst.inst_operands` >>
  `v NOTIN pv` by
    (strip_tac >> qpat_x_assum `ptr_use_static_ok _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_use_static_ok_def] >>
     disch_then (mp_tac o CONJUNCT2) >> disch_then (qspec_then `v` mp_tac) >>
     gvs[MEM, is_pointer_preserving_op_def, Excl "FILTER"] >> metis_tac[]) >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem cut_call_clean[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) /\
  (!off len k. MEM (off,len) (source_memory_read_ranges inst s) /\ k < len ==>
     off+k NOTIN tn.t_mem)
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  simp[taint_ok_def, about_to_revert_def] >>
  strip_tac >> (conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `off <= k+off /\ k+off < len+off` by decide_tac >>
  metis_tac[])
QED

Theorem cut_call_nonopaque[local]:
  active_inst fn inst s /\ opaque_use_ok fn /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
  !op v. MEM op inst.inst_operands /\ op = Var v ==> ~retpc_var fn v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> irule ld_retpc_observable_operand >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  simp[] >> qexists_tac `inst` >> gvs[MEM]
QED

Theorem cut_call_scalar[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  MEM op inst.inst_operands /\ (!v. op = Var v ==> ~retpc_var fn v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  `op_prov G op = NONE` by metis_tac[cut_call_scalar_prov] >>
  drule_all fmp_stage_operand_point >> strip_tac >>
  metis_tac[fmp_mem_value_clean]
QED

Theorem cut_call_ranges[local]:
  eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
    eval_operand vop s = SOME value /\ ~(s.vs_call_ctx.cc_static /\ value <> 0w)) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\ value = 0w)) /\
  inst.inst_operands = prefix ++ [offop;szop;rop;rsop] ==>
  source_memory_read_ranges inst s = [(w2n off,w2n sz)] /\
  source_memory_write_ranges inst s = [(w2n ro,w2n rs)] /\
  (?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = offop) /\
  (?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = rop)
Proof
  simp[MEM] >> strip_tac >>
  gvs[source_memory_read_ranges_def, source_memory_write_ranges_def,
      memory_range_of_operands_def, mem_read_ops_def, mem_write_ops_def]
QED

Theorem cut_call_input_bytes[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  (!k. k < len ==> p+k NOTIN tn.t_mem) /\
  (len = 0 \/ (p=q /\ p+len<=eom) \/
    (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
                    j+len<=z /\ p=b+j /\ q=c+j)) ==>
  read_memory p len s = read_memory q len t
Proof
  disch_tac >> irule o1LowerDloadJointRangeReadTheory.ld_memory_agree_clean_slice >>
  qexistsl_tac [`0`,`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
    fs[fmp_stage_rel_def] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem focus_fmp_cut_call_execute:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  opaque_use_ok fn /\ ~in_revert_forward fn s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  eom <= fmp0 /\ fmp0 <= raw0 /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  step_inst_base inst s = OK s1 ==>
  ?gop adop vop offop szop rop rsop gas addr value off off' sz ro ro' rs
   prefix out kind static rq1 rq2 w1 r1 w2 r2.
    inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
    ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
      eval_operand vop s = SOME value /\ eval_operand vop t = SOME value /\
      ~(s.vs_call_ctx.cc_static /\ value <> 0w)) \/
     (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\
      value = 0w)) /\
    eval_operand gop s = SOME gas /\ eval_operand gop t = SOME gas /\
    eval_operand adop s = SOME addr /\ eval_operand adop t = SOME addr /\
    eval_operand offop s = SOME off /\ eval_operand offop t = SOME off' /\
    eval_operand szop s = SOME sz /\ eval_operand szop t = SOME sz /\
    eval_operand rop s = SOME ro /\ eval_operand rop t = SOME ro' /\
    eval_operand rsop s = SOME rs /\ eval_operand rsop t = SOME rs /\
    inst.inst_outputs = [out] /\ s1 = update_var out w1 r1 /\
    step_inst_base inst t = OK (update_var out w2 r2) /\
    kind = (if inst.inst_opcode = DELEGATECALL then DelegateMessageCall else MessageCall) /\
    static = (if inst.inst_opcode = CALL then s.vs_call_ctx.cc_static
              else inst.inst_opcode = STATICCALL) /\
    rq1 = (venom_call_request s addr value off sz static with cr_kind := kind) /\
    rq2 = (venom_call_request t addr value off' sz static with cr_kind := kind) /\
    consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w1,r1) /\
    consume_call_outcome rq2 (w2n ro') (w2n rs) t = (w2,r2) /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    source_memory_write_ranges inst s = [(w2n ro,w2n rs)] /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n rs<=z /\ w2n ro=b+j /\ w2n ro'=c+j)) /\
    ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
      (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))
Proof
  strip_tac >> drule_all cut_call_decode >>
  disch_then (qx_choosel_then
    [`gop`,`adop`,`vop`,`offop`,`szop`,`rop`,`rsop`,`gas`,`addr`,`value`,
     `off`,`sz`,`ro`,`rs`,`prefix`,`out`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all cut_call_clean >> strip_tac >>
  `!op v. MEM op inst.inst_operands /\ op = Var v ==> ~retpc_var fn v` by
    metis_tac[cut_call_nonopaque] >>
  `inst.inst_opcode <> PHI` by gvs[MEM] >>
  `!op. MEM op (prefix ++ [szop;rsop]) ==>
    MEM op inst.inst_operands /\
    (FILTER ($= op) inst.inst_operands = [op] ==>
     !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
       ops.iao_ofst <> op)` by
    (match_mp_tac (GEN_ALL ld_external_layout_scalars) >>
     qexistsl_tac [`vop`,`szop`,`vop`,`rsop`,`rop`,`offop`,`gop`,`adop`] >>
     qpat_x_assum `(inst.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >>
     fs[]) >>
  `!op x. MEM op (prefix ++ [szop;rsop]) /\ eval_operand op s = SOME x ==>
          eval_operand op t = SOME x` by
    (rpt strip_tac >> irule cut_call_scalar >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_use_static_ok _ _ _`)) >> metis_tac[]) >>
  `source_memory_read_ranges inst s = [(w2n off,w2n sz)] /\
   source_memory_write_ranges inst s = [(w2n ro,w2n rs)] /\
   (?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = offop) /\
   (?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = rop)` by
    (match_mp_tac (GEN_ALL cut_call_ranges) >>
     goal_assum (drule_at (Pat `inst.inst_operands = _`)) >>
     goal_assum (drule_at (Pat `(inst.inst_opcode = CALL /\ _) \/ _`)) >>
     simp[]) >>
  `MEM offop inst.inst_operands /\ MEM rop inst.inst_operands` by simp[] >>
  Q.SUBGOAL_THEN `?off'. eval_operand offop t = SOME off' /\
    (w2n sz=0 \/ (w2n off=w2n off' /\ w2n off+w2n sz<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n sz<=z /\ w2n off=b+j /\ w2n off'=c+j))`
    (qx_choose_then `off'` (MAP_EVERY assume_tac o CONJUNCTS))
  >- (match_mp_tac (GEN_ALL fmp_mem_read_operand_range_point) >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `active_inst _ _ _`)) >> simp[]) >>
  Q.SUBGOAL_THEN `?ro'. eval_operand rop t = SOME ro' /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n rs<=z /\ w2n ro=b+j /\ w2n ro'=c+j))`
    (qx_choose_then `ro'` (MAP_EVERY assume_tac o CONJUNCTS))
  >- (match_mp_tac (GEN_ALL fmp_mem_write_operand_range_point) >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `active_inst _ _ _`)) >> simp[]) >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (match_mp_tac (GEN_ALL cut_call_input_bytes) >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[]) >>
  `ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
     (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by
    (irule fmp_mem_geometry_point >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def,fmp_frame_rel_def] >>
  `MEM gop prefix /\ MEM adop prefix` by
    (qpat_x_assum `(inst.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >> simp[]) >>
  `eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
   eval_operand szop t = SOME sz /\ eval_operand rsop t = SOME rs` by simp[] >>
  Q.SUBGOAL_THEN
    `((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
       eval_operand vop t = SOME value /\ ~(t.vs_call_ctx.cc_static /\ value <> 0w)) \/
      (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\
       value = 0w))` assume_tac
  >- (qpat_x_assum `(inst.inst_opcode = CALL /\ _ /\ eval_operand vop s = _ /\ _) \/ _`
        strip_assume_tac >> simp[] >> metis_tac[]) >>
  qabbrev_tac `kind = if inst.inst_opcode = DELEGATECALL then DelegateMessageCall else MessageCall` >>
  qabbrev_tac `static = if inst.inst_opcode = CALL then s.vs_call_ctx.cc_static
                        else inst.inst_opcode = STATICCALL` >>
  qabbrev_tac `rq1 = venom_call_request s addr value off sz static with cr_kind := kind` >>
  qabbrev_tac `rq2 = venom_call_request t addr value off' sz static with cr_kind := kind` >>
  Cases_on `consume_call_outcome rq1 (w2n ro) (w2n rs) s` >>
  rename1 `consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w1,r1)` >>
  Cases_on `consume_call_outcome rq2 (w2n ro') (w2n rs) t` >>
  rename1 `consume_call_outcome rq2 (w2n ro') (w2n rs) t = (w2,r2)` >>
  `step_inst_base inst s = OK (update_var out w1 r1)` by
    (match_mp_tac (GEN_ALL cut_call_dispatch) >>
     goal_assum (drule_at (Pat `inst.inst_operands = _`)) >>
     goal_assum (drule_at (Pat `consume_call_outcome _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `(inst.inst_opcode = CALL /\ _) \/ _`)) >>
     simp[Abbr `rq1`,Abbr `kind`,Abbr `static`,Excl "consume_call_outcome_eq"]) >>
  `step_inst_base inst t = OK (update_var out w2 r2)` by
    (match_mp_tac (GEN_ALL cut_call_dispatch) >>
     goal_assum (drule_at (Pat `inst.inst_operands = _`)) >>
     goal_assum (drule_at (Pat `consume_call_outcome _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `(inst.inst_opcode = CALL /\ _) \/ _`)) >>
     simp[Abbr `rq2`,Abbr `kind`,Abbr `static`,Excl "consume_call_outcome_eq"]) >>
  `s1 = update_var out w1 r1` by metis_tac[exec_result_11] >>
  qexistsl_tac [`gop`,`adop`,`vop`,`offop`,`szop`,`rop`,`rsop`,`gas`,`addr`,`value`,
                `off`,`off'`,`sz`,`ro`,`ro'`,`rs`,`prefix`,`out`,`kind`,`static`,
                `rq1`,`rq2`,`w1`,`r1`,`w2`,`r2`] >>
  simp[Abbr `kind`,Abbr `static`,Abbr `rq1`,Abbr `rq2`,Excl "consume_call_outcome_eq"] >>
  qpat_x_assum `s.vs_call_ctx = t.vs_call_ctx` (SUBST1_TAC o SYM) >>
  qpat_x_assum `(inst.inst_opcode = CALL /\ _ /\ eval_operand vop s = _ /\ _) \/ _`
    strip_assume_tac >> simp[Excl "consume_call_outcome_eq"] >> metis_tac[MEM]
QED
