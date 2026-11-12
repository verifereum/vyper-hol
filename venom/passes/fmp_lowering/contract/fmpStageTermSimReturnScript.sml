Theory fmpStageTermSimReturn
Ancestors
  fmpStageOpBase fmpStageRel ptrStaticDiscipline ptrDiscipline
  o1LowerDloadRangeTransport o1LowerDloadShared o1LowerDloadOpaque
  o1LowerDloadRelocationKernel o1LowerDloadAddressArithmetic
  fmpLowerSequenceExec words arithmetic memSafeRun passSimulationDefs
  dftGasFromListLookup
  o1PassContract contextCodegenRel venomExecSemantics venomState venomInst
  finite_map pred_set list pointerConfinedDefs memLocDefs unitShapeDefs

Theorem fmp_return_size_prov[local]:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sz] ==>
  op_prov G sz = NONE
Proof
  strip_tac >> Cases_on `sz` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN pv` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `addr = Var v` >> gvs[]
QED

Theorem fmp_return_operand[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  inst.inst_opcode = RETURN /\ MEM op inst.inst_operands /\
  eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) {} x y
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (rpt strip_tac >>
     `opaque_use_ok fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
     gvs[] >> drule_all opaque_use_ok_retpc_use >> simp[retpc_use_ok_def]) >>
  `inst.inst_opcode <> PHI` by simp[] >>
  metis_tac[fmp_stage_operand]
QED

Theorem fmp_return_length[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [addr;sz] /\
  eval_operand sz s = SOME len ==>
  eval_operand sz t = SOME len
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_static_ptr_ok_def] >> metis_tac[]) >>
  `op_prov G sz = NONE` by metis_tac[fmp_return_size_prov] >>
  `MEM sz inst.inst_operands` by simp[] >>
  drule_all fmp_return_operand >> strip_tac >>
  gvs[fmp_value_rel_def] >> metis_tac[ld_value_agree_clean]
QED

Theorem fmp_return_value_range[local]:
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp /\ lo <= w2n raw_fmp /\
  fmp_value_rel sm (op_prov G op) {} x y /\
  (len <> 0 /\ (eom < w2n x+len \/ op_prov G op <> NONE) ==>
   ?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b <= w2n x /\ w2n x+len <= b+z) ==>
  len=0 \/ (w2n x=w2n y /\ w2n x+len<=eom) \/
  (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
    j+len<=z /\ w2n x=b+j /\ w2n y=c+j)
Proof
  strip_tac >> Cases_on `len=0` >> simp[] >>
  Cases_on `op_prov G op = NONE`
  >- (gvs[fmp_value_rel_def] >>
      `x=y` by metis_tac[ld_value_agree_clean] >> gvs[] >>
      Cases_on `eom < w2n x+len` >> gvs[] >>
      gvs[op_prov_def]) >>
  `?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b <= w2n x /\ w2n x+len <= b+z` by metis_tac[] >>
  gvs[op_prov_def, fmp_value_rel_def, ld_value_agree_pointer,
      FLOOKUP_fmp_ld_sites, AllCaseEqs()] >>
  rename1 `FLOOKUP sm (b,z) = SOME (c,id)` >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    (fs[fmp_sites_ok_def] >> metis_tac[w2n_lt, LESS_EQ_LESS_TRANS]) >>
  `w2n (x+n2w c-n2w b) = c+(w2n x-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `z` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`(b,z)`,`b`,`c`,`z`,`w2n x-b`] >>
  simp[FLOOKUP_fmp_ld_sites]
QED

Theorem fmp_return_slice[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = RETURN /\
  inst.inst_operands = [addr;sz] /\
  eval_operand addr s = SOME p /\ eval_operand sz s = SOME len ==>
  ?q. eval_operand addr t = SOME q /\ eval_operand sz t = SOME len /\
    (!k. k < w2n len /\ k NOTIN ret_taint tn inst s ==>
      EL k (read_memory (w2n p) (w2n len) s) =
      EL k (read_memory (w2n q) (w2n len) t))
Proof
  strip_tac >>
  `eval_operand sz t = SOME len` by metis_tac[fmp_return_length] >>
  `MEM addr inst.inst_operands` by simp[] >>
  drule_all fmp_return_operand >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `w2n len <> 0 /\ (eom < w2n p+w2n len \/ op_prov G addr <> NONE) ==>
   ?v b z. addr = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b <= w2n p /\ w2n p+w2n len <= b+z` by
    (gvs[access_ok_def, mem_read_ops_def, source_memory_read_ranges_def,
         memory_range_of_operands_def] >> metis_tac[]) >>
  `fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\ lo <= w2n s.vs_fmp` by
    (fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
     metis_tac[fmp_frontier_rel_le]) >>
  drule_all fmp_return_value_range >>
  strip_tac >>
  qexists_tac `y` >> simp[] >> rpt strip_tac >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[ret_taint_def] >> fs[fmp_stage_rel_def] >> metis_tac[]
QED

Theorem fmp_return_halt[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = RETURN /\
  step_inst fuel C inst s = Halt s1 ==>
  ?t1. step_inst fuel C' inst t = Halt t1 /\
       dead_result_rel D (Halt s1) (Halt t1)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `final_taint vs C s1 (step_taint inst s s1 tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >> metis_tac[]) >>
  `taint_within D C vs` by
    fs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> fs[] >>
  rename1 `inst.inst_operands = [addr;sizeop]` >>
  rename1 `eval_operand addr s = SOME p` >>
  rename1 `eval_operand sizeop s = SOME len` >>
  drule_all fmp_return_slice >> strip_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >> simp[] >>
  irule ld_shared_halt_result >>
  gvs[halt_state_def, set_returndata_def, step_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, ld_read_memory_length,
      GSYM read_memory_def, taint_within_def] >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address) /\
   tn.t_imm SUBSET D.d_imm s.vs_immutables /\
   ret_taint tn inst s SUBSET D.d_ret (read_memory (w2n p) (w2n len) s)` by
    (first_x_assum drule >> simp[]) >>
  conj_tac >- (qexists_tac `ret_taint tn inst s` >> simp[]) >>
  qexistsl_tac [`s.vs_call_ctx.cc_address`, `tn`] >> gvs[ld_shared_agree_def]
QED

Theorem fmp_stage_return_result:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = RETURN /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => s1.vs_halted /\
               ?t1. r' = OK t1 /\ t1.vs_halted /\
                    dead_result_rel D (Halt s1) (Halt t1)
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `wf_function fn` by
    (drule_all fmp_stage_frame_facts >> simp[o1_fn_shape_def]) >>
  drule_all wf_active_lookup >> strip_tac >>
  `~in_revert_forward fn s` by
    (simp[in_revert_forward_def] >> rpt strip_tac >> gvs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  `?s1. r = Halt s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_def] >>
     simp[AllCaseEqs()] >> rpt strip_tac >> gvs[terminates_def]) >>
  gvs[] >> drule_all fmp_return_halt >> strip_tac >>
  qexists_tac `k` >> simp[]
QED
