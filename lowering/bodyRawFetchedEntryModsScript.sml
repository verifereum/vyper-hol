(* Identify the concrete CALL-family instruction at the prepared request cursor. *)
Theory bodyRawFetchedEntryMods
Ancestors
  exprSimRawCallCalldata bodyPtrMakeArrayEmission emitHelperProps exprLoweringProps
  exprOperandVar bodyPtrDefs allocaSiteResource ptrDiscipline fragExec spillSim compileEnv
  memSafeRun unitTransformDefs loweringStateRelDefs venomMemDefs
  contextCodegenRel codegenRel memLocDefs
  venomInst venomState words finite_map alist list arithmetic

val call_opcode = ``case call_ty of RegularCall => CALL | StaticCall => STATICCALL
                                      | DelegateCall => DELEGATECALL``;
val call_ops = ``if call_ty = RegularCall then [gas;addr;vop;dp;len;op;Lit (n2w cap)]
                else [gas;addr;dp;len;op;Lit (n2w cap)]``;
val call_inst = ``mk_inst s7.cs_next_id ^call_opcode ^call_ops
                    [STRING #"%" (toString s7.cs_next_var)]``;
val outsize = ``if cap = 0 then 0 else 32 * ((cap + 31) DIV 32) + 32``;
val outbase = ``if cap = 0 then ob else ob + 32``;

Theorem raw_fetched_code[local]:
  compile_raw_call_finish addr dp len gas vop call_ty cap rev ov op s7 = (result,sb) /\
  fn_has_code sa sb func /\ ci_mono sa s7 /\
  t7.vs_current_bb = s7.cs_current_bb /\ t7.vs_inst_idx = LENGTH s7.cs_current_insts ==>
  ?ok sc bb. emit_op ^call_opcode ^call_ops s7 = (ok,sc) /\
    emitted_insts s7 sc = [^call_inst] /\
    lookup_block t7.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t7.vs_inst_idx = SOME ^call_inst /\
    fn_has_code s7 sc func /\ fn_has_code sc sb func /\ ci_mono s7 sc /\
    ok = Var (STRING #"%" (toString s7.cs_next_var)) /\
    sc.cs_next_id = s7.cs_next_id + 1 /\ sc.cs_next_var = s7.cs_next_var + 1 /\
    sc.cs_current_bb = s7.cs_current_bb /\ LENGTH sc.cs_current_insts = SUC t7.vs_inst_idx /\
    (!x. not_fresh_at s7 x ==> x <> STRING #"%" (toString s7.cs_next_var))
Proof
  strip_tac >> drule raw_call_finish_prefix >> strip_tac >>
  `emit_op ^call_opcode ^call_ops s7 = (success,sc)` by
    (Cases_on `call_ty` >> fs[]) >>
  `ci_mono s7 sc` by
    (qpat_assum `emit_op _ _ _ = _` (fn th =>
       ACCEPT_TAC (REWRITE_RULE [th,pairTheory.SND]
         (Q.SPECL [`^call_opcode`,`^call_ops`,`s7`] ci_mono_emit_op)))) >>
  `cs_extends sa s7 /\ cs_extends s7 sc` by fs[ci_mono_def] >>
  `fn_has_code s7 sc func` by (irule fn_has_code_mid >> metis_tac[]) >>
  `fn_has_code sc sb func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sa`] >>
     simp[cs_extends_refl] >> irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [`success`,`sc`,`bb`] >> simp[not_fresh_at_def] >>
  metis_tac[]
QED

Theorem raw_output_window[local]:
  alloca_inv t7 /\ allocas_from lo t7 /\
  ob + ^outsize < dimword (:256) /\ FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,^outsize) /\
  eval_operand op t7 = SOME (n2w ^outbase) /\ op_prov G7 op = SOME (ob,^outsize) /\
  op_taint tn7 op = {} ==>
  w2n (n2w ^outbase : bytes32) = ^outbase /\
  ^outbase + cap <= ob + ^outsize /\
  (cap <> 0 ==> lo <= ^outbase /\ ^outbase + cap <= t7.vs_alloca_next /\
     ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap)
Proof
  strip_tac >>
  `cap <= 32 * ((cap + 31) DIV 32)` by simp[spillSimTheory.n_le_round_up_32] >>
  `ob + ^outsize <= t7.vs_alloca_next` by drule_all_then ACCEPT_TAC alloca_site_registered_below >>
  `lo <= ob` by (fs[allocas_from_def] >> metis_tac[]) >>
  `^outbase + cap <= ob + ^outsize` by (Cases_on `cap = 0` >> simp[] >> decide_tac) >>
  `^outbase < dimword (:256)` by decide_tac >>
  simp[w2n_n2w] >> disch_tac >>
  `lo <= ob + 32 /\ ob + 32 + cap <= t7.vs_alloca_next` by (fs[] >> decide_tac) >>
  simp[] >>
  qpat_x_assum `op_prov G7 op = _` mp_tac >>
  qpat_x_assum `eval_operand op t7 = _` mp_tac >>
  qpat_x_assum `op_taint tn7 op = {}` mp_tac >>
  Cases_on `op` >> simp[ptr_covers_def, op_prov_def, eval_operand_def, w2n_n2w] >>
  rpt strip_tac >> fs[] >> decide_tac
QED

Theorem raw_fetched_ranges[local]:
  eval_operand gas t7 = SOME gw /\ eval_operand addr t7 = SOME aw /\
  eval_operand vop t7 = SOME vw /\ eval_operand dp t7 = SOME iw /\
  eval_operand len t7 = SOME nw /\ eval_operand op t7 = SOME rw /\
  cap < dimword (:256) /\ EVERY (\p. op_taint tn7 p = {}) [addr;len;dp;gas;vop;op] /\
  (w2n nw = 0 \/ w2n iw + w2n nw <= t7.vs_alloca_next \/
    ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= w2n iw /\ w2n iw + w2n nw <= w2n t7.vs_fmp) /\
  (cap <> 0 ==> w2n rw + cap <= t7.vs_alloca_next) ==>
  source_memory_read_ranges ^call_inst t7 = [(w2n iw,w2n nw)] /\
  source_memory_write_ranges ^call_inst t7 = [(w2n rw,cap)] /\
  EVERY (\p. op_taint tn7 p = {}) (^call_inst).inst_operands /\
  mem_safe_step 0 ctx ^call_inst t7
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `source_memory_read_ranges ^call_inst t7 = [(w2n iw,w2n nw)] /\
   source_memory_write_ranges ^call_inst t7 = [(w2n rw,cap)]` by
    (Cases_on `call_ty` >>
     simp[mk_inst_def,source_memory_read_ranges_def,source_memory_write_ranges_def,
          mem_read_ops_def,mem_write_ops_def,memory_range_of_operands_def,eval_operand_def,w2n_n2w]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_x_assum `EVERY _ _` mp_tac >> Cases_on `call_ty` >>
      simp[mk_inst_def,op_taint_def]) >>
  `(^call_inst).inst_opcode <> INVOKE /\ (^call_inst).inst_opcode <> DALLOCA /\
   inst_dload_in_section ^call_inst t7` by
    (Cases_on `call_ty` >> simp[mk_inst_def,inst_dload_in_section_def]) >>
  simp[mem_safe_step_non_invoke,inst_mem_below_frontier_def,inst_mem_below_frontiers_def] >>
  qpat_x_assum `w2n nw = 0 \/ _` mp_tac >> simp[w2n_eq_0] >> tautLib.TAUT_TAC
QED

Theorem raw_call_fetched_entry_mods:
  compile_raw_call_finish addr dp len gas vop call_ty cap rev ov op s7 = (result,sb) /\
  fn_has_code sa sb func /\ ci_mono sa s7 /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  t7.vs_current_bb = s7.cs_current_bb /\ t7.vs_inst_idx = LENGTH s7.cs_current_insts /\
  alloca_inv t7 /\ allocas_from lo t7 /\ cap < dimword (:256) /\
  eval_operand gas t7 = SOME gw /\ eval_operand addr t7 = SOME aw /\ eval_operand vop t7 = SOME vw /\
  eval_operand dp t7 = SOME (n2w ib) /\ eval_operand len t7 = SOME (n2w (LENGTH bs)) /\
  eval_operand op t7 = SOME (n2w ^outbase) /\ ib < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  (LENGTH bs = 0 \/ ib + LENGTH bs <= t7.vs_alloca_next \/
   ctx_has_dalloca ctx /\ w2n t7.vs_initial_fmp <= ib /\ ib + LENGTH bs <= w2n t7.vs_fmp) /\
  (bs <> [] ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
  ob + ^outsize < dimword (:256) /\ FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,^outsize) /\
  op_prov G7 op = SOME (ob,^outsize) /\ op_taint tn7 op = {} /\
  EVERY (\p. op_taint tn7 p = {}) [addr;len;dp;gas;vop] /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> regions_disjoint ob ^outsize lb sz) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) ob ^outsize) ==>
  ?ok sc inst bb. emit_op ^call_opcode ^call_ops s7 = (ok,sc) /\
    inst = ^call_inst /\ emitted_insts s7 sc = [inst] /\
    lookup_block t7.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t7.vs_inst_idx = SOME inst /\ fn_has_code s7 sc func /\
    fn_has_code sc sb func /\ ci_mono s7 sc /\
    ok = Var (STRING #"%" (toString s7.cs_next_var)) /\
    sc.cs_next_id = s7.cs_next_id + 1 /\ sc.cs_next_var = s7.cs_next_var + 1 /\
    sc.cs_current_bb = s7.cs_current_bb /\ LENGTH sc.cs_current_insts = SUC t7.vs_inst_idx /\
    (!x. not_fresh_at s7 x ==> x <> STRING #"%" (toString s7.cs_next_var)) /\
    local_ptrs_reserved cenv s7 /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s7 x) /\
    source_memory_read_ranges inst t7 = [(ib,LENGTH bs)] /\
    source_memory_write_ranges inst t7 = [(^outbase,cap)] /\
    EVERY (\p. op_taint tn7 p = {}) inst.inst_operands /\ mem_safe_step 0 ctx inst t7 /\
    w2n (n2w ^outbase : bytes32) = ^outbase /\
    ((n2w (LENGTH bs) : bytes32) <> 0w ==> ?p. dp = Var p /\ ptr_covers G7 tn7 p t7 (LENGTH bs)) /\
    (cap <> 0 ==> lo <= ^outbase /\ ^outbase + cap <= t7.vs_alloca_next /\
       ?p. op = Var p /\ ptr_covers G7 tn7 p t7 cap) /\
    (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==> regions_disjoint ^outbase cap lb sz) /\
    (cenv.ce_is_ctor ==> !src tops name tv v off.
      ALOOKUP cenv.ce_modules src = SOME tops /\
      FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
               | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) ^outbase cap)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac raw_fetched_code >>
  drule_all_then strip_assume_tac raw_output_window >>
  `w2n (n2w ib : bytes32) = ib /\ w2n (n2w (LENGTH bs) : bytes32) = LENGTH bs` by simp[w2n_n2w] >>
  `EVERY (\p. op_taint tn7 p = {}) [addr;len;dp;gas;vop;op]` by fs[] >>
  `cap <> 0 ==> ^outbase + cap <= t7.vs_alloca_next` by metis_tac[] >>
  mp_tac (Q.INST [`iw` |-> `n2w ib`, `nw` |-> `n2w (LENGTH bs)`,
                  `rw` |-> `n2w ^outbase`] raw_fetched_ranges) >>
  (impl_tac >- asm_rewrite_tac[]) >> rewrite_tac[] >> strip_tac >>
  qexistsl_tac [`ok`,`sc`, `^call_inst`, `bb`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- metis_tac[compiler_ci_mono_reserved]
  >- metis_tac[compiler_ci_mono_not_fresh]
  >- metis_tac[compiler_ci_mono_not_fresh]
  >- (Cases_on `bs` >> simp[]) 
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name lb sz. local_region _ _ _ _ _ _ ==> _` drule >>
      Cases_on `cap = 0` >- simp[] >>
      qpat_assum `^outbase + cap <= ob + ^outsize` mp_tac >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `cenv.ce_is_ctor ==> !src tops name tv v off. _` (drule_then drule_all) >>
  Cases_on `cap = 0` >- simp[] >>
  qpat_assum `^outbase + cap <= ob + ^outsize` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED
