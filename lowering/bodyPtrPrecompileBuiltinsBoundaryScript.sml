Theory bodyPtrPrecompileBuiltinsBoundary
Ancestors bodyPtrPrecompileBuiltinsOperands ptrSafeRun ptrDiscipline
          venomExecSemantics venomInstProofs venomInst venomState
          contextCodegenRel codegenRel memLocDefs finite_map exprSimPrecompiles
          vyperValue vyperTyping extCallOracle

Theorem staticcall_access_ok:
  ptr_covers G tn src s (w2n an) /\
  ptr_covers G tn dst s (w2n rn) ==>
  access_ok lo G fn
    (mk_inst id STATICCALL [gp; Lit addr; Var src; Lit an; Var dst; Lit rn]
      [out]) s
Proof
  strip_tac >> Cases_on `eval_operand gp s` >>
  gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  simp[access_ok_def, mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, memory_range_of_operands_def,
       eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[mem_read_ops_def, mem_write_ops_def] >> metis_tac[]
QED

Theorem staticcall_taint_ok:
  op_taint tn gp = {} /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  eval_operand (Var src) s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + w2n an ==> i NOTIN tn.t_mem) ==>
  taint_ok fn tn
    (mk_inst id STATICCALL [gp; Lit addr; Var src; Lit an; Var dst; Lit rn]
      [out]) s
Proof
  strip_tac >> simp[taint_ok_def, mk_inst_def] >> conj_tac
  >- (gen_tac >> Cases_on `op` >> Cases_on `gp` >>
      gvs[op_taint_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  simp[source_memory_read_ranges_def, memory_range_of_operands_def,
       eval_operand_def] >>
  Cases_on `eval_operand gp s` >>
  Cases_on `lookup_var dst s` >> simp[] >> metis_tac[]
QED

(* Return-data has no separate taint field: external writes clear only the
   returned prefix, not the whole output allocation. *)
Theorem staticcall_mem_taint:
  inst = mk_inst id STATICCALL
    [gp; Lit addr; Var src; Lit an; Var dst; Lit rn] [out] /\
  eval_operand gp s = SOME gas /\
  eval_operand (Var src) s = SOME ai /\
  eval_operand (Var dst) s = SOME ro /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  (step_taint inst s s' tn).t_mem =
    tn.t_mem DIFF {i | w2n ro <= i /\
                      i < w2n ro + MIN (w2n rn) (LENGTH s'.vs_returndata)}
Proof
  strip_tac >> gvs[eval_operand_def] >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, mk_inst_def,
       source_memory_write_ranges_def, eval_operand_def,
       range_bytes_def, finite_mapTheory.FLOOKUP_DEF] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem staticcall_output_taint:
  inst = mk_inst id STATICCALL
    [gp; Lit addr; Var src; Lit an; Var dst; Lit rn] [out] ==>
  op_taint (step_taint inst s s' tn) (Var out) = {}
Proof
  strip_tac >>
  simp[step_taint_def, op_taint_def, out_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem staticcall_ghost_step:
  inst.inst_opcode = STATICCALL /\ step_inst fuel ctx inst s = OK s' ==>
  ghost_step fuel ctx PG G tn inst s =
    (step_prov PG G inst s', step_taint inst s s' tn)
Proof
  simp[ghost_step_def]
QED

Theorem computed_static_writeback_frame:
  rq = venom_call_request s addr 0w ai an T /\ computed_precompile rq /\
  inst.inst_outputs = [out] /\
  exec_ext_call inst s gas addr 0w ai an ro rs T = OK s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
  s'.vs_returndata = (FST (take_outcome rq s.vs_outcomes)).co_returnData
Proof
  strip_tac >> drule_all computed_static_exec >>
  disch_then (qspecl_then [`rs`, `ro`, `gas`] assume_tac) >>
  gvs[update_var_def, write_memory_with_expansion_def]
QED

Theorem staticcall_empty_output_taint:
  inst = mk_inst id STATICCALL
    [gp; Lit addr; Var src; Lit an; Var dst; Lit rn] [out] /\
  eval_operand gp s = SOME gas /\
  eval_operand (Var src) s = SOME ai /\
  eval_operand (Var dst) s = SOME ro /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
  s'.vs_returndata = [] ==>
  (step_taint inst s s' tn).t_mem = tn.t_mem
Proof
  strip_tac >> drule_all staticcall_mem_taint >> simp[]
QED

Theorem staticcall_full_output_taint:
  inst = mk_inst id STATICCALL
    [gp; Lit addr; Var src; Lit an; Var dst; Lit rn] [out] /\
  eval_operand gp s = SOME gas /\
  eval_operand (Var src) s = SOME ai /\
  eval_operand (Var dst) s = SOME ro /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
  w2n rn <= LENGTH s'.vs_returndata ==>
  (step_taint inst s s' tn).t_mem =
    tn.t_mem DIFF {i | w2n ro <= i /\ i < w2n ro + w2n rn}
Proof
  strip_tac >> drule_all staticcall_mem_taint >>
  `MIN (w2n rn) (LENGTH s'.vs_returndata) = w2n rn` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >> simp[]
QED

Theorem ec_point_read_ready:
  ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v op G tn s /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  eval_operand op s = SOME w ==>
  (?p. op = Var p /\ ptr_covers G tn p s 64) /\
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> conj_tac
  >- (`val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64` by
        (Cases_on `v` >>
         simp[loweringPostsTheory.val_footprint_def,
              valueEncodingTheory.type_memory_size_def]) >>
      drule representationCleanPtrTheory.ptr_val_ok_read_covers >>
      simp[compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def,
           type_slot_size_def, wordsTheory.dimword_def] >> metis_tac[]) >>
  drule representationCleanPtrTheory.ptr_val_ok_static_clean >>
  simp[compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def,
       vyperABITheory.vyper_to_abi_type_def, vyperABITheory.vyper_base_to_abi_type_def,
       contractABITheory.is_dynamic_def, valueEncodingTheory.type_memory_size_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  disch_then drule >> simp[]
QED

