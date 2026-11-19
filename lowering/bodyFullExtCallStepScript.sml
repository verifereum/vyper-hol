Theory bodyFullExtCallStep
Ancestors
  exprSimRawCallCalldata extCallOracleStep vyperInterpreter words
  exprSimHash immutableMemoryFrame loweringSlice localPtrsProps
  loweringStateRelDefs venomExecSemantics venomState stateRelProj

(* A source frame can remove the value even when the emitted opcode is CALL.
   Only the explicit source gas cap must agree with the evaluated gas word. *)
Theorem extcall_framed_oracle_step:
  state_rel H func cenv cx es s /\ inst.inst_outputs = [out] /\
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands =
    (if stat then [gop;aop;iop;zop;rop;cop]
     else [gop;aop;vop;iop;zop;rop;cop]) /\
  eval_operand gop s = SOME gw /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand iop s = SOME ip /\
  eval_operand zop s = SOME iz /\ eval_operand rop s = SOME rp /\
  eval_operand cop s = SOME cap /\
  (stat <=> value_opt = NONE) /\
  w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
  frame_call_value cx value_opt es = (INL framed_value,es) /\
  (!g. OPTION_BIND gas dest_NumV = SOME g ==> g = w2n gw) /\
  w2w aw = target /\ read_memory (w2n ip) (w2n iz) s = calldata /\
  take_call_outcome (OPTION_BIND gas dest_NumV) target calldata framed_value es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    loweringStateRelDefs$regions_disjoint (w2n rp) (w2n cap) b sz) /\
  (cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
                 | SOME imms => get_source_immutables cenv.ce_module imms)
       name = SOME (tv,v) ==>
     loweringStateRelDefs$regions_disjoint (w2n rp) (w2n cap) off
       (type_memory_size tv)) ==>
  ?t. step_inst_base inst s =
        OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
      state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
      t.vs_returndata = outcome.co_returnData /\
      t.vs_memory = (write_memory_with_expansion (w2n rp)
                      (TAKE (w2n cap) outcome.co_returnData) s).vs_memory /\
      t.vs_fmp = s.vs_fmp /\ t.vs_allocas = s.vs_allocas /\
      t.vs_vars = s.vs_vars /\ t.vs_inst_idx = s.vs_inst_idx /\
      t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  drule frame_call_value_success >> strip_tac >>
  `(cx.txn.is_static ==> stat \/ vw = 0w) /\
   framed_value = (if stat \/ cx.txn.is_static then NONE else SOME (w2n vw))` by
    (Cases_on `value_opt` >> Cases_on `cx.txn.is_static` >>
     gvs[wordsTheory.w2n_eq_0]) >>
  `take_call_outcome (OPTION_BIND gas dest_NumV) (w2w aw)
     (read_memory (w2n ip) (w2n iz) s)
     (if stat \/ cx.txn.is_static then NONE else SOME (w2n vw)) es =
     (INL (rq,outcome),es1)` by metis_tac[] >>
  qabbrev_tac `bytes = TAKE (w2n cap) outcome.co_returnData` >>
  `LENGTH bytes <= w2n cap` by simp[Abbr `bytes`, listTheory.LENGTH_TAKE_EQ] >>
  `local_ptrs_rel func cenv es.scopes
     (write_memory_with_expansion (w2n rp) bytes s)` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     rpt conj_tac
     >~ [`mem_bytes_at _ _ _ = mem_bytes_at _ _ _`]
     >- (rpt strip_tac >> sym_tac >> irule hash_write_memory_disjoint >>
         qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
     >~ [`local_ptrs_rel _ _ _ _`] >- drule_then ACCEPT_TAC state_rel_local_ptrs_rel >>
     rpt strip_tac >> gvs[write_memory_with_expansion_def, lookup_var_def]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (write_memory_with_expansion (w2n rp) bytes s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     rpt conj_tac
     >~ [`mem_bytes_at _ _ _ = mem_bytes_at _ _ _`]
     >- (strip_tac >> rpt gen_tac >> strip_tac >> irule hash_write_memory_disjoint >>
         qpat_x_assum `cenv.ce_is_ctor ==> _` drule >> disch_then drule_all >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
     >~ [`immutables_rel _ _ _ _ _ _`]
     >- drule_then ACCEPT_TAC state_rel_immutables_rel >>
     simp[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF,
          write_memory_with_expansion_def]) >>
  qunabbrev_tac `bytes` >> drule_all raw_call_oracle_step >> simp[]
QED
