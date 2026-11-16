(* Optional length-word initialization for the joint MakeArray loop. *)
Theory bodyFullMakeArrayHeader
Ancestors
  bodyFullHashCleanFrame bodyPtrMakeArrayWordStore calldataOverwritePtr
  exprSimAlloc bodyFullMakeArrayInit ghostPcTransportPtr gasOutcomeFull
  exprSimRawLog exprLoweringProps emitHelperProps fragExecPtr
  venomState venomMemDefs valueEncoding valueEncodingProps

val _ = Parse.hide "base";

Theorem make_array_header_joint[local]:
  emit_void MSTORE [Var q; Lit (n2w len)] sm = ((),sh) /\
  lookup_var q s = SOME (n2w base) /\ base + cap < dimword (:256) /\
  32 <= cap /\ base + cap <= s.vs_alloca_next /\
  ptr_covers G tn q s cap /\ allocas_from lo s /\
  fn_has_code sm sh func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tnf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    t = (mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts) /\
    Gf = step_prov PG G (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] [])
      (mstore base (n2w len) s) /\
    tnf = step_taint (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] []) s
      (mstore base (n2w len) s) tn /\
    ci_mono sm sh /\ sh.cs_next_var = sm.cs_next_var /\
    sh.cs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  `base < dimword (:256)` by decide_tac >>
  `ptr_covers G tn q s 32` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand (Var q) s = SOME (n2w base) /\
   eval_operand (Lit (n2w len)) s = SOME (n2w len) /\
   ptrDiscipline$op_taint tn (Lit (n2w len)) = {}` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >>
  `emitted_insts sm sh =
    [mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] []]` by
    metis_tac[emitted_insts_emit_void] >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var q; Lit (n2w len)] []) s =
     OK (mstore base (n2w len) s)` by
    (qspecl_then [`Var q`,`Lit (n2w len)`] mp_tac emitHelperPropsTheory.step_MSTORE >>
     simp[venomStateTheory.eval_operand_def] >>
     disch_then (qspecl_then [`n2w base`,`sm.cs_next_id`,`s`] mp_tac) >>
     simp[wordsTheory.w2n_n2w]) >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (qspec_then `ARB` mp_tac) >>
  simp[fragGasSeqPtrTheory.inst_seq_ptr_def] >> strip_tac >>
  `t = mstore base (n2w len) s with vs_inst_idx := LENGTH sh.cs_current_insts` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def] >>
     strip_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `ci_mono sm sh` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  drule emit_void_same_blocks >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  fs[exprLoweringPropsTheory.same_blocks_def, wordsTheory.w2n_n2w]
QED
