Theory bodyPtrStructLitOwnershipFreshness
Ancestors bodyPtrStructLitOwnershipSteps bodyPtrStructLitCompilerOwnership
  loweringShapeDefs loweringShapeRules compileEnv loweringStateRelDefs emitHelper emitHelperProps
  venomInst list

(* Ownership composition needs output freshness, not the operand restrictions
   and return-PC shape imposed by shape_base_state. *)
Definition fresh_outputs_def:
  fresh_outputs st <=>
    !i x. MEM i (state_insts st) /\ MEM x i.inst_outputs ==>
          not_fresh_at st x
End

Theorem shape_base_fresh_outputs:
  shape_base_state st ==> fresh_outputs st
Proof rw[shape_base_state_def, fresh_outputs_def] >> metis_tac[]
QED

Theorem alloc_run_emit_op_fresh:
  alloc_run fresh_outputs (emit_op opc ops) (\v st. fresh_outputs st)
Proof
  rw[alloc_run_def]
  >- (drule emit_op_facts >> strip_tac >>
      fs[alloc_writers_unique_def, fresh_outputs_def] >>
      rw[] >> gvs[mk_inst_def] >> metis_tac[])
  >- (drule emit_op_facts >> strip_tac >> rw[alloc_frame_def]
      >- (irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
      pure_rewrite_tac[alloc_owned_def] >>
      irule emit_op_preserves_nonowned >> goal_assum (drule_at Any) >>
      fs[fresh_outputs_def, alloc_owned_def] >> metis_tac[]) >>
  drule emit_op_facts >> strip_tac >>
  rw[fresh_outputs_def] >> gvs[mk_inst_def] >>
  fs[fresh_outputs_def] >>
  irule not_fresh_at_mono >> qexists `st` >> simp[] >> metis_tac[]
QED

Theorem fresh_outputs_same_insts:
  fresh_outputs st /\ state_insts st' = state_insts st /\
  st.cs_next_var <= st'.cs_next_var ==> fresh_outputs st'
Proof
  rw[fresh_outputs_def] >> irule not_fresh_at_mono >>
  qexists `st` >> simp[] >> metis_tac[]
QED

Theorem alloc_run_emit_void_fresh:
  alloc_run fresh_outputs (emit_void opc ops) (\v st. fresh_outputs st)
Proof
  rw[alloc_run_def]
  >- (mp_tac (Q.INST [`opc` |-> `opc`, `ops` |-> `ops`] alloc_run_emit_void) >>
      simp[alloc_run_def] >> disch_then drule_all >> simp[])
  >- (mp_tac (Q.INST [`opc` |-> `opc`, `ops` |-> `ops`] alloc_run_emit_void) >>
      simp[alloc_run_def] >> disch_then drule_all >> simp[]) >>
  gvs[emit_void_eq, fresh_outputs_def, state_insts_def, all_blocks_def,
      mk_inst_def, not_fresh_at_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem alloc_run_emit_inst_fresh:
  opc <> ALLOCA ==>
  alloc_run (\st. fresh_outputs st /\
      EVERY (\x. not_fresh_at st x /\ ~alloc_owned st x) outs)
    (emit_inst opc ops outs) (\u st. fresh_outputs st)
Proof
  strip_tac >> rw[alloc_run_def]
  >- (irule alloc_writers_unique_emit_inst >>
      goal_assum (drule_at Any) >> fs[alloc_owned_def, EVERY_MEM])
  >- (drule_all emit_inst_nonalloc_owned >> strip_tac >>
      gvs[alloc_frame_def, alloc_owned_def, emit_inst_eq, not_fresh_at_def]) >>
  gvs[emit_inst_eq, fresh_outputs_def, state_insts_def, all_blocks_def,
      mk_inst_def, not_fresh_at_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem alloc_run_fresh_var_fresh:
  alloc_run fresh_outputs fresh_var
    (\x st. fresh_outputs st /\ not_fresh_at st x /\ ~alloc_owned st x)
Proof
  rw[alloc_run_def]
  >- (mp_tac alloc_run_fresh_var >> simp[alloc_run_def] >>
      disch_then drule_all >> simp[])
  >- (mp_tac alloc_run_fresh_var >> simp[alloc_run_def] >>
      disch_then drule_all >> simp[])
  >- (gvs[fresh_var_def] >> irule fresh_outputs_same_insts >>
      qexists `st` >> simp[state_insts_def, all_blocks_def])
  >- gvs[fresh_var_def, not_fresh_at_def] >>
  gvs[fresh_var_def, alloc_owned_def, opaque_out_def,
      state_insts_def, all_blocks_def, fresh_outputs_def, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem alloc_run_fresh_label_fresh:
  alloc_run fresh_outputs (fresh_label suffix) (\v st. fresh_outputs st)
Proof
  rw[alloc_run_def]
  >- (mp_tac (Q.INST [`suffix` |-> `suffix`] alloc_run_fresh_label) >>
      simp[alloc_run_def] >> disch_then drule_all >> simp[])
  >- (mp_tac (Q.INST [`suffix` |-> `suffix`] alloc_run_fresh_label) >>
      simp[alloc_run_def] >> disch_then drule_all >> simp[]) >>
  gvs[fresh_label_def] >> irule fresh_outputs_same_insts >>
  qexists `st` >> simp[state_insts_def, all_blocks_def]
QED

Theorem alloc_run_new_block_fresh:
  alloc_run fresh_outputs (new_block lbl) (\v st. fresh_outputs st)
Proof
  rw[alloc_run_def]
  >- (mp_tac (Q.INST [`lbl` |-> `lbl`] alloc_run_new_block) >>
      simp[alloc_run_def] >> disch_then drule_all >> simp[])
  >- (mp_tac (Q.INST [`lbl` |-> `lbl`] alloc_run_new_block) >>
      simp[alloc_run_def] >> disch_then drule_all >> simp[]) >>
  gvs[new_block_def, fresh_outputs_def, state_insts_def, all_blocks_def,
      MAP_APPEND, FLAT_APPEND, APPEND_ASSOC, not_fresh_at_def] >> metis_tac[]
QED

Theorem alloc_run_reserved_counter_probe:
  alloc_run fresh_outputs
    (do x <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [x];
        emit_inst ASSIGN [Lit 1w] [x];
        return x od)
    (\x st. fresh_outputs st /\ not_fresh_at st x /\ ~alloc_owned st x)
Proof
  rw[alloc_run_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  namedCases_on `fresh_var st` ["counter s0"] >>
  namedCases_on `emit_inst ASSIGN [Lit 0w] [counter] s0` ["u s1"] >>
  namedCases_on `emit_inst ASSIGN [Lit 1w] [counter] s1` ["w s2"] >> gvs[] >>
  mp_tac alloc_run_fresh_var_fresh >> simp[alloc_run_def] >>
  disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit 0w]`, `outs` |-> `[counter]`]
    alloc_run_emit_inst_fresh) >> simp[alloc_run_def] >>
  disch_then drule_all >> strip_tac >>
  `not_fresh_at s1 counter /\ ~alloc_owned s1 counter` by
    (fs[alloc_frame_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit 1w]`, `outs` |-> `[counter]`]
    alloc_run_emit_inst_fresh) >> simp[alloc_run_def] >>
  disch_then drule_all >> strip_tac >>
  gvs[] >> metis_tac[alloc_frame_trans, alloc_frame_def]
QED

Theorem alloc_run_fresh_vars_fresh:
  !n. alloc_run fresh_outputs (fresh_vars n)
    (\xs st. fresh_outputs st /\
      EVERY (\x. not_fresh_at st x /\ ~alloc_owned st x) xs)
Proof
  Induct
  >- simp[fresh_vars_def, comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rw[alloc_run_def, fresh_vars_def, comp_bind_def, comp_return_def] >>
  namedCases_on `fresh_var st` ["x s0"] >>
  namedCases_on `fresh_vars n s0` ["xs s1"] >> gvs[] >>
  mp_tac alloc_run_fresh_var_fresh >> simp[alloc_run_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `alloc_run _ (fresh_vars n) _`
    (mp_tac o SRULE [alloc_run_def]) >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  metis_tac[alloc_frame_trans, alloc_frame_def]
QED

Theorem alloc_run_emit_multi_op_fresh:
  opc <> ALLOCA ==>
  alloc_run fresh_outputs (emit_multi_op opc ops n) (\v st. fresh_outputs st)
Proof
  strip_tac >> simp[emit_multi_op_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\xs st. fresh_outputs st /\
    EVERY (\x. not_fresh_at st x /\ ~alloc_owned st x) xs` >>
  reverse conj_tac >- simp[alloc_run_fresh_vars_fresh] >>
  qx_gen_tac `xs` >> simp[] >> irule alloc_run_bind >>
  qexists `\u st. fresh_outputs st` >> reverse conj_tac
  >- simp[alloc_run_emit_inst_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
