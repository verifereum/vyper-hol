(* Concrete mixed stack/memory staging for word-valued internal arguments. *)
Theory tupleAssignImmutableDeployIntStageWords
Ancestors
  exprSimMapKey exprSimConcatResult exprSimAlloc exprLoweringProps
  exprLowering emitHelperProps emitHelper freshWrites fragGasMode loweringHalt
  loweringStateRelDefs compileEnv venomState venomInst finite_map list rich_list

Theorem stage_word_shape[local]:
  !vals flags tys ce sa ops sb.
    LENGTH flags = LENGTH vals /\ LENGTH tys = LENGTH vals /\
    EVERY is_word_type tys /\
    EVERY (\vv. ?ty op. vv = StackValue ty op /\ is_word_type ty) vals /\
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    inst_extends sa sb /\ LENGTH ops = LENGTH vals /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >> simp[compile_stage_intcall_args_def, comp_return_def,
                inst_extends_refl, emitted_insts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `flags` >> Cases_on `tys` >> gvs[] >>
  Cases_on `h'`
  >- (gvs[compile_stage_intcall_args_def, unwrap_value_def,
          comp_bind_def, comp_return_def] >>
      pairarg_tac >> gvs[] >>
      first_x_assum (qspecl_then [`t`, `t'`, `ce`, `sa`, `rest`, `cs'`] mp_tac) >>
      simp[emitted_insts_def]) >>
  gvs[compile_stage_intcall_args_def, unwrap_value_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[comp_return_def] >>
  rename1 `inst_extends sa sb` >>
  first_x_assum (qspecl_then [`t`, `t'`, `ce`, `cs''`, `rest`, `sb`] mp_tac) >>
  simp[] >> strip_tac >>
  `cs''.cs_current_bb = sa.cs_current_bb /\
   cs''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs'' /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts sa cs'')` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, DROP_APPEND1, DROP_APPEND2, mk_inst_def,
         is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa cs'' ++ emitted_insts cs'' sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[GSYM emitted_insts_def] >>
  metis_tac[inst_extends_trans, inst_extends_def]
QED
