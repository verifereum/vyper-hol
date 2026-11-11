(* TOP-LEVEL: a uniform verified element-copy contract executes all live
   iterations while preserving the complete source, growing target prefix,
   disjoint typed memory and operands. Empty copies are included. *)
Theory typedDynLoopRun
Ancestors
  typedCopyStateFrame
  typedDynLoopStep typedDynLoopInvariant typedSArrayDynInvariant
  memoryValueDefs valueEncoding compileEnv fragBlockPath venomState venomInst list words arithmetic

Theorem array_copy_loop_run:
  !ctx func counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial start.
    (!j. j < copy_count ==> val_wf atv (at_index j)) /\
    (!j. j < copy_count ==> val_wf ftv (at_index j)) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) /\
    array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial 0 start /\
    (!i current.
      i < copy_count /\
      array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial i current ==>
      ?out. fragment_path ctx func current out /\ copy_state_frame current out /\
        out.vs_current_bb = cond_label /\ out.vs_inst_idx = 0 /\ ~out.vs_halted /\
        eval_operand (Var counter) out = SOME (n2w (SUC i)) /\
        memory_value_rel ftv (at_index i) (w2n dst_data + i * type_memory_size ftv) out.vs_memory /\
        (!other_tv other_v offset.
          memory_value_rel other_tv other_v offset current.vs_memory /\ val_wf other_tv other_v /\
          (offset + type_memory_size other_tv <= w2n dst_data + i * type_memory_size ftv \/
            w2n dst_data + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
          memory_value_rel other_tv other_v offset out.vs_memory) /\
        (!arg_op. EVERY (\name. arg_op <> Var name) modified_names ==>
          eval_operand arg_op out = eval_operand arg_op current)) ==>
    ?out. fragment_path ctx func start out /\
      array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial copy_count out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`copy_count`, `ctx`, `func`,
    `array_copy_loop_inv counter cond_label modified_names ftv atv at_index copy_count src_data dst_data initial`,
    `start`] fragment_path_loop) >> impl_tac
  >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      MAP_EVERY qx_gen_tac [`i`, `current`] >> strip_tac >>
      qpat_x_assum `!i current. _` (qspecl_then [`i`, `current`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
      `!j. j < i ==> val_wf ftv (at_index j)` by
        (rpt gen_tac >> DISCH_TAC >> `j < copy_count` by decide_tac >>
         qpat_x_assum `!j. j < copy_count ==> val_wf ftv _` (qspec_then `j` mp_tac) >> simp[]) >>
      mp_tac (Q.SPECL [`counter`, `cond_label`, `modified_names`, `ftv`, `atv`, `at_index`, `copy_count`,
        `src_data`, `dst_data`, `initial`, `i`, `current`, `out`] array_copy_loop_inv_step) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
      qexists_tac `out` >> simp[]) >> simp[]
QED
