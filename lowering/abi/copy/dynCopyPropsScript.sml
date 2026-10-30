(* TOP-LEVEL: the compiler's identical-element dynamic-array store widens
   capacity while preserving every live typed element and operand frames. *)
Theory dynCopyProps
Ancestors
  typedCopyStateFrame dynCopyCode dynCopyExec dynCopyMemory dynCopyFrame abiBytestringCode memoryValueDefs
  memoryValueTyping memoryValueFrame valueLoadProps valueEncoding valueEncodingProps
  vyperValue vyperTyping compileEnv context exprLoweringProps
  fragBlockPath fragExec instIdxIndep venomState list words arithmetic

Theorem compile_copy_dynarray_execution:
  !cenv dst elem_ty capacity src cs ret cs' ss dst_addr src_addr n.
    compile_copy_dynarray_typed cenv dst elem_ty capacity src elem_ty cs = (ret,cs') /\
    n <= capacity /\ capacity < dimword(:256) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    mload (w2n src_addr) ss = n2w n /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 6) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (dyn_copy_result cs.cs_next_var (type_memory_bytes cenv elem_ty) dst_addr src_addr n ss)
Proof
  rpt strip_tac >> drule_all compile_copy_dynarray_code >> strip_tac >> simp[dyn_copy_execution]
QED

Theorem compile_copy_dynarray_path:
  !ctx func cenv elem_ty elem_tv src_capacity dst_capacity vs dst src cs ret cs' ss dst_addr src_addr.
    compile_copy_dynarray_typed cenv dst elem_ty dst_capacity src elem_ty cs = (ret,cs') /\
    type_memory_bytes cenv elem_ty = type_memory_size elem_tv /\
    src_capacity <= dst_capacity /\ dst_capacity < dimword(:256) /\
    lowered_value_rel (ArrayT elem_ty (Dynamic src_capacity))
      (ArrayTV elem_tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) src ss /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    w2n dst_addr + 32 < dimword(:256) /\ w2n src_addr + 32 < dimword(:256) /\
    LENGTH vs * type_memory_size elem_tv < dimword(:256) /\
    (LENGTH vs * type_memory_size elem_tv = 0 \/
      w2n src_addr + 32 + LENGTH vs * type_memory_size elem_tv <= w2n dst_addr \/
      w2n dst_addr <= w2n src_addr) /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 6) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\
      lowered_value_rel (ArrayT elem_ty (Dynamic dst_capacity))
        (ArrayTV elem_tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs)) dst out /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + 32 + dst_capacity * type_memory_size elem_tv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 6) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_copy_dynarray_code >> strip_tac >>
  `value_has_type (ArrayTV elem_tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) /\
   memory_value_rel (ArrayTV elem_tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs))
     (w2n src_addr) ss.vs_memory` by gvs[lowered_value_rel_def, is_word_type_def] >>
  `LENGTH vs <= src_capacity` by fs[value_has_type_def] >>
  `LENGTH vs <= dst_capacity` by decide_tac >>
  `value_has_type (ArrayTV elem_tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs))` by
    fs[value_has_type_def] >>
  `EVERY (val_wf elem_tv) vs` by
    (`val_wf (ArrayTV elem_tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs))` by
       (irule value_has_type_val_wf >> simp[]) >> fs[val_wf_def, elems_val_wf_every]) >>
  `mload (w2n src_addr) ss = n2w (LENGTH vs)` by
    (qpat_x_assum `memory_value_rel (ArrayTV _ _) _ _ _` mp_tac >>
     simp_tac bool_ss [Once memory_value_rel_def, mem_word_at_eq_mload] >> simp[]) >>
  `run_inst_seq (emitted_insts cs cs') ss =
    OK (dyn_copy_result cs.cs_next_var (type_memory_size elem_tv) dst_addr src_addr (LENGTH vs) ss)` by
    simp[dyn_copy_execution] >>
  `memory_value_rel (ArrayTV elem_tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs))
    (w2n dst_addr) (dyn_copy_result cs.cs_next_var (type_memory_size elem_tv)
      dst_addr src_addr (LENGTH vs) ss).vs_memory` by
    (mp_tac (Q.SPECL [`elem_tv`, `vs`, `src_capacity`, `dst_capacity`, `cs.cs_next_var`,
       `dst_addr`, `src_addr`, `ss`] dyn_copy_result_layout) >> simp[]) >>
  `EVERY (\name. dst <> Var name) (compiler_var_names cs.cs_next_var 6)` by fs[EVERY_CONJ] >>
  `!other_tv other_v offset.
    memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
    (offset + type_memory_size other_tv <= w2n dst_addr \/
      w2n dst_addr + 32 + dst_capacity * type_memory_size elem_tv <= offset) ==>
    memory_value_rel other_tv other_v offset (dyn_copy_result cs.cs_next_var
      (type_memory_size elem_tv) dst_addr src_addr (LENGTH vs) ss).vs_memory` by
    (rpt gen_tac >> DISCH_TAC >>
     mp_tac (Q.SPECL [`other_tv`, `other_v`, `offset`, `cs.cs_next_var`, `type_memory_size elem_tv`,
       `dst_addr`, `src_addr`, `LENGTH (vs:value list)`, `dst_capacity`, `ss`]
       dyn_copy_result_preserves_capacity) >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `dyn_copy_result cs.cs_next_var (type_memory_size elem_tv)
       dst_addr src_addr (LENGTH (vs:value list)) ss`]
    fragment_path_emitted) >> impl_tac >- simp[dyn_copy_straight] >> strip_tac >>
  qexists_tac `(dyn_copy_result cs.cs_next_var (type_memory_size elem_tv)
    dst_addr src_addr (LENGTH (vs:value list)) ss) with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[lowered_value_rel_def, is_word_type_def, eval_op_inst_idx, dyn_copy_result_operand_frame] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]
QED
