(* TOP-LEVEL: connect the actual recursive child compiler and its typed
   copy contract to the parent's body. All child cuts and name ranges come
   from the real compiler result and containing function. *)
Theory typedDynChildContract
Ancestors
  typedCopyStateFrame
  typedCopyContract typedDynLoopCode typedDynLoopStructure typedDynLoopNames
  typedSArrayDynInvariant abiBytestringCode abiStaticLoopCode
  memoryValueDefs valueEncoding context compileEnv fragBlockPath fragExec
  venomState venomInst list words arithmetic

Theorem compile_copy_dynarray_contains_child:
  !cenv dst fty capacity src aty cs ret cs' after func.
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ fty = aty) /\
    compile_copy_dynarray_typed cenv dst fty capacity src aty cs = (ret,cs') /\ fn_has_code cs cs' func /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) ==>
    ret = () /\ cs' = dynarray_copy_finish cs after /\
    fn_has_code cs (dyn_copy_prefix_state cs dst src capacity) func /\
    fn_has_code (dyn_copy_prefix_state cs dst src capacity) (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    fn_has_code (dynarray_copy_start cenv dst fty capacity src aty cs) after func /\ fn_has_code after cs' func
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then (qx_choose_then `built_after` strip_assume_tac) compile_copy_dynarray_loop_contains >>
  `built_after = after` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = ((),built_after)` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem dynarray_copy_child_contract_path:
  !ctx func cenv dst fty capacity src aty cs after ftv atv ss v dst_addr src_addr.
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
      (Var (compiler_var_name cs.cs_next_var 10)) ftv atv
      (dynarray_copy_start cenv dst fty capacity src aty cs) after /\
    fn_has_code (dynarray_copy_start cenv dst fty capacity src aty cs) after func /\
    fn_has_code after (dynarray_copy_finish cs after) func /\
    ss.vs_current_bb = (dynarray_copy_start cenv dst fty capacity src aty cs).cs_current_bb /\
    ss.vs_inst_idx = LENGTH (dynarray_copy_start cenv dst fty capacity src aty cs).cs_current_insts /\ ~ss.vs_halted /\
    value_has_type atv v /\ memory_value_rel atv v (w2n src_addr) ss.vs_memory /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 11)) ss = SOME dst_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 10)) ss = SOME src_addr /\
    w2n src_addr + type_memory_size atv < dimword(:256) /\
    w2n dst_addr + type_memory_size ftv < dimword(:256) /\
    (w2n src_addr + type_memory_size atv <= w2n dst_addr \/
      w2n dst_addr + type_memory_size ftv <= w2n src_addr) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = after.cs_current_bb /\
      out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted /\
      memory_value_rel ftv v (w2n dst_addr) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/ w2n dst_addr + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names (cs.cs_next_var + 12) (after.cs_next_var - (cs.cs_next_var + 12))) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all dynarray_copy_child_continuation >> DISCH_TAC >>
  `EVERY (\name. Var (compiler_var_name cs.cs_next_var 11) <> Var name /\
      Var (compiler_var_name cs.cs_next_var 10) <> Var name)
    (compiler_var_names (dynarray_copy_start cenv dst fty capacity src aty cs).cs_next_var
      (after.cs_next_var - (dynarray_copy_start cenv dst fty capacity src aty cs).cs_next_var))` by
    (simp_tac bool_ss [EVERY_CONJ] >> conj_tac >> irule dynarray_copy_parent_names >> simp[]) >>
  qpat_x_assum `typed_copy_contract _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [typed_copy_contract_def]) >>
  disch_then (qspecl_then [`ss`, `v`, `dst_addr`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  simp_tac bool_ss [MULT_CLAUSES] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic-array child contract bridge: " ^ name)
  end) (DB.thms "typedDynChildContract")
