(* A typed return store followed by the internal RET, on the same path. *)
Theory internalReturnSuffixMem
Ancestors
  internalReturnStoreMem internalReturnPathMem exprSimBufferStore
  fragGasPathMem fragExec exprLoweringProps emitHelperProps emitHelper
  compileEnv loweringPosts exprSimMemDefs venomState venomInst
  list rich_list

Theorem internal_return_memory_suffix_path:
  compile_store_memory ce src dst ty ty sa = ((),sm) /\
  emit_inst RET [Var rpc] [] sm = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  w2n d + type_memory_size tv + 64 < dimword (:256) /\
  eval_operand dst s = SOME d /\ lookup_var rpc s = SOME pc /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  not_fresh_at sa rpc /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0
        (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t) /\
      val_in_memory tv v (w2n d) t.vs_memory
Proof
  strip_tac >> drule buffer_store_memory_shape >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_emit_inst] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all internal_return_store_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `lookup_var rpc (t with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME pc` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `gas_path_mem ctx func
     (t with vs_inst_idx := LENGTH sm.cs_current_insts) 0
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
       (t with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule emit_internal_ret_path_mem >> simp[] >>
     qexistsl_tac [`[]`, `pc`, `rpc`, `sm`, `sb`] >>
     simp[eval_operands_def, same_blocks_def] >>
     gvs[same_blocks_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sm.cs_current_insts` >> simp[] >>
  drule_all gas_path_mem_then >> gvs[]
QED
