(* TOP-LEVEL: saving the next evaluated Log argument preserves all earlier
   saved values. Impure suffixes trigger actual snapshots of nonword values;
   these establish allocation ownership and preserve the allocator invariant.
   The general frame accepts reused SSA outputs; freshness derives the
   required operand bounds for the fresh-state corollary. *)
Theory logArgumentSnapshotFrame
Ancestors
  materializeValuePath memorySnapshotFrame memoryValueSnapshotSource memoryValueTyping
  typedLogArgs typedLogArgsFrames typedSArrayDynInvariant abiLogTopicsReady
  allocationGrowth abiAllocationFrame abiAllocatedWindows abiFieldOperands abiStaticLoopCode abiStateFrame
  valueLoadProps typeLayoutProps typedCopyProducer compileVyper vyperTypeContract vyperContext
  stmtLowering context compileEnv exprLoweringProps emitHelperProps vyperExprEffects
  fragExec fragBlockPath instIdxIndep venomState list pair words arithmetic

Theorem evaluated_operand_before:
  !cs ss arg_op word.
    fresh_vars_wrt cs ss /\ eval_operand arg_op ss = SOME word ==>
    abi_operand_before cs.cs_next_var arg_op
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [abi_operand_before_def, compiler_var_name_def] >>
  qx_gen_tac `n` >> DISCH_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`cs`, `ss`, `arg_op`, `word`, `STRING #"%" (toString (n:num))`, `n`]
    fresh_vars_wrt_eval_operand) >> fs[]
QED

Theorem log_args_rel_before:
  !args atvs values cs ss.
    log_args_rel args atvs values ss /\ fresh_vars_wrt cs ss ==>
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args
Proof
  Induct_on `args` >- simp[] >>
  MAP_EVERY qx_gen_tac [`arg`, `atvs`, `values`, `cs`, `ss`] >>
  Cases_on `arg` >> Cases_on `atvs` >> Cases_on `values` >>
  simp_tac (srw_ss()) [log_args_rel_def] >> strip_tac >>
  rename1 `lowered_value_rel ty tv v src ss` >>
  `?word. eval_operand src ss = SOME word` by fs[lowered_value_rel_def] >>
  `abi_operand_before cs.cs_next_var src` by (drule_all evaluated_operand_before >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem checked_compile_log_save_arg_frame:
  !tops dep layouts addr art ctx func cenv ty tv v src suffix cs op cs' ss args atvs values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src suffix cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\ abi_operand_before cs.cs_next_var src /\
    alloca_inv ss /\ log_args_rel args atvs values ss /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
      abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
      log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      log_args_rel args atvs values out /\ (fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out) /\ alloca_inv out /\
      array_copy_frame tv 1 (w2n (memory_snapshot_addr cs.cs_next_id ss)) ss.vs_memory out.vs_memory /\
      abi_state_frame ss out /\ allocation_growth ss out /\
      (is_word_type ty \/ EVERY pure_expr suffix ==> out = ss) /\ cs.cs_next_var <= cs'.cs_next_var /\
      abi_operand_before cs'.cs_next_var op /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
        eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
        abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\
        out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_allocas /\
        out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_alloca_next /\
        ss.vs_alloca_next <= out.vs_alloca_next /\
        out.vs_alloca_next <= ss.vs_alloca_next + type_memory_size tv)
Proof
  rpt gen_tac >> strip_tac >>
  `?src_addr. eval_operand src ss = SOME src_addr` by fs[lowered_value_rel_def] >>
  Cases_on `is_word_type ty \/ EVERY pure_expr suffix`
  >- (`~(~is_word_type ty /\ ~EVERY pure_expr suffix)` by fs[] >>
      qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [compile_log_save_arg_def, comp_return_def, PAIR_EQ] >> strip_tac >>
      asm_simp_tac bool_ss [fragment_path_refl, abi_state_frame_refl, LESS_EQ_REFL] >> gvs[]) >>
  `~is_word_type ty /\ ~EVERY pure_expr suffix` by fs[] >>
  `ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
    abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
    log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `type_memory_size tv < dimword(:256)` by decide_tac >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all type_memory_bytes_evaluated >> simp[]) >>
  qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_log_save_arg_def] >> strip_tac >>
  `EVERY (\name. src <> Var name)
    (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 5 else 1))` by
    (irule abi_operand_before_names >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `src`,
    `cs`, `op`, `cs'`, `ss`, `src_addr`] compile_materialize_value_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all compile_materialize_value_vars >> strip_tac >>
  `fresh_vars_wrt cs ss ==> fresh_vars_wrt cs' out` by
    (DISCH_TAC >> asm_simp_tac bool_ss [fresh_vars_wrt_def] >>
     mp_tac (Q.SPECL [`ty`, `cs.cs_next_id`, `cs`, `cs'`, `type_memory_size tv`, `src_addr`, `ss`]
       materialized_state_fresh) >> impl_tac >- simp[] >> simp[fresh_vars_wrt_def]) >>
  drule_all materialized_allocation_resources >> strip_tac >>
  drule_all allocation_growth_snapshot_fields >> DISCH_TAC >>
  `log_args_avoid args (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 5 else 1))` by
    (irule log_args_before_names >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  mp_tac (Q.SPECL [`args`, `atvs`, `values`, `ss`, `out`, `tv`, `1`,
    `w2n (memory_snapshot_addr cs.cs_next_id ss)`,
    `compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 5 else 1)`] log_args_frame) >>
  impl_tac >- simp[] >> strip_tac >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`,
       `if is_bytestring_type ty then 5 else 1`, `ss`, `out`] abi_operand_before_frame) >>
     impl_tac >- simp[] >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem checked_compile_log_save_arg_fresh:
  !tops dep layouts addr art ctx func cenv ty tv v src suffix cs op cs' ss args atvs values.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src suffix cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\
    fresh_vars_wrt cs ss /\ alloca_inv ss /\ log_args_rel args atvs values ss /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      ss.vs_alloca_next + type_memory_size tv < dimword(:256) /\
      abi_alloca_request_ok cs.cs_next_id (type_memory_size tv) ss /\
      log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      log_args_rel args atvs values out /\ fresh_vars_wrt cs' out /\ alloca_inv out /\
      array_copy_frame tv 1 (w2n (memory_snapshot_addr cs.cs_next_id ss)) ss.vs_memory out.vs_memory /\
      abi_state_frame ss out /\ allocation_growth ss out /\
      (is_word_type ty \/ EVERY pure_expr suffix ==> out = ss) /\ cs.cs_next_var <= cs'.cs_next_var /\
      abi_operand_before cs'.cs_next_var op /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
        eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
        abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size tv) /\
        out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_allocas /\
        out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_alloca_next /\
        ss.vs_alloca_next <= out.vs_alloca_next /\
        out.vs_alloca_next <= ss.vs_alloca_next + type_memory_size tv)
Proof
  rpt gen_tac >> strip_tac >>
  `?src_addr. eval_operand src ss = SOME src_addr` by fs[lowered_value_rel_def] >>
  `abi_operand_before cs.cs_next_var src` by (drule_all evaluated_operand_before >> simp[]) >>
  `EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args` by
    (drule_all log_args_rel_before >> simp[]) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) checked_compile_log_save_arg_frame >>
  goal_assum drule >> simp[] >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed Log argument snapshot lifetime: " ^ name)
  end) (DB.thms "logArgumentSnapshotFrame")
