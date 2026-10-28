(* TOP-LEVEL: checked recursive Log data packing preserves the complete
   source state and live locals when its actual destination is private.
   Arguments retain their typed values while the packed tuple is produced. *)
Theory abiLogPackingState
Ancestors
  abiLogPackingBoundary abiLogPackingReady typedLogStoreCode typedLogSplitComplete
  typedCopyStateFrame typedLogArgs typedCopyContract typedSArrayDynInvariant
  sourceMemoryFrames allocationGrowth abiFieldOperands abiStateFrame
  memoryValueDefs valueEncoding context stmtLowering compileEnv compileVyper
  vyperTypeContract vyperTypeSystem vyperTypeInvariants vyperContext vyperState
  fragExec fragBlockPath venomState list words arithmetic

Theorem checked_log_packing_source_state:
  !tops dep layouts addr art ctx func cenv cx es flags fts args ftvs atvs values
    buf cs ret packed_cut capacity abi_buf encode_cut ss root_addr.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    compile_log_store_data cenv (SND (split_log_ops args flags))
      (log_non_indexed_types flags fts) buf 0 cs = (ret,packed_cut) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\
    fn_has_code cs packed_cut func /\ fn_has_code packed_cut encode_cut func /\
    state_well_typed es /\ state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    source_memory_separated cenv es.scopes ss (w2n root_addr)
      (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    log_args_rel args atvs values ss /\
    log_args_safe args atvs ss (w2n root_addr) (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    log_args_avoid args (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var)) /\
    w2n root_addr + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) /\
    abi_operand_before cs.cs_next_var buf /\ eval_operand buf ss = SOME root_addr /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ allocation_growth ss out /\
      out.vs_current_bb = packed_cut.cs_current_bb /\ out.vs_inst_idx = LENGTH packed_cut.cs_current_insts /\ ~out.vs_halted /\
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      values_have_types (select_log_args F flags ftvs) (select_log_args F flags values) /\
      memory_tuple_rel (select_log_args F flags ftvs) (select_log_args F flags values) (w2n root_addr) out.vs_memory /\
      log_args_rel args atvs values out /\
      log_args_safe args atvs out (w2n root_addr) (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
      array_copy_frame (TupleTV (select_log_args F flags ftvs)) 1 (w2n root_addr) ss.vs_memory out.vs_memory /\
      cs.cs_next_var <= packed_cut.cs_next_var /\
      (!arg. abi_operand_before cs.cs_next_var arg ==> eval_operand arg out = eval_operand arg ss)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\name. buf <> Var name)
    (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var))` by
    (irule abi_operand_before_names >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `flags`, `fts`, `args`, `ftvs`, `atvs`, `buf`, `0`, `cs`, `ret`, `packed_cut`,
    `capacity`, `abi_buf`, `encode_cut`] checked_compile_split_log_data_allocation_boundary) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`ss`, `values`, `root_addr`] mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  RULE_ASSUM_TAC (REWRITE_RULE [ADD_CLAUSES]) >>
  drule copy_state_frame_external >> DISCH_TAC >> drule allocation_growth_copy_frame >> DISCH_TAC >>
  drule compile_log_store_data_next_var >> DISCH_TAC >>
  `!arg. abi_operand_before cs.cs_next_var arg ==> eval_operand arg out = eval_operand arg ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`,
      `packed_cut.cs_next_var - cs.cs_next_var`, `ss`, `out`] abi_operand_before_frame) >> simp[]) >>
  `source_memory_separated cenv es.scopes ss (w2n root_addr)
    (1 * type_memory_size (TupleTV (select_log_args F flags ftvs)))` by simp[] >>
  drule_all source_relations_copy_frame >> strip_tac >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked Log packing source state: " ^ name)
  end) (DB.thms "abiLogPackingState")
