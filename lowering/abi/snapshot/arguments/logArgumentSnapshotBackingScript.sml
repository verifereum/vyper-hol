(* TOP-LEVEL: the actual snapshot allocation is outside the remaining
   compiler profile and supplies a private backing window for the new
   argument. Instruction identity and allocation provenance discharge
   separation, including cached slots. *)
Theory logArgumentSnapshotBacking
Ancestors
  logArgumentBacking sourceAllocationPrivacy sourceMemorySeparation materializeSeparation
  memoryValueSnapshot bytesSnapshotCode abiBytestringCode abiStaticLoopCode abiFieldOperands abiAllocatedWindows allocationGrowth
  compileAllocaIdentity compileAllocaProvenance
  exprLowering stmtLowering context compileEnv localPtrsProps
  fragExec venomInst venomState list pair words

Theorem compile_log_save_arg_allocation_current:
  !cenv ty src suffix cs saved cut.
    ~is_word_type ty /\ ~EVERY pure_expr suffix /\
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) ==>
    MEM (mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
      [compiler_var_name cs.cs_next_var 0]) cut.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `compile_materialize_vv cenv ty (StackValue ty src) cs = (saved,cut)` by
    (qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_log_save_arg_def]) >>
  Cases_on `is_bytestring_type ty`
  >- (drule_all compile_materialize_bytes_code >> strip_tac >>
      simp[bytes_snapshot_insts_def, compiler_var_names_EL, compiler_var_name_def]) >>
  drule_all compile_materialize_aggregate_code >> strip_tac >> simp[compiler_var_name_def]
QED

Theorem compile_log_save_arg_outside_suffix:
  !cenv ty src suffix cs saved cut final_cut func.
    ~is_word_type ty /\ ~EVERY pure_expr suffix /\
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    fn_has_code cs cut func /\ fn_inst_ids_distinct func /\
    cs_extends cut final_cut /\ fn_has_code cut final_cut func ==>
    ~MEM cs.cs_next_id (compiler_alloca_ids cut final_cut)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_log_save_arg_allocation_current >> DISCH_TAC >>
  qabbrev_tac `inst = mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
    [compiler_var_name cs.cs_next_var 0]` >>
  `MEM inst cut.cs_current_insts` by simp[Abbr`inst`] >>
  `MEM inst (fn_insts func)` by
    (qspecl_then [`cs`, `cut`, `func`, `inst`] mp_tac fn_has_code_current_member >> simp[]) >>
  `compiler_instruction_member cut inst` by simp[compiler_instruction_member_def] >>
  qspecl_then [`cut`, `final_cut`, `func`, `inst`] mp_tac compiler_old_instruction_outside_alloca_profile >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[Abbr`inst`, mk_inst_def]
QED

Theorem compile_log_save_arg_private_window:
  !func cenv scopes ty src suffix cs saved cut final_cut out ids offset byte_count.
    ~is_word_type ty /\ ~EVERY pure_expr suffix /\
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    fn_has_code cs cut func /\ fn_inst_ids_distinct func /\
    cs_extends cut final_cut /\ fn_has_code cut final_cut func /\
    alloca_inv out /\ local_ptrs_rel func cenv scopes out /\
    source_alloca_floor cenv scopes ids out /\ MEM cs.cs_next_id ids /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    abi_allocated_window out cs.cs_next_id offset byte_count ==>
    private_value_window cenv scopes out (compiler_alloca_ids cut final_cut) offset byte_count
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_log_save_arg_outside_suffix >> DISCH_TAC >>
  drule_all compile_log_save_arg_allocation_current >> DISCH_TAC >>
  qabbrev_tac `inst = mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
    [compiler_var_name cs.cs_next_var 0]` >>
  `MEM inst cut.cs_current_insts` by simp[Abbr`inst`] >>
  `MEM inst (fn_insts func)` by
    (qspecl_then [`cs`, `cut`, `func`, `inst`] mp_tac fn_has_code_current_member >> simp[]) >>
  `not_local_ptr cenv scopes (compiler_var_name cs.cs_next_var 0)` by
    (irule source_pointer_operands_not_local >> qexists_tac `cs.cs_next_var` >>
     rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  qspecl_then [`func`, `cenv`, `scopes`, `ids`, `out`, `out`, `inst`, `compiler_var_name cs.cs_next_var 0`,
    `offset`, `byte_count`] mp_tac source_owned_allocation_private >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    simp[Abbr`inst`, allocation_growth_refl, mk_inst_def] >> first_assum MATCH_ACCEPT_TAC]) >>
  DISCH_TAC >> simp_tac bool_ss [private_value_window_def] >> qexists_tac `cs.cs_next_id` >> simp[]
QED

Theorem compile_log_save_arg_value_backing:
  !func cenv scopes ty src suffix cs saved cut final_cut loaded out ids byte_count.
    compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\
    fn_has_code cs cut func /\ fn_inst_ids_distinct func /\
    cs_extends cut final_cut /\ fn_has_code cut final_cut func /\
    alloca_inv out /\ local_ptrs_rel func cenv scopes out /\
    source_alloca_floor cenv scopes ids out /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    (is_word_type ty \/ EVERY pure_expr suffix ==> out = loaded) /\
    (~is_word_type ty /\ ~EVERY pure_expr suffix ==>
      MEM cs.cs_next_id ids /\ ?ptr_addr. eval_operand saved out = SOME ptr_addr /\
        abi_allocated_window out cs.cs_next_id (w2n ptr_addr) byte_count) /\
    (EVERY pure_expr suffix ==> !src_addr. eval_operand src loaded = SOME src_addr ==>
      argument_value_window cenv scopes loaded (compiler_alloca_ids cut final_cut) T (w2n src_addr) byte_count) ==>
    ~is_word_type ty ==> !saved_addr. eval_operand saved out = SOME saved_addr ==>
      argument_value_window cenv scopes out (compiler_alloca_ids cut final_cut)
        (EVERY pure_expr suffix) (w2n saved_addr) byte_count
Proof
  rpt gen_tac >> strip_tac >> DISCH_TAC >> qx_gen_tac `saved_addr` >> DISCH_TAC >>
  Cases_on `EVERY pure_expr suffix`
  >- (`out = loaded` by fs[] >>
      `saved = src` by
        (qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
         asm_simp_tac (srw_ss()) [compile_log_save_arg_def, comp_return_def]) >>
      qpat_x_assum `EVERY pure_expr suffix ==> _` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_then (qspec_then `saved_addr` mp_tac) >> gvs[]) >>
  `MEM cs.cs_next_id ids` by
    (qpat_x_assum `~is_word_type ty /\ ~EVERY pure_expr suffix ==> _` mp_tac >>
     impl_tac >- fs[] >> strip_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_allocated_window out cs.cs_next_id (w2n saved_addr) byte_count` by
    (qpat_x_assum `~is_word_type ty /\ ~EVERY pure_expr suffix ==> _` mp_tac >>
     asm_simp_tac bool_ss [] >> strip_tac >> gvs[]) >>
  `private_value_window cenv scopes out (compiler_alloca_ids cut final_cut) (w2n saved_addr) byte_count` by
    (qspecl_then [`func`, `cenv`, `scopes`, `ty`, `src`, `suffix`, `cs`, `saved`, `cut`, `final_cut`, `out`,
       `ids`, `w2n saved_addr`, `byte_count`] mp_tac compile_log_save_arg_private_window >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  simp[argument_value_window_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Log snapshot backing: " ^ name)
  end) (DB.thms "logArgumentSnapshotBacking")
