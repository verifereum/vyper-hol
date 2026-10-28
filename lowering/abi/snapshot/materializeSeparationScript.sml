(* TOP-LEVEL: the actual materialization instruction owns a buffer disjoint
   from live source pointers, including on loop re-entry. Fixed source
   locations use the static-memory bound at that buffer's base.
   Helpers recover instruction membership from the emitted code. *)
Theory materializeSeparation
Ancestors
  sourceMemorySeparation sourceMemoryFrames materializeValuePath
  memoryValueSnapshot bytesSnapshotCode abiBytestringCode abiAllocationFrame abiFieldOperands abiStaticLoopCode
  vyperCompiler compileEnv context fragExec exprLoweringProps
  venomExecProps venomMemDefs venomState venomInst list rich_list words arithmetic

Theorem fn_has_code_current_instruction:
  !cs cs' func inst.
    fn_has_code cs cs' func /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    MEM inst (emitted_insts cs cs') ==>
    MEM inst (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  rename1 `lookup_block cs'.cs_current_bb func.fn_blocks = SOME bb` >>
  `MEM bb func.fn_blocks` by (drule lookup_block_MEM >> simp[]) >>
  `MEM inst bb.bb_instructions` by
    (qpat_x_assum `isPREFIX _ bb.bb_instructions` mp_tac >> simp[IS_PREFIX_APPEND] >>
     strip_tac >> simp[MEM_APPEND]) >>
  CCONTR_TAC >>
  `EVERY (\i. i <> inst) (fn_insts_blocks func.fn_blocks)` by fs[EVERY_MEM, fn_insts_def] >>
  qpat_x_assum `EVERY _ (fn_insts_blocks _)`
    (mp_tac o REWRITE_RULE [EVERY_fn_insts_blocks, EVERY_MEM]) >>
  disch_then (qspec_then `bb` mp_tac) >> simp[]
QED

Theorem compile_materialize_allocation_member:
  !cenv ty src cs op cs' func.
    ~is_word_type ty /\ compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    fn_has_code cs cs' func ==>
    MEM (mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
      [compiler_var_name cs.cs_next_var 0]) (fn_insts func)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type ty`
  >- (drule_all compile_materialize_bytes_code >> strip_tac >>
      irule fn_has_code_current_instruction >> qexistsl_tac [`cs`, `cs'`] >>
      simp[bytes_snapshot_insts_def, compiler_var_names_EL, compiler_var_name_def]) >>
  drule_all compile_materialize_aggregate_code >> strip_tac >>
  irule fn_has_code_current_instruction >> qexistsl_tac [`cs`, `cs'`] >>
  simp[compiler_var_name_def]
QED

Theorem compile_materialize_source_separated:
  !func cenv scopes ss ty src cs op cs'.
    alloca_inv ss /\ fn_inst_ids_distinct func /\ local_ptrs_rel func cenv scopes ss /\
    ~is_word_type ty /\ compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    fn_has_code cs cs' func /\ ss.vs_alloca_next < dimword(:256) /\
    abi_alloca_request_ok cs.cs_next_id (type_memory_bytes cenv ty) ss /\
    (!name entry p region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
      abi_operand_before cs.cs_next_var (Var p)) /\
    (!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr cs.cs_next_id ss)) ==>
    source_memory_separated cenv scopes ss (w2n (memory_snapshot_addr cs.cs_next_id ss))
      (type_memory_bytes cenv ty)
Proof
  rpt gen_tac >> strip_tac >>
  `not_local_ptr cenv scopes (compiler_var_name cs.cs_next_var 0)` by
    (irule source_pointer_operands_not_local >> qexists_tac `cs.cs_next_var` >>
     rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  drule_all compile_materialize_allocation_member >> DISCH_TAC >>
  Cases_on `FLOOKUP ss.vs_allocas cs.cs_next_id`
  >- (`w2n (memory_snapshot_addr cs.cs_next_id ss) = ss.vs_alloca_next` by
        (asm_simp_tac (srw_ss()) [memory_snapshot_addr_def, w2n_n2w] >>
         irule LESS_MOD >> first_assum MATCH_ACCEPT_TAC) >>
      `!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
        offset + type_memory_size entry.type <= ss.vs_alloca_next` by
        (qpat_x_assum `!name entry offset region_size. _ ==> offset + _ <= _` mp_tac >>
         asm_simp_tac bool_ss []) >>
      mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `ss`, `cs.cs_next_id`, `type_memory_bytes cenv ty`]
        source_memory_separated_fresh_snapshot) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  rename1 `FLOOKUP ss.vs_allocas cs.cs_next_id = SOME allocation` >> Cases_on `allocation` >>
  rename1 `FLOOKUP ss.vs_allocas cs.cs_next_id = SOME (region_base,recorded_size)` >>
  `region_base + recorded_size <= ss.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `region_base < dimword(:256)` by decide_tac >>
  `w2n (memory_snapshot_addr cs.cs_next_id ss) = region_base` by
    (asm_simp_tac (srw_ss()) [memory_snapshot_addr_def, w2n_n2w] >>
     irule LESS_MOD >> first_assum MATCH_ACCEPT_TAC) >>
  `!name entry offset region_size. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
    offset + type_memory_size entry.type <= region_base` by
    (qpat_x_assum `!name entry offset region_size. _ ==> offset + _ <= _` mp_tac >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`func`, `cenv`, `scopes`, `ss`,
    `mk_inst cs.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
      [compiler_var_name cs.cs_next_var 0]`, `compiler_var_name cs.cs_next_var 0`,
    `region_base`, `recorded_size`, `type_memory_bytes cenv ty`]
    source_memory_separated_cached_snapshot) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac (srw_ss()) [mk_inst_def]]) >>
  simp[mk_inst_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed materialization allocation separation: " ^ name)
  end) (DB.thms "materializeSeparation")
