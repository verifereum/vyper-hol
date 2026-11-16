(* Immutable For entry resources, retaining constructor and runtime cases. *)
Theory bodyFullForArrayImmStart
Ancestors
  bodyFullForArrayImmutable bodyFullForArrayFixedStart
  exprSimAggregateLayout ctorDeployDeadSectionFrame
  exprLoweringProps valueEncoding words arithmetic list
  immutableRegionLoadPtr instSeqPtrLo instSeqComposePtr
  ptrDiscipline venomState venomInst memSafeRun storageCopyBodyPtr
  venomExecSemantics context immutableWordExecution fragGasOriginPtrLoop

(* Full typed capacity is word-aligned; this is not a footprint argument. *)
Theorem for_immutable_copy_extent[local]:
  32 * ((type_memory_size tv + 31) DIV 32) = type_memory_size tv
Proof
  qspec_then `tv` assume_tac (CONJUNCT1 type_memory_size_aligned) >>
  intLib.COOPER_TAC
QED

Theorem for_array_immutable_source_extent_full:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_holds cenv cx ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (dst,sz) ==>
  (cenv.ce_is_ctor ==>
    w2n a + 32 * ((type_memory_size tv + 31) DIV 32) <= s.vs_alloca_next /\
    regions_disjoint (w2n a) (type_memory_size tv) dst sz) /\
  (~cenv.ce_is_ctor ==>
    w2n a + 32 * ((type_memory_size tv + 31) DIV 32) <= LENGTH s.vs_data_section)
Proof
  strip_tac >> rewrite_tac[for_immutable_copy_extent] >> conj_tac
  >- (strip_tac >> conj_tac
      >- (drule_all exprSimMemUnwrapTheory.ctor_immutable_frontier >> simp[])
      >> drule_all exprSimCopyTheory.immutable_holds_alloca_disjoint >> simp[]) >>
  strip_tac >> drule_all bodyImmutableUnwrapMemoryTheory.runtime_immutable_data_section >> simp[]
QED

(* Constructor header bytes are live, even though the immutable region is
   below the allocation frontier and deliberately has no pointer provenance. *)
Theorem for_array_immutable_header_clean_full:
  struct_args_unique (cx_tops cx) /\
  cx_tops cx = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env (cx_tops cx)) ty = SOME (ArrayTV tv (Dynamic n)) /\
  off = compute_immutables_len
    (get_struct_fields (make_struct_fields_map (cx_tops cx))) pre /\
  off + 32 <= lo /\ ghost_inv_at D lo d cenv cx es G tn s ==>
  mem_word_taint tn.t_mem off = {}
Proof
  strip_tac >>
  simp[NoAsms, ptrDisciplineTheory.mem_word_taint_def, pred_setTheory.EXTENSION] >>
  gen_tac >> rewrite_tac[GSYM IMP_DISJ_THM] >> ntac 2 strip_tac >>
  `~imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) (off + x)` by
    (`off <= off + x /\ off + x < off + 32 /\
      off + x < off + type_memory_size (ArrayTV tv (Dynamic n))` by
       simp[valueEncodingTheory.type_memory_size_def] >>
     drule_all imm_frame_restrict >>
     disch_then (qspec_then `mem_bytes_at 0 lo s.vs_memory` mp_tac) >>
     metis_tac[ctorDeployDeadSectionTheory.mem_dead_bytes_header_live]) >>
  `off + x < lo` by decide_tac >>
  fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  qpat_x_assum `!i. i < lo /\ _ ==> _`
    (qspec_then `off + x` mp_tac) >> simp[]
QED

Theorem for_array_immutable_header_access_full:
  eval_operand op s = SOME a /\ op_prov G op = NONE /\
  w2n a + 32 <= lo ==>
  access_ok lo G func (mk_inst id ILOAD [op] [out]) s
Proof
  strip_tac >>
  simp[ptrDisciplineTheory.access_ok_def, venomInstTheory.mk_inst_def,
    codegenRelTheory.source_memory_write_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    memLocDefsTheory.mem_read_ops_def,
    memLocDefsTheory.mem_write_ops_def]
QED

Theorem for_array_immutable_header_load_full:
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  op_prov G op = NONE /\ w2n a + 32 <= lo /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D lo ctx func PG G tn [mk_inst id ILOAD [op] [out]] s
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,mem_word_taint tn.t_mem (w2n a)))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ILOAD [op] [out]) s =
     OK (update_var out (immutable_copy_read T a s) s)` by
    metis_tac[immutableLoadPtrTheory.immutable_load_step] >>
  simp[fragGasSeqPtrTheory.inst_seq_ptr_def] >> conj_tac
  >- (simp[ptrSafeRunTheory.ptr_inst_ok_def] >> conj_tac
      >- metis_tac[for_array_immutable_header_access_full] >>
      conj_tac
      >- simp[ptrDisciplineTheory.taint_ok_def, venomInstTheory.mk_inst_def,
           contextCodegenRelTheory.source_memory_read_ranges_def] >>
      simp[venomExecSemanticsTheory.step_inst_non_invoke,
           venomInstTheory.mk_inst_def, venomStateTheory.update_var_def]) >>
  conj_tac
  >- simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def,
       ptrDisciplineTheory.set_prov_def, venomInstTheory.mk_inst_def] >>
  sym_tac >>
  irule (payloadLoadStorePtrTheory.immutable_load_payload_taint
    |> Q.INST [`ctor` |-> `T`] |> SIMP_RULE bool_ss []) >>
  simp[venomStateTheory.update_var_def]
QED

(* The constructor address is scalar, not an invented allocation pointer. *)
Theorem for_array_immutable_ctor_sequence_full[local]:
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w /\
  op_taint tn off = {} /\ op_taint tn region = {} /\
  op_prov G off = NONE /\ op_prov G region = NONE /\
  w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?Gf tf. (!D k. inst_seq_ptr D lo ctx func PG G tn
    [mk_inst ai ADD [off;region] [addr];
     mk_inst li ILOAD [Var addr] [out]] (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf (Var out) = NONE /\ op_taint tf (Var out) = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  qabbrev_tac `u = update_var addr a s` >>
  qabbrev_tac `Ga = step_prov PG G (mk_inst ai ADD [off;region] [addr]) u` >>
  qabbrev_tac `ta = tn with t_var := tn.t_var |+ (addr,{})` >>
  `op_prov Ga (Var addr) = NONE /\ op_taint ta (Var addr) = {} /\
   eval_operand (Var addr) u = SOME a` by
    simp[Abbr `Ga`,Abbr `ta`,Abbr `u`,add_selected_provenance,
      first_prov_def,op_taint_def,eval_operand_def,lookup_var_def,
      update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  qexistsl_tac [`DRESTRICT Ga (COMPL {out})`,
    `ta with t_var := ta.t_var |+ (out,{})`] >>
  reverse conj_tac
  >- simp[Abbr `ta`,op_prov_def,op_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT,finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >>
  irule (inst_seq_ptr_uniform_append |> Q.INST
    [`xs` |-> `[mk_inst ai ADD [off;region] [addr]]`,
     `ys` |-> `[mk_inst li ILOAD [Var addr] [out]]`]
    |> SIMP_RULE list_ss []) >>
  simp[mk_inst_def,is_terminator_def] >>
  qexistsl_tac [`Ga`,`u`,`ta`] >>
  simp[run_inst_seq_def,storage_copy_add_step,Abbr `u`] >>
  rewrite_tac[GSYM mk_inst_def] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >>
      simp[allocas_from_def] >> qexists_tac `D` >>
      simp[Abbr `Ga`,Abbr `ta`] >>
      irule (clean_add_checked_uniform |> SPEC_ALL |> Q.INST [`b` |-> `0w`]
        |> SIMP_RULE (srw_ss()) [WORD_ADD_0]) >> simp[]) >>
  reverse conj_tac
  >- simp[step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,WORD_ADD_0] >>
  gen_tac >>
  `mem_word_taint ta.t_mem (w2n a) = {}` by simp[Abbr `ta`] >>
  qpat_x_assum `mem_word_taint ta.t_mem _ = {}`
    (fn th => GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [GSYM th]) >>
  irule for_array_immutable_header_load_full >>
  simp[allocas_from_def,update_var_def,eval_operand_def,lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Compiler emission and the certificate share the same concrete read. *)
Theorem for_array_immutable_ctor_compiler_full[local]:
  compile_imm_load_word T (SOME region) off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w /\
  op_taint tn off = {} /\ op_taint tn region = {} /\
  op_prov G off = NONE /\ op_prov G region = NONE /\
  w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    run_inst_seq (emitted_insts sa sb) s = OK z /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tf)) /\
    eval_operand r z = SOME (immutable_copy_read T a s) /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\ op_taint tf r = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    z.vs_memory = s.vs_memory /\ z.vs_current_bb = sb.cs_current_bb /\
    ~z.vs_halted /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule compile_imm_load_word_ctor_result >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [off;region] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) ILOAD
       [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var + 1)]]` by
    simp[emitted_insts_def,listTheory.DROP_APPEND] >>
  `?Gf tf. (!D k. inst_seq_ptr D lo ctx func PG G tn
      (emitted_insts sa sb) (s with vs_inst_idx := k) Gf tf) /\
      op_prov Gf r = NONE /\ op_taint tf r = {} /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    (asm_rewrite_tac[] >> irule for_array_immutable_ctor_sequence_full >> simp[]) >>
  drule_all compile_imm_load_word_ctor_execution >> strip_tac >>
  `same_blocks sa sb` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_load_word_def,compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,emitHelperTheory.emit_op_def,
       compileEnvTheory.emit_def,compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def,compileEnvTheory.comp_return_def,
       exprLoweringPropsTheory.same_blocks_def] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`update_var ("%" ++ toString (sa.cs_next_var + 1))
    (mload (w2n a) s) (update_var ("%" ++ toString sa.cs_next_var) a s)`,
    `Gf`,`tf`] >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt gen_tac >>
      `sb.cs_current_bb = sa.cs_current_bb` by
        fs[exprLoweringPropsTheory.same_blocks_def] >>
      `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
        (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >>
         simp[] >> metis_tac[]) >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tf` by
        (qpat_x_assum `!D k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
      `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
        (simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memLocDefsTheory.mem_read_ops_def,memLocDefsTheory.mem_write_ops_def,
          storage_copy_add_step,mk_inst_def,update_var_def,
          eval_operand_def,lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
         simp[step_inst_base_opcode_eqs,exec_pure2_def,exec_read1_def,WORD_ADD_0,
           eval_operand_def,lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
         (emitted_insts sa sb)` by simp[mk_inst_def,is_terminator_def] >>
      drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
      simp[mk_inst_def,is_terminator_def]) >>
  simp[eval_operand_def,lookup_var_def,update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE,immutableCopyExecutionTheory.immutable_copy_read_def] >>
  conj_tac
  >- (simp[exprSimCopyTheory.copy_runtime_frame_def,
        exprSimStorageCopyTheory.copy_static_def,update_var_def] >>
      gen_tac >> strip_tac >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def,lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[exprSimCopyTheory.copy_old_operand_def,
    loweringStateRelDefsTheory.not_fresh_at_def,
    exprLoweringPropsTheory.same_blocks_def] >>
  conj_tac >- fs[exprLoweringPropsTheory.same_blocks_def] >>
  gen_tac >> strip_tac >>
  irule revertReasonPrefixFramePtrTheory.inst_seq_ptr_other_output_frame >>
  qpat_assum `!D k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`ARB`,`0`] assume_tac) >>
  goal_assum (drule_at Any) >>
  simp[mk_inst_def] >> fs[loweringStateRelDefsTheory.not_fresh_at_def]
QED

(* Distinct source declaration keys make the compiler's first lookup exact. *)
Theorem for_immutable_decl_type[local]:
  !pre post vis mut name ty slot.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option))
      (pre ++ VariableDecl vis mut name ty slot :: post))) ==>
    build_var_type_map (pre ++ VariableDecl vis mut name ty slot :: post)
      (NONE,name) = SOME ty
Proof
  Induct_on `pre` >> simp[compileVyperTheory.build_var_type_map_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[compileVyperTheory.build_var_type_map_def,
    vyperTypeContractTheory.toplevel_vtype_keys_toplevel_def,
    listTheory.ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem for_immutable_array_eval_env[local]:
  supported_word_type elem ==>
  evaluate_type tenv (ArrayT elem bd) = evaluate_type tenv' (ArrayT elem bd)
Proof
  Cases_on `elem` >> simp[supportedTypesTheory.supported_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supportedTypesTheory.supported_word_type_def, vyperValueTheory.evaluate_type_def]
QED

Theorem for_immutable_array_decl:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bd) ==>
  ?pre post vis slot. src = NONE /\
    tops = pre ++ VariableDecl vis Immutable name (ArrayT elem bd) slot :: post /\
    supported_word_type elem
Proof
  strip_tac >>
  `src = NONE` by
    (fs[bodySimTheory.body_inv_def, bodySimTheory.cenv_module_pins_def,
        exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  gvs[] >>
  `?off. FLOOKUP cenv.ce_module_vars (NONE,name) = SOME (ImmutableLoc off)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  drule bodySimTheory.body_inv_immutable_section_layout >>
  simp[immutableRelationTheory.immutable_section_layout_def] >>
  disch_then drule >> strip_tac >>
  `cenv.ce_module_var_type (NONE,name) = SOME (ArrayT elem bd)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        exprSimHypsDefsTheory.bare_globals_layout_def] >> metis_tac[]) >>
  `build_var_type_map tops (NONE,name) = SOME ty` by
    (qpat_assum `tops = _` (fn th => once_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     irule for_immutable_decl_type >> fs[bodySimTheory.body_inv_def]) >>
  `ty = ArrayT elem bd` by (fs[bodySimTheory.body_inv_def] >> gvs[] >> metis_tac[]) >>
  gvs[] >> qexistsl_tac [`pre`,`post`,`vis`,`slot`] >> simp[] >>
  `supported_declaration_header
    ((pre ++ [VariableDecl vis Immutable name (ArrayT elem bd) slot]) ++ post)
    (VariableDecl vis Immutable name (ArrayT elem bd) slot)` by
    fs[bodySimTheory.body_inv_def,supportedProgramTheory.supported_program_def,
       supportedDeclsTheory.supported_declaration_headers_def,EVERY_MEM] >>
  Cases_on `vis` >> Cases_on `slot` >> Cases_on `bd` >>
  gvs[supportedDeclsTheory.supported_declaration_header_def,
      supportedTypesTheory.supported_value_type_def,
      supportedTypesTheory.supported_scalar_type_def,
      supportedTypesTheory.supported_word_type_def,
      supportedTypesTheory.supported_string_type_def]
QED

Theorem for_immutable_decl_extent[local]:
  struct_args_unique tops /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
    type_memory_size tv <= imm_len tops
Proof
  strip_tac >> drule_all imm_frame_size >> strip_tac >>
  rewrite_tac[immSectionDeadTheory.imm_len_def] >>
  qpat_assum `tops = _` (fn th => GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    empty_rewrites [th]) >>
  simp[compileVyperTheory.compute_immutables_len_append,
       compileVyperTheory.compute_immutables_len_def]
QED

(* First-match module lookup preserves the main namespace without requiring
   uniqueness of the surrounding module list. *)
Theorem for_type_env_other_source[local]:
  !ts src src' id. src <> src' ==>
    FLOOKUP (type_env_for_module src ts) (src',id) = NONE
Proof
  Induct_on `ts` >> simp[vyperContextTheory.type_env_for_module_def] >>
  Cases_on `h` >> simp[vyperContextTheory.type_env_for_module_def,
    finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem for_main_type_env_submap[local]:
  !mods tops. ALOOKUP mods NONE = SOME tops ==>
    type_env tops SUBMAP type_env_all_modules mods
Proof
  Induct_on `mods` >- simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[vyperContextTheory.type_env_all_modules_def] >>
  Cases_on `h0 = NONE`
  >- (gvs[vyperContextTheory.type_env_def,
        finite_mapTheory.SUBMAP_FLOOKUP_EQN,finite_mapTheory.FLOOKUP_FUNION]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[finite_mapTheory.SUBMAP_FLOOKUP_EQN] >> strip_tac >>
  rpt gen_tac >> strip_tac >> PairCases_on `x` >>
  `x0 = NONE` by
    (Cases_on `x0` >> gvs[vyperContextTheory.type_env_def,
      for_type_env_other_source]) >>
  gvs[finite_mapTheory.FLOOKUP_FUNION,for_type_env_other_source] >>
  metis_tac[]
QED

Theorem for_main_tenv_submap[local]:
  get_module_code cx NONE = SOME tops ==> type_env tops SUBMAP get_tenv cx
Proof
  simp[vyperContextTheory.get_module_code_def,vyperContextTheory.get_tenv_def,
    AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule for_main_type_env_submap >> simp[]
QED

Theorem for_immutable_eval_size[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size tv
Proof
  strip_tac >>
  `type_env tops SUBMAP get_tenv cx` by
    (irule for_main_tenv_submap >> fs[bodySimTheory.body_inv_def]) >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by
    metis_tac[CONJUNCT1 abiTypeBoundPropsTheory.vyper_to_abi_type_submap] >>
  drule_all exprSimHypsTheory.expr_sim_inv_memory_size >>
  fs[bodySimTheory.body_inv_def,
    GSYM structFieldsPropsTheory.type_mem_bytes_type_memory_bytes]
QED

Theorem for_immutable_dynamic_header_live[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME (ArrayTV tv (Dynamic n)) /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  off <= j /\ j < off + 32 ==>
  ~imm_section_dead tops sec j
Proof
  strip_tac >> rewrite_tac[immSectionDeadTheory.imm_section_dead_def] >>
  strip_tac >>
  drule (CONJUNCT1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >> strip_tac >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size (ArrayTV tv (Dynamic n))` by
    (irule for_immutable_eval_size >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
    type_memory_size tv'` by
    (irule for_immutable_eval_size >> metis_tac[]) >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
   pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'` by metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  strip_tac
  >- (fs[] >> gvs[] >> metis_tac[ctorDeployDeadSectionTheory.mem_dead_bytes_header_live])
  >- (ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
      qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >>
      gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
  qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >> gvs[] >> decide_tac
QED

Theorem for_immutable_dynamic_header_extent[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME (ArrayTV tv (Dynamic n)) /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre ==>
  off + 32 <= imm_len tops
Proof
  strip_tac >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size (ArrayTV tv (Dynamic n))` by
    (irule for_immutable_eval_size >> metis_tac[]) >>
  mp_tac (compileVyperTheory.immutable_declaration_interval_bound
    |> Q.INST [`off` |-> `0`, `prefix` |-> `pre`, `suffix` |-> `post`,
      `sft` |-> `get_struct_fields (make_struct_fields_map tops)`]) >>
  simp[GSYM immSectionDeadTheory.imm_len_def] >>
  qpat_x_assum `tops = _` (fn th => rewrite_tac[GSYM th]) >>
  gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac
QED

Theorem for_immutable_dynamic_header_resources[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME (ArrayTV tv (Dynamic n)) /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  off + 32 <= lo /\
  (!j. off <= j /\ j < off + 32 ==>
    ~imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) j) /\
  mem_word_taint tn.t_mem off = {}
Proof
  strip_tac >>
  `cx_tops cx = tops` by
    fs[gasContextTheory.cx_tops_def,bodySimTheory.body_inv_def] >>
  `lo = imm_len tops` by fs[bodyPtrDefsTheory.dead_lo_ok_def] >>
  `off + 32 <= lo` by metis_tac[for_immutable_dynamic_header_extent] >>
  `!j. off <= j /\ j < off + 32 ==>
    ~imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) j` by
    (metis_tac[for_immutable_dynamic_header_live]) >>
  simp[] >>
  simp[NoAsms,ptrDisciplineTheory.mem_word_taint_def,pred_setTheory.EXTENSION] >>
  gen_tac >> rewrite_tac[GSYM IMP_DISJ_THM] >> ntac 2 strip_tac >>
  `~imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) (off+x)` by
    (first_x_assum irule >> decide_tac) >>
  `off + x < lo` by decide_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >> strip_tac >>
  qpat_x_assum `!i. i < _ /\ _ ==> _` (qspec_then `off + x` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> gvs[] >>
  metis_tac[APPEND_ASSOC,APPEND]
QED

(* Actual prefix inputs discharge the constructor header boundary. *)
Theorem for_immutable_prefix_header_resources[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem (Dynamic n)) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) (ArrayT elem (Dynamic n)) =
    SOME (ArrayTV tv (Dynamic n)) /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  off + 32 <= lo /\ mem_word_taint tn.t_mem off = {}
Proof
  strip_tac >> drule_all for_immutable_array_decl >> strip_tac >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  drule bodySimTheory.body_inv_immutable_section_layout >>
  simp[immutableRelationTheory.immutable_section_layout_def] >>
  disch_then drule >> strip_tac >>
  `tops = pre' ++ VariableDecl vis' Immutable name ty slot' :: post'` by
    metis_tac[APPEND_ASSOC,APPEND] >>
  `ty = ArrayT elem (Dynamic n)` by
    (`build_var_type_map tops (NONE,name) = SOME ty` by
       (qpat_assum `tops = pre' ++ _` (fn th => once_rewrite_tac[th]) >>
        pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
        irule for_immutable_decl_type >> fs[bodySimTheory.body_inv_def]) >>
     `cenv.ce_module_var_type (NONE,name) = SOME (ArrayT elem (Dynamic n))` by
       (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
         exprSimHypsDefsTheory.bare_globals_layout_def] >> metis_tac[]) >>
     `cenv.ce_module_var_type (NONE,name) = build_var_type_map tops (NONE,name)` by
       (fs[bodySimTheory.body_inv_def] >> gvs[APPEND_ASSOC,APPEND]) >>
     gvs[]) >>
  `evaluate_type (type_env tops) (ArrayT elem (Dynamic n)) =
    SOME (ArrayTV tv (Dynamic n))` by metis_tac[for_immutable_array_eval_env] >>
  `off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre'` by
    metis_tac[] >>
  metis_tac[for_immutable_dynamic_header_resources]
QED

(* Saved partial join proof for C1.5.immPrefix.assemble.join.
The actual optional prefix: no independent load certificate or endpoint.
Theorem for_array_immutable_length_prefix_full:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src name = SOME (ArrayTV tv bd,ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT elem bd) = SOME (ArrayTV tv bd) /\
  vs = array_elements (ArrayTV tv bd) av /\ arr_op = Lit (n2w off) /\
  (if (case bd of Dynamic n => T | Fixed n => F)
   then compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode arr_op
   else comp_return (Lit (n2w (bound_length bd)))) sa = (len_op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\ z.vs_memory = s.vs_memory /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    eval_operand len_op z = SOME (n2w (LENGTH vs)) /\
    copy_old_operand sb len_op /\
    op_prov Gf len_op = NONE /\ op_taint tf len_op = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!H k. inst_seq_ptr (DF H) lo ctx func PG G tn
      (emitted_insts sa sb) (s with vs_inst_idx := k) Gf tf) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf))
Proof
  strip_tac >> Cases_on `bd`
  >- (gvs[compileEnvTheory.comp_return_def,vyperASTTheory.bound_length_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[exprSimCopyTheory.copy_runtime_frame_refl,
        stmtSimForArrayTheory.fixed_array_elements_length,
        exprSimCopyTheory.copy_old_operand_def,eval_operand_def,
        op_prov_def,op_taint_def,emitted_insts_def,
        fragGasSeqPtrTheory.inst_seq_ptr_def] >>
      conj_tac
      >- (`state_well_typed es` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
          gvs[vyperBareGlobalNameTheory.lookup_immutable_def,
            AllCaseEqs()] >>
          `MEM (cx.txn.target,imms) es.immutables` by
            metis_tac[alistTheory.ALOOKUP_MEM] >>
          fs[vyperTypeInvariantsTheory.state_well_typed_def,EVERY_MEM] >>
          first_x_assum drule >> simp[] >>
          simp[vyperTypeInvariantsTheory.imms_well_typed_def] >> strip_tac >>
          Cases_on `ALOOKUP imms src` >>
          gvs[vyperStateTheory.get_source_immutables_def] >>
          `value_has_type (ArrayTV tv (Fixed n)) (ArrayV av)` by metis_tac[] >>
          Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,vyperValueOperationTheory.array_elements_def]) >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venomStateTheory.venom_state_component_equality] >>
      simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `stmt_state_rel H ctx func cenv cx es s /\
   dead_lo_ok H (DF H) lo cenv cx /\
   ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  FAIL_TAC "dynamic start"
QED
*)

Theorem for_immutable_prefix_value_typed[local]:
  expr_sim_inv cenv cx env es /\
  lookup_immutable cx es src name = SOME (ArrayTV tv bd,ArrayV av) ==>
  value_has_type (ArrayTV tv bd) (ArrayV av)
Proof
  strip_tac >>
  `state_well_typed es` by fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  gvs[vyperBareGlobalNameTheory.lookup_immutable_def,AllCaseEqs()] >>
  `MEM (cx.txn.target,imms) es.immutables` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  fs[vyperTypeInvariantsTheory.state_well_typed_def,EVERY_MEM] >>
  first_x_assum drule >> simp[] >>
  simp[vyperTypeInvariantsTheory.imms_well_typed_def] >> strip_tac >>
  Cases_on `ALOOKUP imms src` >>
  gvs[vyperStateTheory.get_source_immutables_def] >> metis_tac[]
QED

Theorem for_immutable_prefix_read_observation[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem (Dynamic n)) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src name = SOME (ArrayTV tv (Dynamic n),ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT elem (Dynamic n)) =
    SOME (ArrayTV tv (Dynamic n)) /\
  stmt_state_rel H ctx func cenv cx es s ==>
  immutable_copy_read cenv.ce_is_ctor (n2w off) s =
    n2w (LENGTH (array_elements (ArrayTV tv (Dynamic n)) av))
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv (Dynamic n)) (ArrayV av)` by
    metis_tac[for_immutable_prefix_value_typed] >>
  `src = cenv.ce_module /\ off + type_memory_size (ArrayTV tv (Dynamic n)) < dimword (:256)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     qpat_x_assum `!src id ty. _` drule >> strip_tac >> gvs[]) >>
  `immutable_holds cenv cx (ArrayT elem (Dynamic n)) (Value (ArrayV av))
     (n2w off) es s` by
    (gvs[vyperBareGlobalNameTheory.lookup_immutable_def,AllCaseEqs()] >>
     simp[loweringPostsTheory.immutable_holds_def,
       vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
     qexistsl_tac [`name`,`off`,`ArrayTV tv (Dynamic n)`,`ArrayV av`,`0`] >>
     simp[loweringPostsTheory.sub_layout_def]) >>
  `evaluate_type (get_tenv cx) elem = SOME tv` by
    gvs[Once vyperValueTheory.evaluate_type_def,AllCaseEqs()] >>
  drule_all exprSimBopRestWordLoadsTheory.rest_word_array_immutable_header >>
  Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
    vyperValueOperationTheory.array_elements_def,
    vyperValueOperationTheory.array_length_def,
    immutableCopyExecutionTheory.immutable_copy_read_def]
QED

Theorem for_immutable_prefix_runtime_section[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem (Dynamic n)) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src name = SOME (ArrayTV tv (Dynamic n),ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT elem (Dynamic n)) =
    SOME (ArrayTV tv (Dynamic n)) /\
  stmt_state_rel H ctx func cenv cx es s /\ ~cenv.ce_is_ctor ==>
  w2n (n2w off : 256 word) <= LENGTH s.vs_data_section
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv (Dynamic n)) (ArrayV av)` by
    metis_tac[for_immutable_prefix_value_typed] >>
  `src = cenv.ce_module /\ off + type_memory_size (ArrayTV tv (Dynamic n)) < dimword (:256)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     qpat_x_assum `!src id ty. _` drule >> strip_tac >> gvs[]) >>
  `immutable_holds cenv cx (ArrayT elem (Dynamic n)) (Value (ArrayV av))
     (n2w off) es s` by
    (gvs[vyperBareGlobalNameTheory.lookup_immutable_def,AllCaseEqs()] >>
     simp[loweringPostsTheory.immutable_holds_def,
       vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
     qexistsl_tac [`name`,`off`,`ArrayTV tv (Dynamic n)`,`ArrayV av`,`0`] >>
     simp[loweringPostsTheory.sub_layout_def]) >>
  drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_immutable_region_bound >>
  simp[]
QED

Theorem for_array_immutable_runtime_compiler_full[local]:
  compile_imm_load_word F imm off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand off s = SOME a /\ op_taint tn off = {} /\
  w2n a <= LENGTH s.vs_data_section /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    run_inst_seq (emitted_insts sa sb) s = OK z /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tf)) /\
    eval_operand r z = SOME (immutable_copy_read F a s) /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\ op_taint tf r = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    z.vs_memory = s.vs_memory /\ z.vs_current_bb = sb.cs_current_bb /\
    ~z.vs_halted /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op DLOAD [off] sa = (r,sb)` by
    fs[compile_imm_load_word_runtime] >>
  `?out. r = Var out /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id DLOAD [off] [out]] /\
    not_fresh_at sb out /\ ~not_fresh_at sa out /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def,compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,compileEnvTheory.emit_def,compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def,compileEnvTheory.comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def,DROP_APPEND,
       loweringStateRelDefsTheory.not_fresh_at_def,same_blocks_def]) >>
  qabbrev_tac `z = update_var out (immutable_copy_read F a s) s` >>
  qabbrev_tac `Gf = DRESTRICT G (COMPL {out})` >>
  qabbrev_tac `tf = tn with t_var := tn.t_var |+ (out,{})` >>
  `run_inst_seq (emitted_insts sa sb) s = OK z` by
    (drule (immutableLoadPtrTheory.immutable_load_step
       |> Q.INST [`ctor` |-> `F`] |> SIMP_RULE (srw_ss()) []) >>
     disch_then (qspecl_then [`out`,`sa.cs_next_id`] assume_tac) >>
     simp[run_inst_seq_def,Abbr `z`]) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tf` by
    (rpt gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[allocas_from_def,Abbr `Gf`,Abbr `tf`] >> qexists_tac `D` >>
     simp[] >>
     irule (immutableSeqCursorPtrTheory.immutable_load_checked_uniform
       |> Q.INST [`ctor` |-> `F`] |> SIMP_RULE (srw_ss()) []) >> simp[]) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt gen_tac >>
      `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
      `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
        (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >>
         simp[] >> metis_tac[]) >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tf` by
        (qpat_x_assum `!D k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
           (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
      `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
        (simp[] >>
         irule (iffRL (exprSimBopRestWordLoadSafetyTheory.rest_word_load_safety_checks
           |> Q.INST [`opc` |-> `DLOAD`] |> SIMP_RULE (srw_ss()) [])) >>
         simp[] >> goal_assum (drule_at Any) >> simp[]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by simp[mk_inst_def,is_terminator_def] >>
      drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
      simp[mk_inst_def,is_terminator_def]) >>
  simp[Abbr `z`,Abbr `Gf`,Abbr `tf`,eval_operand_def,lookup_var_def,
    update_var_def,finite_mapTheory.FLOOKUP_UPDATE,op_prov_def,op_taint_def,
    finite_mapTheory.FLOOKUP_DRESTRICT,exprSimCopyTheory.copy_old_operand_def] >>
  conj_tac
  >- (simp[exprSimCopyTheory.copy_runtime_frame_def,
        exprSimStorageCopyTheory.copy_static_def,same_blocks_def,update_var_def] >>
      gen_tac >> strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- fs[same_blocks_def] >>
  gen_tac >> strip_tac >> `x <> out` by metis_tac[] >> simp[]
QED

Theorem for_array_immutable_ctor_direct_compiler_full[local]:
  compile_imm_load_word T NONE off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand off s = SOME a /\ op_taint tn off = {} /\
  op_prov G off = NONE /\ w2n a + 32 <= lo /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    run_inst_seq (emitted_insts sa sb) s = OK z /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tf)) /\
    eval_operand r z = SOME (immutable_copy_read T a s) /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\ op_taint tf r = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    z.vs_memory = s.vs_memory /\ z.vs_current_bb = sb.cs_current_bb /\
    ~z.vs_halted /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op ILOAD [off] sa = (r,sb)` by fs[compile_imm_load_word_def] >>
  `?out. r = Var out /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id ILOAD [off] [out]] /\
    not_fresh_at sb out /\ ~not_fresh_at sa out /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def,compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,compileEnvTheory.emit_def,compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def,compileEnvTheory.comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def,DROP_APPEND,
       loweringStateRelDefsTheory.not_fresh_at_def,same_blocks_def]) >>
  qabbrev_tac `z = update_var out (immutable_copy_read T a s) s` >>
  qabbrev_tac `Gf = DRESTRICT G (COMPL {out})` >>
  qabbrev_tac `tf = tn with t_var := tn.t_var |+ (out,{})` >>
  `run_inst_seq (emitted_insts sa sb) s = OK z` by
    (drule (immutableLoadPtrTheory.immutable_load_step
       |> Q.INST [`ctor` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
     disch_then (qspecl_then [`out`,`sa.cs_next_id`] assume_tac) >>
     simp[run_inst_seq_def,Abbr `z`]) >>
  `!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tf` by
    (rpt gen_tac >> simp[Abbr `Gf`,Abbr `tf`] >>
     `tn with t_var := tn.t_var |+ (out,{}) =
      tn with t_var := tn.t_var |+ (out,mem_word_taint tn.t_mem (w2n a))` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule for_array_immutable_header_load_full >>
     simp[allocas_from_def,eval_operand_def,lookup_var_def]) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt gen_tac >>
      `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
      `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
        (drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >>
         simp[] >> metis_tac[]) >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tf` by
        (qpat_x_assum `!D k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
           (qspecl_then [`D`,`s.vs_inst_idx`] mp_tac) >> simp[]) >>
      `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
        (simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          memLocDefsTheory.mem_read_ops_def,memLocDefsTheory.mem_write_ops_def,
          mk_inst_def] >>
         Cases_on `step_inst_base (mk_inst sa.cs_next_id ILOAD [off] [out]) s` >>
         gvs[mk_inst_def]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by simp[mk_inst_def,is_terminator_def] >>
      drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
      simp[mk_inst_def,is_terminator_def]) >>
  simp[Abbr `z`,Abbr `Gf`,Abbr `tf`,eval_operand_def,lookup_var_def,
    update_var_def,finite_mapTheory.FLOOKUP_UPDATE,op_prov_def,op_taint_def,
    finite_mapTheory.FLOOKUP_DRESTRICT,exprSimCopyTheory.copy_old_operand_def] >>
  conj_tac
  >- (simp[exprSimCopyTheory.copy_runtime_frame_def,
        exprSimStorageCopyTheory.copy_static_def,same_blocks_def,update_var_def] >>
      gen_tac >> strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE]) >>
  conj_tac >- fs[same_blocks_def] >>
  gen_tac >> strip_tac >> `x <> out` by metis_tac[] >> simp[]
QED

Theorem for_array_immutable_length_prefix_full:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src name = SOME (ArrayTV tv bd,ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT elem bd) = SOME (ArrayTV tv bd) /\
  vs = array_elements (ArrayTV tv bd) av /\ arr_op = Lit (n2w off) /\
  (if (case bd of Dynamic n => T | Fixed n => F)
   then compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode arr_op
   else comp_return (Lit (n2w (bound_length bd)))) sa = (len_op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\ z.vs_memory = s.vs_memory /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    eval_operand len_op z = SOME (n2w (LENGTH vs)) /\
    copy_old_operand sb len_op /\
    op_prov Gf len_op = NONE /\ op_taint tf len_op = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!H k. inst_seq_ptr (DF H) lo ctx func PG G tn
      (emitted_insts sa sb) (s with vs_inst_idx := k) Gf tf) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf))
Proof
  strip_tac >>
  `value_has_type (ArrayTV tv bd) (ArrayV av)` by
    metis_tac[for_immutable_prefix_value_typed] >>
  Cases_on `bd`
  >- (gvs[compileEnvTheory.comp_return_def,vyperASTTheory.bound_length_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[exprSimCopyTheory.copy_runtime_frame_refl,
        stmtSimForArrayTheory.fixed_array_elements_length,
        exprSimCopyTheory.copy_old_operand_def,eval_operand_def,
        op_prov_def,op_taint_def,emitted_insts_def,
        fragGasSeqPtrTheory.inst_seq_ptr_def] >>
      conj_tac
      >- (Cases_on `av` >>
          gvs[vyperTypingTheory.value_has_type_def,
            vyperValueOperationTheory.array_elements_def]) >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venomStateTheory.venom_state_component_equality] >>
      simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules]) >>
  `stmt_state_rel H ctx func cenv cx es s /\
   dead_lo_ok H (DF H) lo cenv cx /\
   ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `immutable_copy_read cenv.ce_is_ctor (n2w off) s = n2w (LENGTH vs)` by
    metis_tac[for_immutable_prefix_read_observation] >>
  gvs[compile_ptr_load_def] >>
  reverse (Cases_on `cenv.ce_is_ctor`)
  >- (`w2n (n2w off : 256 word) <= LENGTH s.vs_data_section` by
        metis_tac[for_immutable_prefix_runtime_section] >>
      fs[] >>
      `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
       op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def,op_taint_def] >>
      drule for_array_immutable_runtime_compiler_full >>
      disch_then (qspecl_then [`tn`,`s`,`lo`] mp_tac) >>
      simp[eval_operand_def,op_taint_def] >>
      disch_then drule_all >>
      disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
      qexistsl_tac [`z`,`Gf`,`tf`] >> simp[] >>
      `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
        (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
         simp[compile_imm_load_word_runtime,emitHelperTheory.emit_op_def,
           compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.emit_def,compileEnvTheory.fresh_var_def,
           compileEnvTheory.fresh_id_def,compileEnvTheory.comp_return_def] >>
         strip_tac >> gvs[emitted_insts_def,DROP_APPEND]) >>
      simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s /\
   dead_lo_ok H (DF H) lo cenv cx /\
   ghost_inv_at (DF H) lo d cenv cx es G tn s` by metis_tac[] >>
  `off + 32 <= lo /\ mem_word_taint tn.t_mem off = {}` by
    (drule_all for_immutable_prefix_header_resources >> simp[]) >>
  `off < dimword (:256)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     qpat_x_assum `!src id ty. _` drule >> strip_tac >> gvs[] >> decide_tac) >>
  Cases_on `cenv.ce_imm_alloca`
  >- (fs[] >> drule for_array_immutable_ctor_direct_compiler_full >>
      disch_then (qspecl_then [`tn`,`s`,`lo`] mp_tac) >>
      simp[eval_operand_def,op_taint_def,op_prov_def] >>
      disch_then drule_all >>
      disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
      qexistsl_tac [`z`,`Gf`,`tf`] >> simp[] >>
      `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
        (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
         simp[compile_imm_load_word_def,emitHelperTheory.emit_op_def,
           compileEnvTheory.comp_bind_def,compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.emit_def,compileEnvTheory.fresh_var_def,
           compileEnvTheory.fresh_id_def,compileEnvTheory.comp_return_def] >>
         strip_tac >> gvs[emitted_insts_def,DROP_APPEND]) >> simp[]) >>
  rename1 `cenv.ce_imm_alloca = SOME region` >>
  `eval_operand region s = SOME 0w` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
      loweringStateRelDefsTheory.immutable_base_zero_def] >> metis_tac[]) >>
  `op_taint tn region = {} /\ op_prov G region = NONE` by
    (Cases_on `region` >> simp[op_taint_def,op_prov_def] >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
     `lo <> 0` by decide_tac >> fs[op_taint_def,op_prov_def]) >>
  fs[] >> drule for_array_immutable_ctor_compiler_full >>
  disch_then (qspecl_then [`tn`,`s`,`lo`] mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`func`,`ctx`,`PG`,`G`] mp_tac) >>
  simp[op_taint_def] >> strip_tac >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> simp[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (drule compile_imm_load_word_ctor_result >> strip_tac >>
     simp[emitted_insts_def,DROP_APPEND]) >> simp[]
QED

Theorem for_immutable_occurrence_extent[local]:
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  off = compute_immutables_len sft pre /\
  sft = get_struct_fields (make_struct_fields_map tops) /\
  type_mem_bytes sft ty = type_memory_size tv ==>
  off + type_memory_size tv <= imm_len tops
Proof
  strip_tac >>
  mp_tac (compileVyperTheory.immutable_declaration_interval_bound
    |> Q.INST [`off` |-> `0`, `prefix` |-> `pre`, `suffix` |-> `post`]) >>
  simp[] >>
  qpat_x_assum `tops = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[immSectionDeadTheory.imm_len_def]
QED

Theorem for_immutable_scalar_payload_live[local]:
  type_memory_size tv = 32 /\ (!b j. ~mem_dead_bytes sec b tv j) /\
  k < bound_length bd /\
  (!n. bd = Dynamic n ==> k < w2n (mem_word_at off sec)) /\
  a = off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + 32*k ==>
  !j. a <= j /\ j < a+32 ==> ~mem_dead_bytes sec off (ArrayTV tv bd) j
Proof
  strip_tac >> Cases_on `bd`
  >- gvs[immSectionDeadTheory.mem_dead_bytes_def] >>
  gvs[] >> rpt strip_tac >>
  gvs[immSectionDeadTheory.mem_dead_bytes_def] >>
  `k = k'` by
    (irule ctorDeployDeadSectionTheory.mem_region_slot_unique >>
     qexistsl_tac [`off+32`,`32`,`j`] >> simp[] >> decide_tac) >>
  gvs[]
QED

Theorem for_immutable_element_layout[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx es src name = SOME (ArrayTV tv bd,ArrayV av) ==>
  ?pre post vis slot.
    tops = pre ++ VariableDecl vis Immutable name (ArrayT typ bd) slot :: post /\
    off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
    evaluate_type (type_env tops) (ArrayT typ bd) = SOME (ArrayTV tv bd) /\
    off + type_memory_size (ArrayTV tv bd) <= imm_len tops
Proof
  strip_tac >>
  `src = NONE /\ supported_word_type typ` by metis_tac[for_immutable_array_decl] >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  drule bodySimTheory.body_inv_immutable_section_layout >>
  simp[immutableRelationTheory.immutable_section_layout_def] >>
  disch_then drule >> strip_tac >>
  `tops = pre ++ VariableDecl vis Immutable name ty slot :: post` by
    metis_tac[APPEND_ASSOC,APPEND] >>
  `build_var_type_map tops (NONE,name) = SOME ty` by
    (qpat_assum `tops = _` (fn th => once_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
     irule for_immutable_decl_type >> fs[bodySimTheory.body_inv_def]) >>
  `ty = ArrayT typ bd` by
    (`cenv.ce_module_var_type (NONE,name) = SOME (ArrayT typ bd)` by
       (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
         exprSimHypsDefsTheory.bare_globals_layout_def] >> metis_tac[]) >>
     fs[bodySimTheory.body_inv_def] >> gvs[APPEND_ASSOC,APPEND] >> metis_tac[]) >>
  qpat_x_assum `ty = _` SUBST_ALL_TAC >>
  `evaluate_type (type_env tops) (ArrayT typ bd) = SOME (ArrayTV tv bd)` by
    (`evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tv bd)` by
       (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
           vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
        gvs[vyperBareGlobalNameTheory.lookup_immutable_def,AllCaseEqs()] >> metis_tac[]) >>
     metis_tac[for_immutable_array_eval_env]) >>
  qexistsl_tac [`pre`,`post`,`vis`,`slot`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre` by
    metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule for_immutable_occurrence_extent >>
  goal_assum (drule_at Any) >> simp[] >>
  irule for_immutable_eval_size >> metis_tac[]
QED

Theorem for_immutable_occurrence_live[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
  evaluate_type (type_env tops) ty = SOME tv /\
  off = compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre /\
  off <= j /\ j < off + type_memory_size tv /\
  ~mem_dead_bytes sec off tv j ==> ~imm_section_dead tops sec j
Proof
  strip_tac >> rewrite_tac[immSectionDeadTheory.imm_section_dead_def] >> strip_tac >>
  drule (CONJUNCT1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >> strip_tac >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size tv` by (irule for_immutable_eval_size >> metis_tac[]) >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty' =
    type_memory_size tv'` by (irule for_immutable_eval_size >> metis_tac[]) >>
  `pre ++ VariableDecl vis Immutable name ty slot :: post =
   pre' ++ VariableDecl vis' Immutable name' ty' slot' :: post'` by metis_tac[] >>
  drule imm_frame_occurrence_separation >>
  disch_then (qspec_then `get_struct_fields (make_struct_fields_map tops)` mp_tac) >>
  strip_tac
  >- (fs[] >> gvs[]) 
  >- (ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
      qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >> gvs[] >> decide_tac) >>
  ntac 2 (qpat_x_assum `tops = _` kall_tac) >>
  qpat_x_assum `_ ++ _ = _ ++ _` kall_tac >> gvs[] >> decide_tac
QED

Theorem for_immutable_section_header[local]:
  off + 32 <= len ==>
  mem_word_at off (mem_bytes_at 0 len mem) = mem_word_at off mem
Proof
  strip_tac >> rewrite_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  AP_TERM_TAC >>
  simp[valueEncodingDefsTheory.mem_bytes_at_bounded,
    abiCanonicalHeadSizeTheory.mem_bytes_at_window]
QED

Theorem for_immutable_word_live[local]:
  supported_word_type typ /\ evaluate_type tenv typ = SOME tv ==>
  type_memory_size tv = 32 /\ (!sec b j. ~mem_dead_bytes sec b tv j)
Proof
  strip_tac >>
  Cases_on `typ` >> gvs[supportedTypesTheory.supported_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supportedTypesTheory.supported_word_type_def,
    vyperValueTheory.evaluate_type_def,valueEncodingTheory.type_memory_size_def,
    immSectionDeadTheory.mem_dead_bytes_def] >>
  rename1 `BytesT b` >> Cases_on `b` >>
  gvs[supportedTypesTheory.supported_word_type_def,
    vyperValueTheory.evaluate_type_def,valueEncodingTheory.type_memory_size_def,
    immSectionDeadTheory.mem_dead_bytes_def]
QED

Theorem for_immutable_live_word_clean[local]:
  ghost_inv_at D lo d cenv cx ee G tn s /\ cenv.ce_is_ctor /\ a + 32 <= lo /\
  (!j. a <= j /\ j < a+32 ==>
    ~imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) j) ==>
  mem_word_taint tn.t_mem a = {}
Proof
  strip_tac >>
  simp[NoAsms,ptrDisciplineTheory.mem_word_taint_def,pred_setTheory.EXTENSION] >>
  gen_tac >> rewrite_tac[GSYM IMP_DISJ_THM] >> ntac 2 strip_tac >>
  `~imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo s.vs_memory) (a+x)` by
    (first_x_assum irule >> decide_tac) >>
  `a+x < lo` by decide_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >> strip_tac >>
  qpat_x_assum `!i. i < _ /\ _ ==> _` (qspec_then `a+x` mp_tac) >> simp[]
QED

Theorem for_array_immutable_element_resources_full:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ee /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  lookup_immutable cx ee src name = SOME (ArrayTV tv bd,ArrayV av) /\
  vs = array_elements (ArrayTV tv bd) av /\ k < LENGTH vs /\
  stmt_state_rel H ctx func cenv cx ee s /\ dead_lo_ok H D lo cenv cx /\
  ghost_inv_at D lo d cenv cx ee G tn s ==>
  type_memory_size tv = 32 /\
  (cenv.ce_is_ctor ==>
    w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*32):bytes32) + 32 <= lo /\
    mem_word_taint tn.t_mem
      (w2n (n2w (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + k*32):bytes32)) = {})
Proof
  strip_tac >>
  `supported_word_type typ` by metis_tac[for_immutable_array_decl] >>
  `type_memory_size tv = 32 /\ (!sec b j. ~mem_dead_bytes sec b tv j)` by
    metis_tac[for_immutable_word_live] >>
  simp[] >> strip_tac >>
  drule_all for_immutable_element_layout >> strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tv bd)` by
    metis_tac[for_immutable_array_eval_env] >>
  `lo = imm_len tops /\ cx_tops cx = tops` by
    fs[bodyPtrDefsTheory.dead_lo_ok_def,bodySimTheory.body_inv_def,gasContextTheory.cx_tops_def] >>
  `value_has_type (ArrayTV tv bd) (ArrayV av)` by metis_tac[for_immutable_prefix_value_typed] >>
  `LENGTH vs <= bound_length bd` by
    (Cases_on `bd` >> Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def,vyperValueOperationTheory.array_elements_def,
       vyperASTTheory.bound_length_def]) >>
  `off + type_memory_size (ArrayTV tv bd) < dimword (:256)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     qpat_x_assum `!src id ty. _` drule >> strip_tac >> gvs[]) >>
  qabbrev_tac `a = off + (case bd of Fixed _ => 0 | Dynamic _ => 32) + 32*k` >>
  `off <= a /\ a+32 <= off + type_memory_size (ArrayTV tv bd)` by
    (Cases_on `bd` >> gvs[Abbr `a`,valueEncodingTheory.type_memory_size_def,
      vyperASTTheory.bound_length_def]) >>
  `a < dimword (:256) /\ off < dimword (:256) /\ LENGTH vs < dimword (:256)` by
    (Cases_on `bd` >> gvs[valueEncodingTheory.type_memory_size_def,
       vyperASTTheory.bound_length_def] >> decide_tac) >>
  `!n. bd = Dynamic n ==> k < w2n (mem_word_at off (mem_bytes_at 0 lo s.vs_memory))` by
    (gen_tac >> disch_then SUBST_ALL_TAC >>
     `immutable_copy_read cenv.ce_is_ctor (n2w off) s = n2w (LENGTH vs)` by
       (drule_all for_immutable_prefix_read_observation >> simp[]) >>
     `off+32 <= lo` by
       (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
     `mem_word_at off (mem_bytes_at 0 lo s.vs_memory) = mem_word_at off s.vs_memory` by
       (irule for_immutable_section_header >> first_assum ACCEPT_TAC) >>
     gvs[immutableCopyExecutionTheory.immutable_copy_read_def,
       GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `k < bound_length bd` by decide_tac >>
  `!j. a <= j /\ j < a+32 ==>
    ~mem_dead_bytes (mem_bytes_at 0 lo s.vs_memory) off (ArrayTV tv bd) j` by
    metis_tac[for_immutable_scalar_payload_live] >>
  `!j. a <= j /\ j < a+32 ==>
    ~imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) j` by
    (gen_tac >> disch_then strip_assume_tac >> irule for_immutable_occurrence_live >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`name`,`off`,`post`,`pre`,`slot`,`ArrayTV tv bd`,`ArrayT typ bd`,`vis`] >>
     `off <= j /\ j < off + type_memory_size (ArrayTV tv bd)` by decide_tac >>
     metis_tac[]) >>
  `a+32 <= lo` by decide_tac >>
  `mem_word_taint tn.t_mem a = {}` by metis_tac[for_immutable_live_word_clean] >>
  gvs[Abbr `a`]
QED
