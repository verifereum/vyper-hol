(* Static charge of the literal ALLOCAs emitted for stack parameters. *)
Theory bodyIntCallFamCallIntEntryCharge
Ancestors
  intCallCallee exprLoweringProps moduleLowering compileEnv compileVyper context entryStateRel
  finite_map list words emitHelper venomInst rich_list removeUnusedSsaProofs

Theorem materialize_internal_params_charge:
  !caps ce a ce' b.
    materialize_internal_params ce caps a = (ce',b) /\
    ALL_DISTINCT (MAP FST caps) /\
    (!n stk op off sz. MEM (n,stk,op) caps /\
      FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==> sz < dimword (:256)) ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) b.cs_current_insts)) =
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) a.cs_current_insts)) +
      internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
Proof
  Induct
  >- simp[materialize_internal_params_def, comp_return_def, internal_stack_size_def] >>
  PairCases >> rpt gen_tac >>
  simp[Once materialize_internal_params_def, internal_stack_size_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >> simp[] >~ [`emit_op _ _`]
      >- (simp[emit_op_def, emit_void_def, comp_bind_def,
               comp_ignore_bind_def, comp_return_def, fresh_id_def,
               fresh_var_def, emit_def] >> strip_tac >>
          first_x_assum drule >>
          simp[mat_tail_stack_size, FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND,
               mk_inst_def, alloca_lit_size_def] >>
          (impl_tac >- (rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[])) >>
          `n0 < dimword (:256)` by metis_tac[] >>
          simp[] >> decide_tac) >>
      strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >>
  simp[mat_tail_stack_size] >>
  (impl_tac >- (rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[])) >>
  simp[]
QED

Theorem current_insts_alloca_charge_le_frame:
  !a b func ctx.
    fn_has_code a b func /\ MEM func ctx.ctx_functions ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) b.cs_current_insts)) <=
    unit_alloca_frame ctx
Proof
  rpt gen_tac >> simp[fragExecTheory.fn_has_code_def] >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
  gvs[IS_PREFIX_APPEND] >>
  qpat_x_assum `MEM func _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  qpat_x_assum `MEM bb _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  simp[unit_alloca_frame_def, fn_insts_def, fn_insts_blocks_flat,
       FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND] >>
  decide_tac
QED

Theorem materialize_internal_params_charge_le_frame:
  !caps ce a ce' b func ctx.
    materialize_internal_params ce caps a = (ce',b) /\
    ALL_DISTINCT (MAP FST caps) /\
    (!n stk op off sz. MEM (n,stk,op) caps /\
      FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==> sz < dimword (:256)) /\
    fn_has_code a b func /\ MEM func ctx.ctx_functions ==>
    internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) <=
      unit_alloca_frame ctx
Proof
  rpt gen_tac >> strip_tac >>
  drule_all materialize_internal_params_charge >>
  drule_all current_insts_alloca_charge_le_frame >> decide_tac
QED

Theorem internal_entry_materialize_segment:
  !ce params rb ctor il rt s ce2 rpc imm t.
    compile_internal_function_entry ce params rb ctor il rt s =
      ((ce2,rpc,imm),t) ==>
    ?caps ce1 a b.
      materialize_internal_params ce1 caps a = (ce2,b) /\
      ce1.ce_vars = ce.ce_vars /\
      MAP (\c. (FST c,FST (SND c))) caps = params /\
      MAP FST caps = MAP FST params /\
      isPREFIX b.cs_current_insts t.cs_current_insts
Proof
  rpt gen_tac >>
  simp[compile_internal_function_entry_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule (SRULE [comp_ignore_bind_def] internal_scratch_shape) >> strip_tac >>
  qpat_x_assum `compile_internal_entry_prefix _ _ _ _ = _` mp_tac >>
  simp[compile_internal_entry_prefix_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  PairCases_on `pr` >> gvs[] >>
  drule internal_param_decls_projection >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem internal_entry_stack_charge_le_frame:
  !ce params rb ctor il rt s ce2 rpc imm t func ctx.
    compile_internal_function_entry ce params rb ctor il rt s =
      ((ce2,rpc,imm),t) /\
    ALL_DISTINCT (MAP FST params) /\
    (!n off sz. FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==>
      sz < dimword (:256)) /\
    fn_has_code s t func /\ MEM func ctx.ctx_functions ==>
    internal_stack_size ce params <= unit_alloca_frame ctx
Proof
  rpt gen_tac >> strip_tac >>
  drule internal_entry_materialize_segment >> strip_tac >>
  drule materialize_internal_params_charge >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  strip_tac >>
  drule internal_stack_size_vars >>
  disch_then (qspec_then `params` assume_tac) >>
  drule_all current_insts_alloca_charge_le_frame >>
  gvs[IS_PREFIX_APPEND, FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND] >>
  decide_tac
QED

Theorem allocate_args_memloc_size_bound:
  !args sft off vars bound n p sz.
    EVERY (\a. type_mem_bytes sft (SND a) < bound) args /\
    (!n p sz. FLOOKUP vars n = SOME (MemLoc p sz) ==> sz < bound) /\
    FLOOKUP (FST (allocate_args sft args off vars)) n = SOME (MemLoc p sz) ==>
    sz < bound
Proof
  Induct >- (simp[allocate_args_def] >> metis_tac[]) >>
  PairCases >> rpt gen_tac >>
  simp[allocate_args_def] >> strip_tac >>
  qpat_x_assum `!sft off vars bound n p sz. _`
    (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then irule >> simp[] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]
QED

Theorem build_compile_env_memloc_size_bound:
  !tops vis mut fname args ret body ut bound n p sz.
    EVERY (\a. type_memory_bytes
      (build_compile_env tops vis mut fname args ret body ut) (SND a) < bound) args /\
    FLOOKUP (build_compile_env tops vis mut fname args ret body ut).ce_vars n =
      SOME (MemLoc p sz) ==> sz < bound
Proof
  rpt gen_tac >>
  simp[GSYM type_mem_bytes_type_memory_bytes, build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule allocate_args_memloc_size_bound >>
  disch_then (qspecl_then [`0`, `FEMPTY`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem package_internal_fn_memloc_size_bound:
  !tops ut keys ctor il mut nr rr name args dflts ret body
    lbl ce params rb nr' key ut' view ctor' il' body' rt n off sz.
    package_internal_fn tops ut keys ctor il
      (mut,nr,rr,name,args,dflts,ret,body) =
      (lbl,ce,params,rb,nr',key,ut',view,ctor',il',body',rt) /\
    fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,body) /\
    FLOOKUP ce.ce_vars n = SOME (MemLoc off sz) ==>
    sz < dimword (:256)
Proof
  rpt gen_tac >>
  simp[package_internal_fn_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[] >>
  `EVERY (\a. type_memory_bytes
    (build_compile_env tops Internal mut name args ret body' ut) (SND a) < 2 ** 64)
    args` by
    (qpat_x_assum `fn_allocs_ok _ _` mp_tac >>
     simp[fn_allocs_ok_def, GSYM type_mem_bytes_type_memory_bytes,
          build_compile_env_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> simp[]) >>
  drule_all build_compile_env_memloc_size_bound >>
  simp[dimword_def] >> decide_tac
QED

Theorem package_internal_fn_entry_stack_charge_le_frame:
  !tops ut keys ctor il mut nr rr name args dflts ret body
    lbl ce params rb nr' key ut' view ctor' il' body' rt
    s ce2 rpc imm t func ctx.
    package_internal_fn tops ut keys ctor il
      (mut,nr,rr,name,args,dflts,ret,body) =
      (lbl,ce,params,rb,nr',key,ut',view,ctor',il',body',rt) /\
    fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,body) /\
    ALL_DISTINCT (MAP FST args) /\
    compile_internal_function_entry ce params rb ctor' il' rt s =
      ((ce2,rpc,imm),t) /\
    fn_has_code s t func /\ MEM func ctx.ctx_functions ==>
    internal_stack_size ce params <= unit_alloca_frame ctx
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP FST params)` by
    (qpat_x_assum `package_internal_fn _ _ _ _ _ _ = _` mp_tac >>
     simp[package_internal_fn_def] >> strip_tac >> gvs[] >>
     simp[MAP_ZIP, LENGTH_compute_pass_via_stack]) >>
  irule internal_entry_stack_charge_le_frame >>
  rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[package_internal_fn_memloc_size_bound]
QED
