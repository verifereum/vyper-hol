(* Exact modular calldata address used by a dynamic registration head. *)
Theory defaultConcreteBytesRegistration
Ancestors defaultConcreteRegistrationDefs defaultConcreteRegistrationInit
  defaultBytesRegistration vyperCalldata abiDecoderContract words list rich_list
  defaultConcreteRegistrationCompiler defaultConcreteRegistrationResources
  defaultConcreteRegistrationOwners compileEnv moduleLowering finite_map pred_set arithmetic

Theorem default_registration_dynamic_decode:
  4 <= off /\ off < dimword (:256) /\ tv_abi_dynamic tv /\
  calldata_decode_args s.vs_call_ctx.cc_calldata [tv] (off-4) = SOME [x] ==>
  4 <= w2n ((4w + abi_decode_load CALLDATALOAD
    ((4w+n2w(off-4)):bytes32) s):bytes32) /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32)) = SOME x
Proof
  strip_tac >>
  `4 + (off-4) = off` by decide_tac >>
  `((4w + n2w (off-4)):bytes32) = n2w off` by
    (simp[word_add_n2w]) >>
  gvs[calldata_decode_args_def, AllCaseEqs()] >>
  gvs[abi_decode_load_def, abi_decode_source_def, cd_word_def,
       cd_bytes_def, word_add_def, w2n_n2w]
QED

Theorem default_registration_invariant_advance:
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce st off
    ((name,prim,dyn,sz,info)::rest) (tv::tvs) s G tn owners /\
  DROP (LENGTH owners) args = (name,ty)::tail /\
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st = (ce1,st1) /\
  default_registration_resources ctx fn site k st1 t u /\
  default_registration_entry_frame initial t /\
  LIST_REL (default_registration_owner fn ce1 st1 t H u)
    (ZIP (TAKE (LENGTH (owners++[owner])) args,
          TAKE (LENGTH (owners++[owner])) all_tvs)) (owners++[owner]) ==>
  default_registration_invariant tops cx ctx fn site k initial ce0 start
    args all_tvs specs cef sa ce1 st1 (off+sz) rest tvs
    t H u (owners++[owner])
Proof
  strip_tac >> drule_all default_registration_compiler_advance >> strip_tac >>
  `default_registration_slot tops ce ((name,ty),tv) (name,prim,dyn,sz,info)` by
    fs[default_registration_invariant_def] >>
  `sz = tv_abi_size tv` by fs[default_registration_slot_def] >>
  fs[default_registration_invariant_def, GSYM ADD1, DROP_SUC, TAKE_SUC] >>
  qpat_x_assum `tv::tvs = DROP _ _` (assume_tac o GSYM) >>
  qpat_x_assum `(_::rest) = DROP _ _` (assume_tac o GSYM) >>
  `SUC (LENGTH owners) <= LENGTH all_tvs` by
    (qpat_x_assum `DROP _ all_tvs = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  qpat_assum `ce1 = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `DROP _ all_tvs = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `DROP _ specs = _` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [TAKE_def, DROP_def, MAP, SUM_APPEND, SUM] >>
  pure_rewrite_tac[GSYM ADD_ASSOC] >>
  qpat_assum `LIST_REL (default_registration_owner fn _ st1 t H u) _ _` mp_tac >>
  qpat_assum `ce1 = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `DROP _ args = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `DROP _ all_tvs = _` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [TAKE_def, DROP_def] >> disch_tac >>
  `fn_has_code st1 sa fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_x_assum `compile_register_positional_args ce1 rest _ st1 = _` mp_tac >>
     qpat_x_assum `off = _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[] >>
     `SUM (MAP tv_abi_size (TAKE (LENGTH owners) all_tvs)) + tv_abi_size tv + 4 =
      SUM (MAP tv_abi_size (TAKE (LENGTH owners) all_tvs)) + 4 + tv_abi_size tv`
       by decide_tac >> metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qpat_assum `ce1 = _` SUBST1_TAC >>
  qpat_x_assum `ce.ce_module = NONE` SUBST_ALL_TAC >>
  fs[loweringStateRelDefsTheory.storage_vars_rel_def,
     loweringStateRelDefsTheory.transient_vars_rel_def,
     immutableRelationTheory.immutable_section_layout_def]
QED

Theorem default_registration_bytes_head:
  EVERY (\tv. type_memory_size tv < dimword (:256)) all_tvs /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  venomInst$lookup_function fn.fn_name ctx.ctx_functions = SOME fn ==>
  !ce st off name dyn sz info rest tv tvs s G tn owners ce1 st1 x.
    4 <= off /\ ~s.vs_halted /\
    default_registration_invariant tops cx ctx fn site k initial ce0 start
      args all_tvs specs cef sa ce st off
      ((name,F,dyn,sz,info)::rest) (tv::tvs) s G tn owners /\
    compile_register_positional_args ce [(name,F,dyn,sz,info)] off st = (ce1,st1) /\
    calldata_decode_args initial.vs_call_ctx.cc_calldata [tv] (off-4) = SOME [x] ==>
    sz = tv_abi_size tv /\
    ?t H1 u1 owner.
      (\(v,dst,p,id). v) owner = x /\ ~t.vs_halted /\
      default_registration_invariant tops cx ctx fn site k initial ce0 start
        args all_tvs specs cef sa ce1 st1 (off+sz) rest tvs
        t H1 u1 (owners++[owner]) /\
      gas_path_mem ctx fn s 0 (OK t) /\
      (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,H1,u1)) /\
      (!D. (!fuel. ptr_safe_run D 0 fuel ctx fn PG H1 u1 t) ==>
        !fuel. ptr_safe_run D 0 fuel ctx fn PG G tn s)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?ty tail. DROP (LENGTH owners) args = (name,ty)::tail` by
    (fs[default_registration_invariant_def] >>
     `LENGTH (DROP (LENGTH owners) args) = LENGTH (tv::tvs)` by
       metis_tac[LENGTH_DROP] >>
     Cases_on `DROP (LENGTH owners) args` >- fs[] >>
     PairCases_on `h` >> gvs[default_registration_slot_def]) >>
  drule_all default_registration_compiler_advance >> strip_tac >>
  `default_registration_slot tops ce ((name,ty),tv) (name,F,dyn,sz,info)` by
    fs[default_registration_invariant_def] >>
  fs[default_registration_slot_def] >> fs[] >>
  `is_bytestring_type ty /\ tv_abi_dynamic tv /\ dyn` by suspend "type" >>
  `type_memory_size tv < dimword (:256)` by
    (`MEM tv all_tvs` by
       (irule MEM_DROP_IMP >> qexists `LENGTH owners` >>
        fs[default_registration_invariant_def] >>
        qpat_x_assum `tv::tvs = DROP _ _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
     fs[EVERY_MEM]) >>
  `is_abi_dynamic ce.ce_struct_fields ty` by metis_tac[] >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    default_registration_singleton_stages >> simp[] >> strip_tac >>
  `fn_has_code st first fn /\ fn_has_code first st1 fn` by suspend "code" >>
  `4 <= w2n ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32) /\
   cd_decode F s.vs_call_ctx.cc_calldata tv
      (w2n ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32)) = SOME x` by suspend "decode" >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (fs[default_registration_invariant_def, default_registration_resources_def] >>
     Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> fs[] >> metis_tac[prim_recTheory.LESS_REFL]) >>
  `alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
   k + unit_alloca_budget ctx < dimword (:256) /\
   allocas_from 0 s /\ 0 <= s.vs_alloca_next /\ alloca_history fn s /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[default_registration_invariant_def, default_registration_resources_def] >>
  drule_all default_bytes_registration_step_footprint >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  suspend "finish"
QED

Resume default_registration_bytes_head[type]:
  `is_bytestring_type ty` by metis_tac[] >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  Cases_on `b` >> gvs[is_bytestring_type_def,
    abiDecoderCoherenceTheory.abi_decoder_coherent_string_iff,
    tv_abi_dynamic_def, is_abi_dynamic_def] >>
  Cases_on `b'` >> gvs[is_bytestring_type_def,
    abiDecoderCoherenceTheory.abi_decoder_coherent_bytes_iff,
    tv_abi_dynamic_def, is_abi_dynamic_def]
QED

Resume default_registration_bytes_head[code]:
  drule defaultBytesGuardPreludeTheory.default_bytes_guard_shape >> strip_tac >>
  `cs_extends after_src first` by
    (fs[exprLoweringPropsTheory.same_blocks_def, emitHelperPropsTheory.inst_extends_def] >>
     simp[cs_extends_def] >> qexists `[]` >> simp[]) >>
  `cs_extends st after_src` by
    (drule loweringHaltTheory.compile_alloc_buffer_extends >> strip_tac >>
     qpat_assum `emit_op ADD _ allocated = _`
       (mp_then Any strip_assume_tac ctorDeployMemoryRunPtrPrefixRegisterAddressTheory.prefix_register_address_emit_shape) >>
     qpat_assum `emit_op CALLDATALOAD _ after_head = _`
       (mp_then Any strip_assume_tac ctorDeployMemoryRunPtrPrefixRegisterAddressTheory.prefix_register_address_emit_shape) >>
     qpat_assum `emit_op ADD _ after_load = _`
       (mp_then Any strip_assume_tac ctorDeployMemoryRunPtrPrefixRegisterAddressTheory.prefix_register_address_emit_shape) >>
     metis_tac[cs_extends_trans]) >>
  drule abiDecoderAppendTheory.cs_extends_abi_decode >> strip_tac >>
  fs[default_registration_invariant_def] >>
  metis_tac[cs_extends_trans, fragExecTheory.fn_has_code_split]
QED

Resume default_registration_bytes_head[decode]:
  `off < dimword (:256)` by
    (fs[default_registration_invariant_def] >>
     `SUM (MAP tv_abi_size (TAKE (LENGTH owners) all_tvs)) <=
      SUM (MAP tv_abi_size all_tvs)` by
       (qspecl_then [`LENGTH owners`, `all_tvs:type_value list`]
          (mp_tac o Q.AP_TERM `SUM o MAP tv_abi_size`) TAKE_DROP >>
        simp[MAP_APPEND, SUM_APPEND] >> decide_tac) >>
     fs[LENGTH_DROP, dimword_def] >> decide_tac) >>
  irule default_registration_dynamic_decode >>
  fs[default_registration_invariant_def, default_registration_entry_frame_def] >>
  gvs[]
QED

Resume default_registration_bytes_head[finish]:
  `p'' = p` by
    (qpat_x_assum `(ce with ce_vars updated_by _) = (ce with ce_vars updated_by _)`
       (mp_tac o Q.AP_TERM `\c. FLOOKUP c.ce_vars name`) >>
     simp[default_registration_vars_update, FLOOKUP_UPDATE]) >>
  fs[] >>
  `st.cs_next_var <= st1.cs_next_var /\ st.cs_next_id <= st1.cs_next_id` by
    metis_tac[calldataRegistrationExecTheory.registration_compile_counters] >>
  `?ins. MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
    ins.inst_operands = [Lit (n2w (type_memory_size tv))] /\ ins.inst_outputs = [p] /\
    ins.inst_id = st.cs_next_id /\ st.cs_next_id < st1.cs_next_id` by
    suspend "allocation" >>
  `default_registration_resources ctx fn site k st1 out u` by
    (irule default_registration_resources_transport >>
     simp[] >> qexistsl [`s`,`st`,`tn`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[] >>
         qexistsl [`ins`,`n2w (type_memory_size tv):bytes32`] >> simp[w2n_n2w]) >>
     conj_tac
     >- (rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[]) >>
     fs[default_registration_invariant_def]) >>
  `default_registration_owner fn ce1 st1 out H u ((name,ty),tv)
    (x,Var p,s.vs_alloca_next,st.cs_next_id)` by
    (irule default_registration_bytes_owner >> simp[] >> metis_tac[]) >>
  `default_registration_entry_frame initial out` by
    (irule default_registration_entry_frame_transport >>
     qexistsl [`out.vs_allocas`,`LENGTH st1.cs_current_insts`,
       `out.vs_memory`,`out.vs_alloca_next`,`s`,`out.vs_vars`] >>
     fs[default_registration_invariant_def] >> metis_tac[]) >>
  `LIST_REL (default_registration_owner fn ce1 st1 out H u)
    (ZIP (TAKE (LENGTH (owners++[(x,Var p,s.vs_alloca_next,st.cs_next_id)])) args,
          TAKE (LENGTH (owners++[(x,Var p,s.vs_alloca_next,st.cs_next_id)])) all_tvs))
    (owners++[(x,Var p,s.vs_alloca_next,st.cs_next_id)])` by suspend "owners" >>
  qexistsl [`out`,`H`,`u`,`(x,Var p,s.vs_alloca_next,st.cs_next_id)`] >>
  simp[] >> irule default_registration_invariant_advance >>
  gvs[] >> metis_tac[]
QED

Resume default_registration_bytes_head[allocation]:
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
  `cs_extends st allocated` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends allocated first /\ cs_extends allocated st1` by suspend "allocated_suffix" >>
  `fn_has_code st allocated fn` by
    (irule (cj 1 fragExecTheory.fn_has_code_split) >> simp[] >> qexists `first` >> simp[]) >>
  `fn_has_code sx allocated fn` by
    (qspecl_then [`st`,`sx`,`allocated`,`fn`] mp_tac fragExecTheory.fn_has_code_split >>
     impl_tac >- metis_tac[] >> simp[]) >>
  drule_all loweringHaltTheory.emit_inst_fn_member >> strip_tac >>
  qexists `mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [p]` >>
  `allocated.cs_next_id = st.cs_next_id + 1` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_inst_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >> strip_tac >> gvs[]) >>
  `allocated.cs_next_id <= st1.cs_next_id` by suspend "allocation_id" >>
  gvs[venomInstTheory.mk_inst_def] >> decide_tac
QED

Resume default_registration_bytes_head[owners]:
  irule default_registration_owners_advance >>
  (conj_tac >- fs[default_registration_invariant_def]) >>
  conj_tac
  >- (qexistsl [`G`,`ce`,`type_memory_size tv`,`s`,`st`,`tn`] >>
      fs[default_registration_invariant_def] >> conj_tac
      >- (rpt strip_tac >> fs[default_registration_owner_def] >>
          `name' <> name` by (spose_not_then assume_tac >> gvs[]) >>
          simp[FLOOKUP_UPDATE] >> metis_tac[prim_recTheory.LESS_REFL]) >>
      rpt gen_tac >> disch_tac >> conj_tac
      >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
      qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` irule >>
      fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def,
         loweringStateRelDefsTheory.not_fresh_at_def]) >>
  qexistsl [`tvs`,`(name,ty)`,`tail`,`tv`] >>
  fs[default_registration_invariant_def]
QED

Resume default_registration_bytes_head[allocated_suffix]:
  `cs_extends allocated after_head` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `cs_extends after_head after_load` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `cs_extends after_load after_src` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `cs_extends after_src first` by
    (mp_tac (Q.SPECL [`CALLDATALOAD`,`src`,`Lit 4w`,`after_src`]
      externalEntryShapeTheory.compile_abi_arg_ptr_guard_labels) >> simp[]) >>
  `cs_extends first st1` by
    metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_compile_abi_decode,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  metis_tac[cs_extends_trans]
QED
Resume default_registration_bytes_head[allocation_id]:
  `allocated.cs_next_id <= after_head.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `after_head.cs_next_id <= after_load.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `after_load.cs_next_id <= after_src.cs_next_id` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  `after_src.cs_next_id <= first.cs_next_id` by
    (qpat_x_assum `compile_abi_arg_ptr_guard _ _ _ _ = _` mp_tac >>
     simp[moduleLoweringTheory.compile_abi_arg_ptr_guard_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >> strip_tac >> gvs[]) >>
  `first.cs_next_id <= st1.cs_next_id` by
    metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_compile_abi_decode,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  decide_tac
QED

Finalise default_registration_bytes_head
