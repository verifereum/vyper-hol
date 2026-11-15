(* Exact word callback for the concrete registration fold. *)
Theory defaultConcreteWordHead
Ancestors defaultConcreteRegistrationDefs defaultConcreteRegistrationInit
  defaultConcreteRegistrationCompiler defaultConcreteRegistrationResources
  defaultConcreteRegistrationOwners defaultWordRegistration abiDecoderCoherence
  calldataSourceSize calldataSourceDecisions calldataRegistrationExec entryArgPtrs freshWrites
  exprLowering exprLoweringProps compileEnv moduleLowering list rich_list finite_map words pred_set arithmetic

Theorem default_registration_word_head:
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  venomInst$lookup_function fn.fn_name ctx.ctx_functions = SOME fn ==>
  !ce st off name dyn sz info rest tv tvs s G tn owners ce1 st1 x.
    4 <= off /\ ~s.vs_halted /\
    default_registration_invariant tops cx ctx fn site k initial ce0 start
      args all_tvs specs cef sa ce st off
      ((name,T,dyn,sz,info)::rest) (tv::tvs) s G tn owners /\
    compile_register_positional_args ce [(name,T,dyn,sz,info)] off st = (ce1,st1) /\
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
  `default_registration_slot tops ce ((name,ty),tv) (name,T,dyn,sz,info)` by
    fs[default_registration_invariant_def] >>
  fs[default_registration_slot_def] >>
  `(?clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp) /\
   type_memory_size tv = 32` by
    (drule abi_decoder_coherent_header >>
     simp[abi_decoder_header_def] >> strip_tac >>
     Cases_on `ty` >> gvs[is_word_type_def, type_to_abi_dec_info_def,
       type_memory_bytes_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_word_type_def, type_to_abi_dec_info_def, type_memory_bytes_def,
       AllCaseEqs()] >>
     Cases_on `b` >> gvs[is_word_type_def, type_to_abi_dec_info_def,
       type_memory_bytes_def]) >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    default_registration_singleton_stages >> simp[] >>
  strip_tac >>
  `cs_extends st allocated` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends allocated after_head` by metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `cs_extends after_head st1` by metis_tac[abiDecoderAppendTheory.cs_extends_abi_decode] >>
  `fn_has_code st after_head fn /\ fn_has_code after_head st1 fn` by
    (fs[default_registration_invariant_def] >>
     metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
  `~tv_abi_dynamic tv` by
    (drule calldataSourceDecisionsTheory.calldata_coherent_offset >>
     simp[abiEncoderTheory.dec_info_needs_offset_def]) >>
  `cd_decode F s.vs_call_ctx.cc_calldata tv
     (w2n ((4w + n2w (off-4)):bytes32)) = SOME x` by
    suspend "decode" >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (fs[default_registration_invariant_def, default_registration_resources_def] >>
     Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> fs[] >> metis_tac[prim_recTheory.LESS_REFL]) >>
  `compile_abi_decode_to_buf buf.buf_operand head CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) after_head = ((),st1)` by simp[] >>
  `alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
   k + unit_alloca_budget ctx < dimword (:256) /\
   allocas_from 0 s /\ 0 <= s.vs_alloca_next /\ alloca_history fn s /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[default_registration_invariant_def, default_registration_resources_def] >>
  drule_all default_word_registration_step_footprint >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  `p'' = p` by
    (qpat_x_assum `(ce with ce_vars updated_by _) = (ce with ce_vars updated_by _)`
       (mp_tac o Q.AP_TERM `\c. FLOOKUP c.ce_vars name`) >>
     simp[default_registration_vars_update, FLOOKUP_UPDATE]) >>
  fs[] >>
  `st.cs_next_var <= st1.cs_next_var /\ st.cs_next_id <= st1.cs_next_id` by
    metis_tac[registration_compile_counters] >>
  `?ins. MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
    ins.inst_operands = [Lit 32w] /\ ins.inst_outputs = [p] /\
    ins.inst_id = st.cs_next_id /\ st.cs_next_id < st1.cs_next_id` by
    suspend "allocation" >>
  `default_registration_resources ctx fn site k st1 out u` by
    suspend "resources" >>
  `default_registration_owner fn ce1 st1 out H u ((name,ty),tv)
    (x,Var p,s.vs_alloca_next,st.cs_next_id)` by
    (irule default_registration_bytes_owner >> simp[] >> metis_tac[]) >>
  qexistsl [`out`,`H`,`u`,`(x,Var p,s.vs_alloca_next,st.cs_next_id)`] >>
  simp[] >> suspend "invariant"
QED

Resume default_registration_word_head[decode]:
  markerLib.RESUME_TAC >>
  `off < dimword (:256)` by
    (fs[default_registration_invariant_def] >>
     `SUM (MAP tv_abi_size all_tvs) =
       SUM (MAP tv_abi_size (TAKE (LENGTH owners) all_tvs)) +
       SUM (MAP tv_abi_size (DROP (LENGTH owners) all_tvs))` by
       metis_tac[TAKE_DROP, MAP_APPEND, SUM_APPEND] >>
     `tv_abi_size tv = 32` by
       (drule calldata_coherent_embedded_size >>
        Cases_on `ty` >> gvs[is_word_type_def, abi_embedded_static_size_def,
          is_abi_dynamic_def, abi_static_size_def] >>
        Cases_on `b` >> gvs[is_word_type_def, abi_embedded_static_size_def,
          is_abi_dynamic_def, abi_static_size_def, AllCaseEqs()] >>
        Cases_on `b'` >> gvs[is_word_type_def, abi_embedded_static_size_def,
          is_abi_dynamic_def, abi_static_size_def]) >>
     qpat_x_assum `tv::tvs = DROP _ _` (mp_tac o GSYM) >>
     strip_tac >> fs[] >> decide_tac) >>
  `w2n ((4w + n2w (off-4)):bytes32) = off` by
    (`4 + (off-4) = off` by decide_tac >>
     simp[word_add_n2w, w2n_n2w]) >>
  `4 + (off-4) = off` by decide_tac >>
  `default_registration_entry_frame initial s` by
    fs[default_registration_invariant_def] >>
  fs[default_registration_entry_frame_def,
     vyperCalldataTheory.calldata_decode_args_def, AllCaseEqs()]
QED

Resume default_registration_word_head[allocation]:
  markerLib.RESUME_TAC >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
  `fn_has_code st allocated fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `fn_has_code sx allocated fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all loweringHaltTheory.emit_inst_fn_member >> strip_tac >>
  qexists `mk_inst st.cs_next_id ALLOCA [Lit 32w] [p]` >>
  `allocated.cs_next_id = st.cs_next_id + 1` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_inst_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >> strip_tac >> gvs[]) >>
  `allocated.cs_next_id <= st1.cs_next_id` by
    (`after_head.cs_next_id <= st1.cs_next_id` by
       (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ (DecPrimWord _) _ = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[cj 1 ci_mono_compile_abi_decode, ci_mono_def, pairTheory.SND]) >>
     `allocated.cs_next_id <= after_head.cs_next_id` by
       (qpat_x_assum `emit_op ADD _ allocated = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND]) >> decide_tac) >>
  gvs[venomInstTheory.mk_inst_def] >> decide_tac
QED

Resume default_registration_word_head[resources]:
  markerLib.RESUME_TAC >>
  (irule default_registration_resources_transport >>
   simp[] >> qexistsl [`s`,`st`,`tn`] >> simp[] >>
   conj_tac
   >- (rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[] >>
       qexistsl [`ins`,`32w`] >> simp[]) >>
   conj_tac
   >- (rpt strip_tac >> Cases_on `id = st.cs_next_id` >> gvs[]) >>
   fs[default_registration_invariant_def])
QED

Resume default_registration_word_head[invariant]:
  markerLib.RESUME_TAC >>
  (`default_registration_entry_frame initial out` by
     (irule default_registration_entry_frame_transport >>
      qexistsl [`out.vs_allocas`,`LENGTH st1.cs_current_insts`,
        `out.vs_memory`,`out.vs_alloca_next`,`s`,`out.vs_vars`] >>
      fs[default_registration_invariant_def] >> metis_tac[]) >>
   `LIST_REL (default_registration_owner fn ce1 st1 out H u)
     (ZIP (TAKE (LENGTH (owners++[(x,Var p,s.vs_alloca_next,st.cs_next_id)])) args,
           TAKE (LENGTH (owners++[(x,Var p,s.vs_alloca_next,st.cs_next_id)])) all_tvs))
     (owners++[(x,Var p,s.vs_alloca_next,st.cs_next_id)])` by
     suspend "owners" >>
   fs[default_registration_invariant_def, GSYM ADD1, DROP_SUC, TAKE_SUC] >>
   qpat_x_assum `tv::tvs = DROP _ _` (assume_tac o GSYM) >>
   qpat_x_assum `(_::rest) = DROP _ _` (assume_tac o GSYM) >>
   `SUC (LENGTH owners) <= LENGTH all_tvs` by
     (qpat_x_assum `DROP _ all_tvs = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
      simp[LENGTH_DROP] >> decide_tac) >>
   qpat_assum `ce1 = _` (fn th => once_rewrite_tac[GSYM th]) >>
   qpat_x_assum `out = _` kall_tac >>
   qpat_assum `DROP _ all_tvs = _` (fn th => rewrite_tac[th]) >>
   qpat_assum `DROP _ specs = _` (fn th => rewrite_tac[th]) >>
   simp_tac (srw_ss()) [TAKE_def, DROP_def, MAP, SUM_APPEND, SUM] >>
   pure_rewrite_tac[GSYM ADD_ASSOC] >>
   qpat_assum `LIST_REL (default_registration_owner fn ce1 st1 out H u) _ _`
     (mp_tac) >>
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
   conj_tac
   >- (`MEM (name,ty) args` by
         (irule MEM_DROP_IMP >> qexists `LENGTH owners` >> simp[]) >>
       `MEM name (MAP FST args)` by (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
       irule pred_setTheory.ABSORPTION_RWT >> simp[]) >>
   conj_tac >- (first_assum ACCEPT_TAC) >>
   qpat_assum `ce1 = _` SUBST1_TAC >>
   qpat_x_assum `ce.ce_module = NONE` SUBST_ALL_TAC >>
   fs[loweringStateRelDefsTheory.storage_vars_rel_def,
      loweringStateRelDefsTheory.transient_vars_rel_def,
      immutableRelationTheory.immutable_section_layout_def])
QED

Resume default_registration_word_head[owners]:
  markerLib.RESUME_TAC >>
  (irule default_registration_owners_advance >>
   (conj_tac >- fs[default_registration_invariant_def]) >>
   conj_tac
   >- (qexistsl [`G`,`ce`,`32`,`s`,`st`,`tn`] >>
       fs[default_registration_invariant_def] >> conj_tac
       >- (rpt strip_tac >>
           fs[default_registration_owner_def] >>
           `name' <> name` by (spose_not_then assume_tac >> gvs[]) >>
           simp[FLOOKUP_UPDATE] >>
           metis_tac[prim_recTheory.LESS_REFL]) >>
       rpt gen_tac >> disch_tac >> conj_tac
       >- metis_tac[not_fresh_at_mono] >>
       qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` irule >>
       fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def,
          loweringStateRelDefsTheory.not_fresh_at_def]) >>
   qexistsl [`tvs`,`(name,ty)`,`tail`,`tv`] >>
   fs[default_registration_invariant_def])
QED

Finalise default_registration_word_head

