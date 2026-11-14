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

Theorem default_registration_bytes_owner:
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var dst) (type_memory_size tv)) /\
  val_wf tv x /\ val_in_memory tv x s.vs_alloca_next t.vs_memory /\
  eval_operand (Var dst) t = SOME (n2w s.vs_alloca_next) /\
  ptr_covers H u dst t (type_memory_size tv) /\
  FLOOKUP t.vs_allocas st.cs_next_id =
    SOME (s.vs_alloca_next,type_memory_size tv) /\
  t.vs_alloca_next = s.vs_alloca_next + type_memory_size tv /\
  s.vs_alloca_next + type_memory_size tv < dimword (:256) /\
  st.cs_next_id < st1.cs_next_id /\ not_fresh_at st1 dst /\
  MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
  ins.inst_outputs = [dst] /\ ins.inst_id = st.cs_next_id ==>
  default_registration_owner fn ce st1 t H u ((name,ty),tv)
    (x,Var dst,s.vs_alloca_next,st.cs_next_id)
Proof
  simp[default_registration_owner_def] >> strip_tac >>
  qexists `ins` >> simp[]
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
