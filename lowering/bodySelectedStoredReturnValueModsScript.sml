(* Interpret the selected return registers in their placed caller buffer. *)
Theory bodySelectedStoredReturnValueMods
Ancestors
  bodyFullIntCallReturnValue bodyFullPostsMods typedMemoryCopy typedStructMetadata
  vyperTypeValues vyperTypeExprSoundness vyperTypeABI intCallResult
  exprSimProps exprSimHyps stmtSimReturn valueTypingMemoryProps
  compileEnv loweringStateRelDefs vyperValue list rich_list pair finite_map
  exprLowering loweringPosts exprBodyPreProps exprSimHypsDefs vyperTypeSystem
  exprSimMemDefs bodyPtrDefs ptrDiscipline venomState vyperState words valueEncoding
  context[qualified,ignore_grammar]

Theorem evaluated_word_members[local]:
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
  EVERY is_word_type tys ==>
  EVERY (\tv. ?ty. is_word_type ty /\ evaluate_type tenv ty = SOME tv) tvs
Proof
  qid_spec_tac `tvs` >> Induct_on `tys` >> Cases_on `tvs` >> simp[] >>
  metis_tac[]
QED

Theorem positive_result_not_bytes[local]:
  0 < returns_stack_count sft ret ==> ~is_bytestring_type ret
Proof
  Cases_on `ret` >> simp[returns_stack_count_def, is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[returns_stack_count_def, is_bytestring_type_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_bytestring_type_def, is_word_type_def]
QED

Theorem positive_result_abi_layout[local]:
  sfields_tenv_consistent sf tenv /\ evaluate_type tenv ret = SOME tv /\
  nret = returns_stack_count (\n. MAP (FST o SND) (get_struct_fields sf n)) ret /\
  0 < nret ==>
  type_memory_size tv = 32 * nret /\
  ((?ty. is_word_type ty /\ evaluate_type tenv ty = SOME tv) \/
   (?tvs. tv = TupleTV tvs /\
          EVERY (\etv. ?ty. is_word_type ty /\ evaluate_type tenv ty = SOME etv) tvs) \/
   (?fields. tv = StructTV fields /\
       EVERY (\etv. ?ty. is_word_type ty /\ evaluate_type tenv ty = SOME etv)
         (MAP SND fields)))
Proof
  strip_tac >> Cases_on `is_word_type ret`
  >- (`nret = 1` by (Cases_on `ret` >> gvs[returns_stack_count_def, is_word_type_def]) >>
      drule_all word_tv_memory_size >> simp[] >> metis_tac[]) >>
  Cases_on `ret` >> gvs[returns_stack_count_def]
  >~ [`evaluate_type tenv (TupleT tys) = SOME tv`] >-
    (drule evaluate_type_TupleT_cases >> strip_tac >>
     gvs[tuple_like_stack_count_def] >> IF_CASES_TAC >> gvs[] >>
     drule_all word_tuple_size >> simp[type_memory_size_def] >>
     metis_tac[evaluated_word_members]) >>
  rename1 `evaluate_type tenv (StructT key) = SOME tv` >>
  drule evaluate_type_struct_fields >> strip_tac >> gvs[] >>
  `MAP (FST o SND) (get_struct_fields sf (nsid_to_string key)) = MAP SND args` by
    (qpat_assum `sfields_tenv_consistent _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [sfields_tenv_consistent_def]) >>
     disch_then drule >> strip_tac >> simp[get_struct_fields_def]) >>
  gvs[tuple_like_stack_count_def] >> IF_CASES_TAC >> gvs[] >>
  drule (CONJUNCT2 evaluate_type_mono) >> strip_tac >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by metis_tac[LENGTH_MAP, LIST_REL_LENGTH] >>
  `LENGTH (get_struct_fields sf (nsid_to_string key)) = LENGTH args` by
    (qpat_assum `MAP (FST o SND) _ = MAP SND args` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by metis_tac[UNZIP_MAP, UNZIP_ZIP, PAIR_EQ] >>
  drule_all word_tuple_size >> simp[type_memory_size_def, struct_layout_size_zip] >>
  metis_tac[evaluated_word_members]
QED

Theorem selected_register_post_type[local]:
  cenv.ce_func_return_type (nsid_to_string key) = ret /\
  type_widens_to tenv ret ann /\ ~is_bytestring_type ret ==>
  post_value_type cenv (Call ann (IntCall key) es dflt) = ret
Proof
  strip_tac >>
  `~is_bytestring_type ann` by
    metis_tac[type_widens_to_def, arg_type_fits_bytestring_source] >>
  Cases_on `is_word_type ann`
  >- (drule_all compileEnvTheory.type_widens_to_word >> simp[]) >>
  simp[lowered_value_type_def]
QED

Theorem selected_register_layout[local]:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  expr_body_pre_mods mods cenv cx env (Call ann (IntCall (src,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ safe_cast rtv v = SOME v /\
  cenv.ce_func_info (nsid_to_string (src,name)) = (nret,rbs,pvs) /\
  cenv.ce_func_info (nsid_to_string (src,name)) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n))
      ret (type_memory_bytes cenv ret) (MAP SND args) /\ 0 < nret /\
  LENGTH ws = nret /\ intret_vals_match rtv v ws /\
  (!mem i. mem_agree_outside tn.t_mem z.vs_memory mem /\ i < LENGTH ws ==>
     mem_word_at (off + 32*i) mem = EL i ws) ==>
  cenv.ce_func_return_type (nsid_to_string (src,name)) = ret /\
  post_value_type cenv (Call ann (IntCall (src,name)) es dflt) = ret /\
  type_memory_bytes cenv ret = 32*nret /\ type_memory_size rtv = 32*nret /\
  value_has_type rtv v /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==> val_in_memory rtv v off mem)
Proof
  strip_tac >> drule_all_then strip_assume_tac intcall_return_type_facts_mods >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_mods_def] >> strip_tac >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `nret = returns_stack_count
          (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n)) ret` by
    (qpat_assum `cenv.ce_func_info _ = compute_func_info _ _ _ _` (mp_tac o Q.AP_TERM `FST`) >>
     qpat_assum `cenv.ce_func_info _ = (_,_,_)` (pure_rewrite_tac o single) >>
     Cases_on `ret` >> simp[compute_func_info_def]) >>
  drule_all_then (CONJUNCTS_THEN2 assume_tac assume_tac) positive_result_abi_layout >>
  `type_memory_bytes cenv ret = type_memory_size rtv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> asm_rewrite_tac[]) >>
  `~is_bytestring_type ret` by metis_tac[positive_result_not_bytes] >>
  drule_all_then assume_tac selected_register_post_type >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule stack_results_val_in_memory >> simp[] >>
  conj_tac >- (qexists_tac `get_tenv cx` >> simp[] >> metis_tac[]) >>
  qexists_tac `ws` >> simp[] >>
  Cases_on `ws` >> gvs[]
QED

Theorem selected_stored_return_value_mods:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods src = SOME tops /\
  expr_body_pre_mods mods cenv cx env (Call ann (IntCall (src,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\ safe_cast rtv v = SOME v /\
  cenv.ce_func_info (nsid_to_string (src,name)) = (nret,rbs,pvs) /\
  cenv.ce_func_info (nsid_to_string (src,name)) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n))
      ret (type_memory_bytes cenv ret) (MAP SND args) /\ 0 < nret /\
  LENGTH ws = nret /\ intret_vals_match rtv v ws /\
  (!mem i. mem_agree_outside tn.t_mem z.vs_memory mem /\ i < LENGTH ws ==>
     mem_word_at (off + 32*i) mem = EL i ws) /\
  vv = LocatedValue (cenv.ce_func_return_type (nsid_to_string (src,name))) (base_ptr rbuf) /\
  rbuf.buf_operand = Var root /\ rbuf.buf_size = 32*nret /\
  eval_operand (Var root) z = SOME (n2w off) /\ off < dimword (:256) /\
  FLOOKUP G root = SOME (off,rbuf.buf_size) /\ op_taint tn (Var root) = {} /\
  FLOOKUP z.vs_allocas aid = SOME (off,rbuf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sm.cs_next_id /\ off + rbuf.buf_size <= z.vs_alloca_next /\
  (!n b sz. local_region cenv ee.scopes z n b sz ==>
     off + rbuf.buf_size <= b \/ b + sz <= off) ==>
  let e = Call ann (IntCall (src,name)) es dflt in
  let ty = post_value_type cenv e in
  vv_holds_mods cenv cx ty (Value v) vv ee z /\
  vv_at cenv cx ty sa sm ee (Value v) vv z /\
  vv_place_ptr_mods cenv cx ee z (Value v) vv /\
  vv_own cenv cx ty sa sm ee (Value v) vv z /\
  vv_store_bound cx ty (lowered_value_type cenv e) ee (Value v) vv z /\
  ptr_vv_ok cx ty (Value v) vv ee G tn z /\
  (!ty' p. vv = LocatedValue ty' p ==> p.ptr_location = LocMemory) /\
  (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (!ty' op. vv = StackValue ty' op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op G z) /\
  ~(vv_location vv = SOME LocCode)
Proof
  strip_tac >> drule_all_then strip_assume_tac selected_register_layout >>
  `val_wf rtv v` by metis_tac[value_has_type_memory_wf] >>
  `val_footprint rtv v <= 32*nret` by metis_tac[val_footprint_le] >>
  `val_store_size rtv v <= 32*nret` by metis_tac[val_store_size_le] >>
  `val_in_memory rtv v off z.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  simp[LET_THM, vv_holds_mods_def, contextTheory.base_ptr_def,
       vv_place_ptr_mods_def, vv_place_ptr_def, contextTheory.vv_location_def,
       lowered_value_type_def] >>
  `is_word_type ret ==> mem_word_at off z.vs_memory = typed_val_to_w256 rtv v` by
    (strip_tac >> irule val_in_memory_word_type >> simp[] >> qexistsl_tac [`ret`,`get_tenv cx`] >> simp[]) >>
  simp[vv_holds_def, vv_at_def, vv_own_def, vv_store_bound_def, ptr_vv_ok_def,
       ptr_mem_ok_def, ptr_buf_ok_def, read_result_def, return_def, lowered_value_type_def] >>
  conj_tac >> disj1_tac >> qexistsl_tac [`aid`,`off`,`rbuf.buf_size`] >>
  simp[] >> rpt gen_tac >> disch_tac >>
  qpat_assum `!n b sz. local_region _ _ _ n b sz ==> _` drule >> simp[] >> decide_tac
QED
