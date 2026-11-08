(* Arbitrary-calldata registration: compiler boundaries before execution. *)
Theory calldataRegistration
Ancestors
  actualRegistrationCode calldataRecursiveExecution allocLimitsProps
  abiCallerBuiltinInput compileVyper finite_map moduleLowering compileEnv
  venomInst fragExec compilerFirstEmission exprLowering abiDecoderCoherence context

Theorem register_singleton_allocated_boundary:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st =
    (cef,stf) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME mem_size ==>
  ?buf allocated.
    compile_alloc_buffer mem_size st = (buf,allocated) /\
    cef = ce with ce_vars updated_by
      (\m. m |+ (name,PtrVar buf.buf_operand mem_size)) /\
    compile_decode_args cef [(name,prim,dyn,sz,info)] off
      CALLDATALOAD (Lit 0w) 4 allocated = ((),stf)
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[compile_register_positional_args_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem decode_singleton_aggregate_prelude:
  compile_decode_args ce [(name,F,dyn,sz,info)] off
    CALLDATALOAD (Lit 0w) 4 st = ((),stf) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==>
  ?head after_head src first.
    emit_op ADD [Lit (n2w 4); Lit (n2w (off - 4))] st = (head,after_head) /\
    (if dyn then
       ?offset after_load.
         emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
         emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
     else src = head /\ first = after_head) /\
    compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) info first = ((),stf)
Proof
  strip_tac >>
  qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dyn` >>
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

Theorem first_emission_alloc_buffer_strong[local]:
  compile_alloc_buffer n a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w n)] a` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >> gvs[] >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_register_positional_args:
  !args ce off a x z.
  compile_register_positional_args ce args off a = (x,z) ==>
  cs_extends a z /\
  ((a.cs_blocks = z.cs_blocks /\ a.cs_current_bb = z.cs_current_bb /\
    a.cs_current_insts = z.cs_current_insts) \/
   (!fn. fn_has_code a z fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def, cs_extends_refl] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp_tac (srw_ss()) []
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x'` >> simp_tac (srw_ss()) []
  >- metis_tac[] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer x'' a` >>
  simp_tac (srw_ss()) [LET_THM] >>
  pairarg_tac >> simp_tac (srw_ss()) [] >> strip_tac >>
  gvs[pairTheory.FORALL_PROD] >>
  drule first_emission_alloc_buffer_strong >> strip_tac >>
  drule decode_args_suffix_extends >> disch_tac >>
  drule register_positional_args_suffix_extends >> disch_tac >>
  (conj_tac >- metis_tac[cs_extends_trans]) >> disj2_tac >>
  `cs_extends r z` by metis_tac[cs_extends_trans] >>
  rpt strip_tac >> drule_all fn_has_code_split >> strip_tac >> metis_tac[]
QED

(* A suffix either emits a non-PHI first instruction or leaves its entry
   block untouched. In the latter case only the caller's final exit is used. *)
Theorem registration_suffix_empty_phi:
  compile_register_positional_args ce args off a = (cef,z) /\
  a.cs_current_insts = [] /\ fn_has_code a z fn /\
  (z.cs_current_insts = [] ==>
    !bb. lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  !bb. lookup_block a.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule first_emission_register_positional_args >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  metis_tac[first_emission_empty_phi]
QED

Theorem word_type_decoder_primitive:
  !ty. is_word_type ty ==>
    ?c. type_to_abi_dec_info sf ce ty = DecPrimWord c
Proof
  Cases >> simp[is_word_type_def, type_to_abi_dec_info_def] >>
  Cases_on `b` >> simp[is_word_type_def, type_to_abi_dec_info_def] >>
  Cases_on `b'` >> simp[is_word_type_def, type_to_abi_dec_info_def]
QED

Theorem positional_descriptor_metadata:
  !args tys.
    sf = ce.ce_struct_fields /\
    LIST_REL (\(name,ty) (ty',tv).
      ty = ty' /\ abi_decoder_coherent ce env sf ty tv) args tys ==>
    LIST_REL (\(name,prim,dyn,sz,info) (ty,tv).
      abi_decoder_coherent ce env sf ty tv /\
      info = type_to_abi_dec_info sf ce ty /\
      (prim ==> ?c. info = DecPrimWord c))
      (build_positional_args ce args) tys
Proof
  Induct >> Cases_on `tys` >> simp[build_positional_args_def] >>
  gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  simp[build_positional_arg_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[word_type_decoder_primitive, build_positional_args_def]
QED

Theorem registration_list_specialize[local]:
  !xs ys.
    LIST_REL (\ty tv. !ce'.
      ce'.ce_struct_fields = ce.ce_struct_fields /\
      ce'.ce_flag_n_members = ce.ce_flag_n_members ==>
      abi_decoder_coherent ce' env sf ty tv) xs ys ==>
    !ce'. ce'.ce_struct_fields = ce.ce_struct_fields /\
      ce'.ce_flag_n_members = ce.ce_flag_n_members ==>
      LIST_REL (abi_decoder_coherent ce' env sf) xs ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem registration_coherent_env_cong:
  !ce env sf ty tv.
    abi_decoder_coherent ce env sf ty tv ==>
    !ce'. ce'.ce_struct_fields = ce.ce_struct_fields /\
      ce'.ce_flag_n_members = ce.ce_flag_n_members ==>
      abi_decoder_coherent ce' env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `type_memory_bytes ce' = type_memory_bytes ce` by
    (simp[FUN_EQ_THM] >> metis_tac[type_memory_bytes_struct_fields]) >>
  gvs[abi_decoder_header_def] >>
  simp[Once abi_decoder_coherent_cases, abi_decoder_header_def] >>
  drule registration_list_specialize >> simp[] >>
  strip_tac >> qexists_tac `tvs` >> simp[]
QED

Theorem constructed_positional_metadata:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  ce.ce_struct_fields =
    (build_compile_env tops External mut fname args ret (code_stmts:stmt list) use_trans).ce_struct_fields /\
  ce.ce_flag_n_members =
    (build_compile_env tops External mut fname args ret (code_stmts:stmt list) use_trans).ce_flag_n_members /\
  LIST_REL (\(name,ty) (ty',tv).
    ty = ty' /\ assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv) args tys ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv).
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
    (prim ==> ?c. info = DecPrimWord c)) (build_positional_args ce args) tys
Proof
  strip_tac >>
  `!ty tv. assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv ==>
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv` by
    (rpt strip_tac >>
     `abi_decoder_coherent
       (build_compile_env tops External mut fname args ret code_stmts use_trans)
       (type_env tops) ce.ce_struct_fields ty tv` by
       (asm_rewrite_tac[] >> irule abi_caller_coherent >> metis_tac[]) >>
     drule registration_coherent_env_cong >>
     disch_then (qspec_then `ce` mp_tac) >> asm_rewrite_tac[]) >>
  qpat_x_assum `ce.ce_struct_fields = _` kall_tac >>
  qpat_x_assum `ce.ce_flag_n_members = _` kall_tac >>
  irule positional_descriptor_metadata >> simp[] >>
  qpat_x_assum `LIST_REL _ args tys` mp_tac >>
  map_every qid_spec_tac [`tys`, `args`] >>
  Induct >> Cases_on `tys` >> simp[] >>
  gen_tac >> PairCases_on `h` >> PairCases_on `h'` >> simp[] >>
  metis_tac[]
QED

(* This is precisely the environment computed by package_external_fn. *)
Theorem packaged_positional_metadata:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  ce0 = (build_compile_env tops External mut fname args ret code_stmts use_trans
    with ce_raw_return := rr) /\
  ce1 = (if ret <> NoneT then update_cenv_ret_abi ce0 ret else ce0) /\
  ce = update_cenv_nonreentrant ce1 nr nkey use_trans (mut = View) /\
  LIST_REL (\(name,ty) (ty',tv).
    ty = ty' /\ assignable_type (type_env tops) ty /\
    evaluate_type (type_env tops) ty = SOME tv) args tys ==>
  LIST_REL (\(name,prim,dyn,sz,info) (ty,tv).
    abi_decoder_coherent ce (type_env tops) ce.ce_struct_fields ty tv /\
    info = type_to_abi_dec_info ce.ce_struct_fields ce ty /\
    (prim ==> ?c. info = DecPrimWord c)) (build_positional_args ce args) tys
Proof
  strip_tac >> irule constructed_positional_metadata >>
  goal_assum $ drule_at Any >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`code_stmts`, `fname`, `mut`, `ret`, `use_trans`] >>
  gvs[update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
  Cases_on `ret <> NoneT` >> gvs[]
QED

(* Attach evaluated source types to descriptors, without a specification constant. *)
Theorem positional_registration_specs:
  !args tys.
    LIST_REL (\(name,ty) (ty',tv).
      ty = ty' /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args tys ==>
    ?specs.
      MAP (\(name,prim,dyn,sz,ty,tv).
        (name,prim,dyn,sz,type_to_abi_dec_info ce.ce_struct_fields ce ty)) specs =
        build_positional_args ce args /\
      MAP (\(name,prim,dyn,sz,ty,tv). name) specs = MAP FST args /\
      MAP (\(name,prim,dyn,sz,ty,tv). ((name,ty),tv)) specs =
        ZIP (args,MAP SND tys) /\
      EVERY (\(name,prim,dyn,sz,ty,tv).
        abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
        (?loc. FLOOKUP ce.ce_vars name = SOME loc /\
          var_location_memory_size loc = SOME (type_memory_size tv)) /\
        (prim ==> ?c. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord c) /\
        type_memory_size tv < dimword (:256)) specs
Proof
  Induct >> Cases_on `tys` >> simp[build_positional_args_def] >>
  gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  rename1 `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` >>
  rename1 `FLOOKUP ce.ce_vars name = SOME loc` >>
  qexists `(name,is_word_type ty,is_abi_dynamic ce.ce_struct_fields ty,
    abi_embedded_static_size ce.ce_struct_fields ty,ty,tv)::specs` >>
  simp[build_positional_arg_def,build_positional_args_def,
    word_type_decoder_primitive]
QED

Theorem register_singleton_alloca_output:
  compile_register_positional_args ce [(name,prim,dyn,sz,info)] off st =
    (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME n /\
  fn_has_code st final fn ==>
  ?vname ins.
    FLOOKUP cef.ce_vars name = SOME (PtrVar (Var vname) n) /\
    MEM ins (fn_insts fn) /\ ins.inst_opcode = ALLOCA /\
    ins.inst_outputs = [vname] /\ ins.inst_id = st.cs_next_id
Proof
  strip_tac >>
  drule_all register_singleton_allocated_boundary >> strip_tac >>
  `cs_extends st allocated /\ cs_extends allocated final` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends,
      actualRegistrationCodeTheory.decode_args_suffix_extends] >>
  `fn_has_code st allocated fn` by metis_tac[fn_has_code_split] >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >>
  `fn_has_code sx allocated fn` by metis_tac[fn_has_code_split] >>
  drule_all loweringHaltTheory.emit_inst_fn_member >> strip_tac >>
  qexistsl_tac [`p`,`mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [p]`] >>
  gvs[FLOOKUP_UPDATE, mk_inst_def]
QED
