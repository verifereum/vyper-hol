(*
 * External entry: the parameters after compile_register_positional_args
 * (#639)
 *
 * The external entry allocates an ALLOCA per parameter and decodes the
 * argument from calldata into it.  This file shows the parameters' pointers
 * then hold the arguments' values: local_ptrs_rel.
 *
 * TOP-LEVEL:
 *   register_positional_args_local_ptrs -- the parameters' local_ptrs_rel
 *                             after compile_register_positional_args
 *)
Theory entryArgPtrs
Ancestors
  list rich_list finite_map alist
  vyperLoweringCorrect entryDecodePlanProps entryDecodeProps fragExec
  compileEnv compileVyper moduleLowering selectorDispatch
  vyperInterpreter vyperState vyperContext vyperAST
  venomState vyperCall loweringHalt entryDecodeStaticProps retAbiPlanProps
  valueEncodingProofs vyperABIRoundtrip contractABI entryDispatchProps
  valueTypingMemoryProps localPtrsProps abiDecodeStaticProps entryDecodeStructure
  exprLoweringProps emitHelperProps exprLowering valueEncoding intCallCallee
  venomExecSemantics venomInst words entrySinkExtraction

Theorem dec_frame_mstore:
  !st q w s t.
    vars_pc_only (mstore q w s) t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
    dec_frame st q 32 s t
Proof
  rpt strip_tac >>
  `t.vs_memory = (mstore q w s).vs_memory` by
    metis_tac[moduleLoweringPropsTheory.vars_pc_only_memory] >>
  simp[dec_frame_def] >> conj_tac
  >- fs[moduleLoweringPropsTheory.vars_pc_only_def, mstore_def,
        venom_state_component_equality] >>
  rpt strip_tac >> simp[mem_bytes_at_mstore_outside]
QED

Theorem dec_frame_allocas:
  !st q n s t.
    dec_frame st q n s t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rw[dec_frame_def] >>
  fs[moduleLoweringPropsTheory.vars_pc_only_def, venom_state_component_equality]
QED

Theorem dec_frame_local_backed:
  !st q n s t func p b sz.
    dec_frame st q n s t /\ local_backed func p s b sz ==>
    local_backed func p t b sz
Proof
  rpt strip_tac >> drule dec_frame_allocas >>
  strip_tac >> fs[local_backed_def] >> metis_tac[]
QED

Theorem dec_frame_disjoint_memory:
  !st q n s t b sz.
    dec_frame st q n s t /\ regions_disjoint b sz q n ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  rpt strip_tac >> irule mem_bytes_at_bytewise >>
  fs[dec_frame_def, regions_disjoint_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem dec_frame_local_ptrs:
  !st q n s t func cenv scopes.
    dec_frame st q n s t /\ local_ptrs_rel func cenv scopes s /\
    (!name entry p sz.
       lookup_scopes name scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at st p) /\
    (!name b sz. local_region cenv scopes s name b sz ==>
       regions_disjoint b sz q n) ==>
    local_ptrs_rel func cenv scopes t
Proof
  rpt strip_tac >> irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  drule dec_frame_allocas >> strip_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule dec_frame_disjoint_memory >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> fs[dec_frame_def] >>
      qpat_x_assum `!x. not_fresh_at _ _ ==> _` irule >>
      first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

(* A single registration step exposes its two emitted fragments. *)
Theorem register_positional_args_step:
  !cenv name prim dyn sz dec rest off st cenvf stf loc msz.
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME msz ==>
    (compile_register_positional_args cenv
       ((name, prim, dyn, sz, dec)::rest) off st = (cenvf, stf) <=>
     ?buf sa sb.
       compile_alloc_buffer msz st = (buf, sa) /\
       compile_decode_args
         (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar buf.buf_operand msz)))
         [(name, prim, dyn, sz, dec)] off CALLDATALOAD (Lit 0w) 4 sa = ((), sb) /\
       compile_register_positional_args
         (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar buf.buf_operand msz)))
         rest (off + sz) sb = (cenvf, stf))
Proof
  rpt strip_tac >>
  simp[Once compile_register_positional_args_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem register_positional_args_nil:
  !cenv off st.
    compile_register_positional_args cenv [] off st = (cenv, st)
Proof
  simp[compile_register_positional_args_def, comp_return_def]
QED

Theorem register_positional_args_straight:
  !args cenv off st cenv' st'.
    EVERY (\(name,prim,dyn,sz,info).
      prim \/ (~dyn /\ ?n. static_dec info n)) args /\
    compile_register_positional_args cenv args off st = (cenv',st') ==>
    dec_straight st st' /\ st.cs_next_id <= st'.cs_next_id
Proof
  Induct
  >- simp[register_positional_args_nil, dec_straight_def,
          inst_extends_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >>
  rename1 `(name,prim,dyn,sz,info)::args` >>
  rpt gen_tac >> pure_rewrite_tac[EVERY_DEF, pairTheory.pair_case_thm] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `FLOOKUP cenv.ce_vars name`
  >- (qpat_x_assum `compile_register_positional_args _ (_::_) _ _ = _`
        mp_tac >> simp[Once compile_register_positional_args_def] >>
      metis_tac[]) >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME loc` >>
  Cases_on `var_location_memory_size loc`
  >- (qpat_x_assum `compile_register_positional_args _ (_::_) _ _ = _`
        mp_tac >> simp[Once compile_register_positional_args_def] >>
      metis_tac[]) >>
  drule_all register_positional_args_step >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ (_::_) _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `!prim dyn sz dec' rest off st cenvf stf. _` kall_tac >>
  drule compile_alloc_buffer_straight >> strip_tac >>
  `dec_straight sa sb /\ sa.cs_next_id <= sb.cs_next_id` by
    (irule compile_decode_arg_straight >>
     goal_assum (drule_at Any) >>
     simp[FLOOKUP_UPDATE, var_location_decode_operand_def] >>
     gvs[pairTheory.pair_case_thm] >> metis_tac[]) >>
  `dec_straight sb st' /\ sb.cs_next_id <= st'.cs_next_id` by
    (first_x_assum irule >> metis_tac[]) >>
  metis_tac[dec_straight_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem static_decs_replicate:
  !ei m n. static_dec ei m ==>
    static_decs (REPLICATE n (ei,m,m)) (n * m)
Proof
  rpt gen_tac >> strip_tac >> Induct_on `n` >>
  simp[static_dec_nil, arithmeticTheory.MULT_CLAUSES] >>
  irule static_dec_cons >> simp[] >>
  metis_tac[arithmeticTheory.MULT_COMM]
QED

Theorem abi_dec_plan_static:
  (!env ty info. abi_dec_plan env ty info ==> !tv.
    evaluate_type env ty = SOME tv ==> static_dec info (type_memory_size tv)) /\
  (!env ts elems. abi_dec_plans env ts elems ==> !tvs.
    OPT_MMAP (evaluate_type env) ts = SOME tvs ==>
    static_decs elems (SUM (MAP type_memory_size tvs)))
Proof
  ho_match_mp_tac abi_dec_plan_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule_all word_type_memory_size >>
      simp[static_dec_prim]) >>
  rpt strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      vyperValueTheory.evaluate_types_OPT_MMAP, type_memory_size_def]
  >- (simp[type_memory_size_list_sum] >> metis_tac[static_dec_complex])
  >- metis_tac[static_dec_complex, static_decs_replicate]
  >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> strip_tac >>
      gvs[type_memory_size_fields_sum, MAP_ZIP] >>
      metis_tac[static_dec_complex])
  >- simp[static_dec_nil] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule static_dec_cons >> simp[]
QED

Theorem build_positional_args_admissible:
  !cenv tenv args vals env.
    dec_cenv_agrees cenv tenv /\ bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args ==>
    EVERY (\(name,prim,dyn,sz,info).
      prim \/ (~dyn /\ ?n. static_dec info n)) (build_positional_args cenv args)
Proof
  rpt gen_tac >> strip_tac >>
  simp[build_positional_args_def, EVERY_EL, EL_MAP] >>
  qx_gen_tac `i` >> strip_tac >>
  drule_all bind_arguments_word_arg >> strip_tac >>
  gns[EVERY_EL] >>
  `is_word_type (SND (EL i args)) \/
   (assignable_type tenv (SND (EL i args)) /\
    ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))` by
    metis_tac[EVERY_EL] >>
  `int_byte_widths tv` by metis_tac[EVERY_EL] >>
  Cases_on `EL i args` >> rename1 `EL i args = (name,ty)` >>
  gvs[build_positional_arg_def] >>
  Cases_on `is_word_type ty` >> simp[] >> gvs[] >>
  `abi_dec_plan tenv ty (type_to_abi_dec_info cenv.ce_struct_fields cenv ty)` by
    (irule type_to_abi_dec_info_plan >> fs[dec_cenv_agrees_def] >>
     qexists_tac `tenv` >> fs[dec_cenv_agrees_def]) >>
  `static_dec (type_to_abi_dec_info cenv.ce_struct_fields cenv ty)
    (type_memory_size tv)` by metis_tac[abi_dec_plan_static] >>
  conj_tac >- (
    fs[dec_cenv_agrees_def] >>
    `tenv SUBMAP tenv` by simp[] >>
    drule_all abi_elem_props >> simp[]) >>
  metis_tac[]
QED

Theorem dec_straight_cs_extends:
  !st st'. dec_straight st st' ==> cs_extends st st'
Proof
  rw[dec_straight_def, inst_extends_def, cs_extends_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem dec_straight_code_phases:
  !st sa sb st' func.
    dec_straight st sa /\ dec_straight sa sb /\ dec_straight sb st' /\
    fn_has_code st st' func ==>
    fn_has_code st sa func /\ fn_has_code sa sb func /\
    fn_has_code sb st' func
Proof
  rpt strip_tac >>
  `cs_extends st sa /\ cs_extends sa sb /\ cs_extends sb st'` by
    metis_tac[dec_straight_cs_extends] >>
  `cs_extends sa st'` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem entry_ptr_update_remaining:
  !args cenv name ptr sz.
    ~MEM name (MAP FST args) ==>
    EVERY (\a. FLOOKUP
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar ptr sz))).ce_vars
      (FST a) = FLOOKUP cenv.ce_vars (FST a)) args
Proof
  simp[EVERY_MEM, MEM_MAP, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem build_positional_args_drop:
  !cenv args i.
    DROP i (build_positional_args cenv args) =
    build_positional_args cenv (DROP i args)
Proof
  simp[build_positional_args_def, MAP_DROP]
QED

(* Successful binding preserves the positional value at each distinct name. *)
Theorem bind_arguments_lookup_index:
  !args vals tenv env i.
    bind_arguments tenv args vals = SOME env /\
    ALL_DISTINCT (MAP FST args) /\ i < LENGTH args ==>
    ?tv. evaluate_type tenv (SND (EL i args)) = SOME tv /\
         FLOOKUP env (FST (EL i args)) =
           SOME <| assignable := T; type := tv; value := EL i vals |>
Proof
  Induct_on `args` >- simp[] >>
  qx_gen_tac `arg` >> Cases_on `arg` >>
  rename1 `(name, ty)::args` >>
  Cases_on `vals` >- simp[bind_arguments_def] >>
  simp[bind_arguments_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  drule (CONJUNCT1 safe_cast_some_eq) >> strip_tac >> gvs[] >>
  Cases_on `i` >> simp[FLOOKUP_UPDATE] >>
  rename1 `SUC j < SUC (LENGTH args)` >>
  `j < LENGTH args` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  `MEM (FST (EL j args)) (MAP FST args)` by
    (simp[MEM_MAP] >> qexists_tac `EL j args` >> simp[EL_MEM]) >>
  `name <> FST (EL j args)` by metis_tac[] >> simp[]
QED

Theorem bind_arguments_memory_wf:
  !tenv args vals env i tv.
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    evaluate_type tenv (SND (EL i args)) = SOME tv ==>
    val_wf tv (EL i vals)
Proof
  rpt strip_tac >> drule_all bind_arguments_word_arg >> strip_tac >>
  gvs[] >> irule value_has_type_memory_wf >> simp[]
QED

Theorem bind_arguments_initial_local_ptrs:
  !tenv args vals env cenv func s.
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. ?off. FLOOKUP cenv.ce_vars (FST a) =
      SOME (MemLoc off (type_memory_bytes cenv (SND a)))) args ==>
    local_ptrs_rel func cenv [env] s
Proof
  rpt strip_tac >>
  drule bind_arguments_fdom >> strip_tac >>
  `!name entry p sz.
     FLOOKUP env name = SOME entry ==>
     FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var p) sz)` by
    (rpt strip_tac >>
     `MEM name (MAP FST args)` by (fs[FLOOKUP_DEF] >> gvs[]) >>
     gvs[MEM_MAP, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  simp[local_ptrs_rel_def, local_region_def, lookup_scopes_def,
       AllCaseEqs()] >>
  metis_tac[]
QED

Theorem entry_static_arg_size:
  !cenv tenv ty tv.
    dec_cenv_agrees cenv tenv /\ evaluate_type tenv ty = SOME tv /\
    (is_word_type ty \/ ~is_dynamic (vyper_to_abi_type tenv ty)) ==>
    abi_embedded_static_size cenv.ce_struct_fields ty =
      type_memory_bytes cenv ty
Proof
  rpt strip_tac
  >- (simp[abi_embedded_static_size_word] >>
      drule_all word_type_memory_size >> strip_tac >>
      fs[dec_cenv_agrees_def] >>
      qpat_x_assum `!t tv. _` drule >> simp[]) >>
  fs[dec_cenv_agrees_def] >>
  drule_at (Pat `evaluate_type _ _ = _`) abi_elem_props >>
  disch_then (qspecl_then [`tenv`, `cenv`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all (cj 1 static_length_memory_size) >> simp[]
QED

Theorem entry_static_prefix_sizes:
  !cenv tenv args vals env i.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args ==>
    SUM (MAP (abi_embedded_static_size cenv.ce_struct_fields o SND)
             (TAKE i args)) =
    SUM (MAP (type_memory_bytes cenv o SND) (TAKE i args))
Proof
  rpt strip_tac >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
  rpt strip_tac >>
  `MEM x args` by metis_tac[MEM_TAKE] >>
  fs[EVERY_MEM] >>
  `?j. j < LENGTH args /\ x = EL j args` by metis_tac[MEM_EL] >>
  drule_all bind_arguments_word_arg >> strip_tac >>
  irule entry_static_arg_size >> simp[] >> metis_tac[]
QED

Theorem entry_static_abi_types:
  !tenv args vals env avs.
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args /\
    vyper_to_abi_list tenv (MAP SND args) vals = SOME avs ==>
    EVERY is_static (vyper_to_abi_types tenv (MAP SND args))
Proof
  rpt strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >> fs[] >>
  simp[EVERY_EL, vyper_to_abi_types_length] >> rpt strip_tac >>
  rename1 `j < LENGTH vals` >>
  `j < LENGTH args` by decide_tac >>
  drule_all bind_arguments_word_arg >> strip_tac >>
  qpat_x_assum `LENGTH vals = LENGTH args` kall_tac >>
  `EL j (vyper_to_abi_types tenv (MAP SND args)) =
     vyper_to_abi_type tenv (SND (EL j args))` by
    (qspecl_then [`MAP SND args`, `j`] mp_tac vyper_to_abi_types_EL >>
     simp[EL_MAP]) >> gvs[] >>
  `vyper_to_abi tenv (SND (EL j args)) (EL j vals) = SOME (EL j avs)` by
    (qpat_x_assum `!i. _` (qspec_then `j` mp_tac) >> simp[EL_MAP]) >>
  fs[EVERY_EL] >>
  qpat_x_assum `!n. n < _ ==> is_word_type _ \/ _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  drule_all vyper_to_abi_word_enc >> simp[]
QED

Theorem entry_static_encoding_sizes:
  !cenv tenv args vals env avs.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY is_static (vyper_to_abi_types tenv (MAP SND args)) /\
    vyper_to_abi_list tenv (MAP SND args) vals = SOME avs ==>
    MAP LENGTH (MAP2 enc (vyper_to_abi_types tenv (MAP SND args)) avs) =
    MAP (type_memory_bytes cenv o SND) args
Proof
  rpt strip_tac >> drule vyper_to_abi_list_EL >> strip_tac >>
  fs[] >> irule LIST_EQ >>
  simp[vyper_to_abi_types_length, EL_MAP, EL_MAP2] >>
  rpt strip_tac >> rename1 `x < LENGTH vals` >>
  `x < LENGTH args` by decide_tac >>
  drule_all bind_arguments_word_arg >> strip_tac >>
  qpat_x_assum `LENGTH vals = LENGTH args` kall_tac >>
  `EL x (vyper_to_abi_types tenv (MAP SND args)) =
     vyper_to_abi_type tenv (SND (EL x args))` by
    (qspecl_then [`MAP SND args`, `x`] mp_tac vyper_to_abi_types_EL >>
     simp[EL_MAP]) >>
  `vyper_to_abi tenv (SND (EL x args)) (EL x vals) = SOME (EL x avs)` by
    (qpat_x_assum `!i. _` (qspec_then `x` mp_tac) >> simp[EL_MAP]) >>
  `~is_dynamic (vyper_to_abi_type tenv (SND (EL x args)))` by
    (fs[EVERY_EL, vyper_to_abi_types_length] >>
     qpat_x_assum `!n. n < _ ==> is_static _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  drule_all (cj 1 vyper_to_abi_static_enc_length) >>
  fs[dec_cenv_agrees_def] >>
  qpat_x_assum `!t tv. _` drule >> simp[]
QED

Theorem entry_static_calldata_length:
  !cenv tenv fname args vals env cd.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args /\
    calldata_encodes tenv fname (MAP SND args) vals cd ==>
    LENGTH cd = 4 + SUM (MAP (type_memory_bytes cenv o SND) args)
Proof
  rpt strip_tac >> drule bind_arguments_length >> strip_tac >>
  fs[calldata_encodes_def] >>
  `TAKE (LENGTH vals) (MAP SND args) = MAP SND args` by
    (irule TAKE_LENGTH_TOO_LONG >> simp[]) >> gvs[] >>
  drule_all entry_static_abi_types >> strip_tac >>
  drule_all entry_static_encoding_sizes >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >> fs[] >>
  qpat_assum `LENGTH args = LENGTH vals`
    (fn th => REWRITE_TAC [GSYM th]) >>
  simp[TAKE_LENGTH_TOO_LONG, enc_tuple_static_acc, function_selector_length,
       LENGTH_FLAT, vyper_to_abi_types_length]
QED

Theorem entry_static_prefix_bound:
  !cenv tenv fname args vals env cd i.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args /\
    calldata_encodes tenv fname (MAP SND args) vals cd /\
    LENGTH cd < dimword (:256) /\ i < LENGTH args ==>
    4 + SUM (MAP (type_memory_bytes cenv o SND) (TAKE i args)) +
        type_memory_bytes cenv (SND (EL i args)) < dimword (:256)
Proof
  rpt strip_tac >> drule_all entry_static_calldata_length >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv o SND) (TAKE i args)) +
     type_memory_bytes cenv (SND (EL i args)) <=
     SUM (MAP (type_memory_bytes cenv o SND) args)` suffices_by decide_tac >>
  qpat_x_assum `i < LENGTH args` mp_tac >>
  map_every qid_spec_tac [`i`, `args`] >>
  POP_ASSUM_LIST (K all_tac) >>
  Induct >> simp[] >> qx_gen_tac `arg` >> Cases >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Theorem entry_decode_arg_frame:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory) (\r. F)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv (EL i vals)` by
    (drule_all bind_arguments_word_arg >> strip_tac >> gvs[]) >>
  `LENGTH vals = LENGTH args` by metis_tac[bind_arguments_length] >>
  `!j. j < i ==> ?tv. evaluate_type tenv (SND (EL j args)) = SOME tv /\
                        value_has_type tv (EL j vals)` by
    (rpt strip_tac >> drule bind_arguments_word_arg >>
     disch_then (qspec_then `j` mp_tac) >> impl_tac >- simp[] >> metis_tac[]) >>
  Cases_on `is_word_type (SND (EL i args))`
  >- (drule_all word_type_memory_size >> strip_tac >>
      `off < dimword (:256)` by decide_tac >>
      `off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                              (TAKE i args))` by simp[] >>
      drule_all compile_decode_word_arg_calldata >>
      disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
      drule frag_exec_weaken >> disch_then irule >>
      simp[] >> rpt strip_tac >> simp[] >>
      irule dec_frame_mstore >> metis_tac[]) >>
  qpat_x_assum `is_word_type _ \/ _` mp_tac >> simp[] >> strip_tac >>
  drule_all compile_decode_static_arg_calldata >>
  disch_then (qspec_then `ctx` ACCEPT_TAC)
QED

Theorem entry_decode_arg_run:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    ~s0.vs_halted /\ s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?u. dec_straight st st' /\
      run_inst_seq (emitted_insts st st') s0 = OK u /\
      let t = u with vs_inst_idx := LENGTH st'.cs_current_insts in
        dec_frame st (w2n p) (type_memory_size tv) s0 t /\
        fresh_vars_wrt st' t /\
        val_in_memory tv (EL i vals) (w2n p) t.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = s0.vs_current_bb /\
        t.vs_prev_bb = s0.vs_prev_bb
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `dec_straight st st'` by
    (Cases_on `EL i args` >> rename1 `EL i args = (name,ty)` >>
     gvs[build_positional_arg_def] >>
     irule (cj 1 compile_decode_arg_straight) >>
     qpat_assum `compile_decode_args _ _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[] >>
     gvs[] >>
     `abi_dec_plan tenv ty
        (type_to_abi_dec_info cenv0.ce_struct_fields cenv0 ty)` by
       (irule type_to_abi_dec_info_plan >> fs[dec_cenv_agrees_def] >>
        qexists_tac `tenv` >> fs[dec_cenv_agrees_def]) >>
     disj2_tac >> conj_tac
     >- (fs[dec_cenv_agrees_def] >>
         `tenv SUBMAP tenv` by simp[] >>
         drule_all abi_elem_props >> simp[]) >>
     metis_tac[cj 1 abi_dec_plan_static]) >>
  drule_all entry_decode_arg_frame >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_at (Pos (el 2)) frag_exec_straight_run >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `u` >> simp[]
QED
Theorem entry_decode_arg_frame_pc:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory /\
           t.vs_prev_bb = s0.vs_prev_bb /\ t.vs_current_bb = s0.vs_current_bb)
      (\r. F)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `~s0.vs_halted /\ s0.vs_current_bb = st.cs_current_bb /\
            s0.vs_inst_idx = LENGTH st.cs_current_insts`
  >- (pop_assum strip_assume_tac >> drule_all entry_decode_arg_run >> strip_tac >>
      irule frag_exec_run_inst_seq >>
      fs[dec_straight_def, inst_extends_def, IS_PREFIX_APPEND] >>
      rpt strip_tac >> gvs[] >> disj1_tac >>
      qexists_tac `u` >> simp[]) >>
  simp[frag_exec_def] >> rpt strip_tac >> gvs[]
QED


(* Decoder frames preserve every live pointer: freshness rules out a live
   pointer being one of the decoder's new temporaries. *)
Theorem entry_live_ptrs_not_fresh:
  !func cenv scopes s st name entry p sz.
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p
Proof
  rpt strip_tac >> simp[not_fresh_at_def] >> rpt strip_tac >>
  gvs[local_ptrs_rel_def, fresh_vars_wrt_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[lookup_var_def, FLOOKUP_DEF, arithmeticTheory.GREATER_EQ] >> metis_tac[]
QED

Theorem entry_decode_bind_ptr:
  !func cenv scopes s t st name entry p w sz.
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    dec_frame st (w2n w) sz s t /\
    lookup_scopes name scopes = SOME entry /\
    (!q sq. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var q) sq)) /\
    lookup_var p s = SOME w /\ not_fresh_at st p /\
    local_backed func p s (w2n w) sz /\
    w2n w + sz <= s.vs_alloca_next /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n w) t.vs_memory /\
    (!n b sz'. local_region cenv scopes s n b sz' ==>
               regions_disjoint (w2n w) sz b sz') ==>
    local_ptrs_rel func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
      scopes t
Proof
  rpt strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s` by
    fs[dec_frame_def] >>
  `!n b sz'. local_region cenv scopes t n b sz' ==>
             local_region cenv scopes s n b sz'` by
    (rw[local_region_def] >> rename1 `lookup_var oldp t = SOME _` >>
     `not_fresh_at st oldp` by
       (irule entry_live_ptrs_not_fresh >> metis_tac[]) >>
     metis_tac[]) >>
  irule local_ptrs_rel_bind_ptr >> simp[] >> conj_tac
  >- (irule dec_frame_local_ptrs >> goal_assum (drule_at Any) >>
      simp[] >> conj_tac
      >- metis_tac[entry_live_ptrs_not_fresh] >>
      fs[regions_disjoint_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[dec_frame_local_backed] >>
  conj_tac >- (drule dec_frame_allocas >> strip_tac >> simp[]) >>
  metis_tac[dec_frame_local_backed]
QED

Theorem entry_alloc_buffer_inst:
  !n st buf sa func.
    compile_alloc_buffer n st = (buf, sa) /\ fn_has_code st sa func ==>
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
           [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  fs[fn_has_code_def] >> irule lookup_block_fn_insts >>
  goal_assum (drule_at Any) >>
  fs[IS_PREFIX_APPEND] >> simp[]
QED

Theorem entry_alloc_buffer_local_ptrs:
  !n st buf sa func cenv scopes s ctx.
    compile_alloc_buffer n st = (buf, sa) /\ fn_has_code st sa func /\
    n < dimword (:256) /\ s.vs_alloca_next < dimword (:256) /\
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?a. buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
      local_ptrs_rel func cenv scopes a /\
      lookup_var (STRING #"%" (toString st.cs_next_var)) a =
        SOME (n2w s.vs_alloca_next) /\
      local_backed func (STRING #"%" (toString st.cs_next_var)) a s.vs_alloca_next n /\
      a.vs_alloca_next = s.vs_alloca_next + n /\ fresh_vars_wrt sa a /\
      not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
      (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
      (!name q sz. local_region cenv scopes a name q sz ==>
                   regions_disjoint s.vs_alloca_next n q sz) /\
      a with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
                vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
      ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
      a.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel r. run_from fuel ctx func a = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt strip_tac >>
  qabbrev_tac `a = (update_var (STRING #"%" (toString st.cs_next_var))
    (n2w s.vs_alloca_next)
    (s with <| vs_allocas := s.vs_allocas |+
      (st.cs_next_id, (s.vs_alloca_next,n));
      vs_alloca_next := s.vs_alloca_next+n |>))
    with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `frag_exec ctx st sa (\u. u = s) (\u. u = a) (\r. F)` by
    (irule compile_alloc_buffer_fresh_frag >>
     qexistsl_tac [`buf`, `n`] >> simp[Abbr `a`]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `a` >> simp[] >>
  drule compile_alloc_buffer_parts >> strip_tac >> simp[] >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by simp[] >>
  `not_local_ptr cenv scopes (STRING #"%" (toString st.cs_next_var))` by
    (irule local_ptrs_rel_fresh_not_local_ptr >>
     qexistsl_tac [`func`, `s`, `st`] >> simp[arithmeticTheory.GREATER_EQ]) >>
  `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString st.cs_next_var)]) s (n2w n : bytes32) =
    OK (a with vs_inst_idx := s.vs_inst_idx)` by
    simp[exec_alloca_def, mk_inst_def, Abbr `a`, w2n_n2w,
         arithmeticTheory.LESS_MOD, update_var_def,
         venom_state_component_equality] >>
  drule local_ptrs_rel_exec_alloca_fresh >> simp[mk_inst_def] >>
  disch_then (qspecl_then [`func`, `cenv`, `scopes`] mp_tac) >>
  simp[local_ptrs_rel_inst_idx] >> strip_tac >>
  conj_tac >- simp[Abbr `a`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (simp[local_backed_def] >> disj1_tac >>
      qexists_tac `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString st.cs_next_var)]` >>
      drule_all entry_alloc_buffer_inst >> simp[mk_inst_def]) >>
  conj_tac >- simp[Abbr `a`, update_var_def] >> conj_tac
  >- (simp[Abbr `a`, fresh_vars_wrt_def, update_var_def] >>
      fs[fresh_vars_wrt_def, arithmeticTheory.GREATER_EQ] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (simp[Abbr `a`, update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
      IF_CASES_TAC >> gvs[] >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!name b sz. _` mp_tac >>
      fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  simp[Abbr `a`, update_var_def, venom_state_component_equality]
QED

Theorem entry_register_arg_runtime:
  !n st buf sa sb func cenv scopes s ctx name entry.
    compile_alloc_buffer n st = (buf, sa) /\ fn_has_code st sa func /\
    fn_has_code sa sb func /\ sa.cs_next_id <= sb.cs_next_id /\
    n < dimword (:256) /\ s.vs_alloca_next < dimword (:256) /\
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    lookup_scopes name scopes = SOME entry /\
    (!q sz. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var q) sz)) /\
    type_memory_size entry.type <= n /\ val_wf entry.type entry.value /\
    (!a. fresh_vars_wrt sa a /\
         lookup_var (STRING #"%" (toString st.cs_next_var)) a =
           SOME (n2w s.vs_alloca_next) /\ a.vs_call_ctx = s.vs_call_ctx ==>
       frag_exec ctx sa sb (\u. u = a)
         (\t. dec_frame sa s.vs_alloca_next n a t /\ fresh_vars_wrt sb t /\
              val_in_memory entry.type entry.value s.vs_alloca_next t.vs_memory /\
              t.vs_prev_bb = a.vs_prev_bb /\ t.vs_current_bb = a.vs_current_bb)
         (\r. F)) ==>
    ?t. local_ptrs_rel func
          (cenv with ce_vars updated_by (\m. m |+
            (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) n))) scopes t /\
        fresh_vars_wrt sb t /\ t.vs_alloca_next = s.vs_alloca_next + n /\
        (!aid. sb.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE) /\
        t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next;
                  vs_inst_idx := s.vs_inst_idx |> = s /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt strip_tac >>
  drule_all entry_alloc_buffer_local_ptrs >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `a.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `_ with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qpat_x_assum `!a. _ ==> frag_exec _ _ _ _ _ _`
    (qspec_then `a` mp_tac) >> simp[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  conj_tac
  >- (irule entry_decode_bind_ptr >> simp[] >>
      qexistsl_tac [`a`, `sa`, `n2w s.vs_alloca_next`] >>
      simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> metis_tac[]) >>
  drule dec_frame_allocas >> strip_tac >> simp[] >>
  qpat_x_assum `dec_frame _ _ _ _ _` mp_tac >>
  qpat_x_assum `_ with <| vs_vars := _; vs_allocas := _;
                         vs_alloca_next := _; vs_inst_idx := _ |> = s` mp_tac >>
  simp[dec_frame_def, moduleLoweringPropsTheory.vars_pc_only_def,
       venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

(* ===== The parameters ===== *)
Theorem entry_register_index_phases:
  !args cenv0 tenv vals env i cenv m off st cf sf func.
    i < LENGTH args /\ dec_cenv_agrees cenv0 tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) =
      SOME (MemLoc m (type_memory_bytes cenv0 (SND (EL i args)))) /\
    compile_register_positional_args cenv
      (build_positional_args cenv0 (DROP i args)) off st = (cf,sf) /\
    fn_has_code st sf func ==>
    ?buf sa sb.
      compile_alloc_buffer (type_memory_bytes cenv0 (SND (EL i args))) st = (buf,sa) /\
      let cenv1 = cenv with ce_vars updated_by (\v. v |+
        (FST (EL i args), PtrVar buf.buf_operand
           (type_memory_bytes cenv0 (SND (EL i args))))) in
      compile_decode_args cenv1 [build_positional_arg cenv0 (EL i args)]
        off CALLDATALOAD (Lit 0w) 4 sa = ((),sb) /\
      compile_register_positional_args cenv1
        (build_positional_args cenv0 (DROP (SUC i) args))
        (off + abi_embedded_static_size cenv0.ce_struct_fields (SND (EL i args)))
        sb = (cf,sf) /\
      fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb sf func /\
      sa.cs_next_id <= sb.cs_next_id
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `DROP i args = EL i args :: DROP (SUC i) args` by
    metis_tac[DROP_CONS_EL] >>
  `EVERY (\(name,prim,dyn,sz,info).
    prim \/ (~dyn /\ ?n. static_dec info n)) (build_positional_args cenv0 args)` by
    (irule build_positional_args_admissible >> metis_tac[]) >>
  `EVERY (\(name,prim,dyn,sz,info).
    prim \/ (~dyn /\ ?n. static_dec info n))
      (build_positional_args cenv0 (DROP i args))` by
    (metis_tac[build_positional_args_drop, EVERY_DROP]) >>
  Cases_on `EL i args` >> rename1 `EL i args = (name,ty)` >>
  gvs[build_positional_args_def, build_positional_arg_def] >>
  drule register_positional_args_step >>
  simp[var_location_memory_size_def] >> strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  first_x_assum (fn th => rewrite_tac[th]) >> strip_tac >>
  drule compile_alloc_buffer_straight >> strip_tac >>
  `dec_straight sa sb /\ sa.cs_next_id <= sb.cs_next_id` by
    (irule compile_decode_arg_straight >>
     qpat_assum `compile_decode_args _ _ _ _ _ _ _ = _` (irule_at Any) >>
     simp[FLOOKUP_UPDATE, var_location_decode_operand_def] >> metis_tac[]) >>
  `dec_straight sb sf` by
    (irule (cj 1 register_positional_args_straight) >>
     qpat_assum `compile_register_positional_args _ _ _ _ = _` (irule_at Any) >>
     simp[]) >>
  `fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb sf func` by
    (irule dec_straight_code_phases >> metis_tac[]) >>
  qexistsl_tac [`buf`, `sa`, `sb`] >> simp[]
QED

Theorem entry_register_index_step:
  !args cenv0 tenv vals env fname i cenv st s cf sf ctx func off q.
    dec_cenv_agrees cenv0 tenv /\ ALL_DISTINCT (MAP FST args) /\
    EVERY (\a. ?m. FLOOKUP cenv0.ce_vars (FST a) =
      SOME (MemLoc m (type_memory_bytes cenv0 (SND a)))) args /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
      (TAKE i args)) /\
    q = SUM (MAP (type_memory_bytes cenv0 o SND) (TAKE i args)) /\
    compile_register_positional_args cenv
      (build_positional_args cenv0 (DROP i args)) off st = (cf,sf) /\
    fn_has_code st sf func /\ local_ptrs_rel func cenv [env] s /\
    EVERY (\a. FLOOKUP cenv.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
      (DROP i args) /\
    s.vs_alloca_next = q /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    fresh_vars_wrt st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    calldata_encodes tenv fname (MAP SND args) vals s.vs_call_ctx.cc_calldata /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
    ?sb cenv1 t.
      compile_register_positional_args cenv1
        (build_positional_args cenv0 (DROP (SUC i) args))
        (4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
          (TAKE (SUC i) args))) sb = (cf,sf) /\
      fn_has_code sb sf func /\ local_ptrs_rel func cenv1 [env] t /\
      EVERY (\a. FLOOKUP cenv1.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
        (DROP (SUC i) args) /\
      t.vs_alloca_next = SUM (MAP (type_memory_bytes cenv0 o SND)
        (TAKE (SUC i) args)) /\
      (!aid. sb.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE) /\
      fresh_vars_wrt sb t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next;
                vs_inst_idx := s.vs_inst_idx |> = s /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP cenv.ce_vars (FST (EL i args)) =
     FLOOKUP cenv0.ce_vars (FST (EL i args))` by
    (fs[EVERY_MEM] >> first_x_assum irule >>
     metis_tac[DROP_CONS_EL, MEM]) >>
  `?m. FLOOKUP cenv.ce_vars (FST (EL i args)) =
     SOME (MemLoc m (type_memory_bytes cenv0 (SND (EL i args))))` by
    (fs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  drule_all entry_register_index_phases >> strip_tac >>
  drule_all bind_arguments_lookup_index >> strip_tac >>
  fs[LET_THM] >>
  qabbrev_tac `n = type_memory_bytes cenv0 (SND (EL i args))` >>
  SUBGOAL_THEN
    ``is_word_type (SND (EL i (args : (string # type) list))) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))`` assume_tac
  >- (fs[EVERY_EL]) >>
  `int_byte_widths tv` by (fs[EVERY_EL] >> metis_tac[]) >>
  `type_memory_size tv = n` by
    (fs[dec_cenv_agrees_def, Abbr `n`] >> metis_tac[]) >>
  `val_wf tv (EL i vals)` by (irule bind_arguments_memory_wf >> metis_tac[]) >>
  `EVERY (\a. is_word_type (SND a) \/
    ~is_dynamic (vyper_to_abi_type tenv (SND a))) args` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `off = 4 + q` by
    (drule_all entry_static_prefix_sizes >>
     disch_then (qspec_then `i` assume_tac) >> simp[]) >>
  `4 + q + n < dimword (:256)` by
    (drule_all entry_static_prefix_bound >> simp[Abbr `n`] >> metis_tac[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_decode_args c1 _ _ _ _ _ _ = _` >>
  `!a. fresh_vars_wrt sa a /\
       lookup_var (STRING #"%" (toString st.cs_next_var)) a =
         SOME (n2w s.vs_alloca_next) /\ a.vs_call_ctx = s.vs_call_ctx ==>
     frag_exec ctx sa sb (\u. u = a)
       (\t. dec_frame sa s.vs_alloca_next n a t /\ fresh_vars_wrt sb t /\
            val_in_memory tv (EL i vals) s.vs_alloca_next t.vs_memory /\
            t.vs_prev_bb = a.vs_prev_bb /\ t.vs_current_bb = a.vs_current_bb)
       (\r. F)` by
    (rpt gen_tac >> strip_tac >>
     `w2n (n2w s.vs_alloca_next : bytes32) = s.vs_alloca_next` by
       (simp[w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
     `s.vs_alloca_next = w2n (n2w s.vs_alloca_next : bytes32)` by simp[] >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     qpat_assum `type_memory_size tv = n` (fn th => rewrite_tac[GSYM th]) >>
     irule entry_decode_arg_frame_pc >>
     simp[] >>
     qpat_assum `bind_arguments _ _ _ = _` (irule_at Any) >>
     qpat_assum `dec_cenv_agrees _ _` (irule_at Any) >>
     qexistsl_tac [`PtrVar buf.buf_operand n`, `Lit 0w`, `fname`,
       `buf.buf_operand`, `c1`] >>
     simp[Abbr `c1`, FLOOKUP_UPDATE, var_location_decode_operand_def,
          eval_operand_def] >>
     gvs[]) >>
  `lookup_scopes (FST (EL i args)) [env] =
     SOME <| assignable := T; type := tv; value := EL i vals |>` by
    simp[lookup_scopes_def] >>
  `!p sz. FLOOKUP cenv.ce_vars (FST (EL i args)) <>
     SOME (PtrVar (Var p) sz)` by (rpt gen_tac >>
      qpat_assum `FLOOKUP cenv.ce_vars _ = SOME (MemLoc _ _)`
        (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  `n < dimword (:256) /\ s.vs_alloca_next < dimword (:256)` by decide_tac >>
  drule_at (Pat `lookup_scopes _ _ = _`) entry_register_arg_runtime >>
  simp[] >> disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`sb`, `ctx`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  `TAKE (SUC i) args = TAKE i args ++ [EL i args]` by
    (qpat_x_assum `i < LENGTH args` mp_tac >>
     map_every qid_spec_tac [`i`, `args`] >>
     POP_ASSUM_LIST (K all_tac) >> Induct >> simp[] >>
     qx_gen_tac `arg` >> Cases >> simp[]) >>
  qexistsl_tac [`sb`, `c1`, `t`] >>
  simp[MAP_APPEND, SUM_APPEND, Abbr `c1`] >>
  conj_tac >- gvs[] >>
  `DROP i args = EL i args :: DROP (SUC i) args` by metis_tac[DROP_CONS_EL] >>
  `ALL_DISTINCT (MAP FST (DROP i args))` by
    metis_tac[ALL_DISTINCT_DROP, MAP_DROP] >>
  `~MEM (FST (EL i args)) (MAP FST (DROP (SUC i) args))` by
    (qpat_x_assum `ALL_DISTINCT (MAP FST (DROP i args))` mp_tac >>
     qpat_assum `DROP i args = _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  `EVERY (\a. FLOOKUP cenv.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
    (DROP (SUC i) args)` by fs[] >>
  drule entry_ptr_update_remaining >>
  disch_then (qspecl_then [`cenv`, `buf.buf_operand`, `n`] mp_tac) >>
  simp[EVERY_MEM] >> fs[EVERY_MEM]
QED


Theorem entry_register_suffix_local_ptrs:
  !cenv0 tenv args vals env fname ctx func i cenv st s cf sf.
    dec_cenv_agrees cenv0 tenv /\ ALL_DISTINCT (MAP FST args) /\
    EVERY (\a. ?m. FLOOKUP cenv0.ce_vars (FST a) =
      SOME (MemLoc m (type_memory_bytes cenv0 (SND a)))) args /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args /\
    bind_arguments tenv args vals = SOME env /\ i <= LENGTH args /\
    compile_register_positional_args cenv
      (build_positional_args cenv0 (DROP i args))
      (4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
        (TAKE i args))) st = (cf,sf) /\
    fn_has_code st sf func /\ local_ptrs_rel func cenv [env] s /\
    EVERY (\a. FLOOKUP cenv.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
      (DROP i args) /\
    s.vs_alloca_next = SUM (MAP (type_memory_bytes cenv0 o SND) (TAKE i args)) /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    fresh_vars_wrt st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    calldata_encodes tenv fname (MAP SND args) vals s.vs_call_ctx.cc_calldata /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
    ?t. local_ptrs_rel func cf [env] t /\
        t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next;
                  vs_inst_idx := s.vs_inst_idx |> = s /\
        fresh_vars_wrt sf t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
          ?fuel'. run_from fuel' ctx func s = r)
Proof
  ntac 8 gen_tac >> measureInduct_on `LENGTH args - i` >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `i = LENGTH args`
  >- (gvs[build_positional_args_def, register_positional_args_nil] >>
      qexists_tac `s` >> simp[venom_state_component_equality] >> metis_tac[]) >>
  `i < LENGTH args` by decide_tac >>
  drule_at (Pat `compile_register_positional_args _ _ _ _ = _`)
    entry_register_index_step >> simp[] >> disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `local_ptrs_rel func cenv1 [env] u` >>
  `u.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `_ with <| vs_memory := _; vs_vars := _;
       vs_inst_idx := _; vs_allocas := _; vs_alloca_next := _ |> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qpat_x_assum `!y. LENGTH args - y < _ ==> _`
    (qspec_then `SUC i` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`cenv1`, `sb`, `u`, `cf`, `sf`] mp_tac) >>
  impl_tac >- gvs[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (qpat_x_assum `_ with <| vs_vars := _; vs_memory := _;
         vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = u` mp_tac >>
      qpat_x_assum `_ with <| vs_memory := _; vs_vars := _;
         vs_inst_idx := _; vs_allocas := _; vs_alloca_next := _ |> = s` mp_tac >>
      simp[venom_state_component_equality]) >>
  metis_tac[]
QED

(* Allocating and decoding the parameters from calldata that encodes the
   call puts each argument's value at its own fresh ALLOCA, the parameters
   in scope being env, the arguments bound.  Only word arguments and
   static ones (no dynamic ABI encoding, #762); integer widths are whole
   bytes (#733).  Nothing but variables, memory and allocations changes,
   and nothing reverts. *)
(* Why it holds: every argument is word or ABI-static, so calldata is the
   selector then the static tuple encoding, of length 4 + the sum of the
   arguments' memory sizes (dec_cenv_agrees, static_length_memory_size);
   that bound keeps every offset, ALLOCA base and size below dimword.
   ALLOCAs are bump-allocated from 0 with no alignment, so argument i's
   region starts at the sum of the earlier sizes, disjoint from the others.
   The decode code is straight-line (no new blocks), so the ALLOCAs stay in
   st'.cs_current_bb and fn_has_code puts them in func.  The bound values
   are the arguments (bind_arguments, safe_cast_some_eq) and satisfy val_wf
   by their typing.  An induction over a suffix of the arguments, with a
   general calldata offset, alloca_next and vs_allocas, gives the base case
   stated here. *)
Theorem register_positional_args_local_ptrs:
  !cenv0 tenv fname fargs vals env st cenv st' ctx func s0.
    compile_register_positional_args cenv0
      (build_positional_args cenv0 fargs) 4 st = (cenv, st') /\
    dec_cenv_agrees cenv0 tenv /\
    ALL_DISTINCT (MAP FST fargs) /\
    EVERY (\a. ?off. FLOOKUP cenv0.ce_vars (FST a) =
                     SOME (MemLoc off (type_memory_bytes cenv0 (SND a)))) fargs /\
    EVERY (\a. is_word_type (SND a) \/
               (assignable_type tenv (SND a) /\
                ~is_dynamic (vyper_to_abi_type tenv (SND a)))) fargs /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
                    int_byte_widths tv) fargs /\
    bind_arguments tenv fargs vals = SOME env /\
    calldata_encodes tenv fname (MAP SND fargs) vals
      s0.vs_call_ctx.cc_calldata /\
    LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) /\
    s0.vs_allocas = FEMPTY /\ s0.vs_alloca_next = 0 /\
    fresh_vars_wrt st s0 /\ fn_has_code st st' func /\ ~s0.vs_halted /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. local_ptrs_rel func cenv [env] t /\
        t with <| vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
                  vs_allocas := s0.vs_allocas;
                  vs_alloca_next := s0.vs_alloca_next;
                  vs_inst_idx := s0.vs_inst_idx |> = s0 /\
        fresh_vars_wrt st' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule entry_register_suffix_local_ptrs >>
  simp[] >>
  qexistsl_tac [`fargs`, `cenv0`, `cenv0`, `fname`, `0`, `st`, `tenv`, `vals`] >>
  simp[] >> metis_tac[bind_arguments_initial_local_ptrs]
QED
