(* Static calling convention for the checked, qualified source callee. *)
Theory bodyIntCallArgMetadataMods
Ancestors
  bodyIntCallSource bodyInvMetadataProps bodyInvSplit compileUnit compileEnv
  structFieldsProps linkedNsidProps vyperTypeContractContext vyperTypeContract
  venomFnInstsProofs list pair alist words

Triviality arg_metadata_src_fold:
  !tops info params result.
    (!v m n raw f a d r b.
       MEM (FunctionDecl v m n raw f a d r b) tops /\ v <> External /\
       nsid_to_string (src,f) = key ==> a = args /\ r = ret) ==>
    let hit = ?v m n raw f a d r b.
      MEM (FunctionDecl v m n raw f a d r b) tops /\ v <> External /\
      nsid_to_string (src,f) = key in
      build_func_info_src sft src tops info key =
        (if hit then compute_func_info (\s. MAP (FST o SND) (sft s)) ret
                       (type_mem_bytes sft ret) (MAP SND args) else info key) /\
      build_func_param_types_src src tops params key =
        (if hit then MAP SND args else params key) /\
      build_func_return_type_src src tops result key =
        (if hit then ret else result key)
Proof
  Induct
  >- simp[build_func_info_src_def, build_func_param_types_src_def,
          build_func_return_type_src_def] >>
  Cases >> rpt gen_tac >> disch_tac >>
  pure_rewrite_tac[build_func_info_src_def, build_func_param_types_src_def,
                   build_func_return_type_src_def, LET_THM, MEM] >>
  SIMP_TAC bool_ss [vyperASTTheory.toplevel_case_def, vyperASTTheory.toplevel_distinct,
                    vyperASTTheory.toplevel_11, COND_RATOR] >>
  `!v m n raw f a d r b. MEM (FunctionDecl v m n raw f a d r b) tops /\
       v <> External /\ nsid_to_string (src,f) = key ==> a = args /\ r = ret` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) tops` mp_tac >>
     metis_tac[MEM]) >>
  qpat_x_assum `!info params result. _ ==> _`
    (qspecl_then [`info`,`params`,`result`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  SIMP_TAC bool_ss [RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  qpat_x_assum `build_func_info_src _ _ _ _ _ = _` SUBST1_TAC >>
  qpat_x_assum `build_func_param_types_src _ _ _ _ = _` SUBST1_TAC >>
  qpat_x_assum `build_func_return_type_src _ _ _ _ = _` SUBST1_TAC >>
  SIMP_TAC bool_ss [] >>
  rename1 `if vis = External then _ else _` >>
  rename1 `key = nsid_to_string (src,name)` >>
  Cases_on `vis = External`
  >- (pop_assum (fn th => SIMP_TAC bool_ss [th])) >>
  Cases_on `key = nsid_to_string (src,name)`
  >- (qmatch_goalsub_rename_tac
        `if key = nsid_to_string (src,name) then
           compute_func_info _ ret' _ (MAP SND args') else _` >>
      `args' = args /\ ret' = ret` by metis_tac[MEM] >>
      qpat_x_assum `!v m n raw f a d r b. _` kall_tac >>
      qpat_x_assum `!v m n raw f a d r b. _` kall_tac >> simp[]) >>
  qpat_x_assum `!v m n raw f a d r b. _` kall_tac >>
  qpat_x_assum `!v m n raw f a d r b. _` kall_tac >>
  simp[Once EQ_SYM_EQ]
QED

Triviality arg_metadata_mods_fold:
  !mods.
    (!src tops v m n raw f a d r b.
       MEM (src,tops) mods /\ MEM (FunctionDecl v m n raw f a d r b) tops /\
       v <> External /\ nsid_to_string (src,f) = key ==> a = args /\ r = ret) ==>
    let hit = ?src tops v m n raw f a d r b.
      MEM (src,tops) mods /\ MEM (FunctionDecl v m n raw f a d r b) tops /\
      v <> External /\ nsid_to_string (src,f) = key in
      build_func_info_mods sft mods key =
        (if hit then compute_func_info (\s. MAP (FST o SND) (sft s)) ret
                       (type_mem_bytes sft ret) (MAP SND args) else (0,0,[])) /\
      build_func_param_types_mods mods key = (if hit then MAP SND args else []) /\
      build_func_return_type_mods mods key = (if hit then ret else NoneT)
Proof
  Induct
  >- simp[build_func_info_mods_def, build_func_param_types_mods_def,
          build_func_return_type_mods_def] >>
  Cases >> rpt gen_tac >>
  rename1 `build_func_info_mods _ ((owner,decls)::mods) _` >> disch_tac >>
  `!src tops v m n raw f a d r b.
       MEM (src,tops) mods /\ MEM (FunctionDecl v m n raw f a d r b) tops /\
       v <> External /\ nsid_to_string (src,f) = key ==> a = args /\ r = ret`
     by metis_tac[MEM] >>
  `!v m n raw f a d r b. MEM (FunctionDecl v m n raw f a d r b) decls /\
       v <> External /\ nsid_to_string (owner,f) = key ==> a = args /\ r = ret`
     by metis_tac[MEM] >>
  first_x_assum (drule_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM])) >>
  drule arg_metadata_src_fold >>
  disch_then (qspecl_then [`sft`, `build_func_info_mods sft mods`,
    `build_func_param_types_mods mods`, `build_func_return_type_mods mods`] mp_tac) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  rpt (PRED_ASSUM boolSyntax.is_forall kall_tac) >>
  ASM_SIMP_TAC bool_ss [build_func_info_mods_def, build_func_param_types_mods_def,
     build_func_return_type_mods_def, LET_THM, MEM, PAIR_EQ,
     RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  qabbrev_tac `hit = ?v m n raw f a d r b.
    MEM (FunctionDecl v m n raw f a d r b) decls /\ v <> External /\
    nsid_to_string (owner,f) = key` >>
  Cases_on `hit` >> simp[]
QED

(* Printed keys are unambiguous in the checked self namespace, even when
   two modules declare the same unqualified name. *)
Triviality selected_function_row_unique:
  contract_namespaces_ok deploy mods /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops /\
  MEM (owner,decls) mods /\
  MEM (FunctionDecl v m n rr f a d r b) decls /\
  nsid_to_string (owner,f) = nsid_to_string (src,name) ==>
  a = args /\ r = ret
Proof
  strip_tac >>
  `MEM (src,tops) mods` by metis_tac[ALOOKUP_MEM] >>
  `!s ts v m n raw f a d r b.
     MEM (s,ts) mods /\ MEM (FunctionDecl v m n raw f a d r b) ts ==>
     ~MEM #"." f` by
    (qpat_assum `contract_namespaces_ok _ _`
       (strip_assume_tac o REWRITE_RULE [contract_namespaces_ok_def]) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `EVERY (\(_,tls). EVERY _ tls) mods`
       (mp_tac o REWRITE_RULE [EVERY_MEM, FORALL_PROD]) >>
     disch_then (qspec_then `(s,ts)` mp_tac) >> simp[] >>
     disch_then drule >> simp[]) >>
  `(owner,f) = (src,name)` by
    (irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
  gvs[] >>
  rename1 `ALOOKUP mods src = SOME tops` >>
  rename1 `MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops` >>
  `ALOOKUP mods src = SOME decls` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  `decls = tops` by fs[] >>
  qpat_x_assum `decls = tops` SUBST_ALL_TAC >>
  `ALL_DISTINCT (FLAT (MAP (self_member_keys_toplevel src) tops))` by
    (irule vyperTypeContractTheory.contract_keys_module_distinct >>
     qexists `mods` >> fs[contract_namespaces_ok_def]) >>
  `FunctionDecl v m n rr name a d r b =
   FunctionDecl vis mut nr raw name args ds ret ss` suffices_by simp[] >>
  drule all_distinct_flat_map_unique >>
  disch_then (qspecl_then [`FunctionDecl v m n rr name a d r b`,
    `FunctionDecl vis mut nr raw name args ds ret ss`,`(src,name)`] mp_tac) >>
  simp[self_member_keys_toplevel_def]
QED

Triviality selected_function_tables:
  contract_namespaces_ok deploy mods /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops /\
  vis <> External ==>
  let key = nsid_to_string (src,name) in
    build_func_info_mods sft mods key =
      compute_func_info (\s. MAP (FST o SND) (sft s)) ret
        (type_mem_bytes sft ret) (MAP SND args) /\
    build_func_param_types_mods mods key = MAP SND args /\
    build_func_return_type_mods mods key = ret
Proof
  strip_tac >> simp[] >>
  `MEM (src,tops) mods` by metis_tac[ALOOKUP_MEM] >>
  `?s ts v m n raw' f a d r b.
     MEM (s,ts) mods /\ MEM (FunctionDecl v m n raw' f a d r b) ts /\
     v <> External /\ nsid_to_string (s,f) = nsid_to_string (src,name)` suffices_by
    (disch_tac >>
     qspec_then `mods` mp_tac (Q.INST [`key` |-> `nsid_to_string (src,name)`]
       arg_metadata_mods_fold) >>
     (impl_tac >- (rpt gen_tac >> strip_tac >> metis_tac[selected_function_row_unique])) >>
     simp[]) >>
  qexistsl [`src`,`tops`,`vis`,`mut`,`nr`,`raw`,`name`,`args`,`ds`,`ret`,`ss`] >> simp[]
QED

Triviality arg_metadata_stack_flags:
  !tys n. LIST_REL (\ty stack. stack ==> is_word_type ty)
                   tys (compute_pass_via_stack tys n)
Proof
  Induct >> simp[compute_pass_via_stack_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[]
QED

Triviality arg_metadata_stack_returns_bound:
  returns_stack_count sft ty <= 2
Proof
  Cases_on `ty` >> simp[returns_stack_count_def, tuple_like_stack_count_def,
                        MAX_STACK_RETURNS_def] >> rw[]
QED

Triviality arg_metadata_info_layout:
  compute_func_info sft ret bytes_n tys =
  let rc = returns_stack_count sft ret in
    (rc, (if ret = NoneT \/ 0 < rc then 0 else bytes_n),
     compute_pass_via_stack tys rc)
Proof
  Cases_on `ret` >> simp[compute_func_info_def, arithmeticTheory.GREATER_DEF]
QED

Triviality arg_metadata_buffer_bound:
  (nret:num) <= 2 /\ (bytes_n:num) < 2 ** 64 ==>
  (if ret = NoneT \/ 0 < nret then 0 else bytes_n) < 2 ** 64 /\
  (if 0 < nret then 32 * nret else if ret = NoneT then 0 else bytes_n)
    < dimword (:256)
Proof
  simp[dimword_def] >> rpt strip_tac >> rw[] >> decide_tac
QED
(* No assumption or conclusion about the presence of an emitted target. *)
Theorem selected_arg_metadata_mods:
  contract_inv mods exps ctx cenv cx /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
  MEM (FunctionDecl vis mut nr raw name args ds ret ss) tops ==>
  let key = nsid_to_string (src,name) in
  let rc = returns_stack_count
    (\s. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields s)) ret in
  let rbs = if ret = NoneT \/ 0 < rc then 0 else type_memory_bytes cenv ret in
  let pvs = compute_pass_via_stack (MAP SND args) rc in
    cenv.ce_func_info key = (rc,rbs,pvs) /\
    cenv.ce_func_param_types key = MAP SND args /\
    cenv.ce_func_return_type key = ret /\
    cenv.ce_func_ids key = build_func_ids_mods 0 mods key /\
    cenv.ce_is_ctor = cx.in_deploy /\
    internal_fn_label (cenv.ce_func_ids key) key (cenv.ce_func_param_types key)
      cenv.ce_is_ctor =
    internal_fn_label (build_func_ids_mods 0 mods key) key (MAP SND args) cx.in_deploy /\
    LENGTH pvs = LENGTH args /\
    LIST_REL (\ty stack. stack ==> is_word_type ty) (MAP SND args) pvs /\
    rc <= 2 /\
    (type_memory_bytes cenv ret < 2 ** 64 ==>
     rbs < 2 ** 64 /\ (if 0 < rc then 32 * rc else rbs) < dimword (:256))
Proof
  strip_tac >>
  drule_then assume_tac check_contract_namespaces_ok >>
  `vis <> External` by metis_tac[vyperASTTheory.function_visibility_distinct] >>
  drule_all selected_function_tables >>
  disch_then (qspec_then `get_struct_fields cenv.ce_struct_fields` mp_tac) >>
  simp[type_mem_bytes_type_memory_bytes] >> strip_tac >>
  `cenv.ce_func_ids = build_func_ids_mods 0 mods /\
   cenv.ce_func_param_types = build_func_param_types_mods mods /\
   cenv.ce_func_return_type = build_func_return_type_mods mods /\
   cenv.ce_func_info = build_func_info_mods (get_struct_fields cenv.ce_struct_fields) mods /\
   cenv.ce_is_ctor = cx.in_deploy` by fs[contract_inv_def] >>
  simp[arg_metadata_info_layout, LENGTH_compute_pass_via_stack,
       arg_metadata_stack_flags, arg_metadata_stack_returns_bound] >>
  strip_tac >> irule (SIMP_RULE (srw_ss()) [] arg_metadata_buffer_bound) >>
  simp[arg_metadata_stack_returns_bound]
QED
