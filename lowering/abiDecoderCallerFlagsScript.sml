(* Flag metadata supplied by checked namespaces and compiler construction. *)
Theory abiDecoderCallerFlags
Ancestors
  compileVyper compileEnv exprLowering abiDecoderCoherence abiDecodeRanges
  vyperContext vyperABI valueEncoding contractABI vyperTypeContract
  finite_map list rich_list arithmetic

Theorem build_flag_info_count_unchanged[local]:
  !tops fmid fnm fid.
  ~MEM ((src:num option),fid)
    (FLAT (MAP (type_def_keys_toplevel src) tops)) ==>
  SND (build_flag_info tops fmid fnm) fid = fnm fid
Proof
  Induct_on `tops` >- simp[build_flag_info_def] >>
  qx_gen_tac `top` >> Cases_on `top` >>
  simp[build_flag_info_def, type_def_keys_toplevel_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem type_env_flag_declaration:
  !tops sid fid n.
  FLOOKUP (type_env_for_module src tops) (sid,fid) = SOME (FlagArgs n) ==>
  sid = src /\ ?members. MEM (FlagDecl fid members) tops /\ LENGTH members = n
Proof
  Induct_on `tops` >- simp[type_env_for_module_def] >>
  qx_gen_tac `top` >> Cases_on `top` >>
  simp[type_env_for_module_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem build_compile_env_ce_flag_n_members:
  !tops vis mut func_name args ret_type (body:stmt list) use_trans.
  (build_compile_env tops vis mut func_name args ret_type body use_trans).
    ce_flag_n_members = SND (build_flag_info tops (K (K 0)) (K 0))
Proof
  rpt strip_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem build_flag_info_append[local]:
  !pre post fmid fnm.
  build_flag_info (pre ++ post) fmid fnm =
    let (mid,count) = build_flag_info pre fmid fnm in
    build_flag_info post mid count
Proof
  Induct_on `pre` >- simp[build_flag_info_def] >>
  qx_gen_tac `top` >> Cases_on `top` >> simp[build_flag_info_def]
QED

Theorem build_flag_info_count_member[local]:
  !tops fmid fnm fid members.
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  MEM (FlagDecl fid members) tops ==>
  SND (build_flag_info tops fmid fnm) fid = LENGTH members
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM (FlagDecl fid members) tops`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 `tops = pre ++ FlagDecl fid members::post` >>
  gvs[MAP_APPEND, FLAT_APPEND, type_def_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  simp[build_flag_info_append] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[build_flag_info_def,
       Q.INST [`src` |-> `NONE:num option`] build_flag_info_count_unchanged]
QED

Theorem decoder_caller_flag_count:
  !tops vis mut func_name args ret_type (code_stmts:stmt list) use_trans
    in_deploy fid n.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  FLOOKUP (type_env tops) (NONE,fid) = SOME (FlagArgs n) ==>
  (build_compile_env tops vis mut func_name args ret_type code_stmts use_trans).
    ce_flag_n_members fid = n
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    fs[contract_namespaces_ok_def, contract_keys_def] >>
  qpat_x_assum `FLOOKUP (type_env tops) _ = _` mp_tac >>
  pure_rewrite_tac[type_env_def] >> strip_tac >>
  drule_all (Q.INST [`src` |-> `NONE:num option`] type_env_flag_declaration) >>
  simp[] >> strip_tac >> rename1 `MEM (FlagDecl fid members) tops` >>
  simp[build_compile_env_ce_flag_n_members] >>
  `SND (build_flag_info tops (K (K 0)) (K 0)) fid = LENGTH members` by
    (irule build_flag_info_count_member >> simp[]) >>
  gvs[]
QED

Theorem decoder_caller_flag:
  !tops vis mut func_name args ret_type (code_stmts:stmt list) use_trans
    in_deploy fid n sf.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) (FlagT (NONE,fid)) = SOME (FlagTV n) ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name args ret_type code_stmts use_trans)
    (type_env tops) sf (FlagT (NONE,fid)) (FlagTV n)
Proof
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `(build_compile_env tops vis mut func_name args ret_type code_stmts use_trans).
      ce_flag_n_members fid = n` by
    (irule decoder_caller_flag_count >> simp[] >>
     qexists_tac `in_deploy` >> first_assum ACCEPT_TAC) >>
  simp[abi_decoder_coherent_flag_iff, abi_decoder_header_def,
       vyperValueTheory.evaluate_type_def, type_memory_size_def,
       type_memory_bytes_def, is_abi_dynamic_def, nsid_to_string_def,
       abi_embedded_static_size_def, abi_static_size_def,
       abi_member_head_size_def, is_dynamic_def, static_length_def]
QED

Theorem decoder_caller_flag256:
  !tops vis mut func_name args ret_type (code_stmts:stmt list) use_trans
    in_deploy fid sf.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  FLOOKUP (type_env tops) (NONE,fid) = SOME (FlagArgs 256) ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name args ret_type code_stmts use_trans)
    (type_env tops) sf (FlagT (NONE,fid)) (FlagTV 256) /\
  type_to_abi_dec_info sf
    (build_compile_env tops vis mut func_name args ret_type code_stmts use_trans)
    (FlagT (NONE,fid)) = DecPrimWord NoClamp
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule decoder_caller_flag >> simp[vyperValueTheory.evaluate_type_def] >>
      qexists_tac `in_deploy` >> first_assum ACCEPT_TAC) >>
  `(build_compile_env tops vis mut func_name args ret_type code_stmts use_trans).
      ce_flag_n_members fid = 256` by
    (irule decoder_caller_flag_count >> simp[] >>
     qexists_tac `in_deploy` >> first_assum ACCEPT_TAC) >>
  simp[type_to_abi_dec_info_def, nsid_to_string_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CALLER_FLAGS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller flag metadata not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCallerFlags");
