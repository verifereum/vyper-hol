Theory ctorDeployLoweringEntryTransport
Ancestors
  valueEncodingDefs
 structFieldsProps
 ctorSourceInputs ctorDeployLoweringEntryQuantitativeInputs compileVyper
 compileEnv entryStateRel vyperContext vyperState valueEncoding finite_map list
 ctorDeployDefs e2eDeployDefs e2eEntry o1PassContract rich_list
 ctorDeployLoweringDefs deployUnitProducers unitShapeDefs venomExecSemantics
 venomInst venomState ctorDeployShape venomExecProps ctorDeployInitcode

Theorem deploy_ctor_singleton_type_env:
 type_env_all_modules [(NONE,tops)] = type_env tops
Proof
 simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2]
QED

Theorem deploy_ctor_target_package_layout:
 !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
 target ce pos_args imm ce0.
 set_constructor_package_target target
  (package_constructor tops use_trans nkey_map
   (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
  (ce,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
 ce0 = (ce with ce_imm_alloca := imm) ==>
 pos_args = build_positional_args ce0 fargs /\
 ce0.ce_struct_fields =
  (build_compile_env tops Deploy mut fname fargs ret fbody use_trans).ce_struct_fields /\
 ce0.ce_flag_n_members =
  (build_compile_env tops Deploy mut fname fargs ret fbody use_trans).ce_flag_n_members /\
 ce0.ce_vars =
  (build_compile_env tops Deploy mut fname fargs ret fbody use_trans).ce_vars
Proof
 simp[package_constructor_def, set_constructor_package_target_def,
      update_cenv_nonreentrant_def] >> rpt strip_tac >>
 gvs[build_positional_args_imm_alloca] >>
 irule build_positional_args_layout_cong >> simp[]
QED

Theorem deploy_ctor_argument_bounds_transport:
 !(args : (string # type) list) cenv ce0.
 EVERY (\a. type_memory_bytes cenv (SND a) < 2 ** 64) args /\
 ce0.ce_struct_fields = cenv.ce_struct_fields ==>
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword(:256)) args
Proof
 rpt strip_tac >> drule type_memory_bytes_frame >> strip_tac >>
 gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
 CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem deploy_ctor_entry_data_section:
 !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
 deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) ==>
 constructor_args_encode tops tx vs.vs_data_section
Proof
 rpt strip_tac >>
 `vs.vs_data_section = (deploy_entry_state prog cplan tops es).vs_data_section` by
  (gvs[gas_variant_def] >>
   pop_assum (mp_tac o Q.AP_TERM `\s. s.vs_data_section`) >> simp[]) >>
 gvs[deploy_phases_def, deploy_state_rel_def,
     deploy_entry_state_def, entry_venom_state_def, DROP_LENGTH_APPEND]
QED

Theorem deploy_ctor_prefix_data_bytes:
 !tops tx vs initial.
 constructor_args_encode tops tx vs.vs_data_section /\
 initial.vs_data_section = vs.vs_data_section ==>
 ?mut args body avs.
 lookup_function NONE "__init__" Deploy tops =
   SOME (mut,F,args,[],NoneT,body) /\
 vyper_to_abi_list (type_env tops) (MAP SND args) tx.args = SOME avs /\
 mem_bytes_at 0
  (LENGTH (enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs)))
  initial.vs_data_section =
  enc (Tuple (vyper_to_abi_types (type_env tops) (MAP SND args))) (ListV avs)
Proof
 rpt strip_tac >> gvs[constructor_args_encode_def] >>
 simp[mem_bytes_at_def, TAKE_LENGTH_APPEND]
QED

Theorem deploy_ctor_raw_blocks_no_phi:
 !tops rp runtime unit body ce nr key ut imm lbl sa sb sj se sp sf func bb label.
 supported_program tops /\
 deploy_ctor_code tops rp runtime unit
  (body,ce,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\
 lookup_block label func.fn_blocks = SOME bb ==>
 phi_prefix_length bb.bb_instructions = 0
Proof
 rpt gen_tac >> strip_tac >> fs[deploy_ctor_code_def] >>
 drule_all lower_vyper_deploy_unit_source_unit_ok >> strip_tac >>
 `EVERY (\inst. raw_opcode_ok inst.inst_opcode) (fn_insts func)` by
  (gvs[o1_source_unit_ok_def, EVERY_MEM] >>
   qpat_x_assum `!fn. MEM fn _ ==> !inst. _`
    (drule_then assume_tac) >> simp[]) >>
 `MEM bb func.fn_blocks` by
  metis_tac[lookup_block_MEM] >>
 Cases_on `bb.bb_instructions` >> simp[phi_prefix_length_def] >>
 qpat_x_assum `EVERY _ (fn_insts func)` mp_tac >>
 simp[fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >>
 disch_then (qspec_then `h` mp_tac) >>
 impl_tac >- (qexists `bb` >> simp[]) >>
 simp[raw_opcode_ok_def]
QED

Theorem deploy_ctor_entry_data_size:
 !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs.
 deploy_phases policy tops (deploy_bc,runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
 deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
 gas_variant vs (deploy_entry_state prog cplan tops es) ==>
 LENGTH vs.vs_data_section < dimword(:256)
Proof
 rpt strip_tac >> drule_all deploy_ctor_entry_data_section >> strip_tac >>
 drule_all constructor_args_size_bounded >>
 CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem deploy_ctor_target_package_memlocs:
 !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
 target ce pos_args imm ce0.
 set_constructor_package_target target
  (package_constructor tops use_trans nkey_map
   (mut,nr,rr,fname,fargs,dflts,ret,fbody)) =
  (ce,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
 ce0 = (ce with ce_imm_alloca := imm) /\ ALL_DISTINCT (MAP FST fargs) ==>
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
  SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs
Proof
 rpt gen_tac >> strip_tac >> drule_all deploy_ctor_target_package_layout >> strip_tac >>
 `ce0.ce_struct_fields = make_struct_fields_map tops` by
  simp[build_compile_env_ce_struct_fields] >>
 `ce0.ce_vars = FST (allocate_args
    (get_struct_fields (make_struct_fields_map tops)) fargs 0 FEMPTY)` by
  (simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
 drule_then (qspecl_then [`get_struct_fields (make_struct_fields_map tops)`,
  `0`, `FEMPTY`] strip_assume_tac) allocate_args_lookup >>
 gvs[EVERY_MEM, GSYM type_mem_bytes_type_memory_bytes]
QED
