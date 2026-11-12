(* Stack layout is independent of package code-generation options. *)
Theory bodyIntCallPackageResource
Ancestors
  bodyIntCallResource compileVyper intCallCallee compileEnv context list
  loweringShapeDefs exprLoweringProps venomInst

Theorem internal_package_stack_layout:
  !target tops trans keys ctor imm mut nr rr name args dflts ret body
   lbl ce params has_rb is_nr key use_tr view is_ctor imm_len ss rt.
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm
      (mut,nr,rr,name,args,dflts,ret,body)) =
    (lbl,ce,params,has_rb,is_nr,key,use_tr,view,is_ctor,imm_len,ss,rt) ==>
  ce.ce_vars =
    (build_compile_env tops Internal mut name args ret body F).ce_vars /\
  params = ZIP (MAP FST args,
    compute_pass_via_stack (MAP SND args)
      (returns_stack_count
        (\n. MAP (FST o SND)
          (get_struct_fields (make_struct_fields_map tops) n)) ret))
Proof
  rpt gen_tac >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

(* Preserve multiplicity: extension appends an instruction list, not a set. *)
Theorem state_alloca_charge_mono:
  cs_extends sa sb ==>
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sa))) <=
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sb)))
Proof
  strip_tac >> drule state_insts_cs_extends >>
  disch_then SUBST1_TAC >>
  simp[FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND]
QED

Theorem materialized_stack_charge_bound:
  !caps ce sa ce' sm sb.
  materialize_internal_params ce caps sa = (ce',sm) /\
  ALL_DISTINCT (MAP FST caps) /\
  (!nm off sz. MEM nm (MAP FST caps) /\
     FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==>
     sz < dimword (:256)) /\ cs_extends sm sb ==>
  internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps) <=
  SUM (MAP alloca_lit_size
    (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sb)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all materialize_internal_params_charge >> strip_tac >>
  drule state_alloca_charge_mono >>
  simp[state_insts_def, all_blocks_def, FILTER_APPEND_DISTRIB,
       MAP_APPEND, SUM_APPEND] >> decide_tac
QED
