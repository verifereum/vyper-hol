Theory readonlyMemoryArgsParam
Ancestors readonlyMemoryArgsSound readonlyMemoryArgsDefs finite_map list rich_list
  venomWf venomInst invokeCopyFwdCommonDefs allocaRemapSSA
  readonlyMemoryArgsOrigin dfgAnalysisProps pointerConfinedDefs

Theorem param_index_fold_absent:
  !params fm (i:num) v.
    ~MEM v params ==>
    FLOOKUP (FST (FOLDL (\(fm,i) x. (fm |+ (x,i), i+1))
      (fm,i) params)) v = FLOOKUP fm v
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[FLOOKUP_UPDATE]
QED

Theorem param_index_fold_lookup:
  !params fm i k.
    ALL_DISTINCT params /\ k < LENGTH params ==>
    FLOOKUP (FST (FOLDL (\(fm,i) x. (fm |+ (x,i), i+1))
      (fm,i) params)) (EL k params) = SOME (i+k)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `k` >> simp[]
  >- (drule param_index_fold_absent >>
      disch_then (qspecl_then [`fm |+ (h,i)`, `i+1`] mp_tac) >>
      simp[FLOOKUP_UPDATE]) >>
  first_x_assum irule >> simp[]
QED

Theorem build_param_index_lookup:
  !params k. ALL_DISTINCT params /\ k < LENGTH params ==>
    FLOOKUP (build_param_index params) (EL k params) = SOME k
Proof
  simp[build_param_index_def, param_index_fold_lookup]
QED

Theorem collect_param_info_index:
  !fn_meta fn params k.
    params = (case entry_block fn of NONE => []
              | SOME bb => entry_param_outputs bb.bb_instructions) /\
    ALL_DISTINCT params /\
    k < LENGTH (collect_param_info fn_meta fn).fpi_invoke_params ==>
    FLOOKUP (collect_param_info fn_meta fn).fpi_invoke_param_index
      (EL k params) = SOME k
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `params = _` (fn th => fs[GSYM th, collect_param_info_def]) >>
  Cases_on `NULL params` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `build_param_index (TAKE cnt params)` >>
  `k < LENGTH (TAKE cnt params)` by gvs[Abbr `cnt`] >>
  `EL k params = EL k (TAKE cnt params)` by (gvs[LENGTH_TAKE_EQ] >> simp[EL_TAKE]) >>
  pop_assum SUBST1_TAC >> irule build_param_index_lookup >>
  simp[ALL_DISTINCT_TAKE]
QED

Theorem entry_param_outputs_mem:
  !insts v. MEM v (entry_param_outputs insts) ==>
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts))
Proof
  Induct >> simp[entry_param_outputs_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem entry_param_outputs_distinct:
  !insts. ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) ==>
    ALL_DISTINCT (entry_param_outputs insts)
Proof
  Induct >> simp[entry_param_outputs_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[ALL_DISTINCT_APPEND] >>
  first_x_assum drule >> strip_tac >> simp[] >>
  metis_tac[entry_param_outputs_mem]
QED

Theorem wf_ssa_entry_param_outputs_distinct:
  !fn. wf_ssa fn ==>
    ALL_DISTINCT (case entry_block fn of NONE => []
      | SOME bb => entry_param_outputs bb.bb_instructions)
Proof
  rpt strip_tac >> Cases_on `fn.fn_blocks` >>
  gvs[entry_block_def, wf_ssa_def, ssa_form_def, fn_insts_def,
      fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  irule entry_param_outputs_distinct >> simp[]
QED

Theorem ricf_param_index_lookup:
  !fn_meta fn inst idx v.
    wf_ssa fn /\ ricf_param_order_ok fn /\
    MEM inst (fn_insts fn) /\ inst.inst_opcode = PARAM /\
    inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [v] /\
    w2n idx < LENGTH (collect_param_info fn_meta fn).fpi_invoke_params ==>
    FLOOKUP (collect_param_info fn_meta fn).fpi_invoke_param_index v =
      SOME (w2n idx)
Proof
  rpt gen_tac >> strip_tac >>
  drule wf_ssa_entry_param_outputs_distinct >> strip_tac >>
  fs[ricf_param_order_ok_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  irule collect_param_info_index >> simp[]
QED

Theorem entry_param_outputs_origin:
  !insts v. MEM v (entry_param_outputs insts) ==>
    ?inst. MEM inst insts /\ inst.inst_opcode = PARAM /\
      MEM v inst.inst_outputs
Proof
  Induct >> simp[entry_param_outputs_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem collect_param_info_nonparam_absent:
  !fn_meta fn inst v.
    ssa_form fn /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PARAM /\ MEM v inst.inst_outputs ==>
    FLOOKUP (collect_param_info fn_meta fn).fpi_invoke_param_index v = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM v (case entry_block fn of NONE => []
    | SOME bb => entry_param_outputs bb.bb_instructions)` by
    (Cases_on `fn.fn_blocks` >> simp[entry_block_def] >> strip_tac >>
     drule entry_param_outputs_origin >> strip_tac >>
     `MEM inst' (fn_insts fn)` by
       gvs[fn_insts_def, fn_insts_blocks_def, MEM_FLAT, MEM_MAP] >>
     metis_tac[ssa_unique_output]) >>
  simp[collect_param_info_def] >> IF_CASES_TAC >> simp[] >>
  simp[build_param_index_def, param_index_fold_absent,
       MEM_TAKE] >>
  irule EQ_TRANS >>
  irule_at Any param_index_fold_absent >> simp[] >>
  metis_tac[MEM_TAKE]
QED

Theorem rma_origin_pointer_preserving:
  !fn_meta fn inst u v k.
    ssa_form fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ MEM v inst.inst_outputs /\
    rma_origin (dfg_build_function fn)
      (collect_param_info fn_meta fn).fpi_invoke_param_index u k ==>
    rma_origin (dfg_build_function fn)
      (collect_param_info fn_meta fn).fpi_invoke_param_index v k
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> PARAM` by
    (Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def]) >>
  drule_all collect_param_info_nonparam_absent >> strip_tac >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >>
  `inst' = inst` by metis_tac[ssa_unique_output] >> gvs[] >>
  irule (cj 2 rma_origin_rules) >> simp[] >>
  qexists_tac `u` >> simp[] >>
  metis_tac[root_from_inst_ops_pointer_preserving]
QED
