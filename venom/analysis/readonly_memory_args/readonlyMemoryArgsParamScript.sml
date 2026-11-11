Theory readonlyMemoryArgsParam
Ancestors readonlyMemoryArgsSound readonlyMemoryArgsDefs finite_map list rich_list
  venomWf venomInst invokeCopyFwdCommonDefs

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
