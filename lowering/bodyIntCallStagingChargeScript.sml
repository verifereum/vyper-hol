(* Static instruction charge of caller-side internal argument staging. *)
Theory bodyIntCallStagingCharge
Ancestors
  bodyIntCallPackageResource externalEntryShape exprSimUnwrap loweringHalt
  exprLowering exprLoweringProps context emitHelper loweringShapeDefs compileEnv venomInst
  list words

Theorem compile_alloc_buffer_state_charge:
  !sz sa buf sb.
    compile_alloc_buffer sz sa = (buf,sb) /\ sz < dimword (:256) ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sb))) =
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sa))) + sz
Proof
  rpt strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  simp[state_insts_def, all_blocks_def, FILTER_APPEND_DISTRIB,
       MAP_APPEND, SUM_APPEND, alloca_lit_size_def, mk_inst_def]
QED

Theorem compile_stage_intcall_args_state_charge:
  !vals flags tys ce sa ops sb.
    compile_stage_intcall_args ce vals flags tys sa = (ops,sb) /\
    LENGTH vals = LENGTH flags /\ LENGTH vals = LENGTH tys /\
    EVERY (\ty. MAX 32 (type_memory_bytes ce ty) < dimword (:256)) tys ==>
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sa))) +
      32 * LENGTH (FILTER (\b. ~b) flags) <=
    SUM (MAP alloca_lit_size
      (FILTER (\i. i.inst_opcode = ALLOCA) (state_insts sb)))
Proof
  Induct >- (Cases >> simp[compile_stage_intcall_args_def, comp_return_def]) >>
  rpt gen_tac >>
  Cases_on `flags` >- simp[] >> Cases_on `tys` >- simp[] >>
  rename1 `compile_stage_intcall_args ce (vv::vals) (flag::flags) (ty::tys)` >>
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac
  >- (gvs[] >> first_x_assum drule >> simp[] >> strip_tac >>
      drule unwrap_value_extends >>
      disch_then (mp_tac o MATCH_MP state_alloca_charge_mono) >> decide_tac) >>
  gvs[] >> first_x_assum drule >> simp[] >> strip_tac >>
  rename1 `compile_alloc_buffer _ su = (buf,sm)` >>
  rename1 `compile_stage_intcall_args ce vals flags tys sn = _` >>
  `cs_extends sm sn` by
    (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
     rpt IF_CASES_TAC >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     metis_tac[emit_void_labels, compile_store_bytestring_labels,
               compile_store_memory_labels, pairTheory.SND]) >>
  `MAX 32 (type_memory_bytes ce ty) < dimword (:256)` by simp[] >>
  drule_all compile_alloc_buffer_state_charge >> strip_tac >>
  drule unwrap_value_extends >>
  disch_then (mp_tac o MATCH_MP state_alloca_charge_mono) >>
  drule state_alloca_charge_mono >>
  simp[arithmeticTheory.MULT_CLAUSES] >>
  `32 <= MAX 32 (type_memory_bytes ce ty)` by simp[] >> decide_tac
QED
