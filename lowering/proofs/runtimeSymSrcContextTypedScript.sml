Theory runtimeSymSrcContextTyped
Ancestors
  runtimeSymSrcContextTypedBranches runtimeSymSrcContextTypedArrays
  runtimeSymSrcContextTypedGuarded
  runtimeSymSrcContextTypedBase runtimeSymSrcContext runtimeSymSrcEmission
  context compileEnv emitHelper loweringShapeDefs venomInst stackPlanTypes list

Theorem runtime_sym_store_memory_typed_all:
  (!ce dst dty src sty s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dst dty src sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst src dtys stys doff soff s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_typed_copy_fields ce dst src dtys stys doff soff s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst dty src sty n s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_sarray_typed ce dst dty src sty n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst dty cap src sty s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_copy_dynarray_typed ce dst dty cap src sty s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!ce dst src dfs sfs doff soff s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_struct_typed_copy ce dst src dfs sfs doff soff s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s'))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- (simp[compile_store_memory_typed_def, comp_return_def])
  >- (simp[compile_store_memory_typed_def, comp_return_def])
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- (simp[compile_store_memory_typed_def, comp_return_def])
  >> suspend "struct"
QED

Resume runtime_sym_store_memory_typed_all[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_typed_dispatch) >>
  impl_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt (qpat_x_assum `!a. _` kall_tac) >> simp[]
QED

Resume runtime_sym_store_memory_typed_all[fields]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_typed_fields_step) >>
  impl_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt (qpat_x_assum `!a. _` kall_tac) >> simp[]
QED
Resume runtime_sym_store_memory_typed_all[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `type_memory_bytes ce dty = type_memory_bytes ce sty /\
            ~is_abi_dynamic ce.ce_struct_fields dty`
  >- (qpat_x_assum `!a. _` kall_tac >>
      qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def] >>
      metis_tac[runtime_sym_copy_memory]) >>
  qpat_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_copy_sarray_typed_branch) >>
  impl_tac >- (rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `!a. _` kall_tac >> simp[]
QED
Resume runtime_sym_store_memory_typed_all[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_copy_dynarray_typed_guarded) >>
  impl_tac >- (rpt strip_tac >> metis_tac[]) >>
  qpat_x_assum `!a. _` kall_tac >> simp[]
QED
Resume runtime_sym_store_memory_typed_all[struct]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_typed_struct_step) >>
  impl_tac >- (Cases_on `ALOOKUP sfs name`
    >- (rpt strip_tac >> fs[NoAsms] >> metis_tac[]) >>
    PairCases_on `x` >> rpt strip_tac >> fs[NoAsms] >> metis_tac[]) >>
  rpt (qpat_x_assum `!a. _` kall_tac) >> simp[]
QED
Finalise runtime_sym_store_memory_typed_all

Theorem runtime_sym_store_memory_typed:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_memory_typed ce dst dty src sty s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[cj 1 runtime_sym_store_memory_typed_all]
QED

Theorem runtime_sym_typed_copy_fields:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_typed_copy_fields ce dst src dtys stys doff soff s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[cj 2 runtime_sym_store_memory_typed_all]
QED

Theorem runtime_sym_copy_sarray_typed:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_sarray_typed ce dst dty src sty n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[cj 3 runtime_sym_store_memory_typed_all]
QED

Theorem runtime_sym_copy_dynarray_typed:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_dynarray_typed ce dst dty cap src sty s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[cj 4 runtime_sym_store_memory_typed_all]
QED

Theorem runtime_sym_struct_typed_copy:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_struct_typed_copy ce dst src dfs sfs doff soff s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[cj 5 runtime_sym_store_memory_typed_all]
QED

Theorem runtime_sym_store_memory:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_memory ce src dst dty sty s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type dty`
  >- (simp[] >> strip_tac >>
      qpat_assum `emit_void _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
  Cases_on `is_bytestring_type dty`
  >- (simp[] >> metis_tac[runtime_sym_store_bytestring]) >>
  Cases_on `dty <> sty /\ ~tuple_memory_layout_eq dty sty` >> simp[]
  >- metis_tac[runtime_sym_store_memory_typed] >>
  metis_tac[runtime_sym_copy_memory]
QED
