Theory runtimeSymSrcContextTypedBranches
Ancestors
  runtimeSymSrcContextTypedBase runtimeSymSrcContext runtimeSymSrcEmission
  context compileEnv emitHelper loweringShapeDefs venomInst stackPlanTypes list

Theorem runtime_sym_typed_fields_step:
  (!dp sp s u s'.
    ~is_label_operand dp /\ ~is_label_operand sp /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dp dt sp st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_typed_copy_fields ce dst src dts sts
      (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st)
      s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')) ==>
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_typed_copy_fields ce dst src (dt::dts) (st::sts) doff soff s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[NoAsms, comp_bind_def, comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then Any mp_tac runtime_sym_with_byte_offset) >> simp[] >> strip_tac >>
  qpat_assum `compile_with_byte_offset src _ _ = _`
    (mp_then Any mp_tac runtime_sym_with_byte_offset) >> simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[]
QED

Theorem runtime_sym_typed_struct_step:
  (!dp sp s u s'.
    ~is_label_operand dp /\ ~is_label_operand sp /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_memory_typed ce dp dt sp
      (case ALOOKUP sfs name of NONE => dt | SOME (ft,sz) => ft)
      s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')) /\
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_struct_typed_copy ce dst src dfs sfs (doff + dsz)
      (soff + (case ALOOKUP sfs name of NONE => dsz | SOME (ft,sz) => sz))
      s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')) ==>
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_struct_typed_copy ce dst src ((name,dt,dsz)::dfs) sfs doff soff s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name` >>
  fs[NoAsms] >>
  TRY (PairCases_on `x`) >>
  fs[NoAsms, comp_bind_def, comp_ignore_bind_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (uv,ss)` >>
  Cases_on `uv` >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then Any mp_tac runtime_sym_with_byte_offset) >> simp[] >> strip_tac >>
  qpat_assum `compile_with_byte_offset src _ _ = _`
    (mp_then Any mp_tac runtime_sym_with_byte_offset) >> simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem runtime_sym_typed_dispatch:
  (~is_word_type dt /\ ~(is_bytestring_type dt /\ is_bytestring_type st) /\
   acyclic_struct_metadata ce.ce_struct_fields ==>
   ((!de dc se sc s u s'.
      dt = ArrayT de (Dynamic dc) /\ st = ArrayT se (Dynamic sc) /\
      ~is_label_operand dst /\ ~is_label_operand src /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_copy_dynarray_typed ce dst de dc src se s = (u,s') ==>
      EVERY runtime_sym_inst (state_insts s')) /\
    (!de n se m s u s'.
      dt = ArrayT de (Fixed n) /\ st = ArrayT se (Fixed m) /\
      ~is_label_operand dst /\ ~is_label_operand src /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_copy_sarray_typed ce dst de src se n s = (u,s') ==>
      EVERY runtime_sym_inst (state_insts s')) /\
    (!dts sts s u s'. dt = TupleT dts /\ st = TupleT sts /\
      ~is_label_operand dst /\ ~is_label_operand src /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_typed_copy_fields ce dst src dts sts 0 0 s = (u,s') ==>
      EVERY runtime_sym_inst (state_insts s')) /\
    (!dn sn s u s'. dt = StructT dn /\ st = StructT sn /\
      ~is_label_operand dst /\ ~is_label_operand src /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_struct_typed_copy ce dst src
        (get_struct_fields ce.ce_struct_fields (nsid_to_string dn))
        (get_struct_fields ce.ce_struct_fields (nsid_to_string sn)) 0 0 s = (u,s') ==>
      EVERY runtime_sym_inst (state_insts s')))) ==>
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_memory_typed ce dst dt src st s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  disch_tac >>
  Cases_on `is_word_type dt`
  >- (pop_assum mp_tac >> qpat_x_assum `_ ==> _` kall_tac >> strip_tac >>
      simp[Once compile_store_memory_typed_def, comp_bind_def, comp_ignore_bind_def] >>
      pairarg_tac >> simp[] >> strip_tac >>
      qpat_assum `emit_op _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_assum `emit_void _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (qpat_x_assum `_ ==> _` kall_tac >>
      simp[Once compile_store_memory_typed_def] >>
      metis_tac[runtime_sym_store_bytestring]) >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (qpat_x_assum `_ ==> _` drule_all >> strip_tac >>
      pure_once_rewrite_tac[compile_store_memory_typed_def] >>
      pure_asm_rewrite_tac[] >>
      Cases_on `dt` >> Cases_on `st` >>
      fs[NoAsms] >>
      all_tac >>~-
        ([`compile_copy_memory _ _ _ _ = _`],
         rpt strip_tac >>
         qpat_assum `compile_copy_memory _ _ _ _ = _`
           (mp_then Any mp_tac runtime_sym_copy_memory) >> simp[]) >>
      all_tac >>~-
        ([`compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`], first_assum MATCH_ACCEPT_TAC) >>
      all_tac >>~-
        ([`compile_struct_typed_copy _ _ _ _ _ _ _ _ = _`], first_assum MATCH_ACCEPT_TAC) >>
      Cases_on `b` >> Cases_on `b'` >> fs[NoAsms] >>
      all_tac >>~-
        ([`compile_copy_memory _ _ _ _ = _`],
         rpt strip_tac >>
         qpat_assum `compile_copy_memory _ _ _ _ = _`
           (mp_then Any mp_tac runtime_sym_copy_memory) >> simp[]) >>
      first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `_ ==> _` kall_tac >>
  simp[Once compile_store_memory_typed_def] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED
