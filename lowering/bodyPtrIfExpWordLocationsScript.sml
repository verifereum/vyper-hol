Theory bodyPtrIfExpWordLocations
Ancestors
  bodyPtrDefs compileEnv context vyperAST vyperValue
  ptrDiscipline venomInst exprSimUnwrap

Theorem ifexp_runtime_code_word_compile:
  compile_ptr_load F imm LocCode op = emit_op DLOAD [op]
Proof
  simp[compile_ptr_load_def, compile_imm_load_word_def]
QED

Theorem ifexp_word_type_has_no_dead_storage_bytes:
  is_word_type t /\ evaluate_type tenv t = SOME tv ==>
  !st base j b. ~dead_bytes st base tv j b
Proof
  strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT BoolT \/ t = BaseT AddressT \/ t = BaseT DecimalT \/
   (?m. t = BaseT (BytesT (Fixed m)) /\ m <= 32) \/ (?n. t = FlagT n)` by
    (Cases_on `t` >> fs[is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[is_word_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs(), dead_bytes_def, type_slot_size_def]
QED

Theorem ifexp_runtime_dload_output_taint:
  out_taint tn (mk_inst id DLOAD [op] [out]) s = {}
Proof
  simp[out_taint_def, mk_inst_def] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem ifexp_located_word_storage_key_clean:
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  ptr_vv_ok cx t raw (LocatedValue ty p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME slot ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >> drule_all word_type_slot_size >> strip_tac >>
  `!st base j b. ~dead_bytes st base tv j b` by
    metis_tac[ifexp_word_type_has_no_dead_storage_bytes] >>
  gvs[ptr_vv_ok_def] >>
  Cases_on `tr` >> gvs[key_taint_def, pred_setTheory.EXTENSION] >>
  gen_tac >> Cases_on `x < 32` >> simp[] >>
  first_x_assum (qspecl_then [`slot`,`x`] mp_tac) >> simp[]
QED
