(* First-emission boundaries for declaration and value support. *)
Theory entryReachBodyFirstEmissionSupport
Ancestors
  compilerFirstEmission stmtLowering exprLowering context compileEnv fragExec
  emitHelper venomInst finite_map externalEntryShape

Theorem first_emission_declare_local:
  declare_local ce id ty a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  simp[declare_local_def] >> IF_CASES_TAC >>
  simp[comp_bind_def, comp_return_def, fresh_var_def] >> strip_tac >> gvs[] >>
  irule cs_extends_same_block >> simp[]
QED

Theorem first_emission_declare_stmt_local:
  declare_stmt_local ce s a = (x,b) ==>
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, first_emission_declare_local,
    comp_return_def, cs_extends_refl] >>
  metis_tac[first_emission_declare_local]
QED

Theorem first_emission_alloc_buffer:
  compile_alloc_buffer n a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  simp_tac bool_ss [compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w n)] a` >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >> gvs[] >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

Theorem first_emission_local_alloca:
  !ce id a x b. emit_local_alloca ce id a = (x,b) ==>
  cs_extends a b /\
  ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
    a.cs_current_insts = b.cs_current_insts) \/
   (!fn. fn_has_code a b fn ==> ?bb i.
     lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  rpt gen_tac >> simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[]
  >- metis_tac[first_emission_return] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME loc` >>
  Cases_on `loc` >> simp[comp_return_def, cs_extends_refl] >>
  rename1 `PtrVar op sz` >> Cases_on `op` >>
  simp[comp_return_def, cs_extends_refl] >> strip_tac >>
  drule_at Any (CONJUNCT1 first_emission_emit_helpers) >> simp[]
QED

Theorem first_emission_ptr_load:
  !ctor imm loc op a x b. compile_ptr_load ctor imm loc op a = (x,b) ==>
  cs_extends a b /\
  (!fn. fn_has_code a b fn ==> ?bb i.
    lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI)
Proof
  rpt gen_tac >> Cases_on `loc` >> simp[compile_ptr_load_def]
  >~ [`compile_imm_load_word ctor imm op a = (x,b)`]
  >- (simp[compile_imm_load_word_def] >> reverse (Cases_on `ctor`) >> simp[]
  >- (strip_tac >> drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  Cases_on `imm` >> simp[]
  >- (strip_tac >> drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  map_every qid_spec_tac [`b`, `x`, `a`] >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac >>
  rpt strip_tac >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]) >>
  strip_tac >>
  drule_at Any (CONJUNCT2 (CONJUNCT2 first_emission_emit_helpers)) >> simp[]
QED

