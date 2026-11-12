(* A constructor immutable assignment always finishes with ISTORE. *)
Theory immutableAssignOpen
Ancestors
  stmtLowering context exprOpenPrimitives compileEnv emitHelper venomInst
  immutableCopyExecution

Theorem immutable_assign_word_open[local]:
  compile_imm_store_word imm dst value sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, emit_void_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  Cases_on `sa.cs_current_insts` >>
  simp[block_is_terminated_def, listTheory.LAST_APPEND_CONS,
       listTheory.LAST_CONS_cond, mk_inst_def, is_terminator_def]
QED

Theorem immutable_assign_words_open[local]:
  !n off sa sb.
  compile_imm_store_words imm src dst n off sa = ((),sb) /\ 0 < n ==>
  ~block_is_terminated sb
Proof
  Induct >- simp[] >>
  simp[compile_imm_store_words_def, immutable_comp_bind_cases,
       comp_ignore_bind_def] >>
  rpt strip_tac >> Cases_on `n`
  >- (gvs[compile_imm_store_words_def, comp_return_def] >>
      metis_tac[immutable_assign_word_open]) >>
  first_x_assum drule >> simp[]
QED

Theorem immutable_word_copy_loop_base_open[local]:
  !src dst count load store ctor imm sa u sb.
    compile_word_copy_loop_base src dst count load store ctor imm sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_word_copy_loop_base_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule new_block_open >> simp[]
QED

Theorem immutable_bytestring_store_open[local]:
  compile_store_immutable_bytestring imm src dst sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  simp[compile_store_immutable_bytestring_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[immutable_word_copy_loop_base_open]
QED

Theorem immutable_assign_loccode_open:
  compile_assign_value ce dst LocCode src prim loc dt st bytes sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  simp[compile_assign_value_def, LET_THM, immutable_comp_bind_cases] >>
  rpt strip_tac >>
  Cases_on `prim` >> gvs[]
  >- metis_tac[immutable_assign_word_open] >>
  qpat_x_assum `(if dt <> st /\ _ then _ else _) sa = _` kall_tac >>
  Cases_on `is_bytestring_type dt` >> gvs[]
  >- metis_tac[immutable_bytestring_store_open] >>
  Cases_on `bytes <= 32` >> gvs[immutable_comp_bind_cases]
  >- metis_tac[immutable_assign_word_open] >>
  `0 < (bytes + 31) DIV 32` by
    (irule dividesTheory.DIV_POS >> decide_tac) >>
  metis_tac[immutable_assign_words_open]
QED
