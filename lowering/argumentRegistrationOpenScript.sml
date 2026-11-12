(* Compiler openness of argument decoding and positional registration. *)
Theory argumentRegistrationOpen
Ancestors exprOpenTerminals exprOpenPrimitives moduleLowering abiEncoder
  compileEnv venomInst list vyperMisc

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem compile_abi_clamp_basetype_open:
  !cl op sa u sb.
    ~block_is_terminated sa /\
    compile_abi_clamp_basetype op cl sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  Cases >> rpt gen_tac >>
  rw[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_decode_args_open:
  !args cenv off load hi base sa u sb.
    ~is_terminator load /\ ~block_is_terminated sa /\
    compile_decode_args cenv args off load hi base sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  Induct >- simp[compile_decode_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> disch_then strip_assume_tac >>
  Cases_on `h1` >> Cases_on `h2` >>
  gvs[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[option_CASE_rator, AllCaseEqs(), comp_return_def,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  last_x_assum irule >> goal_assum $ drule_at Any >> simp[] >>
  imp_res_tac emit_op_nonterminator_open >> gvs[is_terminator_def] >>
  imp_res_tac emit_void_terminated >> gvs[is_terminator_def] >>
  FIRST
    [irule compile_abi_clamp_basetype_open >>
       goal_assum $ drule_at (Pat `compile_abi_clamp_basetype _ _ _ = _`) >> simp[],
     irule (calldata_pos compile_abi_decode_to_buf_open) >>
       goal_assum $ drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) >> simp[]]
QED

Theorem compile_register_positional_args_open:
  !args cenv off sa cenv' sb.
    ~block_is_terminated sa /\
    compile_register_positional_args cenv args off sa = (cenv',sb) ==>
    ~block_is_terminated sb
Proof
  Induct >- simp[compile_register_positional_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> disch_then strip_assume_tac >>
  gvs[compile_register_positional_args_def, option_CASE_rator,
    AllCaseEqs(), comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  last_x_assum irule >>
  goal_assum $ drule_at (Pat `compile_register_positional_args _ _ _ _ = _`) >>
  simp[] >>
  irule compile_decode_args_open >>
  goal_assum $ drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) >>
  simp[is_terminator_def] >>
  irule compile_alloc_buffer_open >> goal_assum $ drule_at Any
QED
