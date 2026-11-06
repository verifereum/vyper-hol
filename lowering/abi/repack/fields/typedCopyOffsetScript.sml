(* TOP-LEVEL: actual byte-offset compilation executes either no code or
   its address ADD, preserving memory and operands outside its allocation. *)
Theory typedCopyOffset
Ancestors
  typedCopyStateFrame fieldAddressProps copyAppend compileAppendProps abiBytestringCode abiStaticLoopCode
  context compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem compile_with_byte_offset_code:
  !base_op offset cs op cs'.
    compile_with_byte_offset base_op offset cs = (op,cs') ==>
    if offset = 0 then op = base_op /\ cs' = cs
    else emit_op ADD [base_op; Lit (n2w offset)] cs = (op,cs') /\
      op = Var (compiler_var_name cs.cs_next_var 0) /\ cs'.cs_next_var = cs.cs_next_var + 1
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `offset = 0`
  >- gvs[compile_with_byte_offset_def, comp_return_def] >>
  `emit_op ADD [base_op; Lit (n2w offset)] cs = (op,cs')` by gvs[compile_with_byte_offset_def] >>
  drule emit_field_address_code >> simp[compiler_var_name_def]
QED

Theorem compile_with_byte_offset_extends:
  !base_op offset cs op cs'.
    compile_with_byte_offset base_op offset cs = (op,cs') ==> cs_extends cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`base_op`, `offset`] cs_appends_compile_with_byte_offset) >>
  simp_tac bool_ss [cs_appends_def] >>
  disch_then (qspecl_then [`cs`, `op`, `cs'`] mp_tac) >> simp[]
QED

Theorem compile_with_byte_offset_path:
  !ctx func base_op offset cs op cs' ss ptr_addr.
    compile_with_byte_offset base_op offset cs = (op,cs') /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ eval_operand base_op ss = SOME ptr_addr ==>
    ?out. fragment_path ctx func ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ out.vs_halted = ss.vs_halted /\
      out.vs_memory = ss.vs_memory /\ copy_state_frame ss out /\ eval_operand op out = SOME (ptr_addr + n2w offset) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule compile_with_byte_offset_code >> DISCH_TAC >>
  Cases_on `offset = 0`
  >- (gvs[] >> qexists_tac `ss` >> simp[WORD_ADD_0]) >>
  fs[] >> qpat_x_assum `op = _` SUBST_ALL_TAC >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) emit_field_address_path >>
  qexists_tac `out` >> fs[compiler_var_names_def, GENLIST_CONS, compiler_var_name_def]
QED
