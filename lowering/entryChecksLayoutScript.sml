(* Compiler interfaces for the two optional straight-line entry checks. *)
Theory entryChecksLayout
Ancestors entryChecksProps moduleLowering moduleLoweringProps compileEnv
  emitHelper emitHelperProps exprLoweringProps fragExec codegenRel list rich_list
  venomInst

Theorem compile_entry_checks_split:
  compile_entry_checks m pay st = ((),st') /\ fn_has_code st st' fn ==>
  ?mid.
    compile_entry_checks 4 pay st = ((),mid) /\
    compile_entry_checks m T mid = ((),st') /\
    (~pay ==> fn_has_code st mid fn) /\
    (4 < m ==> fn_has_code mid st' fn) /\
    (pay ==> mid = st) /\ (~(4 < m) ==> st' = mid)
Proof
  Cases_on `pay` >> Cases_on `4 < m` >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> strip_tac >>
  irule fn_has_code_split >> simp[] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  fs[same_blocks_def] >>
  conj_tac >> simp[cs_extends_def, IS_PREFIX_APPEND]
QED

Theorem compile_entry_checks_value_layout:
  compile_entry_checks 4 F st = ((),st') /\ fn_has_code st st' fn ==>
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_next_var = st.cs_next_var + 2 /\
  LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts + 3 /\
  ?bb.
    lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id CALLVALUE []
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction bb (LENGTH st.cs_current_insts + 1) =
      SOME (mk_inst (st.cs_next_id + 1) ISZERO
        [Var (STRING #"%" (toString st.cs_next_var))]
        [STRING #"%" (toString (st.cs_next_var + 1))]) /\
    get_instruction bb (LENGTH st.cs_current_insts + 2) =
      SOME (mk_inst (st.cs_next_id + 2) ASSERT
        [Var (STRING #"%" (toString (st.cs_next_var + 1)))] [])
Proof
  strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_next_var = st.cs_next_var + 2 /\
   st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id CALLVALUE [] [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id + 1) ISZERO [Var (STRING #"%" (toString st.cs_next_var))]
       [STRING #"%" (toString (st.cs_next_var + 1))];
     mk_inst (st.cs_next_id + 2) ASSERT
       [Var (STRING #"%" (toString (st.cs_next_var + 1)))] []]` by
    (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_assum (qspec_then `1` mp_tac) >>
  first_x_assum (qspec_then `2` mp_tac) >> simp[]
QED

Theorem compile_entry_checks_size_layout:
  compile_entry_checks m T st = ((),st') /\ fn_has_code st st' fn /\ 4 < m ==>
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_next_var = st.cs_next_var + 3 /\
  LENGTH st'.cs_current_insts = LENGTH st.cs_current_insts + 4 /\
  ?bb.
    lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id CALLDATASIZE []
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction bb (LENGTH st.cs_current_insts + 1) =
      SOME (mk_inst (st.cs_next_id + 1) LT
        [Var (STRING #"%" (toString st.cs_next_var)); Lit (n2w m)]
        [STRING #"%" (toString (st.cs_next_var + 1))]) /\
    get_instruction bb (LENGTH st.cs_current_insts + 2) =
      SOME (mk_inst (st.cs_next_id + 2) ISZERO
        [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
        [STRING #"%" (toString (st.cs_next_var + 2))]) /\
    get_instruction bb (LENGTH st.cs_current_insts + 3) =
      SOME (mk_inst (st.cs_next_id + 3) ASSERT
        [Var (STRING #"%" (toString (st.cs_next_var + 2)))] [])
Proof
  strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_next_var = st.cs_next_var + 3 /\
   st'.cs_current_insts = st.cs_current_insts ++
    [mk_inst st.cs_next_id CALLDATASIZE [] [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id + 1) LT
       [Var (STRING #"%" (toString st.cs_next_var)); Lit (n2w m)]
       [STRING #"%" (toString (st.cs_next_var + 1))];
     mk_inst (st.cs_next_id + 2) ISZERO
       [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
       [STRING #"%" (toString (st.cs_next_var + 2))];
     mk_inst (st.cs_next_id + 3) ASSERT
       [Var (STRING #"%" (toString (st.cs_next_var + 2)))] []]` by
    (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >> simp[] >>
  first_assum (qspec_then `0` mp_tac) >>
  first_assum (qspec_then `1` mp_tac) >>
  first_assum (qspec_then `2` mp_tac) >>
  first_x_assum (qspec_then `3` mp_tac) >> simp[]
QED
