(* Equations for the actual runtime dynamic header, including bounds control. *)
Theory bodyPtrBopInHeaderCode
Ancestors bodyPtrBopInLoopLayout exprLowering context compileEnv emitHelper
  codegenRel contextCodegenRel venomExecSemantics venomInst list arithmetic
  fragExec rich_list

Theorem membership_dynamic_compile_split:
  compile_var_array_membership cenv needle arr (ArrayT ety (Dynamic cap)) is_in =
  (do len <- (do len <- compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
                    (case vv_location arr of SOME l => l | NONE => LocMemory)
                    (vv_operand arr);
                 flag <- emit_op GT [len;Lit (n2w cap)];
                 valid <- emit_op ISZERO [flag];
                 emit_inst ASSERT [valid] [];
                 comp_return len od);
      compile_array_membership_loop needle (vv_operand arr) len
        (elem_size_in_location cenv
          (case vv_location arr of SOME l => l | NONE => LocMemory) ety)
        (word_scale (case vv_location arr of SOME l => l | NONE => LocMemory))
        (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
          (case vv_location arr of SOME l => l | NONE => LocMemory)) is_in od)
Proof
  simp[FUN_EQ_THM, compile_var_array_membership_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem membership_runtime_header_layout:
  (do len <- compile_ptr_load F imm loc arr;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\
  opc = (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
    LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD) /\
  length_var = "%" ++ toString sa.cs_next_var /\
  flag = "%" ++ toString (sa.cs_next_var+1) /\
  valid = "%" ++ toString (sa.cs_next_var+2) ==>
  len = Var length_var /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id opc [arr] [length_var];
     mk_inst (sa.cs_next_id+1) GT [len;Lit (n2w cap)] [flag];
     mk_inst (sa.cs_next_id+2) ISZERO [Var flag] [valid];
     mk_inst (sa.cs_next_id+3) ASSERT [Var valid] []] /\
  sb.cs_next_var = sa.cs_next_var+3 /\ sb.cs_next_id = sa.cs_next_id+4 /\
  sb.cs_current_bb = sa.cs_current_bb /\ sb.cs_blocks = sa.cs_blocks
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[APPEND_ASSOC]
QED

Theorem membership_header_code_lookup:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [load_i;gt_i;iz_i;check_i] /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) = SOME load_i /\
    get_instruction bb (LENGTH sa.cs_current_insts+1) = SOME gt_i /\
    get_instruction bb (LENGTH sa.cs_current_insts+2) = SOME iz_i /\
    get_instruction bb (LENGTH sa.cs_current_insts+3) = SOME check_i
Proof
  strip_tac >> fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  qexists_tac `bb` >> simp[] >>
  fs[get_instruction_def, APPEND_ASSOC, EL_APPEND_EQN] >> metis_tac[]
QED

Theorem membership_runtime_header_code:
  (do len <- compile_ptr_load F imm loc arr;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\ fn_has_code sa sb fn ==>
  len = Var ("%" ++ toString sa.cs_next_var) /\
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id
        (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
         LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)
        [arr] ["%" ++ toString sa.cs_next_var]) /\
    get_instruction bb (LENGTH sa.cs_current_insts+1) =
      SOME (mk_inst (sa.cs_next_id+1) GT [len;Lit (n2w cap)]
        ["%" ++ toString (sa.cs_next_var+1)]) /\
    get_instruction bb (LENGTH sa.cs_current_insts+2) =
      SOME (mk_inst (sa.cs_next_id+2) ISZERO
        [Var ("%" ++ toString (sa.cs_next_var+1))]
        ["%" ++ toString (sa.cs_next_var+2)]) /\
    get_instruction bb (LENGTH sa.cs_current_insts+3) =
      SOME (mk_inst (sa.cs_next_id+3) ASSERT
        [Var ("%" ++ toString (sa.cs_next_var+2))] [])
Proof
  strip_tac >>
  drule (SRULE [] (GEN_ALL membership_runtime_header_layout)) >> strip_tac >>
  simp[] >> irule membership_header_code_lookup >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_fixed_compile_split:
  compile_var_array_membership cenv needle arr (ArrayT ety (Fixed n)) is_in =
  compile_array_membership_loop needle (vv_operand arr) (Lit (n2w n))
    (elem_size_in_location cenv
      (case vv_location arr of SOME l => l | NONE => LocMemory) ety) 0
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
      (case vv_location arr of SOME l => l | NONE => LocMemory)) is_in
Proof
  simp[FUN_EQ_THM, compile_var_array_membership_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def]
QED
