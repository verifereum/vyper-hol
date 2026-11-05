(* Local producer boundaries for the operand-linked Extract32 window. *)
Theory bodyMemTbExtract32Origin
Ancestors
  bodyMemTbExtract32Witness builtinBytes exprLowering context emitHelper compileEnv
  venomInst builtinMisc builtinCreate

Theorem extract32_slice_data_opcodes:
  compile_slice_data len data start amount outsz sa = (op,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sa.cs_current_insts ++
    [ADD; LT; GT; OR; ISZERO; ASSERT; ALLOCA; ADD; ADD; MCOPY; MSTORE]
Proof
  simp[compile_slice_data_def, compile_assert_slice_bounds_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_mul_check_opcodes:
  compile_mul_overflow_check x y res signed bits sa = (u,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sa.cs_current_insts ++
    ([if signed then SDIV else Div; EQ; ISZERO; OR] ++
     (if signed /\ bits = 256 then [EQ; NOT; ISZERO; AND; ISZERO; AND] else []) ++
     [ASSERT])
Proof
  Cases_on `signed` >> Cases_on `bits = 256` >>
  simp[compile_mul_overflow_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_wei_int_opcodes:
  compile_as_wei_value_int valop scale signed sa = (u,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sa.cs_current_insts ++
    (if scale = 1 then [] else
     [MUL; Div; EQ; ISZERO; OR] ++
     (if signed then [SLT; ISZERO; AND] else []) ++ [ASSERT])
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_array_subscript_opcodes:
  (if dynamic then loader baseop else comp_return (Lit (n2w n))) sa = (len,sm) /\
  compile_array_subscript baseop idx dynamic n stride elemsz signed loader sa = (u,sb) ==>
  MAP (\i. i.inst_opcode) sb.cs_current_insts =
  MAP (\i. i.inst_opcode) sm.cs_current_insts ++
    ((if signed then [SLT] else []) ++
     [LT; ISZERO; OR; ISZERO; ASSERT] ++
     (if dynamic then [ADD] else []) ++ [MUL; ADD])
Proof
  Cases_on `dynamic` >> Cases_on `signed` >>
  simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_list_membership_opcodes:
  !needle args sa.
    ?ops. MAP (\i. i.inst_opcode)
             (SND (compile_list_membership_in needle args sa)).cs_current_insts =
          MAP (\i. i.inst_opcode) sa.cs_current_insts ++ ops /\
          EVERY (\opc. opc = EQ \/ opc = OR) ops
Proof
  recInduct compile_list_membership_in_ind >> rpt strip_tac >>
  simp[Once compile_list_membership_in_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def,
       mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `compile_list_membership_in needle rest sm` >>
  pairarg_tac >> simp[] >>
  first_x_assum (qspec_then `sm` mp_tac) >>
  simp[Abbr `sm`] >> rpt strip_tac >>
  qexists_tac `[EQ] ++ ops ++ [OR]` >> simp[]
QED

Theorem extract32_create_copy_prefix_opcodes:
  compile_create_copy target value salt rof sa = (r,sb) ==>
  ?result sm.
    compile_check_create_result result rof sm = (r,sb) /\
    MAP (\i. i.inst_opcode) sm.cs_current_insts =
    MAP (\i. i.inst_opcode) sa.cs_current_insts ++
      ([EXTCODESIZE; ASSERT; SHL; OR; ADD; DALLOCA; MSTORE; ADD;
        EXTCODECOPY; ADD; ADD] ++
       [case salt of NONE => CREATE | SOME s => CREATE2] ++
       (if rof then [SETFMP] else []))
Proof
  Cases_on `salt` >> Cases_on `rof` >>
  simp[compile_create_copy_def, compile_alloc_dynamic_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       mk_inst_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_check_create_result out flag sm` >>
  qexistsl_tac [`out`, `sm`] >> simp[Abbr `sm`]
QED

(* Reads of a comparison are either explicit inputs or local results. *)
Theorem extract32_compare_operand_provenance:
  compile_compare cmp x y ty sa = (r,sb) ==>
  ?delta.
    sb.cs_current_insts = sa.cs_current_insts ++ delta /\
    !v. x <> Var v /\ y <> Var v /\
        EVERY (\i. ~MEM v i.inst_outputs) delta ==>
        r <> Var v /\
        EVERY (\i. ~MEM (Var v) i.inst_operands) delta
Proof
  Cases_on `cmp` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_inst_def, fresh_id_def,
       fresh_var_def, emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem extract32_generic_or_suffix:
  compile_binop Or x y ty base_literal exp_literal sa = (r,sb) ==>
  ?i v. sb.cs_current_insts = sa.cs_current_insts ++ [i] /\
      i.inst_opcode = OR /\ i.inst_operands = [x;y] /\
      i.inst_outputs = [v] /\ r = Var v
Proof
  simp[compile_binop_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

(* Conditional consumer: the GT read belongs to the right operand region.
   The region provenance premise, not an opcode-only test, excludes the read. *)
Theorem extract32_or_right_region_separation:
  (!i v. MEM i right /\ MEM (Var v) i.inst_operands ==>
         MEM v imports \/ ?j. MEM j right /\ MEM v j.inst_outputs) /\
  ~MEM v0 imports /\ EVERY (\i. ~MEM v0 i.inst_outputs) right ==>
  ~(?addi lti gt ori winpre.
      pre ++ left ++ right ++ [ori] =
        winpre ++ [addi; lti; gt; ori] /\
      MEM gt right /\ gt.inst_opcode = GT /\
      gt.inst_operands = [Var v0;len])
Proof
  rpt strip_tac >>
  fs[listTheory.EVERY_MEM] >>
  first_x_assum (qspecl_then [`gt`, `v0`] mp_tac) >>
  simp[] >> metis_tac[]
QED
