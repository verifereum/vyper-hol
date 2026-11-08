(* Static emission, including code after an abort: no runtime premises. *)
Theory bodyPtrBytestringBuiltinsExtcodeEmission
Ancestors
  bodyPtrBytestringBuiltinsSliceDispatch bodyPtrBytestringBuiltinsExternalSlice
  fragExec exprLowering compileEnv emitHelper venomInst list rich_list

Theorem slice_extcode_copy_in_final_current:
  compile_slice_extcode addr start len root data sa = (out,sb) ==>
  EXISTS (\i. i.inst_opcode = EXTCODECOPY) sb.cs_current_insts
Proof
  strip_tac >> drule compile_slice_extcode_stages >> strip_tac >>
  gvs[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, emit_def] >>
  simp[EXISTS_APPEND, mk_inst_def]
QED

Theorem slice_extcode_copy_in_function:
  compile_slice_extcode addr start len root data sa = (out,sb) /\
  fn_has_code first sb f ==>
  EXISTS (\i. i.inst_opcode = EXTCODECOPY) (fn_insts f)
Proof
  strip_tac >> drule slice_extcode_copy_in_final_current >>
  simp[EXISTS_MEM] >> strip_tac >>
  fs[fn_has_code_def] >>
  `MEM i bb.bb_instructions` by metis_tac[IS_PREFIX_MEM] >>
  metis_tac[lookup_block_fn_insts]
QED

Theorem slice_extcode_mandatory_copy:
  ~is_msg_data src /\ ~is_self_code src /\ is_extcode src /\
  compile_expr cenv ty (Builtin ann (Slice n) [src;start;len]) sa = (vv,sb) /\
  fn_has_code sa sb f ==>
  EXISTS (\i. i.inst_opcode = EXTCODECOPY) (fn_insts f)
Proof
  strip_tac >> drule_all slice_extcode_compile_cut >> strip_tac >>
  Cases_on `compile_slice_extcode addr a b out data s4` >>
  gvs[as_ptr_val_def] >>
  drule_all slice_extcode_copy_in_function >> simp[]
QED
