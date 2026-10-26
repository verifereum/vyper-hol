(* Compiler provenance for the complete tuple producer. *)
Theory abiTupleEncodeCode
Ancestors
  abiTupleProps abiTupleEncodeSlot exprLowering context compileEnv emitHelperProps
  exprLoweringProps venomInst words list rich_list arithmetic

Theorem abi_tuple_encode_store_cons:
  compile_store_abi_tuple ce buf off ((op,ty)::xs) =
  do compile_abi_tuple_slot ce buf off op ty;
     compile_store_abi_tuple ce buf (off+type_memory_bytes ce ty) xs od
Proof
  simp[FUN_EQ_THM, compile_store_abi_tuple_def, compile_abi_tuple_slot_def,
    comp_bind_def, comp_ignore_bind_def] >>
  qx_gen_tac `st` >> Cases_on `emit_op ADD [buf;Lit (n2w off)] st` >> simp[]
QED

Theorem abi_tuple_encode_store_shape:
  !xs ce buf off st final. compile_store_abi_tuple ce buf off xs st = ((),final) ==>
  final.cs_next_var = st.cs_next_var+LENGTH xs /\ st.cs_next_id <= final.cs_next_id /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def, emitted_insts_def, inst_extends_refl] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >> first_x_assum drule >> strip_tac >>
  `inst_extends st final` by
    (irule inst_extends_trans >> qexists_tac `middle` >> asm_simp_tac bool_ss []) >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    (irule isPREFIX_TRANS >> qexists_tac `middle.cs_current_insts` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder compiler provenance not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeCode");
