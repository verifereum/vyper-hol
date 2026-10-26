(* Structural facts for the actual ascending Empty buffer initializer. *)
Theory abiEmptyCode
Ancestors
  builtinSimple abiTupleProps abiTupleEncodeSlot exprLoweringProps emitHelperProps
  compileEnv context emitHelper venomState venomInst words list rich_list arithmetic

Theorem abi_empty_zero_words_successor:
  compile_zero_words base_op (SUC n) st =
    let (_,middle) = compile_zero_words base_op n st in
      compile_abi_tuple_slot (ARB:compile_env) base_op (n*32)
        (Lit 0w) (BaseT (UintT 256)) middle
Proof
  simp[Once compile_zero_words_def, compile_abi_tuple_slot_def, is_word_type_def,
    comp_ignore_bind_def, comp_bind_def, LET_THM, pairTheory.UNCURRY_DEF]
QED

Theorem abi_empty_zero_words_shape:
  !n base_op st final.
  compile_zero_words base_op n st = ((),final) ==>
  final.cs_next_var = st.cs_next_var+n /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, inst_extends_refl] >>
  rpt gen_tac >> simp_tac bool_ss [abi_empty_zero_words_successor, LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words base_op n st = (ignored,middle)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  asm_simp_tac (srw_ss()) [] >>
  conj_tac >- decide_tac >>
  irule inst_extends_trans >> qexists_tac `middle` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty code not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyCode");

