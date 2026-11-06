(* TOP-LEVEL: a checked recursive typed store widens a dynamic-array
   capacity while preserving every live element and disjoint typed memory.
   This is the recursive child used inside fixed-array repacking loops.
   Helper: actual dispatcher equation, including equal capacities. *)
Theory typedDynStoreProps
Ancestors
  typedCopyStateFrame dynCopyProps dynCopySource memoryValueDefs valueLoadProps valueEncoding
  checkedCopyAcyclic typeLayoutProps typedCopyProducer typedCopyDomain
  context compileEnv compileVyper exprLoweringProps
  vyperTypeContract vyperContext vyperValue vyperTyping
  fragBlockPath fragExec venomState list words arithmetic

Theorem compile_typed_dynarray_dispatch:
  !cenv dst dst_elem dst_capacity src src_elem src_capacity.
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    compile_store_memory_typed cenv dst (ArrayT dst_elem (Dynamic dst_capacity))
      src (ArrayT src_elem (Dynamic src_capacity)) =
    compile_copy_dynarray_typed cenv dst dst_elem dst_capacity src src_elem
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem checked_compile_typed_dynarray_path:
  !tops in_deploy layouts addr art ctx func cenv elem_ty elem_tv src_capacity dst_capacity
      vs dst src cs ret cs' ss dst_addr src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) elem_ty = SOME elem_tv /\
    src_capacity <= dst_capacity /\ dst_capacity < dimword(:256) /\
    compile_store_memory_typed cenv dst (ArrayT elem_ty (Dynamic dst_capacity))
      src (ArrayT elem_ty (Dynamic src_capacity)) cs = (ret,cs') /\
    lowered_value_rel (ArrayT elem_ty (Dynamic src_capacity))
      (ArrayTV elem_tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) src ss /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    w2n dst_addr + 32 < dimword(:256) /\ w2n src_addr + 32 < dimword(:256) /\
    type_memory_size (ArrayTV elem_tv (Dynamic src_capacity)) < dimword(:256) /\
    (LENGTH vs * type_memory_size elem_tv = 0 \/
      w2n src_addr + 32 + LENGTH vs * type_memory_size elem_tv <= w2n dst_addr \/
      w2n dst_addr <= w2n src_addr) /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 6) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ copy_state_frame ss out /\
      lowered_value_rel (ArrayT elem_ty (Dynamic dst_capacity))
        (ArrayTV elem_tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs)) dst out /\
      memory_value_rel (ArrayTV elem_tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs))
        (w2n dst_addr) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_addr \/
          w2n dst_addr + 32 + dst_capacity * type_memory_size elem_tv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 6) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
  `type_memory_bytes cenv elem_ty = type_memory_size elem_tv` by
    (drule_all type_memory_bytes_evaluated >> simp[]) >>
  `LENGTH vs * type_memory_size elem_tv < dimword(:256)` by
    (irule array_live_copy_bound >> qexists_tac `src_capacity` >> fs[lowered_value_rel_def]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_typed_dynarray_dispatch] >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `elem_ty`, `elem_tv`, `src_capacity`, `dst_capacity`,
    `vs`, `dst`, `src`, `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`]
    compile_copy_dynarray_path) >> impl_tac >- simp[] >> strip_tac >>
  `eval_operand dst out = SOME dst_addr` by
    (qpat_x_assum `!arg_op. _` (qspec_then `dst` mp_tac) >>
     impl_tac >- fs[EVERY_CONJ] >> simp[]) >>
  `memory_value_rel (ArrayTV elem_tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs))
    (w2n dst_addr) out.vs_memory` by
    (qpat_x_assum `lowered_value_rel _ _ _ dst out` mp_tac >>
     simp[lowered_value_rel_def, is_word_type_def]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC
QED
