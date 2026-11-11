(* TOP-LEVEL: checked source metadata supplies the element stride and
   acyclicity guard for the actual dynamic-array capacity-widening store.
   Physical memory bounds remain explicit. *)
Theory dynCopySource
Ancestors
  typedCopyStateFrame dynCopyProps memoryValueDefs typeLayoutProps typedCopyProducer typedCopyDomain checkedCopyAcyclic
  memoryLayoutDefs valueLoadProps valueEncoding vyperValue vyperTyping
  vyperTypeContract vyperContext compileVyper compileEnv context exprLoweringProps
  fragBlockPath fragExec venomState list words arithmetic

Theorem compile_store_memory_dynarray_dispatch:
  !cenv elem_ty src_capacity dst_capacity src dst.
    src_capacity < dst_capacity /\ acyclic_struct_metadata cenv.ce_struct_fields ==>
    compile_store_memory cenv src dst (ArrayT elem_ty (Dynamic dst_capacity))
      (ArrayT elem_ty (Dynamic src_capacity)) =
    compile_copy_dynarray_typed cenv dst elem_ty dst_capacity src elem_ty
Proof
  rpt gen_tac >> strip_tac >> `src_capacity <> dst_capacity` by decide_tac >>
  simp[compile_store_memory_def, is_word_type_def, is_bytestring_type_def,
    tuple_memory_layout_eq_def, Once compile_store_memory_typed_def]
QED

Theorem array_live_copy_bound:
  !tv capacity vs.
    value_has_type (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) /\
    type_memory_size (ArrayTV tv (Dynamic capacity)) < dimword(:256) ==>
    LENGTH vs * type_memory_size tv < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >> `LENGTH vs <= capacity` by fs[value_has_type_def] >>
  `capacity * type_memory_size tv < dimword(:256)` by (fs[type_memory_size_def] >> decide_tac) >>
  `LENGTH vs * type_memory_size tv <= capacity * type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
  decide_tac
QED

Theorem compile_store_memory_dynarray_widening_path:
  !tops in_deploy layouts addr art ctx func cenv elem_ty elem_tv src_capacity dst_capacity
      vs dst src cs ret cs' ss dst_addr src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) elem_ty = SOME elem_tv /\
    src_capacity < dst_capacity /\ dst_capacity < dimword(:256) /\
    compile_store_memory cenv src dst (ArrayT elem_ty (Dynamic dst_capacity))
      (ArrayT elem_ty (Dynamic src_capacity)) cs = (ret,cs') /\
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
  `src_capacity <= dst_capacity` by decide_tac >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_store_memory_dynarray_dispatch] >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `elem_ty`, `elem_tv`, `src_capacity`, `dst_capacity`,
    `vs`, `dst`, `src`, `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `src_addr`]
    compile_copy_dynarray_path) >> simp[]
QED
