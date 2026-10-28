(* TOP-LEVEL: execute every field of a mixed aggregate from its recursive
   semantic assertions. The actual compiler continuation bounds each
   child inside the enclosing profile, including the parent's final code. *)
Theory abiNativeDynamicRun
Ancestors
  abiNativeDynamicStep abiNativeDynamicState abiNativeCursor abiNativeTraversal abiNativeEncodingDefs
  abiFieldsStructure abiFieldsCons abiComplexStructure abiComplexCode abiFieldLayoutDefs
  compileEnv fragExec venomState list pair arithmetic

Theorem abi_native_dynamic_traversal:
  !entries ctx func root_cs root_after source_id target_id initial reference full dst src dyn_ptr dst_addr dyn_addr
      root_addr source_capacity source_offset head_offset cs ret after ss counter_inst.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss /\
    compile_abi_encode_complex_elems dst src entries source_offset head_offset dyn_ptr cs = (ret,after) /\
    fn_has_code cs after func /\ cs_extends after root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out.
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial after out /\
      abi_native_cursor func root_cs root_after counter_inst dyn_addr after out /\
      abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference []
        (source_offset + SUM (MAP (\(_,_,mem_sz,_). mem_sz) entries))
        (head_offset + SUM (MAP (\(_,abi_sz,_,_). abi_sz) entries)) after out /\
      out.vs_current_bb = after.cs_current_bb /\ out.vs_inst_idx = LENGTH after.cs_current_insts /\ ~out.vs_halted
Proof
  Induct_on `entries`
  >- (rpt gen_tac >> strip_tac >> gvs[abi_complex_fields_nil] >> qexists_tac `ss` >> simp[]) >>
  simp_tac bool_ss [FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`info`, `abi_sz`, `mem_sz`, `is_dyn`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [compile_abi_fields_cons_cuts]) >>
  disch_then (qx_choose_then `child_ret` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all abi_fields_step_contains >> strip_tac >>
  `cs_extends mid after` by (drule_all compile_abi_fields_extends >> simp[]) >>
  `cs_extends mid root_after` by
    (irule cs_extends_trans >> qexists_tac `after` >> simp[]) >>
  drule_all abi_native_dynamic_step >> disch_then (qx_choose_then `child_out` strip_assume_tac) >>
  first_x_assum drule_all >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> simp_tac bool_ss [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >> asm_rewrite_tac []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native mixed field traversal: " ^ name)
  end) (DB.thms "abiNativeDynamicRun")
