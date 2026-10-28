(* TOP-LEVEL: execute the complete native static field traversal using the
   semantic child induction assertions. The actual remaining compiler action
   bounds each recursive child and supplies its containing function code. *)
Theory abiNativeStaticRun
Ancestors
  abiNativeStaticStep abiNativeStaticState abiNativeTraversal abiNativeEncodingDefs
  abiFieldsStructure abiFieldsCons abiComplexStructure abiComplexCode
  compileEnv fragExec venomState list pair arithmetic

Theorem abi_native_static_traversal:
  !entries ctx func root_cs root_after source_id target_id initial reference full dst src dst_addr root_addr
      source_capacity source_offset head_offset cs ret ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss /\
    compile_abi_encode_complex_elems dst src entries source_offset head_offset (Lit 0w) cs = (ret,root_after) /\
    fn_has_code cs root_after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out.
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial root_after out /\
      abi_native_static_state full dst src dst_addr root_addr source_capacity reference []
        (source_offset + SUM (MAP (\(_,_,mem_sz,_). mem_sz) entries))
        (head_offset + SUM (MAP (\(_,abi_sz,_,_). abi_sz) entries)) root_after out /\
      out.vs_current_bb = root_after.cs_current_bb /\
      out.vs_inst_idx = LENGTH root_after.cs_current_insts /\ ~out.vs_halted
Proof
  Induct_on `entries`
  >- (rpt gen_tac >> strip_tac >> gvs[abi_complex_fields_nil] >> qexists_tac `ss` >> simp[]) >>
  simp_tac bool_ss [FORALL_PROD] >>
  MAP_EVERY qx_gen_tac [`info`, `abi_sz`, `mem_sz`, `is_dyn`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [compile_abi_fields_cons_cuts]) >>
  disch_then (qx_choose_then `child_ret` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all abi_fields_step_contains >> strip_tac >>
  `cs_extends mid root_after` by (drule_all compile_abi_fields_extends >> simp[]) >>
  drule_all abi_native_static_step >>
  disch_then (qx_choose_then `child_out` strip_assume_tac) >>
  first_x_assum drule_all >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> simp_tac bool_ss [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >> asm_rewrite_tac []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native static field traversal: " ^ name)
  end) (DB.thms "abiNativeStaticRun")
