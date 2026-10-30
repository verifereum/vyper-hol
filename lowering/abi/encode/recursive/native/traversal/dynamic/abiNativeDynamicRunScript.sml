(* TOP-LEVEL: native mixed traversal instantiates the shared generative member
   recursion. Its whole-step callback preserves the dynamic cursor and state;
   the common engine owns compiler cuts, code spans and list recursion. *)
Theory abiNativeDynamicRun
Ancestors
  abiNativeDynamicStep abiNativeDynamicState abiNativeCursor abiNativeTraversal abiNativeEncodingDefs
  abiEncoderMembersGenerate abiComplexStructure
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
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `end_so = source_offset + SUM (MAP (\(_,_,mz,_). mz) entries)` >>
  qabbrev_tac `end_ho = head_offset + SUM (MAP (\(_,az,_,_). az) entries)` >>
  Q.ISPECL_THEN [
    `\pending (current,so,ho) (result:operand,en) (x:unit) state.
      cs_extends en root_after /\
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial current state /\
      abi_native_cursor func root_cs root_after counter_inst dyn_addr current state /\
      abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
        pending so ho current state /\
      so + SUM (MAP (\(_,_,mz,_). mz) pending) = end_so /\
      ho + SUM (MAP (\(_,az,_,_). az) pending) = end_ho /\
      state.vs_current_bb = current.cs_current_bb /\
      state.vs_inst_idx = LENGTH current.cs_current_insts /\ ~state.vs_halted`,
    `\(pending:(abi_enc_info # num # num # bool) list)
        (current:compile_state,so:num,ho:num) (result:operand,en:compile_state)
        (state:venom_state) out.
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial en out /\
      abi_native_cursor func root_cs root_after counter_inst dyn_addr en out`,
    `\(result:operand,en) out.
      abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
        [] end_so end_ho en out /\
      out.vs_current_bb = en.cs_current_bb /\
      out.vs_inst_idx = LENGTH en.cs_current_insts /\ ~out.vs_halted`] mp_tac
    (Q.GENL [`Inv`, `Run`, `Post`]
      (Q.INST [`dp` |-> `dyn_ptr`] abi_encoder_members_generate)) >>
  simp_tac bool_ss [] >> impl_tac
  >- (conj_tac
      >- (rpt gen_tac >> strip_tac >> gvs[] >>
          `cs_extends ce root_after` by
            (irule cs_extends_trans >> qexists_tac `en` >> simp[]) >>
          drule_all abi_native_dynamic_step >>
          disch_then (qx_choose_then `child_out` strip_assume_tac) >>
          qexists_tac `child_out` >> gvs[ADD_COMM]) >>
      rpt gen_tac >> strip_tac >> gvs[abi_complex_fields_nil]) >>
  disch_then (qspecl_then [`entries`, `cs`, `source_offset`, `head_offset`, `ret`,
    `after`, `()`, `ss`] mp_tac) >>
  impl_tac >- gvs[Abbr`end_so`, Abbr`end_ho`] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >> qexists_tac `out` >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native mixed field traversal: " ^ name)
  end) (DB.thms "abiNativeDynamicRun")
