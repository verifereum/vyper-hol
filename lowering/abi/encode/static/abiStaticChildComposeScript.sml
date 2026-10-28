(* TOP-LEVEL: compose the actual destination ADD with an encoder summary.
   The composition retains its memory frame and all untouched SSA operands. *)
Theory abiStaticChildCompose
Ancestors
  abiStateFrameOps abiStateFrame abiFieldAddress abiFieldReady abiMemoryFrame abiStaticLoopCode
  compileEnv fragBlockPath venomState list words arithmetic

Theorem abi_static_child_compose:
  !ctx func cs head_offset dst_addr ss out child_count writes.
    fragment_path ctx func ss (abi_field_address_state cs head_offset dst_addr ss) /\
    fragment_path ctx func (abi_field_address_state cs head_offset dst_addr ss) out /\
    abi_memory_frame writes (abi_field_address_state cs head_offset dst_addr ss) out /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names (cs.cs_next_var + 1) child_count) ==>
      eval_operand arg_op out = eval_operand arg_op (abi_field_address_state cs head_offset dst_addr ss)) ==>
    fragment_path ctx func ss out /\ abi_memory_frame writes ss out /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names cs.cs_next_var (child_count + 1)) ==>
      eval_operand arg_op out = eval_operand arg_op ss) /\
    (abi_state_frame (abi_field_address_state cs head_offset dst_addr ss) out ==> abi_state_frame ss out)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule fragment_path_trans >> qexists_tac `abi_field_address_state cs head_offset dst_addr ss` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `abi_memory_frame _ _ _` mp_tac >>
      simp[abi_memory_frame_def, read_memory_def, abi_field_address_state_frame]) >>
  conj_tac
  >- (qx_gen_tac `arg_op` >> DISCH_TAC >>
      mp_tac (Q.SPECL [`arg_op`, `cs.cs_next_var`, `child_count`] abi_field_input_names) >>
      impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
      qpat_x_assum `!arg_op. EVERY _ _ ==> _` (qspec_then `arg_op` mp_tac) >>
      simp[abi_field_address_state_operand]) >>
  simp[abi_state_frame_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed static ABI child execution composition: " ^ name)
  end) (DB.thms "abiStaticChildCompose")
