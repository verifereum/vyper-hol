(* Scope the physical output-allocation and method/data-pointer steps.
   The raw runs come from the very witnesses of abi_encode_alloc_origin_run
   and abi_encode_setup_tail_origin_run, not from uniqueness of an empty
   GAS trace. The static cut does not need either run to succeed. *)
Theory entryCreateAbiSetupSegment
Ancestors
  entryCreateAdminSequence bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail
  abiBuiltinEncodeCode abiBuiltinAllocation abiEncoderProps
  emitHelper emitHelperProps exprLoweringProps compileEnv
  fragExec venomExecSemantics venomInst list rich_list pred_set arithmetic

Theorem abi_encode_setup_alloc_layout:
  compile_alloc_buffer n a = (buf,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode = ALLOCA)
    (emitted_insts a b)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  fs[same_blocks_def, frag_ids_def, mk_inst_def]
QED

Theorem abi_encode_setup_tail_layout:
  abi_builtin_encode_method_id mid buf a = ((),method_st) /\
  emit_op ADD [buf;Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))]
    method_st = (data,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ MEM i.inst_opcode [ADD;MSTORE])
    (emitted_insts a b)
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, frag_ids_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_setup_admin_phase[local]:
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  EVERY (\i. i.inst_id IN frag_ids a b /\
             MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts a b) ==>
  (!explicit ctx func s raw.
     fn_has_code a b func /\ create_operand_at a s /\ ~s.vs_halted /\
     run_inst_seq (emitted_insts a b) s = OK raw ==>
     create_operand_full_scope a b explicit ctx func s []
       (OK (raw with vs_inst_idx := LENGTH b.cs_current_insts))) /\
  (!explicit ctx func tops cx st0 source es s.
     fn_has_code a b func /\ create_operand_at a s ==>
     create_operand_cut a b explicit ctx func tops cx st0 source (es,s))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> irule create_admin_sequence_scope >> simp[] >>
      fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  rpt strip_tac >> irule create_admin_sequence_cut >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]
QED

Theorem abi_encode_setup_scoped_phases:
  (!n a b buf. compile_alloc_buffer n a = (buf,b) ==>
    (!explicit ctx func s raw.
       fn_has_code a b func /\ create_operand_at a s /\ ~s.vs_halted /\
       run_inst_seq (emitted_insts a b) s = OK raw ==>
       create_operand_full_scope a b explicit ctx func s []
         (OK (raw with vs_inst_idx := LENGTH b.cs_current_insts))) /\
    (!explicit ctx func tops cx st0 source es s.
       fn_has_code a b func /\ create_operand_at a s ==>
       create_operand_cut a b explicit ctx func tops cx st0 source (es,s))) /\
  (!mid buf a method_st data b.
     abi_builtin_encode_method_id mid buf a = ((),method_st) /\
     emit_op ADD [buf;Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))]
       method_st = (data,b) ==>
     (!explicit ctx func s raw.
       fn_has_code a b func /\ create_operand_at a s /\ ~s.vs_halted /\
       run_inst_seq (emitted_insts a b) s = OK raw ==>
       create_operand_full_scope a b explicit ctx func s []
         (OK (raw with vs_inst_idx := LENGTH b.cs_current_insts))) /\
     (!explicit ctx func tops cx st0 source es s.
       fn_has_code a b func /\ create_operand_at a s ==>
       create_operand_cut a b explicit ctx func tops cx st0 source (es,s)))
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule abi_encode_setup_alloc_layout >> strip_tac >>
      irule abi_encode_setup_admin_phase >> simp[] >> fs[EVERY_MEM]) >>
  rpt gen_tac >> strip_tac >> drule_all abi_encode_setup_tail_layout >> strip_tac >>
  irule abi_encode_setup_admin_phase >> simp[] >> fs[EVERY_MEM]
QED
