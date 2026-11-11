(* TOP-LEVEL: arbitrary concrete static/bytes/string field lists execute the
   actual compiler traversal. Initial observations, common arena ownership
   and old operands suffice; no unproved child execution contract is assumed. *)
Theory abiFlatRun
Ancestors
  abiAllocatorState
  abiStateFrame
  abiFlatStep abiFlatFieldsDefs abiFieldOperands abiFieldLayoutDefs abiComplexStructure
  abiMemoryFrame abiMemoryFrameCover compileEnv fragExec fragBlockPath venomState list words arithmetic

Theorem abi_operand_before_frame_trans:
  !var_base next_var before middle after.
    var_base <= next_var /\
    (!arg_op. abi_operand_before var_base arg_op ==> eval_operand arg_op middle = eval_operand arg_op before) /\
    (!arg_op. abi_operand_before next_var arg_op ==> eval_operand arg_op after = eval_operand arg_op middle) ==>
    !arg_op. abi_operand_before var_base arg_op ==> eval_operand arg_op after = eval_operand arg_op before
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  `abi_operand_before next_var arg_op` by
    (irule abi_operand_before_mono >> qexists_tac `var_base` >> simp[]) >>
  asm_simp_tac bool_ss []
QED

Theorem compile_abi_flat_fields_run:
  !rows ctx func dst src dyn_ptr source_offset fields tail_offset capacity cs ret cs' ss dst_addr dyn_addr root_addr.
    EVERY abi_flat_valid rows /\
    compile_abi_encode_complex_elems dst src (MAP abi_flat_entry rows)
      source_offset (abi_field_head_size fields) dyn_ptr cs = (ret,cs') /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_flat_state fields rows tail_offset dst_addr dyn_addr root_addr source_offset capacity ss ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand dst out = SOME dst_addr /\ eval_operand src out = SOME root_addr /\ eval_operand dyn_ptr out = SOME dyn_addr /\
      abi_flat_state (fields ++ MAP abi_flat_output rows) [] tail_offset dst_addr dyn_addr root_addr
        (source_offset + SUM (MAP abi_flat_mem_size rows)) capacity out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  Induct_on `rows`
  >- (rw[abi_complex_fields_nil] >> qexists_tac `ss` >> simp[]) >>
  qx_gen_tac `row` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `EVERY _ (_::_)` (strip_assume_tac o SIMP_RULE list_ss []) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `dyn_ptr`, `row`, `rows`, `source_offset`, `fields`,
    `tail_offset`, `capacity`, `cs`, `ret`, `cs'`, `ss`, `dst_addr`, `dyn_addr`, `root_addr`]
    compile_abi_flat_field_step) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `mid` (qx_choose_then `step_out` strip_assume_tac)) >>
  `abi_operand_before mid.cs_next_var src /\ abi_operand_before mid.cs_next_var dst /\
      abi_operand_before mid.cs_next_var dyn_ptr` by
    (rpt conj_tac >> irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  first_x_assum (qspecl_then [`ctx`, `func`, `dst`, `src`, `dyn_ptr`, `source_offset + abi_flat_mem_size row`,
    `fields ++ [abi_flat_output row]`, `tail_offset`, `capacity`, `mid`, `ret`, `cs'`, `step_out`,
    `dst_addr`, `dyn_addr`, `root_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `step_out` >> simp[]) >>
  `abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out` by
    (irule abi_memory_frame_trans_same >> qexists_tac `step_out` >> simp[]) >>
  `abi_state_frame ss out` by (irule abi_state_frame_trans >> qexists_tac `step_out` >> simp[]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `mid.cs_next_var`, `ss`, `step_out`, `out`]
       abi_operand_before_frame_trans) >> impl_tac >- simp[] >> simp[]) >>
  qpat_x_assum `abi_flat_state _ [] _ _ _ _ _ _ out`
    (ASSUME_TAC o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  qexists_tac `out` >> gvs[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >> PURE_REWRITE_TAC [ADD_ASSOC] >> asm_simp_tac bool_ss []
QED
