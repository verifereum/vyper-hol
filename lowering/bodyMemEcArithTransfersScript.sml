Theory bodyMemEcArithTransfers
Ancestors
  bodyMemEcArithPrefix emitHelperProps exprLoweringProps context venomState
  exprSimWordBuiltins emitHelper compileEnv
  venomExecSemantics venomInst valueEncodingProps

(* Restatement of private exprSimECArith.ec_point_word_transfer_run;
   reference: alan-ref/base/exprSimECArithScript.sml.txt, lines 578-624. *)
Theorem ec_point_word_transfer_run:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  eval_operand point_op s = SOME point /\
  eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword + boff))
        (mem_word_at (w2n (point + poff)) s.vs_memory) s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `!q k z t. MEM q [point_op;base_op] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_read1_def, exec_write2_def, bind_outputs_def,
       eval_operand_def, lookup_var_update_var, mem_word_at_eq_mload] >>
  qpat_x_assum `!q k z t. _` kall_tac >>
  simp[mload_def, mstore_def, update_var_def] >>
  rpt strip_tac >> simp[lookup_var_update_var] >>
  gvs[not_fresh_at_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Strengthened restatement of private exprSimECArith.ec_point_word_transfer_shape;
   reference: alan-ref/base/exprSimECArithScript.sml.txt, lines 626-640. *)
Theorem ec_point_word_transfer_shape:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_next_id = sa.cs_next_id + 4 /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [point_op; Lit poff]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MLOAD
       [Var (STRING #"%" (toString sa.cs_next_var))]
       [STRING #"%" (toString (sa.cs_next_var+1))];
     mk_inst (sa.cs_next_id+2) ADD [base_op; Lit boff]
       [STRING #"%" (toString (sa.cs_next_var+2))];
     mk_inst (sa.cs_next_id+3) MSTORE
       [Var (STRING #"%" (toString (sa.cs_next_var+2)));
        Var (STRING #"%" (toString (sa.cs_next_var+1)))] []]
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ec_scalar_store_run:
  (do dst <- emit_op ADD [ib; Lit off];
      emit_void MSTORE [dst; scalar] od) sa = ((),sb) /\
  eval_operand ib s = SOME bw /\ eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [ib;scalar] ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (w2n (bw+off)) wscalar s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `!q k z t. MEM q [ib;scalar] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_write2_def, bind_outputs_def,
       eval_operand_def, lookup_var_update_var] >>
  qpat_x_assum `!q k z t. _` kall_tac >>
  simp[mstore_def, update_var_def] >>
  rpt strip_tac >> simp[lookup_var_update_var] >>
  gvs[not_fresh_at_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ec_scalar_store_shape:
  (do dst <- emit_op ADD [ib; Lit off];
      emit_void MSTORE [dst; scalar] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 1 /\
  sb.cs_next_id = sa.cs_next_id + 2 /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [ib; Lit off]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [Var (STRING #"%" (toString sa.cs_next_var)); scalar] []]
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ec_scalar_store_mem_ok:
  (do dst <- emit_op ADD [ib; Lit off];
      emit_void MSTORE [dst; scalar] od) sa = ((),sb) /\
  eval_operand ib s = SOME bw /\ eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [ib;scalar] ==> not_fresh_at sa x) /\
  w2n (bw+off) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule ec_scalar_store_shape >> strip_tac >> simp[] >>
  `eval_operand scalar
     (update_var (STRING #"%" (toString sa.cs_next_var)) (bw+off) s) = SOME wscalar` by
    (`eval_operand scalar
       (update_var (STRING #"%" (toString sa.cs_next_var)) (bw+off) s) =
       eval_operand scalar s` suffices_by simp[] >>
     irule eval_operand_update_not_fresh >> qexists_tac `sa` >>
     gvs[] >> metis_tac[]) >>
  simp[Once fragExecMemTheory.run_inst_seq_mem_ok_def,
       instMemFrontierTheory.below_frontier_no_ranges,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, bind_outputs_def,
       eval_operand_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[fragExecMemTheory.run_inst_seq_mem_ok_last,
       instMemFrontierTheory.below_frontier_MSTORE,
       memSafeRunTheory.inst_dload_in_section_def,
       eval_operand_def, lookup_var_update_var, update_var_def]
QED
