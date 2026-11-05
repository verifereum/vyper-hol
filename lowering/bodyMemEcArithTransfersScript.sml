Theory bodyMemEcArithTransfers
Ancestors
  bodyMemEcArithPrefix emitHelperProps exprLoweringProps context venomState
  exprSimWordBuiltins emitHelper compileEnv exprSimCalldataSlice
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

(* Restatement of private exprSimECArith.ec_point_transfers_run;
   reference: alan-ref/base/exprSimECArithScript.sml.txt, lines 642-701. *)
Theorem ec_point_transfers_run:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  regions_disjoint (w2n (bword+boff)) 64 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword+boff)+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n (bword+boff)) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all ec_point_word_transfer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK s1` >>
  rev_drule_then strip_assume_tac ec_point_word_transfer_shape >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `_ = s` (mp_tac o Q.AP_TERM `\st. st.vs_labels`) >> simp[]) >>
  `eval_operand point_op s1 = SOME point /\ eval_operand base_op s1 = SOME bword` by
    (conj_tac >> Cases_on `point_op` >> Cases_on `base_op` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sb x` by metis_tac[] >>
  drule_all ec_point_word_transfer_run >> strip_tac >>
  `w2n (point+32w) = w2n point+32 /\
   w2n ((bword+boff)+32w) = w2n (bword+boff)+32` by
    (conj_tac >> irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `mem_word_at (w2n point+32) s1.vs_memory =
   mem_word_at (w2n point+32) s.vs_memory` by
    (simp[] >> irule mstore_mem_word_at_disjoint >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  qexists_tac `t` >> conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac
  >- (qpat_x_assum `t.vs_memory = _` mp_tac >>
      qpat_x_assum `s1.vs_memory = _` mp_tac >>
      pure_asm_rewrite_tac[wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_0] >>
      ntac 2 strip_tac >> qpat_x_assum `t.vs_memory = _` SUBST1_TAC >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then
        [`w2n (bword+boff)+32`, `mem_word_at (w2n point+32) s.vs_memory`] mp_tac) >>
      simp[NoAsms]) >>
  conj_tac
  >- (qpat_assum `_ = s1`
        (mp_tac o Q.AP_TERM `\st. st with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>`) >>
      simp[]) >>
  metis_tac[]
QED

(* Restatement of private exprSimECArith.ec_point_pair_transfer_run;
   reference: alan-ref/base/exprSimECArithScript.sml.txt, lines 826-872. *)
Theorem ec_point_pair_transfer_run:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value];
      src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sa = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  regions_disjoint (w2n (bword+boff)) 64 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword+boff)+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n (bword+boff)) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `(do (do src <- emit_op ADD [point_op; Lit 0w];
           value <- emit_op MLOAD [src];
           dst <- emit_op ADD [base_op; Lit boff];
           emit_void MSTORE [dst; value] od);
       src <- emit_op ADD [point_op; Lit 32w];
       value <- emit_op MLOAD [src];
       dst <- emit_op ADD [base_op; Lit (boff+32w)];
       emit_void MSTORE [dst; value] od) sa = ((),sc)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `_ sa = (u,sb)` >>
  Cases_on `u` >> strip_tac >>
  drule_all ec_point_transfers_run >> strip_tac >>
  rev_drule_then strip_assume_tac ec_point_word_transfer_shape >>
  drule_then strip_assume_tac ec_point_word_transfer_shape >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  qexists_tac `t` >> simp[] >> gvs[venom_state_component_equality]
QED

(* Restatement of private exprSimECArith.ec_point_prefix_then_run;
   reference: alan-ref/base/exprSimECArithScript.sml.txt, lines 876-949. *)
Theorem ec_point_prefix_then_run:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y]; tail od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) (p::ib::ops) ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n bw + len < dimword (:256) /\ 64 <= len /\
  regions_disjoint (w2n bw) len (w2n point) 64 ==>
  ?sc t.
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib; Lit 32w];
        emit_void MSTORE [dst1; y] od) sa = ((),sc) /\
    tail sc = ((),sb) /\
    run_inst_seq (emitted_insts sa sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sc.cs_next_var = sa.cs_next_var + 6 /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    (!op. MEM op (ib::ops) ==> eval_operand op t = eval_operand op s) /\
    (!x. MEM (Var x) (ib::ops) ==> not_fresh_at sc x)
Proof
  strip_tac >>
  `(do (do xp <- emit_op ADD [p; Lit 0w];
           x <- emit_op MLOAD [xp];
           dst0 <- emit_op ADD [ib; Lit 0w];
           emit_void MSTORE [dst0; x];
           yp <- emit_op ADD [p; Lit 32w];
           y <- emit_op MLOAD [yp];
           dst1 <- emit_op ADD [ib; Lit 32w];
           emit_void MSTORE [dst1; y] od); tail od) sa = ((),sb)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `_ sa = (u,sc)` >>
  Cases_on `u` >> strip_tac >>
  `!x. MEM (Var x) [p;ib] ==> not_fresh_at sa x` by (gvs[] >> metis_tac[]) >>
  `w2n bw + 64 < dimword (:256) /\
   regions_disjoint (w2n bw) 64 (w2n point) 64` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  drule (Q.INST [`boff` |-> `0w`] (SPEC_ALL ec_point_pair_transfer_run)
    |> SRULE [wordsTheory.WORD_ADD_0]) >>
  disch_then (qspecl_then [`s`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `sc.cs_next_var = sa.cs_next_var + 6 /\
   sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    (qpat_assum `_ sa = ((),sc)` mp_tac >>
     simp[NoAsms, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum irule >> simp[] >> decide_tac
QED
