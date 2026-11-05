(* Local ECRecover input-store boundaries, restated from the identically
   named local lemmas in exprSimPrecompilesScript.sml (S1 base proofs).
   Generic scratch-store and frame results are imported, not duplicated. *)
Theory bodyMemBiECRecoverStores
Ancestors
  bodyMemBiECRecoverFacts exprSimPrecompiles exprSimDefs
  exprSimAlloc exprSimLiteralBuffer exprSimProps exprSimOps
  compileEnv emitHelper emitHelperProps fragExec loweringPosts
  venomExecSemantics venomMemDefs venomState venomInst
  words rich_list list ASCIInumbers dftCommutation
  abiDecodeStaticProps immutableMemoryFrame exprLoweringProps valueEncodingProps
Libs
  monadsyntax

Theorem ecrecover_input_stores:
  mem_bytes_at a 128
    (mstore (a+96) sig
      (mstore (a+64) r (mstore (a+32) v (mstore a h s)))).vs_memory =
    word_to_bytes h T ++ word_to_bytes v T ++
    word_to_bytes r T ++ word_to_bytes sig T
Proof
  simp[scratch_four_word_stores]
QED

Theorem ecrecover_input_stores_shape:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig]
   od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id = sa.cs_next_id + 7
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ecrecover_lookup_generated_update:
  not_fresh_at sa x /\ sa.cs_next_var <= k ==>
  lookup_var x (update_var (STRING #"%" (toString k)) z t) = lookup_var x t
Proof
  simp[not_fresh_at_def, emitHelperPropsTheory.lookup_var_update_var] >>
  metis_tac[]
QED

Theorem ecrecover_operand_generated_update:
  (!x. q = Var x ==> not_fresh_at sa x) /\ sa.cs_next_var <= k ==>
  eval_operand q (update_var (STRING #"%" (toString k)) z t) = eval_operand q t
Proof
  Cases_on `q` >> simp[eval_operand_def] >>
  metis_tac[ecrecover_lookup_generated_update]
QED

Theorem ecrecover_operand_mstore:
  eval_operand q (mstore a z t) = eval_operand q t
Proof
  Cases_on `q` >> simp[eval_operand_def, mstore_def, lookup_var_def]
QED

Theorem ecrecover_input_stores_run:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig]
   od) sa = ((),sb) /\
  eval_operand base_op s = SOME p /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n p+96) ws (mstore (w2n p+64) wr
        (mstore (w2n p+32) wv (mstore (w2n p) wh s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  `!q k z t. MEM q [base_op;h;v;r;sig] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt strip_tac >> irule ecrecover_operand_generated_update >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_write2_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def,
       ecrecover_operand_mstore] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[run_inst_seq_def] >>
  `w2n (p+32w) = w2n p + 32 /\
   w2n (p+64w) = w2n p + 64 /\
   w2n (p+96w) = w2n p + 96` by
    (rpt conj_tac >> irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
     decide_tac) >>
  qpat_x_assum `!q k z t. _` kall_tac >>
  simp[GSYM dftCommutationTheory.update_var_mstore_commute] >>
  `!a z t m vs. (mstore a z t) with <|vs_memory := m; vs_vars := vs|> =
     t with <|vs_memory := m; vs_vars := vs|>` by simp[mstore_def] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >> simp[emitHelperPropsTheory.lookup_var_update_var] >>
  gvs[not_fresh_at_def]
QED

Theorem ecrecover_input_stores_sim:
  (do emit_void MSTORE [base_op; h];
      p1 <- emit_op ADD [base_op; Lit 32w];
      emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [base_op; Lit 64w];
      emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [base_op; Lit 96w];
      emit_void MSTORE [p3; sig]
   od) sa = ((),sb) /\
  eval_operand base_op s = SOME p /\
  eval_operand h s = SOME wh /\ eval_operand v s = SOME wv /\
  eval_operand r s = SOME wr /\ eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [base_op;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n p) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 128 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,iv) ==>
     regions_disjoint (w2n p) 128 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n p+96) ws (mstore (w2n p+64) wr
        (mstore (w2n p+32) wv (mstore (w2n p) wh s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n p) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T
Proof
  rpt strip_tac >> drule_all ecrecover_input_stores_run >> strip_tac >>
  `!b len. regions_disjoint (w2n p) 128 b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `b + len <= w2n p \/ w2n p + 128 <= b` by
       gvs[compileEnvTheory.regions_disjoint_def] >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[immutableMemoryFrameTheory.immutable_mstore_capacity] >> decide_tac) >>
  drule_all scratch_memory_frame >> strip_tac >>
  qexists_tac `t` >> simp[scratch_four_word_stores]
QED
