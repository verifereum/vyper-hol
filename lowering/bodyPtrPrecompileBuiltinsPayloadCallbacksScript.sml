Theory bodyPtrPrecompileBuiltinsPayloadCallbacks
Ancestors bodyPtrPrecompileBuiltinsPayloadRuns bodyPtrPrecompileBuiltinsPayloadCompose
          bodyPtrPrecompileBuiltinsPayloadNormalize dftCommutation
          emitHelper context compileEnv loweringStateRelDefs venomState exprLoweringProps
          exprSimWordBuiltins exprSimPrecompiles emitHelperProps
          immutableMemoryFrame valueEncodingProps moduleLoweringProps
          venomMemProps immutableCopyExecution exprSimHash exprSimHashBoundary
          loweringPosts vyperValue vyperTyping valueEncoding

Theorem recovery_payload_run:
  (do emit_void MSTORE [buf; h];
      p1 <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [p3; sig] od)
    sa = ((),sb) /\
  eval_operand buf s = SOME p /\ eval_operand h s = SOME wh /\
  eval_operand v s = SOME wv /\ eval_operand r s = SOME wr /\
  eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [buf;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (w2n p+96) ws (mstore (w2n p+64) wr
      (mstore (w2n p+32) wv (mstore (w2n p) wh s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    mem_bytes_at (w2n p) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `!op n z u. MEM op [buf;h;v;r;sig] /\ sa.cs_next_var <= n ==>
    eval_operand op (update_var (STRING #"%" (toString n)) z u) =
    eval_operand op u` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists `sa` >> gvs[] >> metis_tac[]) >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_write2_def, eval_operand_lit,
       eval_operand_update_var, eval_operand_mstore] >>
  `w2n (p+32w) = w2n p + 32 /\
   w2n (p+64w) = w2n p + 64 /\
   w2n (p+96w) = w2n p + 96` by
    (rpt conj_tac >> irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
     decide_tac) >>
  qpat_x_assum `!op n z u. _` kall_tac >>
  pure_rewrite_tac[GSYM update_var_mstore_commute] >>
  simp[update_var_def, mstore_vars_memory_overwrite,
       scratch_four_word_stores] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[GSYM lookup_var_def, lookup_var_mstore]
QED

Theorem recovery_payload_callback:
  (do emit_void MSTORE [buf; h];
      p1 <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [p1; v];
      p2 <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [p2; r];
      p3 <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [p3; sig] od)
    sa = ((),sb) /\
  eval_operand buf s = SOME p /\ eval_operand h s = SOME wh /\
  eval_operand v s = SOME wv /\ eval_operand r s = SOME wr /\
  eval_operand sig s = SOME ws /\
  (!x. MEM (Var x) [buf;h;v;r;sig] ==> not_fresh_at sa x) /\
  w2n p + 128 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,128) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n p) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 128 b sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sc s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ eval_operand buf t = SOME p /\
    mem_bytes_at (w2n p) 128 t.vs_memory =
      word_to_bytes wh T ++ word_to_bytes wv T ++
      word_to_bytes wr T ++ word_to_bytes ws T
Proof
  strip_tac >> drule_all recovery_payload_run >> strip_tac >>
  drule precompile_alloca_immutable_disjoint >> disch_tac >>
  `!b len. regions_disjoint (w2n p) 128 b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `b + len <= w2n p \/ w2n p + 128 <= b` by
       gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[immutable_mstore_capacity] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sc s t` by
    (irule scratch_memory_frame >> simp[] >>
     conj_tac >- metis_tac[] >> qexists `sa` >> simp[]) >>
  qexists `t` >> simp[] >>
  conj_tac
  >- (drule bodyPtrPrecompileBuiltinsPayloadFramesTheory.scratch_reset_allocations >>
      simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
      (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  Cases_on `buf` >> gvs[eval_operand_def] >> metis_tac[]
QED

Theorem point_pair_payload_run:
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit off]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit (off+32w)]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) /\
  eval_operand point s = SOME p /\ eval_operand buf s = SOME b /\
  (!x. MEM (Var x) [point;buf] ==> not_fresh_at sa x) /\
  w2n p + 64 < dimword (:256) /\
  w2n (b+off) + 64 < dimword (:256) /\
  regions_disjoint (w2n (b+off)) 64 (w2n p) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (w2n (b+off)+32) (mload (w2n p+32) s)
      (mstore (w2n (b+off)) (mload (w2n p) s) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `!op n z u. MEM op [point;buf] /\ sa.cs_next_var <= n ==>
    eval_operand op (update_var (STRING #"%" (toString n)) z u) =
    eval_operand op u` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists `sa` >> gvs[] >> metis_tac[]) >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomExecSemanticsTheory.exec_write2_def, eval_operand_lit,
       eval_operand_update_var, eval_operand_update_other,
       fresh_var_distinct, eval_operand_mstore] >>
  qpat_x_assum `!op n z u. _` kall_tac >>
  pure_rewrite_tac[GSYM update_var_mstore_commute] >>
  `w2n (p+32w) = w2n p + 32 /\
   w2n (b+(off+32w)) = w2n (b+off) + 32` by
    (rewrite_tac[wordsTheory.WORD_ADD_ASSOC] >> rpt conj_tac >>
     irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `!w. mload (w2n p+32) (mstore (w2n (b+off)) w s) =
       mload (w2n p+32) s` by
    (gen_tac >> irule venomMemPropsTheory.mload_mstore_disjoint >>
     gvs[venomMemDefsTheory.regions_disjoint_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[GSYM mem_word_at_eq_mload, update_var_def,
       mstore_vars_memory_overwrite] >>
  conj_tac >- simp[mem_word_at_eq_mload, wordsTheory.WORD_ADD_0] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[GSYM lookup_var_def, lookup_var_mstore]
QED

Theorem payload_operand_preserved:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s`
      (mp_tac o Q.AP_TERM `\z. z.vs_labels`) >> simp[]) >>
  Cases_on `op` >> simp[eval_operand_def]
QED

Theorem mul_payload_stages_run:
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 0w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [dst; value] od)
    sa = ((),sm) /\
  (do dst <- emit_op ADD [buf; Lit 64w];
      emit_void MSTORE [dst; scalar] od) sm = ((),sb) /\
  eval_operand point s = SOME p /\ eval_operand buf s = SOME b /\
  eval_operand scalar s = SOME w /\
  (!x. MEM (Var x) [point;buf;scalar] ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sm.cs_next_var /\
  w2n p + 64 < dimword (:256) /\ w2n b + 96 < dimword (:256) /\
  regions_disjoint (w2n b) 64 (w2n p) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
    t.vs_memory = (mstore (w2n b+64) w
      (mstore (w2n b+32) (mload (w2n p+32) s)
        (mstore (w2n b) (mload (w2n p) s) s))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    mem_bytes_at (w2n b) 96 t.vs_memory =
      word_to_bytes (mload (w2n p) s) T ++
      word_to_bytes (mload (w2n p+32) s) T ++ word_to_bytes w T
Proof
  strip_tac >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
    u.vs_memory = (mstore (w2n b+32) (mload (w2n p+32) s)
      (mstore (w2n b) (mload (w2n p) s) s)).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)` by
    (simp[] >> irule (point_pair_payload_run |> SPEC_ALL |>
       Q.INST [`off` |-> `0w`] |> SRULE [wordsTheory.WORD_ADD_0]) >> simp[] >>
     qexistsl [`buf`,`point`] >> simp[] >> metis_tac[listTheory.MEM]) >>
  `eval_operand buf u = SOME b /\ eval_operand scalar u = SOME w` by
    (conj_tac >> irule EQ_TRANS >> goal_assum (drule_at Any) >>
     irule payload_operand_preserved >> goal_assum (drule_at Any) >>
     qexists `sa` >> simp[] >> metis_tac[listTheory.MEM]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  `!x. scalar = Var x ==> not_fresh_at sm x` by
    metis_tac[listTheory.MEM] >>
  drule_all (offset_store_run |> SPEC_ALL |> Q.INST [`s` |-> `u`]) >> strip_tac >>
  qexists `t` >>
  `w2n (b+64w) = w2n b + 64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `t.vs_memory = (mstore (w2n b+64) w
      (mstore (w2n b+32) (mload (w2n p+32) s)
        (mstore (w2n b) (mload (w2n p) s) s))).vs_memory` by
    (simp[] >> irule immutable_mstore_memory_cong >> simp[]) >>
  simp[scratch_three_word_stores] >>
  conj_tac >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  gvs[mstore_vars_memory_overwrite, update_var_def]
QED

Theorem allocated_scratch_point_disjoint:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v op s /\
  eval_operand op s = SOME p /\ sf.cs_next_id <= sc.cs_next_id /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
     regions_disjoint b n a sz) /\
  (!aid a sz. aid < sc.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
     regions_disjoint b n a sz) ==>
  regions_disjoint b n (w2n p) 64
Proof
  strip_tac >>
  `val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64` by
    (Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]) >>
  drule expr_val_at_footprint >>
  simp[evaluate_type_def, is_word_type_def, type_slot_size_def,
       wordsTheory.dimword_def] >>
  strip_tac >>
  `regions_disjoint b n b' sz` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem mul_payload_callback:
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 0w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [dst; value] od)
    sa = ((),sm) /\
  (do dst <- emit_op ADD [buf; Lit 64w];
      emit_void MSTORE [dst; scalar] od) sm = ((),sb) /\
  eval_operand point s = SOME p /\ eval_operand buf s = SOME b /\
  eval_operand scalar s = SOME w /\
  (!x. MEM (Var x) [point;buf;scalar] ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sm.cs_next_var /\
  w2n p + 64 < dimword (:256) /\ w2n b + 96 < dimword (:256) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v point s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,96) /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
     regions_disjoint (w2n b) 96 a sz) /\
  (!aid a sz. aid < sf.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
     regions_disjoint (w2n b) 96 a sz) ==>
  ?t. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sf s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ eval_operand buf t = SOME b /\
    mem_bytes_at (w2n b) 96 t.vs_memory =
      word_to_bytes (mload (w2n p) s) T ++
      word_to_bytes (mload (w2n p+32) s) T ++ word_to_bytes w T
Proof
  strip_tac >>
  `regions_disjoint (w2n b) 96 (w2n p) 64` by
    (irule allocated_scratch_point_disjoint >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `regions_disjoint (w2n b) 64 (w2n p) 64` by
    (gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_all mul_payload_stages_run >> strip_tac >>
  drule precompile_alloca_immutable_disjoint >> disch_tac >>
  `!a len. regions_disjoint (w2n b) 96 a len ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >>
     `a + len <= w2n b \/ w2n b + 96 <= a` by
       gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[immutable_mstore_capacity] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sf s t` by
    (irule scratch_memory_frame >> simp[] >>
     conj_tac >- metis_tac[] >> qexists `sa` >> simp[]) >>
  qexists `t` >> simp[] >> conj_tac
  >- (drule bodyPtrPrecompileBuiltinsPayloadFramesTheory.scratch_reset_allocations >>
      simp[]) >>
  irule EQ_TRANS >> goal_assum (drule_at Any) >>
  irule payload_operand_preserved >> goal_assum (drule_at Any) >>
  qexists `sa` >> simp[] >> metis_tac[listTheory.MEM]
QED

Theorem add_payload_stages_run:
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 0w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [dst; value] od)
    sa = ((),sm) /\
  (do src <- emit_op ADD [other; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [other; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [dst; value] od)
    sm = ((),sb) /\
  eval_operand point s = SOME p /\ eval_operand other s = SOME q /\
  eval_operand buf s = SOME b /\
  (!x. MEM (Var x) [point;other;buf] ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sm.cs_next_var /\
  w2n p + 64 < dimword (:256) /\ w2n q + 64 < dimword (:256) /\
  w2n b + 128 < dimword (:256) /\
  regions_disjoint (w2n b) 128 (w2n p) 64 /\
  regions_disjoint (w2n b) 128 (w2n q) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
    t.vs_memory = (mstore (w2n b+96) (mload (w2n q+32) s)
      (mstore (w2n b+64) (mload (w2n q) s)
      (mstore (w2n b+32) (mload (w2n p+32) s)
        (mstore (w2n b) (mload (w2n p) s) s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    mem_bytes_at (w2n b) 128 t.vs_memory =
      word_to_bytes (mload (w2n p) s) T ++ word_to_bytes (mload (w2n p+32) s) T ++
      word_to_bytes (mload (w2n q) s) T ++ word_to_bytes (mload (w2n q+32) s) T
Proof
  strip_tac >>
  `regions_disjoint (w2n b) 64 (w2n p) 64` by
    (gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `?u. run_inst_seq (emitted_insts sa sm) s = OK u /\
    u.vs_memory = (mstore (w2n b+32) (mload (w2n p+32) s)
      (mstore (w2n b) (mload (w2n p) s) s)).vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)` by
    (simp[] >> irule (point_pair_payload_run |> SPEC_ALL |>
       Q.INST [`off` |-> `0w`] |> SRULE [wordsTheory.WORD_ADD_0]) >> simp[] >>
     qexistsl [`buf`,`point`] >> simp[] >> metis_tac[listTheory.MEM]) >>
  `eval_operand buf u = SOME b /\ eval_operand other u = SOME q` by
    (conj_tac >> irule EQ_TRANS >> goal_assum (drule_at Any) >>
     irule payload_operand_preserved >> goal_assum (drule_at Any) >>
     qexists `sa` >> simp[] >> metis_tac[listTheory.MEM]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> decide_tac) >>
  `w2n (b+64w) = w2n b + 64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `!a z r. w2n q <= a /\ a+32 <= w2n q+64 /\
      (r = w2n b \/ r = w2n b+32) ==> !v.
      mload a (mstore r v z) = mload a z` by
    (rpt strip_tac >> irule mload_mstore_disjoint >>
     gvs[venomMemDefsTheory.regions_disjoint_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mload (w2n q) u = mload (w2n q) s /\
   mload (w2n q+32) u = mload (w2n q+32) s` by
    (simp[GSYM mem_word_at_eq_mload] >> simp[mem_word_at_eq_mload]) >>
  `!x. MEM (Var x) [other;buf] ==> not_fresh_at sm x` by
    metis_tac[listTheory.MEM] >>
  drule (point_pair_payload_run |> SPEC_ALL |> Q.INST [`off` |-> `64w`] |>
    SRULE [wordsTheory.word_add_n2w]) >>
  simp[] >> disch_then (qspecl_then [`u`,`q`,`b`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >>
  `run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
   (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)` by
    (irule payload_run_frame_compose >> qexistsl [`not_fresh_at sm`,`u`] >> simp[]) >>
  `t.vs_memory = (mstore (w2n b+96) (mload (w2n q+32) s)
    (mstore (w2n b+64) (mload (w2n q) s)
      (mstore (w2n b+32) (mload (w2n p+32) s)
        (mstore (w2n b) (mload (w2n p) s) s)))).vs_memory` by
    (simp[] >> irule immutable_mstore_memory_cong >>
     irule immutable_mstore_memory_cong >> simp[]) >>
  qexists `t` >> simp[scratch_four_word_stores] >>
  fs[venom_state_component_equality]
QED

Theorem add_payload_callback:
  (do src <- emit_op ADD [point; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 0w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [point; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 32w]; emit_void MSTORE [dst; value] od)
    sa = ((),sm) /\
  (do src <- emit_op ADD [other; Lit 0w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 64w]; emit_void MSTORE [dst; value];
      src <- emit_op ADD [other; Lit 32w]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit 96w]; emit_void MSTORE [dst; value] od)
    sm = ((),sb) /\
  eval_operand point s = SOME p /\ eval_operand other s = SOME q /\
  eval_operand buf s = SOME b /\
  (!x. MEM (Var x) [point;other;buf] ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sm.cs_next_var /\
  w2n p + 64 < dimword (:256) /\ w2n q + 64 < dimword (:256) /\
  w2n b + 128 < dimword (:256) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vp point s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es vq other s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n b,128) /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
     regions_disjoint (w2n b) 128 a sz) /\
  (!aid a sz. aid < sf.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
     regions_disjoint (w2n b) 128 a sz) ==>
  ?t. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sf s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ eval_operand buf t = SOME b /\
    mem_bytes_at (w2n b) 128 t.vs_memory =
      word_to_bytes (mload (w2n p) s) T ++ word_to_bytes (mload (w2n p+32) s) T ++
      word_to_bytes (mload (w2n q) s) T ++ word_to_bytes (mload (w2n q+32) s) T
Proof
  strip_tac >>
  `regions_disjoint (w2n b) 128 (w2n p) 64` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ vp point s`
       (mp_then Any mp_tac allocated_scratch_point_disjoint) >>
     disch_then drule >> disch_then irule >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `sf` >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `regions_disjoint (w2n b) 128 (w2n q) 64` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ vq other s`
       (mp_then Any mp_tac allocated_scratch_point_disjoint) >>
     disch_then drule >> disch_then irule >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `sf` >> simp[] >>
     first_assum ACCEPT_TAC) >>
  drule_all add_payload_stages_run >> strip_tac >>
  drule precompile_alloca_immutable_disjoint >> disch_tac >>
  `!a len. regions_disjoint (w2n b) 128 a len ==>
     mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >>
     `a + len <= w2n b \/ w2n b + 128 <= a` by
       gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     simp[mstore_mem_bytes_at_disjoint]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[immutable_mstore_capacity] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sf s t` by
    (irule scratch_memory_frame >> simp[] >>
     conj_tac >- metis_tac[] >> qexists `sa` >> simp[]) >>
  qexists `t` >> simp[] >> conj_tac
  >- (drule bodyPtrPrecompileBuiltinsPayloadFramesTheory.scratch_reset_allocations >> simp[]) >>
  irule EQ_TRANS >> goal_assum (drule_at Any) >>
  irule payload_operand_preserved >> goal_assum (drule_at Any) >>
  qexists `sa` >> simp[] >> metis_tac[listTheory.MEM]
QED
