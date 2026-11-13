Theory bodyMemEcArithCallbacks
Ancestors
  bodyMemEcArithPayload exprSimPrecompiles venomState

Theorem ecmul_payload_callback:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 96 off (type_memory_size tv)) /\
  FLOOKUP s.vs_allocas sc.cs_next_id = SOME (w2n bw,96) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sc s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    FLOOKUP t.vs_allocas sc.cs_next_id = SOME (w2n bw,96) /\
    t.vs_alloca_next = s.vs_alloca_next /\
    eval_operand ib t = SOME bw /\
    mem_bytes_at (w2n bw) 96 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes wscalar T
Proof
  strip_tac >> drule_all ecmul_input_stores_sim >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next,z.vs_labels)`) >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  Cases_on `ib` >> gvs[eval_operand_def] >> metis_tac[]
QED

Theorem ecadd_payload_callback:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 128 off (type_memory_size tv)) /\
  FLOOKUP s.vs_allocas sc.cs_next_id = SOME (w2n bw,128) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es es sc s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    FLOOKUP t.vs_allocas sc.cs_next_id = SOME (w2n bw,128) /\
    t.vs_alloca_next = s.vs_alloca_next /\
    eval_operand ib t = SOME bw /\
    mem_bytes_at (w2n bw) 128 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T
Proof
  strip_tac >> drule_all ecadd_input_stores_sim >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next,z.vs_labels)`) >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  Cases_on `ib` >> gvs[eval_operand_def] >> metis_tac[]
QED
