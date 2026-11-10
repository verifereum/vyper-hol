Theory bodyPtrPrecompileBuiltinsPayloadRuns
Ancestors bodyPtrPrecompileBuiltinsCompilerStages
          bodyPtrPrecompileBuiltinsPayloadFrames emitHelperProps
          exprSimWordBuiltins moduleLoweringProps valueEncodingProps
          emitHelper context compileEnv loweringStateRelDefs venomState exprLoweringProps
          exprSimPrecompiles venomMemProps

Theorem direct_store_run:
  emit_void MSTORE [dst; value] sa = ((),sb) /\
  eval_operand dst s = SOME p /\ eval_operand value s = SOME w ==>
  run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n p) w s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[] >> irule run_inst_seq_sing_ok >> simp[step_MSTORE]
QED

Theorem offset_store_run:
  (do dst <- emit_op ADD [buf; Lit off];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  eval_operand buf s = SOME p /\ eval_operand value s = SOME w /\
  (!x. value = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t = mstore (w2n (p+off)) w
      (update_var (STRING #"%" (toString sa.cs_next_var)) (p+off) s) /\
    t.vs_memory = (mstore (w2n (p+off)) w s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [buf; Lit off]
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (p+off) s)`
    by (irule step_ADD >> simp[eval_operand_lit]) >>
  simp[run_inst_seq_def] >>
  `eval_operand value
     (update_var (STRING #"%" (toString sa.cs_next_var)) (p+off) s) = SOME w`
    by (qspec_then `sa` mp_tac eval_operand_update_not_fresh >>
        disch_then drule >> simp[]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE
      [Var (STRING #"%" (toString sa.cs_next_var)); value] [])
      (update_var (STRING #"%" (toString sa.cs_next_var)) (p+off) s) =
    OK (mstore (w2n (p+off)) w
      (update_var (STRING #"%" (toString sa.cs_next_var)) (p+off) s))`
    by (irule step_MSTORE >> simp[eval_operand_def, lookup_var_update_var]) >>
  simp[mstore_def, update_var_def, lookup_var_def] >>
  rpt strip_tac >>
  qspec_then `sa` mp_tac lookup_var_update_not_fresh >>
  disch_then drule >> simp[update_var_def, lookup_var_def]
QED

(* The allocated scratch word itself supplies constructor-immutable
   separation; it is not an additional premise imposed on callers. *)
Theorem allocated_word_store_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,32) /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
    regions_disjoint b 32 a sz) /\
  (!aid a sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
    regions_disjoint b 32 a sz) ==>
  stmt_state_rel ctx func cenv cx es (mstore b w s) /\
  wb_frame cenv es sa s (mstore b w s)
Proof
  strip_tac >> drule precompile_alloca_immutable_disjoint >>
  disch_tac >>
  irule scratch_memory_frame >>
  simp[mstore_memory_nondecreasing] >>
  conj_tac >- simp[mstore_def] >>
  conj_tac
  >- (qexistsl [`b`,`32`] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac
      >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
          gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      metis_tac[]) >>
  qexists `sa` >> simp[]
QED

Theorem allocated_word_store_run:
  emit_void MSTORE [dst; value] sa = ((),sb) /\
  eval_operand dst s = SOME p /\ eval_operand value s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!name a sz. local_region cenv es.scopes s name a sz ==>
    regions_disjoint (w2n p) 32 a sz) /\
  (!aid a sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (a,sz) ==>
    regions_disjoint (w2n p) 32 a sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    t.vs_allocas = s.vs_allocas /\
    (!op. eval_operand op t = eval_operand op s) /\
    mem_bytes_at (w2n p) 32 t.vs_memory = word_to_bytes w T
Proof
  strip_tac >> drule_all direct_store_run >> disch_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n p) w s) /\
   wb_frame cenv es sa s (mstore (w2n p) w s)` by
    (irule allocated_word_store_frame >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >> qexists `inst` >> simp[]) >>
  qexists `mstore (w2n p) w s` >>
  simp[mstore_def, mem_bytes_at_mstore_same, eval_operand_mstore]
QED

Theorem word_transfer_run:
  (do src <- emit_op ADD [p; Lit poff]; value <- emit_op MLOAD [src];
      dst <- emit_op ADD [buf; Lit boff]; emit_void MSTORE [dst; value] od)
    sa = ((),sb) /\
  eval_operand p s = SOME pw /\ eval_operand buf s = SOME bw /\
  (!x. buf = Var x ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (w2n (bw+boff)) (mload (w2n (pw+poff)) s) s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  `!n v u. sa.cs_next_var <= n ==>
    eval_operand buf (update_var (STRING #"%" (toString n)) v u) =
    eval_operand buf u` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists `sa` >> simp[]) >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomExecSemanticsTheory.exec_write2_def, eval_operand_lit,
       eval_operand_update_var, eval_operand_update_not_fresh |> Q.SPEC `sa`,
       eval_operand_update_other, fresh_var_distinct] >>
  simp[mload_def, mstore_def, update_var_def, lookup_var_def] >>
  rpt strip_tac >>
  gvs[not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED
