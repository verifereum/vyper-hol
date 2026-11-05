(* Memory checks for the straight-line selector suffix. *)
Theory bodyMemBiMethodIdSuffix
Ancestors
  builtinHashing builtinBytesMemory builtinBytes exprSimHash
  exprLoweringProps emitHelperProps emitHelper context compileEnv
  fragExecMem instMemFrontier venomState venomExecSemantics
  venomInst venomMemDefs list rich_list words arithmetic

Theorem method_id_bytes_hash_mem_ok:
  !src sa op sb s b len.
    compile_keccak256_bytes src sa = (op,sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w len /\
    b < dimword (:256) /\ b + 32 <= s.vs_alloca_next /\
    (len = 0 \/ b + 32 + len <= s.vs_alloca_next) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_op MLOAD [src] sa` >> rename1 `_ = (lp,sl)` >>
  Cases_on `emit_op ADD [src; Lit 32w] sl` >> rename1 `_ = (dp,sm)` >>
  `emit_op SHA3 [dp; lp] sm = (op,sb)` by
    gvs[compile_keccak256_bytes_def, comp_bind_def] >>
  `compile_bytestring_src src sa = ((lp,dp),sm)` by
    simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule compile_bytestring_src_mem_ok >> goal_assum (drule_at Any) >>
     simp[w2n_n2w, MOD_LESS]) >>
  drule_all hash_data_prefix_run >> strip_tac >>
  qpat_assum `emit_op SHA3 _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with vs_vars := _ = s` (mp_tac o Q.AP_TERM `\u. u.vs_alloca_next`) >> simp[]) >>
  simp[w2n_n2w] >>
  `len MOD dimword (:256) <= len` by simp[MOD_LESS_EQ] >>
  `(b + 32) MOD dimword (:256) <= b + 32` by simp[MOD_LESS_EQ] >>
  decide_tac
QED
