(* Memory checks for the straight-line selector suffix. *)
Theory bodyMemBiMethodIdSuffix
Ancestors
  builtinHashing builtinBytesMemory builtinBytes exprSimHash
  exprLoweringProps emitHelperProps emitHelper context compileEnv
  fragExecMem instMemFrontier venomState venomExecSemantics
  venomInst venomMemDefs list rich_list words arithmetic
  exprSimMemDefs exprSimProps loweringPosts exprLowering compileEnv
  vyperAST vyperValue vyperTypeSystem vyperTyping

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

Theorem method_id_dynamic_hash_mem_ok:
  expr_post ctx func cenv cx e es sa sm s0 es' v src s /\
  expr_type e = BaseT bty /\ is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  expr_store_bound cx (expr_type e) v src s /\
  (!x. src = Var x ==> not_fresh_at sm x) /\
  compile_keccak256_bytes src sm = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `?b len. eval_operand src s = SOME (n2w b) /\
      mem_word_at b s.vs_memory = n2w len /\
      b + 32 < dimword (:256) /\
      b + 32 + len <= s.vs_alloca_next` by
    (Cases_on `bty` >> gvs[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
         Cases_on `v` >> gvs[value_has_type_def] >>
         drule hash_dynamic_post_view >> simp[] >> strip_tac >>
         qexistsl_tac [`b`, `LENGTH l`] >> simp[] >>
         gvs[expr_store_bound_def, is_word_type_def, val_store_size_def,
             evaluate_type_def] >>
         qspec_then `LENGTH l` mp_tac le_word_size_mul >> decide_tac) >>
     Cases_on `v` >> gvs[value_has_type_def] >>
     drule hash_string_post_view >> simp[] >> strip_tac >>
     qexistsl_tac [`b`, `LENGTH s'`] >> simp[] >>
     gvs[expr_store_bound_def, is_word_type_def, val_store_size_def,
         evaluate_type_def] >>
     qspec_then `LENGTH s'` mp_tac le_word_size_mul >> decide_tac) >>
  drule_at (Pat `compile_keccak256_bytes _ _ = _`) method_id_bytes_hash_mem_ok >>
  disch_then irule >> simp[] >>
  qexistsl_tac [`b`, `len`] >> simp[] >> decide_tac
QED
