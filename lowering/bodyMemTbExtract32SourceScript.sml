(* Source footprint and saved-register boundary for dynamic extract32. *)
Theory bodyMemTbExtract32Source
Ancestors
  builtinBytesMemory exprSimHash exprSimHashBoundary exprSimMemDefs exprSimProps loweringPosts
  builtinBytes exprLoweringProps emitHelperProps emitHelper
  vyperValue vyperAST vyperTypeSystem venomExecSemantics venomState
  words arithmetic exprLowering compileEnv

Theorem extract32_source_post_view:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s ==>
  ?b. eval_operand op s = SOME (n2w b) /\
      mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
      b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      b + 32 + LENGTH bs <= s.vs_alloca_next
Proof
  strip_tac >>
  drule hash_dynamic_post_view >>
  disch_then (qspec_then `cap` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  gvs[expr_store_bound_def, is_word_type_def, val_store_size_def,
      vyperValueTheory.evaluate_type_def, eval_operand_def, w2n_n2w] >>
  qspec_then `LENGTH bs` mp_tac le_word_size_mul >> decide_tac
QED

Theorem extract32_source_snapshot:
  compile_bytestring_src src_op sa = ((len_op,data_op),sm) /\
  (!x. src_op = Var x ==> not_fresh_at sa x) /\
  eval_operand src_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\
  b + 32 < dimword (:256) /\ len < dimword (:256) /\
  b + 32 + len <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sm) s /\
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
      eval_operand len_op t = SOME (n2w len) /\
      eval_operand data_op t = SOME (n2w (b + 32)) /\
      w2n (n2w (b + 32):bytes32) + w2n (n2w len:bytes32) <= t.vs_alloca_next /\
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> conj_tac
  >- (irule compile_bytestring_src_mem_ok >> goal_assum (drule_at Any) >>
      simp[w2n_n2w] >> decide_tac) >>
  Cases_on `emit_op MLOAD [src_op] sa` >> rename1 `_ = (lp,sl)` >>
  Cases_on `emit_op ADD [src_op; Lit 32w] sl` >> rename1 `_ = (dp,sc)` >>
  gvs[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  `b < dimword (:256)` by decide_tac >>
  drule_all hash_data_prefix_run >> strip_tac >>
  qexists_tac `t` >> simp[w2n_n2w] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\u. u.vs_alloca_next`) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem extract32_saved_interval_post:
  expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
  not_fresh_at sa len_name /\ not_fresh_at sa data_name /\
  lookup_var len_name s0 = SOME len /\
  lookup_var data_name s0 = SOME data /\
  w2n data + w2n len <= s0.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next ==>
  eval_operand (Var len_name) s = SOME len /\
  eval_operand (Var data_name) s = SOME data /\
  w2n data + w2n len <= s.vs_alloca_next
Proof
  simp[expr_post_def, eval_operand_def] >> rpt strip_tac >>
  metis_tac[LESS_EQ_TRANS]
QED
