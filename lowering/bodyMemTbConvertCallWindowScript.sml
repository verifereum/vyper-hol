(* Same-execution read of a bytestring internal-call return buffer. *)
Theory bodyMemTbConvertCallWindow
Ancestors
  bodyMemTbConvertCallSource bodyMemTbConvertSourceDispatch
  exprSimAggregateChildren exprSimUnwrapProps exprSimUnwrap
  exprSimMemDefs fragGasMode fragGasPathMem exprLowering loweringPosts
  context compileEnv valueCopyBytes vyperState gasSummary gasOutcome
  exprSimMemorySource

Theorem convert_call_result_location[local]:
  compile_expr ce ty (Call ann (IntCall fid) args drv) sa = (vv,sm) ==>
  !t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory
Proof
  simp[Once compile_expr_def] >>
  metis_tac[aggregate_intcall_result_location]
QED

Theorem convert_call_unwrap_identity[local]:
  compile_expr ce ty (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  vv_post ctx func ce cx (Call ann (IntCall fid) args drv)
    es sa sm s0 ee tv vv s /\ is_bytestring_type ann /\
  unwrap_value ce vv sm = (op,sb) ==>
  sb = sm /\
  ((?t. vv = StackValue t op) \/
   ?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
         p.ptr_operand = op /\ ~is_word_type t)
Proof
  strip_tac >> Cases_on `vv`
  >- gvs[unwrap_value_def, comp_return_def] >>
  rename1 `LocatedValue t p` >>
  `p.ptr_location = LocMemory` by metis_tac[convert_call_result_location] >>
  `~is_word_type t` by
    (gvs[vv_post_def, vv_holds_def, post_value_type_def,
         vyperASTTheory.expr_type_def] >>
     metis_tac[is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def]
QED

Theorem convert_call_read_post[local]:
  compile_expr ce ty (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  vv_post ctx func ce cx (Call ann (IntCall fid) args drv)
    es sa sm s0 ee tv vv s /\ is_bytestring_type ann /\
  unwrap_value ce vv sm = (op,sb) /\
  read_result cx tv ee = (INL v,ee) ==>
  sb = sm /\
  expr_post ctx func ce cx (Call ann (IntCall fid) args drv)
    es sa sb s0 ee v op s
Proof
  strip_tac >> drule_all convert_call_unwrap_identity >> strip_tac >> gvs[] >>
  drule vv_post_read_result >> strip_tac >> gvs[] >>
  metis_tac[expr_post_of_vv_post_memory, expr_post_of_vv_post_stack]
QED

Theorem convert_call_marked_read_window:
  compile_expr ce ty (Call ann (IntCall fid) args drv) sa = (vv,sm) /\
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  is_bytestring_type ann /\
  unwrap_value ce vv sm = (op,sb) /\
  evaluate_type (get_tenv cx)
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) = SOME ltv /\
  type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) =
    type_memory_size ltv /\
  vv_post ctx func ce cx (Call ann (IntCall fid) args drv)
    es sa sm s0 ee tv vv s /\
  vv_store_bound cx ann (lowered_value_type ce (Call ann (IntCall fid) args drv))
    ee tv vv s /\
  ~s.vs_halted ==>
  ?v. sb = sm /\
    gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s) [] (INL v) ee (OK s) /\
    expr_post ctx func ce cx (Call ann (IntCall fid) args drv)
      es sa sb s0 ee v op s /\
    (!w. eval_operand op s = SOME w ==>
      w2n w + type_memory_bytes ce
        (lowered_value_type ce (Call ann (IntCall fid) args drv)) <= s.vs_alloca_next) /\
    (lowered_value_type ce (Call ann (IntCall fid) args drv) <>
       BaseT (BytesT (Dynamic 0)) /\
     lowered_value_type ce (Call ann (IntCall fid) args drv) <> BaseT (StringT 0) ==>
     !w. eval_operand op s = SOME w ==> w2n w + 64 <= s.vs_alloca_next)
Proof
  strip_tac >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (Cases_on `read_result cx tv ee` >>
     metis_tac[read_result_state, vv_post_failed_read, sumTheory.sum_CASES]) >>
  drule_all convert_call_unwrap_identity >> disch_then assume_tac >>
  `sb = sm` by metis_tac[] >>
  `is_bytestring_type (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    metis_tac[convert_call_lowered_bytestring] >>
  `0 < type_memory_size ltv` by
    metis_tac[bytestring_memory_bytes_positive] >>
  `!w. eval_operand op s = SOME w ==>
    w2n w + type_memory_size ltv <= s.vs_alloca_next` by
    (gvs[vv_store_bound_def] >> metis_tac[is_bytestring_word_type]) >>
  `!w. eval_operand op s = SOME w ==>
    type_memory_size ltv + w2n w <= s.vs_alloca_next` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  qexists_tac `v` >> simp[] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
      metis_tac[read_result_gas_obs, listTheory.APPEND, gas_path_mem_rules]) >>
  conj_tac >- metis_tac[convert_call_read_post] >>
  strip_tac >>
  `64 <= type_memory_bytes ce
    (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    (irule convert_nonzero_bytestring_memory_size >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED
