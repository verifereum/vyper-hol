(* Numeric uint2str postconditions on the counted memory execution. *)
Theory bodyMemBiUint2StrPost
Ancestors
  bodyMemBiUint2StrSuffix exprWordOperand exprSimWordArgs tupleMemoryFrame
  exprSimHypsDefs exprSimMemDefs loweringPosts exprSimUint2Str exprSimHash
  exprLoweringProps exprSimSource exprSafeOperand vyperTyping vyperTypeSystem vyperArith arithmetic context compileEnv valueEncoding loweringSlice vyperValue vyperAST

Theorem uint2str_numeric_mem_path:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\
  lower_value compile_expr cenv ty e sa = (x,sm) /\
  compile_uint2str x n sz sm = (out,sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_post ctx func cenv cx e es sa sm s0 es' (IntV (&X)) x s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  X < dimword (:256) /\ 78 <= n /\ n+32 <= sz /\ sz+n < dimword (:256) /\
  alloca_history func s ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
      es sa sb s0 es' (Value (StringV (num_to_dec_string X)))
      (LocatedValue (BaseT (StringT n)) (mk_ptr out LocMemory)) t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ?p. eval_operand out t = SOME (n2w p) /\ p < dimword (:256) /\
      p+sz <= t.vs_alloca_next
Proof
  strip_tac >> drule_all compile_uint2str_layout >> strip_tac >>
  drule_all expr_post_frame >> strip_tac >>
  drule_all expr_post_state >> strip_tac >>
  `wb_frame cenv es' es' sm s s` by simp[wb_frame_refl] >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `well_formed_type env.type_defs (expr_type e)` by
    (irule well_typed_expr_type_well_formed >>
     metis_tac[expr_body_pre_var_types_well_formed, expr_body_pre_def]) >>
  `eval_operand x s = SOME (n2w X)` by
    (drule expr_post_word_operand >>
     gvs[well_formed_type_def, is_word_type_def, word_value_def,
        val_to_w256_def, evaluate_type_def, integer_wordTheory.i2w_def]) >>
  `32 <= sz` by decide_tac >>
  drule_all (SRULE [] (Q.INST
    [`sa` |-> `sm`, `sp` |-> `sm`, `spre` |-> `s`] u2s_allocated_mem_exit)) >>
  disch_then (qspec_then `BaseTV (StringT n)` mp_tac) >>
  strip_tac >>
  `wb_frame cenv es es' sa s0 t` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`es'`, `sm`, `s`] >> simp[]) >>
  mp_tac (Q.INST [`X` |-> `X`, `n` |-> `n`] uint2str_result_memory_bounds) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH (num_to_dec_string X) <= n` by
    (mp_tac (Q.INST [`x` |-> `X`] uint256_decimal_length) >>
     fs[wordsTheory.dimword_def] >> decide_tac) >>
  `b <= b+n-LENGTH (num_to_dec_string X) /\
   b+n-LENGTH (num_to_dec_string X) < dimword (:256)` by decide_tac >>
  `sb.cs_current_bb = u2s_label a 5 /\ sb.cs_current_insts = [] /\
   sb.cs_next_id = a.cs_next_id+30` by fs[u2s_layout_def, u2s_end_def] >>
  qexists_tac `t` >> simp[] >>
  reverse conj_tac >-
    (qexists_tac `b+n-LENGTH (num_to_dec_string X)` >> simp[]) >>
  irule (SRULE [expr_type_def] (Q.INST
    [`e` |-> `Builtin (BaseT (StringT n)) (Uint2Str n) [e]`]
    vv_post_allocated_memory_intro)) >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def, mk_ptr_def] >>
  reverse conj_tac >- fs[u2s_safe_def] >>
  qexistsl_tac [`inst.inst_id`, `b`, `sz+n`] >>
  fs[u2s_safe_def, type_slot_size_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `0 < n` by decide_tac >> drule word_size_le >> decide_tac
QED

Theorem uint2str_vv_capacity:
  vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
    es sa sb s0 es' tv (LocatedValue (BaseT (StringT n)) p) t /\
  eval_operand p.ptr_operand t = SOME (n2w addr) /\ addr < dimword (:256) /\
  n < dimword (:256) /\
  addr + type_memory_bytes cenv (BaseT (StringT n)) <= t.vs_alloca_next ==>
  vv_store_bound cx (BaseT (StringT n)) (BaseT (StringT n)) es' tv
    (LocatedValue (BaseT (StringT n)) p) t
Proof
  strip_tac >>
  drule vv_store_bound_capacity >> simp[expr_type_def] >> disch_then irule >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  simp[type_memory_size_def] >>
  fs[type_memory_bytes_def, vfmConstantsTheory.word_size_def, type_slot_size_def] >>
  Cases_on `n = 0` >- simp[wordsTheory.dimword_def] >>
  mp_tac (Q.INST [`n` |-> `n`] word_size_le) >>
  fs[vfmConstantsTheory.word_size_def] >> decide_tac
QED
