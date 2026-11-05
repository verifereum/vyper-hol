(* A bounded test of the exported expression-post interface, not of execution. *)
Theory assignBasePtrSourceBound
Ancestors bodyPtrDefs loweringPosts exprLoweringProps compileEnv exprLowering
  valueEncoding venomState ptrDiscipline words finite_map vyperTyping vyperValue valueEncodingProofs exprSimProps vyperAST vyperState

(* Identity framing isolates the substantive placement and state relation
   obligations; no execution claim is made here. *)
Theorem assign_base_ptr_identity_post:
  !ctx func cenv cx e es sa sb s v op.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_rel cx (expr_type e) v op s /\
    expr_val_at cenv cx (expr_type e) sa sb es v op s ==>
    expr_post ctx func cenv cx e es sa sb s es v op s
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem assign_base_ptr_empty_bytes_placement:
  !cenv cx es sa sb s.
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    FLOOKUP s.vs_allocas 0 = SOME (dimword(:256)-64,32) /\
    sa.cs_next_id = 0 /\ sb.cs_next_id = 1 /\
    (!n b sz. ~local_region cenv es.scopes s n b sz) ==>
    expr_val_at cenv cx (BaseT (BytesT (Dynamic 64))) sa sb es
      (BytesV []) (Var "p") s
Proof
  rpt strip_tac >>
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       val_wf_def, val_footprint_def, eval_operand_def] >>
  EVAL_TAC
QED

Theorem assign_base_ptr_clean_memory_word:
  !mem mem' a.
    mem_agree_outside {} mem mem' ==>
    mem_word_at a mem' = mem_word_at a mem
Proof
  rpt strip_tac >> fs[mem_agree_outside_def] >>
  `mem_bytes_at a 32 mem' = mem_bytes_at a 32 mem` by
    (irule listTheory.LIST_EQ >> simp[EL_mem_bytes_at] >>
     rpt strip_tac >>
     first_x_assum (qspec_then `a + x` mp_tac) >>
     disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
     simp[EL_mem_bytes_at]) >>
  gvs[mem_word_at_def, mem_bytes_at_def]
QED

Theorem assign_base_ptr_empty_bytes_value:
  !cx s G.
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    mem_word_at (dimword(:256)-64) s.vs_memory = 0w /\
    FLOOKUP G "p" = SOME (dimword(:256)-64,96) ==>
    ptr_val_ok cx (BaseT (BytesT (Dynamic 64))) (BytesV [])
      (Var "p") G entry_taint s
Proof
  rpt strip_tac >>
  simp[ptr_val_ok_def, ptr_mem_ok_def, op_taint_def, entry_taint_def,
       evaluate_type_def, eval_operand_def, val_footprint_def,
       val_store_size_def, w2n_n2w, dimword_def] >>
  rpt strip_tac
  >- (drule assign_base_ptr_clean_memory_word >>
      disch_then (qspec_then `dimword(:256)-64` mp_tac) >>
      simp[val_in_memory_def, mem_bytes_at_def, dimword_def]) >>
  EVAL_TAC
QED

(* Conditional diagnostic only: the existence of this entire state relation
   at the indicated address remains to be checked. *)
Theorem assign_base_ptr_source_bound_conditional:
  !ctx func cenv cx es s.
    stmt_state_rel ctx func cenv cx es s /\
    lookup_var "p" s = SOME (n2w (dimword(:256)-64)) /\
    mem_word_at (dimword(:256)-64) s.vs_memory = 0w /\
    FLOOKUP s.vs_allocas 0 = SOME (dimword(:256)-64,32) /\
    (!n b sz. ~local_region cenv es.scopes s n b sz) ==>
    ?e sa sb G tn v op w off tv.
      expr_post ctx func cenv cx e es sa sb s es v op s /\
      ptr_val_ok cx (expr_type e) v op G tn s /\
      ptr_buf_ok cenv e op G s /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
      ~is_word_type (expr_type e) /\ eval_operand op s = SOME w /\
      off < type_memory_bytes cenv (lowered_value_type cenv e) /\
      ~(w2n w + off < dimword(:256))
Proof
  rpt strip_tac >>
  qexistsl [`Name (BaseT (BytesT (Dynamic 64))) "x"`,
            `ARB with cs_next_id := 0`, `ARB with cs_next_id := 1`,
            `FEMPTY |+ ("p",(dimword(:256)-64,96))`, `entry_taint`,
            `BytesV []`, `Var "p"`, `n2w (dimword(:256)-64)`, `64`,
            `BaseTV (BytesT (Dynamic 64))`] >>
  conj_tac
  >- (irule assign_base_ptr_identity_post >> simp[expr_type_def] >>
      conj_tac >- gvs[expr_val_rel_def, eval_operand_def, evaluate_type_def,
                       is_word_type_def, val_in_memory_def, mem_bytes_at_def,
                       w2n_n2w, dimword_def] >>
      irule assign_base_ptr_empty_bytes_placement >> simp[]) >>
  conj_tac
  >- (simp[expr_type_def] >> irule assign_base_ptr_empty_bytes_value >> simp[FLOOKUP_UPDATE]) >>
  simp[ptr_buf_ok_def, eval_operand_def, expr_type_def, evaluate_type_def,
       is_word_type_def, lowered_value_type_def, type_memory_bytes_def,
       type_memory_size_def, w2n_n2w, dimword_def, FLOOKUP_UPDATE] >> EVAL_TAC
QED

