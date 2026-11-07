(* Actual compiler interval and frames for the post-ADD memory word unwrap. *)
Theory bodyPtrStructLitMemoryIntegration
Ancestors bodyPtrStructLitUnwrapSeparation bodyPtrStructLitUnwrapFrame
  bodyPtrStructLitAddContinuation bodyPtrStructLitMemoryCaller
  bodyPtrStructLitMemoryUnwrap bodyPtrStructLitRawChild
  exprLoweringProps exprLowering exprSimAggregateLayout emitHelperProps
  freshWrites context compileEnv fragExec

Theorem structlit_first_unwrap_suffix:
  compile_struct_lit compile_expr ce ty ((fname,e)::rest) buf off sb = (r,sd) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf; Lit (n2w off)] sc = (dst,sm) /\
  unwrap_value ce vv sm = (v,su) ==>
  cs_extends su sd
Proof
  simp[Once compile_struct_lit_def, LET_THM, comp_bind_def] >> strip_tac >>
  `ci_mono su (SND
    (comp_ignore_bind
      (compile_store_memory ce v dst
        (case ALOOKUP (get_struct_fields ce.ce_struct_fields
          (case ty of StructT n => nsid_to_string n | _ => "")) fname of
           SOME (fty,sz) => fty | NONE => expr_type e)
        (lowered_value_type ce e))
      (compile_struct_lit compile_expr ce ty rest buf
        (off + (case ALOOKUP (get_struct_fields ce.ce_struct_fields
          (case ty of StructT n => nsid_to_string n | _ => "")) fname of
           SOME (fty,sz) => sz | NONE => 32))) su))` by
    (ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
     >- simp[ci_mono_compile_store_memory] >>
     gen_tac >> irule ci_mono_compile_struct_lit_cfn >>
     simp[cj 1 compile_expr_ci_mono]) >>
  gvs[comp_ignore_bind_def, comp_bind_def, ci_mono_def]
QED

Theorem structlit_first_unwrap_code:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  unwrap_value ce vv sm = (v,su) /\ fn_has_code sa sd fn ==>
  fn_has_code sm su fn
Proof
  strip_tac >> drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [root.buf_operand; Lit 0w] sc = (dst,sm)` >>
  `cs_extends su sd` by (irule structlit_first_unwrap_suffix >> metis_tac[]) >>
  `cs_extends sm su` by
    (qspecl_then [`ce`, `vv`, `sm`] mp_tac ci_mono_unwrap_value >>
     simp[ci_mono_def]) >>
  `cs_extends sc sm` by
    (qspecl_then [`ADD`, `[root.buf_operand; Lit (n2w 0)]`, `sc`]
       mp_tac ci_mono_emit_op >> simp[ci_mono_def]) >>
  `cs_extends sb sc` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sa sb` by
    (qspecl_then [`SUM (MAP (SND o SND)
       (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))`, `sa`]
       mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `cs_extends sa sm /\ cs_extends sm sd` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm sd fn` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED


Theorem structlit_first_memory_word_continuation:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  fn_has_code sa sd fn /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  q.ptr_location = LocMemory /\ is_word_type cty /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)) /\
  vv_post ctx fn ce cx e es sb sm t ee tv (LocatedValue cty q) s /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue cty q) ee G tn s /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  buf.buf_operand = Var root /\ not_fresh_at sb root /\
  ptr_covers G tn root s N /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn ce cx e es sb su t ee v (Var load) s1 /\
    ptr_val_ok cx cty v (Var load) G1 tn1 s1 /\
    ghost_inv d ce cx ee G1 tn1 s1 /\
    ghost_kept ce es sb G0 tn0 t G1 tn1 /\
    s1.vs_current_bb = su.cs_current_bb /\
    s1.vs_inst_idx = LENGTH su.cs_current_insts /\
    ptr_covers G1 tn1 root s1 N /\
    (!r sz. r <> load /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz) /\
    (?r. dst = Var r /\ r <> load)
Proof
  strip_tac >> drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `fn_has_code sm su fn` by (irule structlit_first_unwrap_code >> metis_tac[]) >>
  drule_all memory_word_unwrap_code >> strip_tac >>
  `?r. dst = Var r /\ r <> load` by
    (irule emitted_operand_fresh_separation >> metis_tac[]) >>
  drule_all raw_child_unwrap_compiler_frame >> strip_tac >>
  `cty = expr_type e` by
    (drule_all bodyPtrStructLitMemoryReadTheory.vv_post_memory_word_read >> simp[]) >>
  `ptr_vv_ok cx cty tv (LocatedValue cty q) ee G tn s` by metis_tac[] >>
  `!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> load` by
      metis_tac[] >>
  `root <> load` by metis_tac[] >>
  `not_local_ptr ce ee.scopes load` by simp[] >>
  gvs[] >> drule memory_word_unwrap_ptr_continuation >> simp[] >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`v`, `G1`, `tn1`, `s1`] >> simp[]
QED
