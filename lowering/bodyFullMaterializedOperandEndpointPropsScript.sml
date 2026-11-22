(* Value and allocation facts for a materialized operand after a later suffix. *)
Theory bodyFullMaterializedOperandEndpointProps
Ancestors
  bodyFullOperandSnapshot logValueFramePtr bodyPtrDefs loweringPosts
  exprLoweringProps exprSimProps exprSimMemDefs valueEncodingProofs compileEnv context
  venomState venomMemDefs vyperState finite_map words arithmetic

Theorem materialized_operand_endpoint:
  compile_snapshot_vv cenv T input a = (saved,ss) /\
  vv_type input = lowered_value_type cenv e /\
  ~is_word_type (lowered_value_type cenv e) /\ vv_operand saved = Var x /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  val_wf tv v /\ val_footprint tv v <= sz /\
  ptr_val_ok cx (lowered_value_type cenv e) v (Var x) G1 tn1 t /\
  val_in_memory tv v (w2n w) t.vs_memory /\ ptr_buf_ok cenv e (Var x) G1 t /\
  lookup_var x t = SOME w /\ not_fresh_at cut x /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  si.cs_next_id <= aid /\ aid < ss.cs_next_id /\ aid < cut.cs_next_id /\
  type_memory_size tv <= sz /\
  w2n w + sz <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  (!n b len. local_region cenv mid.scopes t n b len ==>
    w2n w + sz <= b \/ b + len <= w2n w) /\
  (!n b len. local_region cenv ee.scopes u n b len ==>
    local_region cenv mid.scopes t n b len) /\
  wb_frame cenv mid ee cut t u /\ ghost_kept_at lo cenv mid cut G1 tn1 t G2 tn2 ==>
  saved = LocatedValue (lowered_value_type cenv e) (mk_ptr (Var x) LocMemory) /\
  lookup_var x u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
  (!n b len. local_region cenv ee.scopes u n b len ==>
    w2n w + sz <= b \/ b + len <= w2n w) /\
  read_result cx (Value v) ee = (INL v,ee) /\
  vv_holds cenv cx (lowered_value_type cenv e) (Value v) saved ee u /\
  vv_at cenv cx (lowered_value_type cenv e) si ss ee (Value v) saved u /\
  ptr_vv_ok cx (lowered_value_type cenv e) (Value v) saved ee G2 tn2 u /\
  vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e)
    ee (Value v) saved u /\
  ptr_buf_ok cenv e (Var x) G2 u
Proof
  strip_tac >>
  mp_tac (Q.INST [`copy` |-> `T`, `vv` |-> `input`, `p` |-> `x`,
    `sa` |-> `a`, `sm` |-> `ss`, `es` |-> `mid`, `s` |-> `t`,
    `t` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`,
    `G'` |-> `G2`, `tn'` |-> `tn2`] compile_snapshot_vv_materialized_frame) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_assum `!n b len. local_region cenv mid.scopes t n b len ==> _`
        (qspecl_then [`n`,`b`,`len`] (drule_then strip_assume_tac)) >>
      decide_tac) >>
  simp[] >> strip_tac >>
  `val_in_memory tv v (w2n w) u.vs_memory` by
    (irule val_in_memory_footprint_agree >> simp[] >>
     qexists_tac `t.vs_memory` >> simp[] >>
     qpat_assum `mem_bytes_at (w2n w) sz u.vs_memory = _`
       (mp_tac o MATCH_MP (cj 1 mem_bytes_at_agree_window) o SYM) >>
     disch_then (qspecl_then [`w2n w`,`val_footprint tv v`] mp_tac) >> simp[]) >>
  `ptr_buf_ok cenv e (Var x) G2 u` by
    (irule ptr_buf_ok_frame >> qexistsl_tac [`G1`,`t`] >>
     simp[venomStateTheory.eval_operand_def]) >>
  `(!n b len. local_region cenv ee.scopes u n b len ==>
    sz + w2n w <= b \/ b + len <= w2n w)` by
    (rpt strip_tac >>
     qpat_assum `!n b len. local_region cenv ee.scopes u n b len ==> _`
       (drule_then assume_tac) >>
     qpat_assum `!n b len. local_region cenv mid.scopes t n b len ==> _`
       (drule_then strip_assume_tac) >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `saved = _` SUBST_ALL_TAC >>
  simp[vv_holds_def, vv_at_def, ptr_vv_ok_def, vv_store_bound_def,
       mk_ptr_def, read_result_def, return_def, venomStateTheory.eval_operand_def] >>
  rpt conj_tac
  >- (disj1_tac >> qexistsl_tac [`aid`,`w2n w`,`sz`] >> simp[] >>
      rpt strip_tac >>
      qpat_assum `!n b len. local_region cenv ee.scopes u n b len ==> _ \/ _`
        (drule_then strip_assume_tac) >> decide_tac) >>
  gvs[ptr_val_ok_def] >> rpt strip_tac >>
  TRY (drule exprSimPropsTheory.val_store_size_le) >> decide_tac
QED
