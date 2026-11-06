(* Capacity transport for a selected if-expression arm. *)
Theory bodyIfExpSelectedMemory
Ancestors
  exprSimMemDefs exprSimUnwrapProps exprLowering

Theorem ifexp_arm_store_bound:
  vv_store_bound cx t at es raw vv s /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    ?avt. evaluate_type (get_tenv cx) at = SOME avt /\
          type_memory_size tvt <= type_memory_size avt) ==>
  vv_store_bound cx t t es raw vv s
Proof
  rewrite_tac[vv_store_bound_def] >> strip_tac >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  qpat_x_assum `!tvt. _` drule >> strip_tac >>
  `type_memory_size avt = 0 \/
   w2n w + type_memory_size avt <= s.vs_alloca_next` by metis_tac[] >>
  decide_tac
QED

Theorem ifexp_memory_arm_endpoint:
  ~is_word_type t /\ same_memory_layout cenv at t /\
  compile_ifexp_arm cenv t at (LocatedValue t (mk_ptr src LocMemory)) sm = (op,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw
    (LocatedValue t (mk_ptr src LocMemory)) s /\
  read_result cx raw ee = (INL v,ee) /\
  vv_store_bound cx t at ee raw (LocatedValue t (mk_ptr src LocMemory)) s /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    ?avt. evaluate_type (get_tenv cx) at = SOME avt /\
          type_memory_size tvt <= type_memory_size avt) ==>
  sb = sm /\ op = src /\
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  vv_store_bound cx t t ee raw (LocatedValue t (mk_ptr op LocMemory)) s
Proof
  simp[compile_ifexp_arm_def, unwrap_value_def,
       contextTheory.mk_ptr_def, compileEnvTheory.comp_return_def] >>
  strip_tac >> gvs[compileEnvTheory.comp_return_def] >> conj_tac
  >- (drule vv_post_read_result >> disch_then (fs o single) >>
      drule expr_post_of_vv_post_memory >> simp[]) >>
  irule ifexp_arm_store_bound >> metis_tac[]
QED
