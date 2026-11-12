(* A ternary at the joint judgments: the condition's value, the jump to the
   selected arm's block, the arm's value moved into the result variable.
   The shared joint unwrap_value lemma is a premise of the arm steps until
   it lands; the shadow side's compile spine likewise.
 *
 * TOP-LEVEL: body_ifexp_case_full is bodyFullCases' IfExp case.
 *)
Theory bodyFullIfExp
Ancestors
  logArgsRunPtr fragGasOrigin fragGasMode fragGasPath
  bodyPtrIfExpWordPrefix freshWrites bodyMemoryDefs
  bodyFullIfExpWiden bodyFullIfExpFinish bodyFullIfExpShadow
  bodyFullIfExpWidenCall typedCopyDomain vyperTypeSystem bodyFullPreds bodySimFull gasOutcomeFullPath
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginJump fragGasOriginPtr
  exprOperandVar exprLoweringProps bodyPtrIfExpConditionalSource
  bodyPtrIfExpConditionSource stmtSimForRounds gasContext gasExemptCert
  exprSimIfExp exprSimOperators exprSimSource exprSimHyps exprSimDefs
  exprSimMemDefs bodyPtrDefs loweringPosts exprLowering fragExec emitHelper
  compileEnv context vyperEvalExprPreservesScopesDom vyperAST
  vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

(* The arm step: the arm's value at z becomes op, by its unwrap (same
   layout) or a widening copy into a buffer of the result type. *)
(* A bytestring type fitting an evaluable one evaluates: its bound is no
   larger. *)
Theorem bytestring_bound_evaluate[local]:
  n <= m /\ word_size m + 1 <= dimword(:256) ==>
  word_size n + 1 <= dimword(:256)
Proof
  strip_tac >>
  `word_size n <= word_size m` by
    (simp[vfmConstantsTheory.word_size_def] >>
     irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  simp[]
QED

Theorem bytestring_fits_evaluate_type:
  is_bytestring_type lt /\ arg_type_fits lt t /\
  evaluate_type tenv t = SOME rt ==> ?rtl. evaluate_type tenv lt = SOME rtl
Proof
  strip_tac >>
  `(?n. lt = BaseT (BytesT (Dynamic n))) \/ (?n. lt = BaseT (StringT n))` by
    (qpat_x_assum `is_bytestring_type _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `lt` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]) >>
  gvs[] >>
  qpat_x_assum `arg_type_fits _ _` mp_tac >>
  qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `t` >> simp[vyperTypeSystemTheory.arg_type_fits_def] >>
  Cases_on `b` >> simp[vyperTypeSystemTheory.arg_type_fits_def] >>
  TRY (qmatch_goalsub_rename_tac `evaluate_type _ (BaseT (BytesT bd'))` >>
       Cases_on `bd'` >> simp[vyperTypeSystemTheory.arg_type_fits_def]) >>
  simp[vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[bytestring_bound_evaluate, arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

(* expr_post sees its expression only through its two types. *)
Theorem expr_post_same_types[local]:
  post_value_type cenv e = post_value_type cenv e0 /\
  expr_type e = expr_type e0 /\
  expr_post ctx func cenv cx e es sa sb s0 es' v op s ==>
  expr_post ctx func cenv cx e0 es sa sb s0 es' v op s
Proof
  simp[expr_post_def] >> strip_tac >> gvs[]
QED

(* The shared unwrap lemma's statement at post_value_type implies its
   earlier one at expr_type, which the different-layout leaf takes. *)
Theorem unwrap_r6_of_r7[local]:
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
       compile_expr cenv ty e sa = (vv,sm) /\
       sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
       unwrap_value cenv vv sb = (op,sc) /\
       local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
       fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
       ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
       (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
       (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       ~is_word_type (post_value_type cenv e) ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
       type_memory_size rt < 2**64) /\
       evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
       (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
       vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
       vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
       ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv_at D lo d cenv cx ee G tn s /\
       ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
       (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
       ptr_buf_ok cenv e op0 G s) /\
       (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand G s) /\
       (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val, ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       eval_operand (vv_operand vv) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory rt val (w2n w) mem)) /\
       ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
       (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
       ?v H tf z.
       read_result cx tv ee = (INL v, ee) /\
       gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (OK z, H, tf) /\
       expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
       expr_store_bound cx (post_value_type cenv e) v op z /\
       z.vs_current_bb = sc.cs_current_bb /\
       z.vs_inst_idx = LENGTH sc.cs_current_insts /\
       alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at D lo d cenv cx ee H tf z /\
       ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
       (~is_word_type (post_value_type cenv e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand op z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
       ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
       (!x. not_fresh_at sb x ==>
            lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
            op_taint tf (Var x) = op_taint tn (Var x)) /\
       wb_frame cenv ee sb s z /\
       ghost_kept_at lo cenv ee sb G tn s H tf) ==>
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
     post_value_type cenv e = expr_type e /\
     compile_expr cenv ty e sa = (vv,sm) /\
     sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
     unwrap_value cenv vv sb = (op,sc) /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
     MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
     ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
     (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
     (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
     ~is_word_type (expr_type e) ==>
     type_memory_bytes cenv (expr_type e) = type_memory_size rt /\
     type_memory_size rt < 2**64) /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
     (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
     vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
     vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
     alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
     ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv_at D lo d cenv cx ee G tn s /\
     ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
     (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G s) /\
     (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
     (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) s = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt val (w2n w) mem)) /\
     ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
     ?v H tf z.
     read_result cx tv ee = (INL v, ee) /\
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK z, H, tf) /\
     expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
     expr_store_bound cx (expr_type e) v op z /\
     z.vs_current_bb = sc.cs_current_bb /\
     z.vs_inst_idx = LENGTH sc.cs_current_insts /\
     alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
     s0.vs_alloca_next <= z.vs_alloca_next /\
     ghost_inv_at D lo d cenv cx ee H tf z /\
     ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
     (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
     eval_operand op z = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
     ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
     (!x. not_fresh_at sb x ==>
          lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x)) /\
     wb_frame cenv ee sb s z /\
     ghost_kept_at lo cenv ee sb G tn s H tf)
Proof
  rpt strip_tac >>
  qpat_x_assum `post_value_type _ _ = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  qpat_x_assum `!e ty sa. _` drule_all >> asm_rewrite_tac[]
QED

Theorem ifexp_arm_step_full:
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
     compile_expr cenv ty e sa = (vv,sm) /\
     sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
     unwrap_value cenv vv sb = (op,sc) /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
     MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
     ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
     (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
     (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     ~is_word_type (post_value_type cenv e) ==>
     type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
     type_memory_size rt < 2**64) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
     (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
     vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
     vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
     alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
     ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv_at D lo d cenv cx ee G tn s /\
     ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
     (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G s) /\
     (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
     (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) s = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt val (w2n w) mem)) /\
     ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
     ?v H tf z.
     read_result cx tv ee = (INL v, ee) /\
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK z, H, tf) /\
     expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
     expr_store_bound cx (post_value_type cenv e) v op z /\
     z.vs_current_bb = sc.cs_current_bb /\
     z.vs_inst_idx = LENGTH sc.cs_current_insts /\
     alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
     s0.vs_alloca_next <= z.vs_alloca_next /\
     ghost_inv_at D lo d cenv cx ee H tf z /\
     ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
     (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
     eval_operand op z = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
     ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
     (!x. not_fresh_at sb x ==>
          lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x)) /\
     wb_frame cenv ee sb s z /\
     ghost_kept_at lo cenv ee sb G tn s H tf) /\
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_type e = t /\ expr_type e0 = t /\ post_value_type cenv e0 = t /\
  (post_value_type cenv e = t /\
   (~is_word_type t ==>
    lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
    same_memory_layout cenv (lowered_value_type cenv e) (expr_type e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e) /\
    (?tvp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvp)) \/
   ~is_word_type t /\ post_value_type cenv e = lowered_value_type cenv e /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==> value_has_type rty v) /\
  (!v ptv. read_result cx tva ee = (INL v,ee) /\
          evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) /\
  (?ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  vv_post ctx func cenv cx e es1 sa sm u ee tva vv z /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee G tn z /\
  ptr_vv_ok cx (post_value_type cenv e) tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' H tf.
    read_result cx tva ee = (INL v,ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (z, G, tn) [] (OK z', H, tf) /\
    expr_post ctx func cenv cx e0 es1 sa sb u ee v op z' /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z' /\
    ptr_val_ok cx t v op H tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op H z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u H tf
Proof
  strip_tac >>
  qpat_x_assum `_ \/ _ /\ _ /\ type_widens_to _ _ _ /\ _` strip_assume_tac
  >~ [`type_widens_to _ _ _`]
  >- (drule_all ifexp_widened_call_arm_step_full >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `post_value_type cenv e = t`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  Cases_on `~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t`
  >- (pop_assum strip_assume_tac >>
      qpat_assum `!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti. _`
        (assume_tac o MATCH_MP unwrap_r6_of_r7) >>
      drule_all ifexp_widen_arm_step_full >> strip_tac >>
      qexistsl_tac [`v`,`z'`,`H`,`tf`] >> simp[] >>
      irule expr_post_same_types >> qexists_tac `e` >> simp[]) >>
  qpat_x_assum `~(~_ /\ ~_)` (assume_tac o SIMP_RULE bool_ss [DE_MORGAN_THM]) >>
  `unwrap_value cenv vv sm = (op,sb)` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     simp[compile_ifexp_arm_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  first_x_assum (qspecl_then [`e`,`ty`,`sa`,`vv`,`sm`,`sm`,`op`,`sb`,`es1`,`ee`,
    `u`,`z`,`tva`,`rty`,`G`,`tn`,`G1`,`tn1`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >>
  strip_tac >>
  `expr_post ctx func cenv cx e0 es1 sa sb u ee v op z'` by
    (irule expr_post_same_types >> qexists_tac `e` >> simp[]) >>
  qexistsl_tac [`v`,`z'`,`H`,`tf`] >> gvs[] >>
  suspend "conv"
QED

Resume ifexp_arm_step_full[conv]:
  conj_tac
  >- (rpt strip_tac >> fs[same_memory_layout_def, ptr_buf_ok_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  `?rtl. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rtl` by
    (Cases_on `is_bytestring_type (lowered_value_type cenv e)` >> gvs[] >>
     metis_tac[bytestring_fits_evaluate_type]) >>
  `type_memory_size rty = type_memory_size rtl` by
    (fs[same_memory_layout_def] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise ifexp_arm_step_full

(* The selected arm with its result conversion, from the arm's own
   judgment: the source runs the arm and conditional_result, the target the
   arm's code and its compile_ifexp_arm code. *)
Theorem ifexp_arm_outcome_full:
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
     compile_expr cenv ty e sa = (vv,sm) /\
     sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
     unwrap_value cenv vv sb = (op,sc) /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
     MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
     fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
     ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
     (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
     (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     ~is_word_type (post_value_type cenv e) ==>
     type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
     type_memory_size rt < 2**64) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
     (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
     vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
     vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
     alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
     ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
     s.vs_inst_idx = LENGTH sb.cs_current_insts /\
     ghost_inv_at D lo d cenv cx ee G tn s /\
     ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
     (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G s) /\
     (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G s) /\
     (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val, ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     eval_operand (vv_operand vv) s = SOME w ==>
     w2n w + type_memory_size rt <= lo /\
     (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory rt val (w2n w) mem)) /\
     ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
     (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
     ?v H tf z.
     read_result cx tv ee = (INL v, ee) /\
     gas_origin_ptr_path (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
     (s, G, tn) [] (OK z, H, tf) /\
     expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
     expr_store_bound cx (post_value_type cenv e) v op z /\
     z.vs_current_bb = sc.cs_current_bb /\
     z.vs_inst_idx = LENGTH sc.cs_current_insts /\
     alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
     s0.vs_alloca_next <= z.vs_alloca_next /\
     ghost_inv_at D lo d cenv cx ee H tf z /\
     ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
     (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
     eval_operand op z = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
     ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
     (!x. not_fresh_at sb x ==>
          lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x)) /\
     wb_frame cenv ee sb s z /\
     ghost_kept_at lo cenv ee sb G tn s H tf) /\
  expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es1 /\
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_expr cenv ty (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx))
    expr_vv_res_ok es1 /\
  return_buf_frame d cenv sa u /\ stmt_state_rel ctx func cenv cx es1 u /\
  alloca_history func u /\ ghost_inv_at D lo d cenv cx es1 G1 tn1 u /\
  ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_type e = t /\ expr_type e0 = t /\ post_value_type cenv e0 = t /\
  (post_value_type cenv e = t /\
   (~is_word_type t ==>
    lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
    same_memory_layout cenv (lowered_value_type cenv e) (expr_type e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e) /\
    (?tvp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvp)) \/
   ~is_word_type t /\ post_value_type cenv e = lowered_value_type cenv e /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!gs v es2. bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs) =
     (INL v,es2) ==> value_has_type rty v) /\
  (!gs v es2 ptv.
     bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs) =
       (INL v,es2) /\
     evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
     value_has_type ptv v) ==>
  gas_outcome_full (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
    (cx_tops cx) (bind (eval_expr cx e) (conditional_result cx))
    (es1, u, G1, tn1)
    (\res ee G tn z. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
       MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
       expr_post ctx func cenv cx e0 es1 sa sb u ee v op z /\
       expr_store_bound cx t v op z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
       alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at D lo d cenv cx ee G tn z /\
       ptr_val_ok cx t v op G tn z /\
       (~is_word_type t ==>
        !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op G z) /\
       (~is_word_type t ==>
        !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
               eval_operand op z = SOME w ==>
               type_memory_size rt = 0 \/
               w2n w + type_memory_size rt <= z.vs_alloca_next) /\
       ghost_kept_at lo cenv es1 sa G1 tn1 u G tn)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es1` by
    (rw[gas_admissible_def] >>
     qpat_x_assum `gas_admissible (bind _ _) _ _`
       (qspec_then `gs` mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     Cases_on `res` >> simp[bind_def, expr_vv_res_ok_def] >>
     rename1 `INL rv0` >> Cases_on `rv0` >>
     simp[conditional_result_def, raise_def, expr_vv_res_ok_def]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`u`,`G1`,`tn1`]
    mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  match_mp_tac gas_outcome_full_bind >> conj_tac
  >- (drule_then match_mp_tac gas_outcome_full_post_source >> conj_tac
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          qpat_x_assum `_ = INL _` SUBST_ALL_TAC >> suspend "arm") >>
      rpt gen_tac >> Cases_on `res` >> simp[] >>
      metis_tac[expr_exit_INR_type]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> drule gas_exempt_cert_bind_result >> simp[] >>
  disch_then irule >> simp[]
QED

Resume ifexp_arm_outcome_full[arm]:
  qmatch_goalsub_rename_tac `gas_outcome_full _ _ _ (ee, z, Gz, tnz) _ _` >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es1 with gas_obs := xs) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[]) >>
  `MAP FDOM es1.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt strip_tac >>
     qpat_x_assum `!gs v es2. _ ==> value_has_type rty v` irule >>
     qexistsl_tac [`ee`,`xs`] >> simp[bind_def]) >>
  `!v ptv. read_result cx tv ee = (INL v,ee) /\
           evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
           value_has_type ptv v` by
    (rpt strip_tac >>
     qpat_x_assum `!gs v es2 ptv. _` irule >>
     qexistsl_tac [`ee`,`xs`] >> simp[bind_def]) >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv` by
    (qpat_assum `_ \/ _ /\ _ /\ type_widens_to _ _ _ /\ _` strip_assume_tac >>
     metis_tac[]) >>
  `vv_store_bound cx t (lowered_value_type cenv e) ee tv vv z` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >> simp[]) >>
  qpat_assum `compile_expr cenv ty e sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  (* TEMPORARY until expr_vv_sim_full's post carries the constructor LocCode
     clause (manager branch). *)
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)` by cheat >>
  drule_all ifexp_arm_step_full >> strip_tac >>
  `gas_admissible (conditional_result cx tv) expr_vv_res_ok (ee with gas_obs := [])` by
    (irule gas_admissible_bind_tail >> metis_tac[]) >>
  `?res0 ss. conditional_result cx tv ee = (res0,ss)` by metis_tac[pairTheory.PAIR] >>
  `expr_vv_res_ok res0` by metis_tac[gas_admissible_result] >>
  drule_all ifexp_conditional_source_success >> strip_tac >>
  rename1 `conditional_result cx tv (_ with gas_obs := _) = (INL tc,_)` >>
  `~z'.vs_halted` by
    metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
              gas_marked_path_exec, gas_path_normal] >>
  qexists_tac `tv` >> simp[] >> irule gas_outcome_full_pure >>
  first_assum (irule_at Any) >>
  qexistsl_tac [`INL tc`,`ee`] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  BETA_TAC >> simp[]
QED

Finalise ifexp_arm_outcome_full

(* The JNZ on the condition's operand, as a joint path into the selected
   arm's block. *)
Theorem ifexp_root_jnz_origin_path[local]:
  expr_post ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  allocas_from lo u /\ op_taint tn cop = {} ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (u, G, tn) [] (OK (jump_to (if sel then tl else el) u), G, tn)
Proof
  strip_tac >>
  irule (Q.INST [`sa` |-> `sj`, `sb` |-> `sn`, `op` |-> `cop`]
           emit_jnz_origin_ptr_path) >>
  drule emit_inst_extends >> strip_tac >> simp[] >>
  fs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
     valueEncodingTheory.typed_val_to_w256_def,
     valueEncodingTheory.val_to_w256_def]
QED

(* The ghost invariant ignores the control position. *)
Theorem ghost_inv_at_jump_to:
  ghost_inv_at D lo d cenv cx es G tn (jump_to lbl s) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       allocas_from_def, lookup_var_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED


(* The ternary's root from the condition's value judgment and the arms'
   vv judgments: the condition, the JNZ into the selected arm's block, the
   arm with its conversion, the ASSIGN and the JMP. *)
Theorem ifexp_vv_full_root:
  (!e ty sa vv sm sb op sc es ee s0 s tv rty G tn Gi ti.
       compile_expr cenv ty e sa = (vv,sm) /\
       sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
       unwrap_value cenv vv sb = (op,sc) /\
       local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes /\
       sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
       fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
       ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
       (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
       (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       ~is_word_type (post_value_type cenv e) ==>
       type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
       type_memory_size rt < 2**64) /\
       evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
       (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
       vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
       vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
       ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv_at D lo d cenv cx ee G tn s /\
       ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
       (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
       ptr_buf_ok cenv e op0 G s) /\
       (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand G s) /\
       (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val, ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
       eval_operand (vv_operand vv) s = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory rt val (w2n w) mem)) /\
       ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
       (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
       ?v H tf z.
       read_result cx tv ee = (INL v, ee) /\
       gas_origin_ptr_path (D, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       (s, G, tn) [] (OK z, H, tf) /\
       expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
       expr_store_bound cx (post_value_type cenv e) v op z /\
       z.vs_current_bb = sc.cs_current_bb /\
       z.vs_inst_idx = LENGTH sc.cs_current_insts /\
       alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at D lo d cenv cx ee H tf z /\
       ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
       (~is_word_type (post_value_type cenv e) ==>
       !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
       eval_operand op z = SOME w ==>
       type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
       ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
       (!x. not_fresh_at sb x ==>
            lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
            op_taint tf (Var x) = op_taint tn (Var x)) /\
       wb_frame cenv ee sb s z /\
       ghost_kept_at lo cenv ee sb G tn s H tf) /\
  (!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
             (compile_expr cenv ty' (gas_shadow_expr e))) /\
  (!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
             (lower_value compile_expr cenv ty' (gas_shadow_expr e))) /\
  (!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
                (compile_ifexp_arm cenv rt at av)) /\
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e. (e = a \/ e = b) ==>
       post_value_type cenv e = t /\
       (~is_word_type t ==>
        lowered_value_type cenv e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type cenv e) /\
        arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
        same_memory_layout cenv (lowered_value_type cenv e) (expr_type e) /\
        arg_type_fits (lowered_value_type cenv e) (expr_type e) /\
        (?tvp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvp)) \/
       ~is_word_type t /\ post_value_type cenv e = lowered_value_type cenv e /\
       type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
       (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  expr_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty b es1 /\
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') ==>
  expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_def] >> rpt strip_tac >>
  drule_all ifexp_shadow_code_layout >> disch_then (assume_tac o GEN_ALL) >>
  `?cop sc shadow_sc.
     lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
     lower_value compile_expr cenv (BaseT BoolT) (gas_shadow_expr c)
       shadow_sa = (cop,shadow_sc) /\
     gas_shadow_state sc shadow_sc /\ fn_has_code sa sc func /\
     fn_has_code shadow_sa shadow_sc shadow_func` by
    (qpat_assum `!sel. ?cop. _` (qspec_then `T` strip_assume_tac) >>
     qexistsl_tac [`cop`,`sc`,`shadow_sc`] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    metis_tac[ifexp_condition_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ c _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then
    [`sa`,`sc`,`shadow_sa`,`shadow_sc`,`cop`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rewrite_tac[ifexp_eval_forced] >>
  match_mp_tac gas_outcome_full_bind >> conj_tac
  >- (drule_then match_mp_tac gas_outcome_full_post_source >> conj_tac
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          qpat_x_assum `_ = INL _` SUBST_ALL_TAC >> suspend "selected") >>
      rpt gen_tac >> Cases_on `res` >> simp[] >>
      metis_tac[expr_exit_INR_type]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >> drule gas_exempt_cert_bind_value >> simp[] >>
  disch_then irule >> simp[]
QED

Resume ifexp_vv_full_root[selected]:
  qmatch_goalsub_rename_tac `gas_outcome_full _ _ _ (mid, u0, Gc, tnc) _ _` >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx c) (read_result cx) (es with gas_obs := xs) =
     (INL v,mid)` by
    (first_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all ifexp_condition_bool >>
  disch_then (qx_choose_then `sel` SUBST_ALL_TAC) >>
  qexists_tac `BoolV sel` >> conj_tac >- simp[] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ STT QQ RR` >>
  `gas_outcome_full (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx)
     (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     STT QQ RR` suffices_by (Cases_on `sel` >> simp[]) >>
  qunabbrev_tac `STT` >>
  `gas_admissible
     (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     expr_vv_res_ok mid` by
    (drule_all ifexp_branch_admissible >> simp[]) >>
  qpat_x_assum `!gs v es1. _ ==> expr_vv_sim_full _ _ _ _ a _ /\ _`
    (qspecl_then [`xs`,`BoolV sel`,`mid`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `!sel. ?cop. _` (qspec_then `sel` mp_tac) >> simp[] >> strip_tac >>
  `allocas_from lo u0` by fs[ghost_inv_at_def] >>
  `op_taint tnc cop = {}` by fs[ptr_val_ok_def] >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (u0,Gc,tnc) [] (OK (jump_to (if sel then tl else el) u0),Gc,tnc)` by
    (drule_all ifexp_root_jnz_origin_path >> simp[]) >>
  qpat_x_assum `gas_origin_ptr_path _ _ [] _`
    (mp_then (Pos hd) irule gas_outcome_full_zero_prefix) >>
  suspend "arm"
QED

Resume ifexp_vv_full_root[arm]:
  unabbrev_all_tac >>
  `expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (if sel then a else b) mid` by
    (Cases_on `sel` >> fs[]) >>
  `!gs' v' es2.
     bind (eval_expr cx (if sel then a else b)) (read_result cx)
       (mid with gas_obs := gs') = (INL v',es2) ==> value_has_type rty v'` by
    (rpt strip_tac >> Cases_on `sel` >> fs[] >> metis_tac[]) >>
  `!gs' v' es2 ptv.
     bind (eval_expr cx (if sel then a else b)) (read_result cx)
       (mid with gas_obs := gs') = (INL v',es2) /\
     evaluate_type (get_tenv cx) (post_value_type cenv (if sel then a else b)) =
       SOME ptv ==>
     value_has_type ptv v'` by
    (rpt strip_tac >> Cases_on `sel` >> fs[] >> metis_tac[]) >>
  qpat_x_assum `!e. (e = a \/ e = b) ==> _`
    (qspec_then `if sel then a else b` mp_tac) >>
  impl_tac >- (Cases_on `sel` >> simp[]) >> disch_then assume_tac >>
  `expr_type (if sel then a else b) = t` by (Cases_on `sel` >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `bind _ _ (es with gas_obs := xs) = _` mp_tac >>
     simp[bind_def] >>
     Cases_on `eval_expr cx c (es with gas_obs := xs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >> strip_tac >>
     drule read_result_state >> strip_tac >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `stmt_state_rel ctx func cenv cx mid (jump_to (if sel then tl else el) u0)` by
    (simp[stmt_state_rel_jump_to] >> fs[expr_post_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     simp[] >> metis_tac[]) >>
  `alloca_history func (jump_to (if sel then tl else el) u0)` by
    (irule alloca_history_jump >> simp[jump_to_def] >>
     qexists_tac `u0` >> simp[]) >>
  qspecl_then [`if sel then a else b`, `mid`, `se`, `sea`, `shadow_se`,
               `shadow_sea`, `av`, `aop`, `sx`,
               `jump_to (if sel then tl else el) u0`, `Gc`, `tnc`, `IfExp t c a b`]
    mp_tac (Q.GENL [`e`,`es1`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`op`,`sb`,
                    `u`,`G1`,`tn1`,`e0`] ifexp_arm_outcome_full) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      simp[return_buf_frame_jump_to, ghost_inv_at_jump_to] >>
      simp[jump_to_def] >> fs[expr_post_def] >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ (mid,_,_,_) _ _`
    (mp_then (Pos hd) irule gas_outcome_full_zero_suffix) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_rename_tac `expr_post _ _ _ _ (IfExp t c a b) mid se sx
    _ ee varm aop za` >>
  qpat_x_assum `ghost_kept_at _ _ mid se _ _ _ _ _` mp_tac >>
  qmatch_goalsub_rename_tac `ghost_kept_at _ _ _ _ _ _ _ Ga tna` >> strip_tac >>
  qspecl_then [`sc`, `mid`, `BoolV sel`, `u0`, `Gc`, `tnc`,
               `if sel then tl else el`, `IfExp t c a b`, `se`, `sx`,
               `ee`, `tv`, `varm`, `aop`, `za`, `Ga`, `tna`,
               `gas_explicit_sites ctx shadow_ctx`]
    mp_tac (Q.GENL [`s1`,`es1`,`v1`,`tt`,`G1`,`tn1`,`lbl`,`e`,`sc`,`sd`,`ee`,
                    `tv`,`v`,`op`,`u`,`G`,`tn`,`explicit`] ifexp_arm_finish_full) >>
  impl_tac
  >- (simp[jump_to_def] >> fs[expr_post_def] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`z`,`H`,`tf`] >> simp[] >>
  Cases_on `is_word_type t` >> gvs[contextTheory.mk_ptr_def]
QED

Finalise ifexp_vv_full_root
