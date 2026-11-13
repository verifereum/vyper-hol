(* A ternary at the joint judgments, on finite horizons: the condition's
   value, the JNZ into the selected arm's block, the arm (no copy, a
   bytestring widening copy, or a widened internal call's typed copy), the
   ASSIGN and the JMP.  The value judgment follows from the vv judgment by
   the shared joint unwrap_value lemma (bodyFullUnwrap).

   The helper lemmas the arm steps take as premises are discharged here:
   the generic ALLOCA/bytestring ones from bodyFullAllocGeneric, the joint
   typed copy from typedCopyOriginPtr.

   DRAFT: statements only; the proofs are not written yet.
 *
 * TOP-LEVEL:
 *   expr_sim_full_of_vv -- the value judgment from the vv judgment
 *   ifexp_vv_full_root -- the ternary's vv judgment from its parts
 *   ifexp_expr_full_ok -- bodyFullCases' IfExp case (body_ifexp_case_full)
 *)
Theory bodyFullIfExp
Ancestors
  bodyFullIfExpArm bodyFullIfExpWiden bodyFullIfExpWidenCall
  bodyFullIfExpFinish bodyFullIfExpShadow bodyFullAllocGeneric typedCopyOriginPtr
  bodyFullUnwrap bodyFullPreds
  bodySimFull gasOutcomeFullCompose gasOutcomeFull gasShadowCompile
  gasShadowCompileHelpers exprSimMemorySource exprSimIfExp exprSimDefs
  exprSimMemDefs bodyPtrDefs loweringPosts exprLowering exprLoweringProps
  typedCopyDomain vyperTypeSystem compileEnv context vyperAST
  vyperInterpreter vyperState venomState

val _ = Parse.hide "body";

(* The value judgment from the vv judgment: lower_value is compile_expr
   then unwrap_value, whose code reads no GAS (unwrap_value_origin_ptr). *)
Theorem expr_sim_full_of_vv:
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es ==>
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty e es
Proof
  cheat
QED

(* Uniform selected-arm conversion; the endpoint is shared by all horizons. *)
Theorem ifexp_selected_arm_step_full[local]:
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  (post_value_type cenv e = t /\
   (is_word_type t \/
    same_memory_layout cenv (lowered_value_type cenv e) t /\
    (?rtp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rtp) \/
    ~same_memory_layout cenv (lowered_value_type cenv e) t /\
    is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) t) \/
   ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
   post_value_type cenv e = lowered_value_type cenv e /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==>
     value_has_type rty v /\
     !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
       value_has_type ptv v) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx t (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
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
  ?v z' Gz tf.
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gz tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf
Proof
  strip_tac
  >>~- ([`type_widens_to _ _ _`], (irule ifexp_widened_call_arm_step_full >>
      rpt conj_tac >>
      FIRST_PROVE [MATCH_ACCEPT_TAC (GEN_ALL unwrap_value_origin_ptr),
             MATCH_ACCEPT_TAC (GEN_ALL ifexp_alloca_origin_ptr_edge),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_ghost_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_kept_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_store_memory_typed_origin_ptr_path),
             first_assum MATCH_ACCEPT_TAC,
             (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
              qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
             (qexistsl_tac [`e`,`stv`,`sm`,`stv`,`ty`,`vv`] >>
              simp[] >> rpt strip_tac >> first_x_assum drule >> simp[])] >> gvs[]))
  >>~- ([`is_bytestring_type _`, `~same_memory_layout _ _ _`], (irule ifexp_widen_arm_step_full >> rpt conj_tac >>
      FIRST [MATCH_ACCEPT_TAC (GEN_ALL unwrap_value_origin_ptr),
             MATCH_ACCEPT_TAC (GEN_ALL ifexp_alloca_origin_ptr_edge),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_ghost_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_alloc_buffer_kept_frame_at),
             MATCH_ACCEPT_TAC (GEN_ALL compile_store_bytestring_origin_ptr_path),
             first_assum MATCH_ACCEPT_TAC,
             (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
              qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
             (irule valueCopyBytesTheory.is_bytestring_word_type >> first_assum MATCH_ACCEPT_TAC),
             (qexistsl_tac [`e`,`sm`,`ty`,`vv`] >> gvs[]),
             FAIL_TAC "bytes concrete"] >> gvs[])) >>
  irule ifexp_unwrap_arm_step_full >> rpt conj_tac >>
  FIRST [MATCH_ACCEPT_TAC (GEN_ALL unwrap_value_origin_ptr),
         first_assum MATCH_ACCEPT_TAC,
         (qexists_tac `rty` >> simp[] >> rpt strip_tac >>
          qpat_x_assum `!v. read_result cx tva ee = _ ==> _` drule >> simp[]),
         (qexistsl_tac [`e`,`sm`,`ty`,`vv`] >> simp[]),
         FAIL_TAC "unwrap concrete"] >> simp[] >>
  gvs[]
QED

(* The ternary's root from the condition's value judgment and the arms'
   vv judgments.  Each arm is one of the three arm steps' kinds. *)
Theorem ifexp_vv_full_root:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e. (e = a \/ e = b) ==>
       (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
       (post_value_type cenv e = t /\
        (is_word_type t \/
         same_memory_layout cenv (lowered_value_type cenv e) t /\
         (?rtp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rtp) \/
         ~same_memory_layout cenv (lowered_value_type cenv e) t /\
         is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) t) \/
        ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
        post_value_type cenv e = lowered_value_type cenv e /\
        type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
        (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv))) /\
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
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty b es1 /\
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') ==>
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED

(* bodyFullCases' IfExp case: the side facts the root takes come from
   body_inv and expr_body_pre, the word agreement by the contrapositive of
   post_value_type_nonword. *)
Theorem ifexp_expr_full_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED
