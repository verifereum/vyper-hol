Theory bodyPtrPopConsumerCut
Ancestors
  bodyPtrPopTargetFactor bodyPtrDefs loweringPosts venomState
  exprLoweringProps compileEnv

(* The first real continuation cut: r is the captured base target result,
   si is both the end of that target and the start of its effectful index.
   No raw storage-frame claim is hidden in this operand transport theorem. *)
Theorem pop_saved_storage_variable_after_index:
  target_post ctx func cenv cx es sc si s0 es1
    (PlaceR (StoragePlace tr w tv)) vt r s1 /\
  FST r = Var x /\
  expr_post ctx func cenv cx e es1 si sj s1 es2 v op s2 ==>
  eval_operand (Var x) s2 = SOME w /\
  FST (SND r) = SOME (slot_loc tr)
Proof
  strip_tac >>
  gvs[target_post_def, place_ptr_rel_def, expr_post_def, eval_operand_def] >>
  qpat_x_assum `!x w. not_fresh_at si x /\ _ ==> _` irule >> simp[]
QED

Theorem pop_reference_consumer_layout:
  type_slot_size
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2)) = 7 /\
  type_slot_size
    (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
      (Dynamic 2)) (Dynamic 2)) = 15 /\
  (0 + 1 + 1 * 7 : num) = 8 /\ (8 + 1 + 0 * 3 : num) = 9
Proof
  EVAL_TAC
QED

(* Exact normal consumer sequent (schematic, NOT an asserted theorem):

   Symbols: cx:evaluation_context, cenv:compile_env, ctx:venom_context,
   func:ir_function, es/es1/es2:evaluation_state,
   s0/s1/s2:venom_state, sc/si/sj:compile_state,
   slot:bytes32, tr:bool, tv:type_value, elem:type,
   r:operand # data_location option # place_ty option, x:string.
   The type names here describe the roles; HOL infers their exact namespace
   at the checked target_post/expr_post instance above.

   body_inv tops ctx cenv cx
   expr_body_pre cenv cx env (Pop ann (SubscriptTarget bt e)) es
   body_base_target_ptr_ok cx (SubscriptTarget bt e)
   type_place_target env bt = SOME (Type (ArrayT elem (Dynamic n)))
   evaluate_type (get_tenv cx) (ArrayT elem (Dynamic n)) =
     SOME (ArrayTV tv (Dynamic n))
   eval_base_place cx bt es =
     (INL (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n)))),es1)
   compile_get_target_ptr compile_expr cenv bt sc = (r,si)
   lower_value compile_expr cenv (expr_type e) e si = (op,sj)
   target_post ctx func cenv cx es sc si s0 es1
     (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
     (Type (ArrayT elem (Dynamic n))) r s1
   FST r = Var x
   bind (eval_expr cx e) (read_result cx) es1 = (INL v,es2)
   expr_post ctx func cenv cx e es1 si sj s1 es2 v op s2
   ghost_inv d cenv cx es2 G2 tn2 s2
   ghost_kept cenv es1 si G1 tn1 s1 G2 tn2
   ptr_val_ok cx (expr_type e) v op G2 tn2 s2
   (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G2 s2)
   s2.vs_current_bb = sj.cs_current_bb
   s2.vs_inst_idx = LENGTH sj.cs_current_insts
   --------------------------------------------------------------
   Required raw read, NOT yet proved from those hypotheses:
   lookup_storage slot (get_storage cx es2 tr) =
     lookup_storage slot
       (if tr then s2.vs_transient s2.vs_call_ctx.cc_address
        else (s2.vs_accounts s2.vs_call_ctx.cc_address).storage)
   Required local observer, separately NOT yet proved:
   pop_region_taint_ok
     (if tr then s2.vs_transient s2.vs_call_ctx.cc_address
      else (s2.vs_accounts s2.vs_call_ctx.cc_address).storage)
     (w2n slot) (ArrayTV tv (Dynamic n))
     (if tr then tn2.t_trans else tn2.t_stor)

   This is a normal-cut ledger, not a claim that those assumptions suffice
   without operational path/source-layout information. All post assumptions
   listed are exactly the normal index judgment's projections; the body and
   target assumptions remain in scope. Entry fn_has_code/local reservation/
   gas_admissible/ghost_inv assumptions are those of expr_sim_ptr_def lines
   269-282, needed before that judgment can be consumed. No source support,
   compatible trace or surviving storage_read_live is silently supplied.

   Producers and next consumer (finite table):
   index body_expr_ptr_ok | pop_target_index_ptr_premise, TargetFactor:60
   intermediate pre      | target_indices_pre_def, targetPlaceSim:109-116;
                           source preservation still needed to instantiate
   saved slot operand    | checked pop_saved_storage_variable_after_index
   saved operand ghost   | ghost_kept_def:103-105 for Var x not_fresh at si
   next dynamic load     | compile_array_subscript_def:1366-1368 invokes
                           compile_ptr_load at Var x AFTER lower_value
   source continuation   | pop_target_subscript_cut, TargetFactor:17-24;
                           extend_place sees captured pv at es2
   raw header equality   | no producer at dead cut; stmt_state_rel is live
                           only; S1 effectful_dead_case is admitted
   local taint observer  | live branch SavedIndexBoundary; dead case missing
                           typed operational write/call/layout bridge

   Reference instantiation: b's source type is
   DynArray[DynArray[DynArray[uint256,2],2],2], root slot 0.
   bt is b[1]; r is the ADD-generated variable at slot 8, carrying the
   middle-array type ArrayTV (ArrayTV uint256 (Dynamic 2)) (Dynamic 2).
   e is b.pop()[0][0]. Inner Pop makes root length 1, returns slot 8,
   and e reads zero from its first inner array's first element. The outer
   compile_array_subscript continuation loads slot 8 to bounds-check index
   zero; then it produces slot 9, whose length the final Pop loads/stores.
   Slot 8 is already dead globally, but its own length remains 2. No internal
   call occurs in this specific e. C1.5.1 checked that this is NOT a supported
   source Pop instance; body expr pre does not itself exclude it, and the
   missing compiled-containment inversion prevents claiming full exclusion.
   For a general e containing IntCall, expr_body_pre only restricts calls to
   main supported modules and call_evaluation_safe; no purity premise is
   available. Internal-function call nesting restrictions do not eliminate
   callee storage writes at this cut. *)
