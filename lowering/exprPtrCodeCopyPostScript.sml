(* Semantic representation is transported to the pointer execution witness,
   rather than selecting a second independently executed copy endpoint. *)
Theory exprPtrCodeCopyPost
Ancestors
  exprPtrCodeCopyInduction exprSimCopy immutableCopyExecution
  compileEnv context loweringPosts venomState venomInst words list fragExec exprLoweringProps

Theorem code_copy_same_endpoint_memory:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  copy_runtime_frame sa s sb z ==>
  z.vs_memory = (immutable_transfers F F a b n off s).vs_memory
Proof
  strip_tac >> drule_all copy_runtime_run >> strip_tac >>
  gvs[copy_runtime_frame_def]
QED

Theorem code_copy_same_endpoint_contents:
  compile_imm_copy_to_memory F imm src dst (type_slot_size ty) 0 sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  copy_runtime_frame sa s sb z /\
  stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx t (Value v) a es input /\
  evaluate_type (get_tenv cx) t = SOME ty /\
  w2n b + type_memory_size ty < dimword (:256) ==>
  val_wf ty v /\ val_in_memory ty v (w2n b) z.vs_memory /\
  val_footprint ty v <= type_memory_size ty
Proof
  strip_tac >> drule_all code_copy_same_endpoint_memory >> strip_tac >>
  irule copy_runtime_contents >> goal_assum drule >>
  goal_assum (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* The S1 suffix post is used only at the identical deterministic endpoint;
   pointer safety remains supplied independently by the counted copy path. *)
Theorem unwrap_code_same_endpoint_post:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    type_memory_bytes cenv t = type_memory_size ty) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  run_inst_seq (emitted_insts sm sb) s = OK z ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op z
Proof
  strip_tac >>
  `t = post_value_type cenv e` by gvs[vv_post_def, vv_holds_def] >>
  gvs[] >> drule_all runtime_code_copy_run_post_physical >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND]
QED
