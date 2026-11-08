Theory abiEncodeArgsSim
Ancestors
  abiEncodeMaterialize abiEncodeArgsScopes abiEncodeArgsWindows abiDecoderReentry
  compileEnv exprSimDefs exprSimProps loweringPosts exprSimHyps exprSimWordArgs abiArgsLabelObserver exprOperandVar
  abiArgsLabelBoundary

Definition abi_args_post_def:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s <=>
    stmt_state_rel ctx func ce cx es' s /\
    LENGTH args = LENGTH vs /\
    LIST_REL (\op ev.
      expr_val_rel cx (lowered_value_type ce (FST ev)) (SND ev) op s /\
      expr_val_at ce cx (lowered_value_type ce (FST ev)) sa sb es' (SND ev) op s)
      ops (ZIP (args,vs)) /\
    wb_frame ce es es' sa s0 s
End

Definition abi_args_ready_def:
  abi_args_ready ctx func ce cx Inv [] = T /\
  abi_args_ready ctx func ce cx Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func ce cx (expr_type e) e es /\
       expr_vv_sim ctx func ce cx (expr_type e) e es /\
       (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
          expr_res_ok res) /\
       (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
          Inv es' /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
          (~is_word_type (expr_type e) /\ exprs_can_mutate ce args ==>
           ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                value_has_type tv v /\ val_wf tv v /\
                type_memory_bytes ce (expr_type e) = type_memory_size tv /\
                type_memory_size tv < 2 ** 64 /\
                type_memory_size tv + 64 < dimword (:256)))) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv,t) /\
                         read_result cx tv s1 = (INL v,t1)) ==>
       abi_args_ready ctx func ce cx Inv args))
End

Theorem abi_args_post_nil:
  abi_args_post ctx func ce cx es sa sb s0 es' [] ops vs s <=>
    ops = [] /\ vs = [] /\ stmt_state_rel ctx func ce cx es' s /\
    wb_frame ce es es' sa s0 s
Proof
  cheat
QED

Theorem abi_args_post_cons:
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) s <=>
    expr_val_rel cx (expr_type e) v op s /\
    expr_val_at ce cx (expr_type e) sa sb es' v op s /\
    abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s
Proof
  cheat
QED

Theorem abi_args_post_lengths:
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s ==>
    LENGTH args = LENGTH vs /\ LENGTH ops = LENGTH args
Proof
  cheat
QED

Theorem abi_args_ready_tail:
  abi_args_ready ctx func ce cx Inv (e::args) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) ==>
  abi_args_ready ctx func ce cx Inv args
Proof
  cheat
QED

(* Readiness premise ledger (applicability remains a separate obligation).
   - head simulations: exprs_case_def at expr_type e.
   - result admissibility and next invariant: expr_body_pre_eval, together
     with the unchanged body-pre environment and call-safety premises.
   - source scope domains: eval_expr_preserves_scopes_dom and
     vyperState.read_result_state (reading never changes source state).
   - evaluated type and value_has_type: expr_body_pre_eval's
     expr_result_typed, unfolded through value_runtime_typed, and the
     environment/get_tenv agreement in expr_sim_inv.
   - val_wf: valueEncodingTyping.value_has_type_val_wf.
   - layout equality and size < 2**64: expr_body_pre_copy_ok.
   - size + 64 < dimword(:256): arithmetic consequence of size < 2**64.
   None of these items permits literal ABI has_type or declared capacity
   to be inferred from expr_val_at. *)

Theorem abi_args_read_state:
  read_result cx result es = (res,es') ==> es' = es
Proof
  cheat
QED

Theorem abi_args_capture_size:
  n < 2 ** 64 ==> n + 64 < dimword (:256)
Proof
  cheat
QED

Theorem abi_args_local_type_coherent:
  expr_sim_inv ce cx env es /\ lookup_scopes name es.scopes = SOME entry ==>
  ?ty. ce.ce_var_type name = SOME ty /\
       evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  cheat
QED

Theorem abi_args_dynamic_local_type:
  expr_sim_inv ce cx env es /\ lookup_scopes name es.scopes = SOME entry /\
  dynarray_local ce name ==>
  ?etv n. entry.type = ArrayTV etv (Dynamic n)
Proof
  cheat
QED

Theorem abi_args_local_region_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  local_region ce es.scopes s0 name b sz ==>
  mem_bytes_at b sz s1.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  cheat
QED

Theorem abi_args_local_window_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  local_region ce es.scopes s0 name b sz /\
  b <= off /\ off + len <= b + sz ==>
  mem_bytes_at off len s1.vs_memory = mem_bytes_at off len s0.vs_memory
Proof
  cheat
QED

Theorem abi_args_operand_kept:
  wb_frame ce es es' st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s1 = SOME w
Proof
  cheat
QED

Theorem abi_args_location_kept_eq:
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\ local_ptrs_reserved ce st /\
  wb_frame ce es es' st s0 s1 /\
  eval_operand op s0 = eval_operand op s1 /\
  expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_at ce cx ty sa sb es' v op s1
Proof
  cheat
QED

Theorem abi_args_location_kept:
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es'.scopes = MAP FDOM es.scopes /\ local_ptrs_reserved ce st /\
  wb_frame ce es es' st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_at ce cx ty sa sb es' v op s1
Proof
  cheat
QED

Theorem abi_args_value_kept_eq:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  sb.cs_next_id <= st.cs_next_id /\
  eval_operand op s0 = eval_operand op s1 /\
  expr_val_rel cx ty v op s0 /\ expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_rel cx ty v op s1
Proof
  cheat
QED

Theorem abi_args_value_kept:
  expr_sim_inv ce cx env es /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es' s1 /\ es'.scopes = es.scopes /\
  local_ptrs_reserved ce st /\ wb_frame ce es es' st s0 s1 /\
  sb.cs_next_id <= st.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  expr_val_rel cx ty v op s0 /\ expr_val_at ce cx ty sa sb es v op s0 ==>
  expr_val_rel cx ty v op s1
Proof
  cheat
QED

Theorem abi_args_captured_value_kept:
  wb_frame ce es es' st s0 s1 /\
  (!x. op = Var x ==> not_fresh_at st x) /\ (!l. op <> Label l) /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_val_rel cx ty v op s0 /\ val_wf tv v /\
  eval_operand op s0 = SOME w /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < st.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
              b + sz <= lb \/ lb + lsz <= b) ==>
  expr_val_rel cx ty v op s1
Proof
  cheat
QED

Theorem abi_args_nil_sim:
  frag_exec ctx sa sa (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. abi_args_post ctx func ce cx es sa sa s0 es [] [] [] s)
    (wb_args_exit (INL []))
Proof
  cheat
QED

Theorem abi_args_ready_head:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es ==>
  expr_sim ctx func ce cx (expr_type e) e es /\
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  (!res es'. (do r <- eval_expr cx e; read_result cx r od) es = (res,es') ==>
     expr_res_ok res) /\
  (!v es'. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
     Inv es' /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
     (~is_word_type (expr_type e) /\ exprs_can_mutate ce args ==>
      ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
           value_has_type tv v /\ val_wf tv v /\
           type_memory_bytes ce (expr_type e) = type_memory_size tv /\
           type_memory_size tv < 2 ** 64 /\
           type_memory_size tv + 64 < dimword (:256)))
Proof
  cheat
QED

Theorem abi_args_compile_mono:
  !args ce st.
    ci_mono st (SND (compile_abi_encode_args compile_expr ce args st))
Proof
  cheat
QED

Theorem abi_args_location_end_mono:
  sm.cs_next_id <= sb.cs_next_id /\ expr_val_at ce cx ty sa sm es v op s ==>
  expr_val_at ce cx ty sa sb es v op s
Proof
  cheat
QED

Theorem abi_args_post_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  abi_args_post ctx func ce cx es sm sb s0 es' args ops vs s /\
  wb_frame ce es es' sa s0 s ==>
  abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s
Proof
  cheat
QED

Theorem abi_args_post_cons_frame:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  expr_val_rel cx (expr_type e) v op u /\
  expr_val_at ce cx (expr_type e) sa sb es' v op u ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  cheat
QED

Theorem abi_args_post_cons_uncaptured:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (expr_type e) ==> es'.scopes = es1.scopes) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  cheat
QED

Theorem abi_args_post_cons_uncaptured_labels:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (expr_type e) ==> es'.scopes = es1.scopes) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  cheat
QED

Theorem abi_args_post_cons_captured:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ val_wf tv v /\
  eval_operand op t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es1.scopes t n lb lsz ==>
              b + sz <= lb \/ lb + lsz <= b) ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  cheat
QED

Theorem abi_args_compile_cons:
  compile_abi_encode_args compile_expr ce (e::args) sa = (ops,sb) <=>
  ?vv mid op sm tail.
    compile_expr ce (expr_type e) e sa = (vv,mid) /\
    (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce args
     then compile_materialize_vv ce (expr_type e) vv mid
     else unwrap_value ce vv mid) = (op,sm) /\
    compile_abi_encode_args compile_expr ce args sm = (tail,sb) /\
    ops = op::tail
Proof
  cheat
QED

Theorem abi_args_materialize_not_label:
  compile_materialize_vv ce ty vv sa = (op,sb) ==> !l. op <> Label l
Proof
  cheat
QED

Theorem abi_args_name_label_forward[local]:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Label l) sz) /\
  ~is_word_type (expr_type (Name ann id)) ==>
  lower_value compile_expr ce ty (Name ann id) sa = (Label l,sa)
Proof
  cheat
QED


Theorem abi_args_operand_live:
  (!x. op = Var x ==> not_fresh_at sm x) /\ ci_mono sm sb ==>
  abi_decoder_operand_live sb.cs_next_var op
Proof
  cheat
QED

Theorem abi_args_uncaptured_cons_sim_live:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (expr_type e) ==> es'.scopes = es1.scopes) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) ops)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops))
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_uncaptured_cons_sim:
  expr_sim ctx func ce cx (expr_type e) e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ expr_sim_inv ce cx env es1 /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (expr_type e) ==> es'.scopes = es1.scopes) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s)
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_captured_cons_sim:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (expr_type e) vv mid = (op,sm) /\
  eval_expr cx e es = (INL tvv,es1) /\
  expr_vv_res_ok (INL tvv) /\ read_result cx tvv es1 = (INL v,es1) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\ type_memory_size tv + 64 < dimword (:256) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s)
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_captured_cons_sim_live:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (expr_type e) vv mid = (op,sm) /\
  eval_expr cx e es = (INL tvv,es1) /\
  expr_vv_res_ok (INL tvv) /\ read_result cx tvv es1 = (INL v,es1) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\ type_memory_size tv + 64 < dimword (:256) /\
  (!t. frag_exec ctx sm sb (\s. s = t /\ stmt_state_rel ctx func ce cx es1 s)
    (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es1 sm sb t es' args ops vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) ops)
    (wb_args_exit rr)) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    (\s. ?vs. (case rr of INL xs => INL (v::xs) | INR ex => INR ex) = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) vs s /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops))
    (wb_args_exit (case rr of INL xs => INL (v::xs) | INR ex => INR ex))
Proof
  cheat
QED

Theorem abi_args_vv_post_read:
  vv_post ctx func ce cx e es sa sb s0 es' tvv vv s ==>
  ?v. read_result cx tvv es' = (INL v,es')
Proof
  cheat
QED

Theorem abi_args_read_vv_res_ok:
  read_result cx tvv es = (res,es') /\ expr_res_ok res ==>
  expr_vv_res_ok (INL tvv)
Proof
  cheat
QED

Theorem abi_args_exit_inr:
  expr_exit (INR exc : 'a + exception) =
  expr_exit (INR exc : value list + exception)
Proof
  cheat
QED

Theorem abi_args_vv_error_prefix:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  eval_expr cx e es = (INR exc,es') /\
  expr_res_ok (INR exc : value + exception) /\
  fn_has_code sa mid func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cs_extends sa mid /\ cs_extends mid sb ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    Q (wb_args_exit (INR exc))
Proof
  cheat
QED

Theorem abi_args_vv_read_error_prefix:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  eval_expr cx e es = (INL tvv,es') /\
  read_result cx tvv es' = (INR exc,es') /\
  expr_res_ok (INR exc : value + exception) /\
  fn_has_code sa mid func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cs_extends sa mid /\ cs_extends mid sb ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
    Q (wb_args_exit (INR exc))
Proof
  cheat
QED

Theorem compile_abi_encode_args_sim_live:
  !args ctx func ce cx Inv env es sa ops sb rr es' s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
      (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops)
      (wb_args_exit rr)
Proof
  cheat
QED

Theorem compile_abi_encode_args_sim:
  !args ctx func ce cx Inv env es sa ops sb rr es' s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    eval_exprs cx args es = (rr,es') /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func ce cx es s)
      (\s. ?vs. rr = INL vs /\ abi_args_post ctx func ce cx es sa sb s0 es' args ops vs s)
      (wb_args_exit rr)
Proof
  cheat
QED
