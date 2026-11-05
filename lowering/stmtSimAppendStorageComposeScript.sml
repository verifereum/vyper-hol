(* Source and code partitions for primitive storage Append composition. *)
Theory stmtSimAppendStorageCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  appendStorageRel stmtSimAppendStorage stmtSimAssignStorage  fragExec
  varsExt freshWrites stateFrame venomState finite_map 
  accountsRelProps vyperStorage vyperStorageBackend vyperValue vfmState
  exprOperandVar stmtSimDecl
  vyperInterpreter vyperState vyperExprNoControl stmtLowering exprLowering
  exprLoweringProps compileEnv emitHelper emitHelperProps venomInst venomExecSemantics
Libs
  monadsyntax

Theorem eval_append_toplevel:
  eval_target_place cx (TopLevelNameTarget nid) es = (INL p,es) /\
  eval_stmt cx (Append (TopLevelNameTarget nid) e) es = (res,es') ==>
  ?r es1.
    (do result <- eval_expr cx e; read_result cx result od) es = (r,es1) /\
    (!ex. r = INR ex ==> res = INR ex /\ es' = es1 /\ no_control_exc ex) /\
    (!v. r = INL v ==> append_place cx p v es1 = (res,es'))
Proof
  cheat
QED

Theorem append_storage_word_code_parts:
  stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e) sa = (c,sf) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 ==>
  c = cenv /\ ?sb op.
    lower_value compile_expr cenv elem e sa = (op,sb) /\
    compile_dynarray_append cenv (Lit slot) op 1 1 elem
      (lowered_value_type cenv e) cap T
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf)
Proof
  cheat
QED

Theorem append_storage_word_suffix_structure:
  compile_dynarray_append cenv bop vop 1 1 dt st cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  same_blocks sa sf /\ inst_extends sa sf /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_ext_call_op i.inst_opcode) (emitted_insts sa sf)
Proof
  cheat
QED

Theorem append_storage_word_code_frame:
  lower_value compile_expr cenv elem e sa = (op,sb) /\
  compile_dynarray_append cenv (Lit slot) op 1 1 elem
    (lowered_value_type cenv e) cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sa sf func ==>
  cs_extends sa sb /\ cs_extends sb sf /\
  fn_has_code sa sb func /\ fn_has_code sb sf func
Proof
  cheat
QED

Theorem append_storage_word_run_frag:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop sbase = SOME slot /\ eval_operand vop sbase = SOME w /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot sbase else sload slot sbase) /\ len < cap /\
  ~sbase.vs_call_ctx.cc_static ==>
  frag_exec ctx sa sf (\s. s = sbase)
    (\s. ?u. s = u with vs_inst_idx := LENGTH sf.cs_current_insts /\
      state_frame u = state_frame
       (if tr then tstore slot (n2w len+1w) (tstore (slot+1w+n2w len) w sbase)
        else sstore slot (n2w len+1w) (sstore (slot+1w+n2w len) w sbase))
       /\ 
      (!x a. not_fresh_at sa x /\ lookup_var x sbase = SOME a ==>
             lookup_var x u = SOME a)) R
Proof
  cheat
QED

Theorem append_storage_word_abort_frag:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop sbase = SOME slot /\ cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot sbase else sload slot sbase) ==>
  frag_exec ctx sa sf (\s. s = sbase) Q
    (stmt_exit RetQ es' (INR (Error (RuntimeError "append full storage array"))))
Proof
  cheat
QED

Theorem stmt_state_rel_reserved_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  state_frame t = state_frame s /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  cheat
QED

Theorem append_storage_word_frame_fields[local]:
  state_frame u = state_frame
    (if tr then tstore slot h (tstore addr w s)
     else sstore slot h (sstore addr w s)) ==>
  u.vs_current_bb = s.vs_current_bb /\
  u.vs_halted = s.vs_halted /\ u.vs_allocas = s.vs_allocas
Proof
  cheat
QED

Theorem append_storage_word_success_frag:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop sbase = SOME slot /\ eval_operand vop sbase = SOME w /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot sbase else sload slot sbase) /\ len < cap /\
  stmt_state_rel ctx func cenv cx es sbase /\ local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\
  encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  sbase.vs_current_bb = sa.cs_current_bb /\ ~sbase.vs_halted ==>
  frag_exec ctx sa sf (\s. s = sbase)
    (\s. stmt_state_rel ctx func cenv cx es' s /\
      stmt_lands lctx sf (INL ()) s /\ ~s.vs_halted /\
      (!x a. not_fresh_at sa x /\ lookup_var x sbase = SOME a ==>
             lookup_var x s = SOME a) /\ s.vs_allocas = sbase.vs_allocas) R
Proof
  cheat
QED

Theorem append_storage_header_agree[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr)
Proof
  cheat
QED

Theorem append_storage_word_value_frag[local]:
  compile_dynarray_append cenv (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,w)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') /\
  s.vs_current_bb = sb.cs_current_bb /\ ~s.vs_halted ==>
  frag_exec ctx sb sf (\t. t = s)
    (\t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
      (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
             lookup_var x t = SOME a) /\ t.vs_allocas = s.vs_allocas)
    (stmt_exit RetQ es' res)
Proof
  cheat
QED

Theorem append_storage_value_run[local]:
  expr_sim ctx func cenv cx elem e es /\
  lower_value compile_expr cenv elem e sa = (op,sb) /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\ is_word_type (expr_type e) /\
  compile_dynarray_append cenv (Lit slot) op 1 1 elem vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  cap < dimword (:256) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,typed_val_to_w256 etv v)] /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es1 = (res,es') /\
  fn_has_code sa sb func /\ fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (?t. res = INL () /\ stmt_state_rel ctx func cenv cx es' t /\
     stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\
     (!x a. not_fresh_at sa x /\ lookup_var x s0 = SOME a ==> lookup_var x t = SOME a) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
     !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
       ?fuel'. run_from fuel' ctx func s0 = r) \/
  (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\ stmt_exit RetQ es' res r)
Proof
  cheat
QED

Theorem append_storage_word_suffix_open[local]:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) ==>
  ~block_is_terminated sf
Proof
  cheat
QED

Theorem compile_append_storage_word_stmt_frag:
  eval_target_place cx (TopLevelNameTarget nid) es =
    (INL (StoragePlace tr slot (ArrayTV tv (Dynamic cap))),es) /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  FLOOKUP cenv.ce_module_vars nid =
    SOME (if tr then TransientLoc slot else StorageLoc slot) /\
  cenv.ce_module_var_type nid = SOME (ArrayT elem (Dynamic cap)) /\
  cenv.ce_module_dynarray_capacity nid = cap /\
  is_word_type elem /\ type_memory_bytes cenv elem = 32 /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  type_slot_size tv = 1 /\ cap < dimword (:256) /\
  (!v es1. (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es1) ==>
    encode_value tv v = SOME [(0,typed_val_to_w256 etv v)]) /\
  expr_sim ctx func cenv cx elem e es ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Append (TopLevelNameTarget nid) e))
    (eval_stmt cx (Append (TopLevelNameTarget nid) e)) es
Proof
  cheat
QED
