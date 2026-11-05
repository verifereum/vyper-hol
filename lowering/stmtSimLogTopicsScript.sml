Theory stmtSimLogTopics
Ancestors
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogArgs stmtSimLogSource stmtLowering compileEnv context
  exprSimHash  exprSimWordArgs vyperEvent valueEncoding
  emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomState
  venomInst freshWrites words string finite_map list ASCIInumbers supportedTypes
  vyperTyping vyperValue exprSimLiteralBuffer byte exprSimOps

Theorem split_log_ops_select:
  !xs flags. LENGTH flags = LENGTH xs ==>
    FST (split_log_ops xs flags) =
      MAP (\p. (FST (FST p), is_bytestring_type (SND (FST p))))
        (FILTER SND (ZIP (xs,flags))) /\
    SND (split_log_ops xs flags) =
      MAP FST (FILTER (\p. ~SND p) (ZIP (xs,flags)))
Proof
  cheat
QED

Theorem split_log_ops_lengths:
  !xs flags. LENGTH flags = LENGTH xs ==>
    LENGTH (FST (split_log_ops xs flags)) = LENGTH (FILTER I flags) /\
    LENGTH (SND (split_log_ops xs flags)) = LENGTH (FILTER ($~) flags)
Proof
  cheat
QED

Theorem split_log_ops_data_types:
  !xs flags. LENGTH flags = LENGTH xs ==>
    MAP SND (SND (split_log_ops xs flags)) =
      log_non_indexed_types flags (MAP SND xs)
Proof
  cheat
QED

Theorem split_log_ops_data_rel:
  !xs vs flags. LIST_REL P xs vs /\ LENGTH flags = LENGTH xs ==>
    LIST_REL P (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)
Proof
  cheat
QED

Theorem compile_encode_log_topic_bytes_run:
  compile_encode_log_topic ptr_op T sa = (op,sb) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME
      (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  cheat
QED

Theorem log_arg_footprint_bound:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sb es s (op,ty) v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ eval_operand op s = SOME p ==>
  w2n p + val_footprint tv v < dimword (:256)
Proof
  cheat
QED

Theorem compile_encode_log_topic_word_run:
  compile_encode_log_topic ptr_op F sa = (op,sb) /\
  eval_operand ptr_op s = SOME w ==>
  run_inst_seq (emitted_insts sa sb) s = OK s /\ eval_operand op s = SOME w
Proof
  cheat
QED

Theorem log_topic_count_exact:
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 ==>
  LENGTH (h::FST (split_log_ops xs flags)) <= 4 /\
  w2n (n2w (LENGTH (h::FST (split_log_ops xs flags))) : 256 word) =
    LENGTH (h::FST (split_log_ops xs flags))
Proof
  cheat
QED

Theorem log_bytestring_arg_view:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sb es s (op,ty) v /\
  supported_scalar_type ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  ?b bs. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    encode_event_topic ty v = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs))
Proof
  cheat
QED



Theorem log_scalar_topic_shape:
  supported_scalar_type ty ==>
  (is_event_bytestring_type ty = is_bytestring_type ty) /\
  (~is_bytestring_type ty ==> supported_word_type ty /\ is_word_type ty)
Proof
  cheat
QED

Theorem compile_encode_log_topic_scalar_run:
  stmt_state_rel ctx func cenv cx es s /\
  log_arg_rel cenv cx sa sm es s (x,ty) v /\
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  compile_encode_log_topic x (is_bytestring_type ty) sm = (op,sb) ==>
  ?t topic. run_inst_seq (emitted_insts sm sb) s = OK t /\
    encode_event_topic ty v = SOME topic /\
    eval_operand op t = SOME topic /\
    (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s)
Proof
  cheat
QED

(* The generic shape theorem is local to loweringShapeProps; expose the
   frontier facts needed by read-only topic composition here. *)
Theorem log_topic_frontier:
  compile_encode_log_topic x flag sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ (!l. x <> Label l) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  cheat
QED

Theorem log_readonly_frame:
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) ==>
  wb_frame cenv es sa s t
Proof
  cheat
QED

Theorem log_readonly_arg:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_id <= sb.cs_next_id /\
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
  (!z. FST arg = Var z ==> not_fresh_at sm z) /\ (!l. FST arg <> Label l) /\
  supported_scalar_type (SND arg) /\ log_arg_rel cenv cx sa sm es s arg v ==>
  log_arg_rel cenv cx sa sb es t arg v
Proof
  cheat
QED

Theorem compile_log_topic_ops_cons:
  compile_log_topic_ops (x::xs) sa = (ops,sb) <=>
  ?op sm rest. compile_encode_log_topic (FST x) (SND x) sa = (op,sm) /\
    compile_log_topic_ops xs sm = (rest,sb) /\ ops = op::rest
Proof
  cheat
QED

Theorem compile_log_topic_ops_frontier:
  !raw sa ops sb.
    compile_log_topic_ops raw sa = (ops,sb) /\
    EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sa z) /\
                (!l. FST p <> Label l)) raw ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\op. (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) ops
Proof
  cheat
QED

Theorem log_readonly_args:
  !xs vs.
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sm.cs_next_id <= sb.cs_next_id /\
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs ==>
  LIST_REL (\arg v. log_arg_rel cenv cx sa sb es t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs
Proof
  cheat
QED

Theorem log_topic_inst_extends:
  compile_encode_log_topic x flag sa = (op,sb) ==> inst_extends sa sb
Proof
  cheat
QED

Theorem log_topics_inst_extends:
  !raw sa ops sb.
    compile_log_topic_ops raw sa = (ops,sb) ==> inst_extends sa sb
Proof
  cheat
QED

Theorem compile_log_topic_ops_run:
  !xs vs sm ops sb s topics.
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  compile_log_topic_ops (MAP (\p. (FST p,is_bytestring_type (SND p))) xs) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics (REPLICATE (LENGTH xs) T) (MAP SND xs) vs = SOME topics ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s)
Proof
  cheat
QED


Theorem log_indexed_selection_rel:
  !xs vs flags. LIST_REL P xs vs /\ LENGTH flags = LENGTH xs ==>
    LIST_REL P (MAP FST (FILTER SND (ZIP (xs,flags))))
               (MAP FST (FILTER SND (ZIP (vs,flags))))
Proof
  cheat
QED

Theorem log_indexed_selection_every:
  !xs flags. LENGTH flags = LENGTH xs /\ EVERY P xs ==>
    EVERY P (MAP FST (FILTER SND (ZIP (xs,flags))))
Proof
  cheat
QED

Theorem log_indexed_encoding_select:
  !xs vs flags. LENGTH flags = LENGTH xs /\ LENGTH vs = LENGTH xs ==>
    encode_indexed_event_topics flags (MAP SND xs) vs =
    encode_indexed_event_topics
      (REPLICATE (LENGTH (MAP FST (FILTER SND (ZIP (xs,flags))))) T)
      (MAP SND (MAP FST (FILTER SND (ZIP (xs,flags)))))
      (MAP FST (FILTER SND (ZIP (vs,flags))))
Proof
  cheat
QED

Theorem compile_split_log_topics_run:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,sb) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\
              (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel cenv cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    LIST_REL (\op w. eval_operand op t = SOME w) ops topics /\
    stmt_state_rel ctx func cenv cx es t /\
    LIST_REL (log_arg_rel cenv cx sa sb es t)
      (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) /\
    wb_frame cenv es sm s t /\
    EVERY (\op. (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)) ops
Proof
  cheat
QED


Theorem compile_log_topic_ops_length:
  !raw sa ops sb. compile_log_topic_ops raw sa = (ops,sb) ==>
    LENGTH ops = LENGTH raw
Proof
  cheat
QED

Theorem log_emitted_topic_count_exact:
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sa = (ops,sb) ==>
  LENGTH (h::ops) <= 4 /\
  w2n (n2w (LENGTH (h::ops)) : 256 word) = LENGTH (h::ops)
Proof
  cheat
QED
