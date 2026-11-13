Theory typedNormalizeFields
Ancestors
  typedNormalizeFieldPathMem


Theorem normalize_tuple_fields_memory_run:
  LENGTH DT = N /\ LENGTH ST = N /\
  (!i. d i = b + d0 + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + s0 + SUM (MAP (type_memory_bytes ce) (TAKE i ST))) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  d N <= s.vs_alloca_next /\ h N <= s.vs_alloca_next /\
  d N < dimword (:256) /\ h N < dimword (:256) /\
  (!i. i < N ==> val_wf (TS i) (VS i) /\
    type_memory_size (TS i) <= h (SUC i) - h i) /\
  (!i. i < N ==> val_wf (TD i) (VD i) /\
    type_memory_size (TD i) <= d (SUC i) - d i) /\
  (!i. i < N ==> val_in_memory (TS i) (VS i) (h i) s.vs_memory) /\
  (!i sd se dp sp u.
    i < N /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i ST) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    val_in_memory (TS i) (VS i) (h i) u.vs_memory ==>
    ?v. mem_cont_sim ctx fn u v /\ val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_typed_copy_fields ce dst src DT ST d0 s0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. mem_cont_sim ctx fn s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!i. i < N ==> val_in_memory (TD i) (VD i) (d i) t.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d N - d 0)] s t /\
    mem_bytes_at (h 0) (h N - h 0) t.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  MATCH_ACCEPT_TAC (normalize_tuple_fields_memory_counted |> SPEC_ALL |>
    Q.INST [`counted` |-> `F`] |>
    PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED

Theorem normalize_nominal_struct_fields_memory_run:
  DT = MAP (FST o SND) fields /\ LENGTH fields = N /\
  (!name ty sz. MEM (name,ty,sz) fields ==>
    ALOOKUP src_fields name = SOME (ty,sz) /\ sz = type_memory_bytes ce ty) /\
  (!i. d i = b + d0 + SUM (MAP (SND o SND) (TAKE i fields))) /\
  (!i. h i = a + s0 + SUM (MAP (SND o SND) (TAKE i fields))) /\
  abi_footprint_disjoint (h 0) (h N - h 0) [(d 0,d N - d 0)] /\
  d N <= s.vs_alloca_next /\ h N <= s.vs_alloca_next /\
  d N < dimword (:256) /\ h N < dimword (:256) /\
  (!i. i < N ==> val_wf (TS i) (VS i) /\
    type_memory_size (TS i) <= h (SUC i) - h i) /\
  (!i. i < N ==> val_wf (TD i) (VD i) /\
    type_memory_size (TD i) <= d (SUC i) - d i) /\
  (!i. i < N ==> val_in_memory (TS i) (VS i) (h i) s.vs_memory) /\
  (!i sd se dp sp u.
    i < N /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i DT) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    val_in_memory (TS i) (VS i) (h i) u.vs_memory ==>
    ?v. mem_cont_sim ctx fn u v /\ val_in_memory (TD i) (VD i) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      abi_decode_footprint_frame [(d i,type_memory_bytes ce (EL i DT))] u v /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      sd.cs_next_var <= se.cs_next_var /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_struct_typed_copy ce dst src fields src_fields d0 s0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. mem_cont_sim ctx fn s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!i. i < N ==> val_in_memory (TD i) (VD i) (d i) t.vs_memory) /\
    abi_decode_footprint_frame [(d 0,d N - d 0)] s t /\
    mem_bytes_at (h 0) (h N - h 0) t.vs_memory =
      mem_bytes_at (h 0) (h N - h 0) s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  MATCH_ACCEPT_TAC (normalize_nominal_struct_fields_memory_counted |> SPEC_ALL |>
    Q.INST [`counted` |-> `F`] |>
    PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED
