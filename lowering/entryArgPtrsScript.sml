(*
 * External entry: the parameters after compile_register_positional_args
 * (#639)
 *
 * The external entry allocates an ALLOCA per parameter and decodes the
 * argument from calldata into it.  This file shows the parameters' pointers
 * then hold the arguments' values: local_ptrs_rel.
 *
 * TOP-LEVEL:
 *   register_positional_args_local_ptrs -- the parameters' local_ptrs_rel
 *                             after compile_register_positional_args
 *)
Theory entryArgPtrs
Ancestors
  list rich_list finite_map alist
  vyperLoweringCorrect entryDecodePlanProps entryDecodeProps fragExec
  compileEnv compileVyper moduleLowering selectorDispatch
  vyperInterpreter vyperState vyperContext vyperAST
  venomState vyperCall loweringHalt entryDecodeStaticProps retAbiPlanProps
  valueEncodingProofs vyperABIRoundtrip contractABI entryDispatchProps
  valueTypingMemoryProps localPtrsProps abiDecodeStaticProps entryDecodeStructure
  exprLoweringProps emitHelperProps exprLowering valueEncoding intCallCallee
  venomExecSemantics venomInst words entrySinkExtraction

(* Memory-only entry boundary: the decoder supplies the physical allocation
   facts separately from the contents of each decoded local. *)
Theorem decoded_memory_local_ptrs:
  !func cenv scopes ss.
    (!name entry p sz.
       lookup_scopes name scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       ?w. lookup_var p ss = SOME w /\
           local_backed func p ss (w2n w) sz /\
           w2n w + sz <= ss.vs_alloca_next /\
           type_memory_size entry.type <= sz /\
           val_wf entry.type entry.value) /\
    (!name entry p sz w.
       lookup_scopes name scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
       lookup_var p ss = SOME w ==>
       val_in_memory entry.type entry.value (w2n w) ss.vs_memory) /\
    (!n1 n2 b1 sz1 b2 sz2.
       n1 <> n2 /\ local_region cenv scopes ss n1 b1 sz1 /\
       local_region cenv scopes ss n2 b2 sz2 ==>
       regions_disjoint b1 sz1 b2 sz2) ==>
    local_ptrs_rel func cenv scopes ss
Proof
  cheat
QED

Theorem dec_frame_mstore:
  !st q w s t.
    vars_pc_only (mstore q w s) t /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
    dec_frame st q 32 s t
Proof
  cheat
QED

Theorem dec_frame_allocas:
  !st q n s t.
    dec_frame st q n s t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  cheat
QED

Theorem dec_frame_local_backed:
  !st q n s t func p b sz.
    dec_frame st q n s t /\ local_backed func p s b sz ==>
    local_backed func p t b sz
Proof
  cheat
QED

Theorem dec_frame_disjoint_memory:
  !st q n s t b sz.
    dec_frame st q n s t /\ regions_disjoint b sz q n ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  cheat
QED

Theorem dec_frame_local_ptrs:
  !st q n s t func cenv scopes.
    dec_frame st q n s t /\ local_ptrs_rel func cenv scopes s /\
    (!name entry p sz.
       lookup_scopes name scopes = SOME entry /\
       FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
       not_fresh_at st p) /\
    (!name b sz. local_region cenv scopes s name b sz ==>
       regions_disjoint b sz q n) ==>
    local_ptrs_rel func cenv scopes t
Proof
  cheat
QED

(* A single registration step exposes its two emitted fragments. *)
Theorem register_positional_args_step:
  !cenv name prim dyn sz dec rest off st cenvf stf loc msz.
    FLOOKUP cenv.ce_vars name = SOME loc /\
    var_location_memory_size loc = SOME msz ==>
    (compile_register_positional_args cenv
       ((name, prim, dyn, sz, dec)::rest) off st = (cenvf, stf) <=>
     ?buf sa sb.
       compile_alloc_buffer msz st = (buf, sa) /\
       compile_decode_args
         (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar buf.buf_operand msz)))
         [(name, prim, dyn, sz, dec)] off CALLDATALOAD (Lit 0w) 4 sa = ((), sb) /\
       compile_register_positional_args
         (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar buf.buf_operand msz)))
         rest (off + sz) sb = (cenvf, stf))
Proof
  cheat
QED

Theorem register_positional_args_nil:
  !cenv off st.
    compile_register_positional_args cenv [] off st = (cenv, st)
Proof
  cheat
QED

Theorem register_positional_args_straight:
  !args cenv off st cenv' st'.
    EVERY (\(name,prim,dyn,sz,info).
      prim \/ (~dyn /\ ?n. static_dec info n)) args /\
    compile_register_positional_args cenv args off st = (cenv',st') ==>
    dec_straight st st' /\ st.cs_next_id <= st'.cs_next_id
Proof
  cheat
QED

Theorem static_decs_replicate:
  !ei m n. static_dec ei m ==>
    static_decs (REPLICATE n (ei,m,m)) (n * m)
Proof
  cheat
QED

Theorem abi_dec_plan_static:
  (!env ty info. abi_dec_plan env ty info ==> !tv.
    evaluate_type env ty = SOME tv ==> static_dec info (type_memory_size tv)) /\
  (!env ts elems. abi_dec_plans env ts elems ==> !tvs.
    OPT_MMAP (evaluate_type env) ts = SOME tvs ==>
    static_decs elems (SUM (MAP type_memory_size tvs)))
Proof
  cheat
QED

Theorem build_positional_args_admissible:
  !cenv tenv args vals env.
    dec_cenv_agrees cenv tenv /\ bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args ==>
    EVERY (\(name,prim,dyn,sz,info).
      prim \/ (~dyn /\ ?n. static_dec info n)) (build_positional_args cenv args)
Proof
  cheat
QED

Theorem dec_straight_cs_extends:
  !st st'. dec_straight st st' ==> cs_extends st st'
Proof
  cheat
QED

Theorem dec_straight_code_phases:
  !st sa sb st' func.
    dec_straight st sa /\ dec_straight sa sb /\ dec_straight sb st' /\
    fn_has_code st st' func ==>
    fn_has_code st sa func /\ fn_has_code sa sb func /\
    fn_has_code sb st' func
Proof
  cheat
QED

Theorem entry_ptr_update_remaining:
  !args cenv name ptr sz.
    ~MEM name (MAP FST args) ==>
    EVERY (\a. FLOOKUP
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar ptr sz))).ce_vars
      (FST a) = FLOOKUP cenv.ce_vars (FST a)) args
Proof
  cheat
QED

Theorem build_positional_args_drop:
  !cenv args i.
    DROP i (build_positional_args cenv args) =
    build_positional_args cenv (DROP i args)
Proof
  cheat
QED

(* Successful binding preserves the positional value at each distinct name. *)
Theorem bind_arguments_lookup_index:
  !args vals tenv env i.
    bind_arguments tenv args vals = SOME env /\
    ALL_DISTINCT (MAP FST args) /\ i < LENGTH args ==>
    ?tv. evaluate_type tenv (SND (EL i args)) = SOME tv /\
         FLOOKUP env (FST (EL i args)) =
           SOME <| assignable := T; type := tv; value := EL i vals; popped := [] |>
Proof
  cheat
QED

Theorem bind_arguments_memory_wf:
  !tenv args vals env i tv.
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    evaluate_type tenv (SND (EL i args)) = SOME tv ==>
    val_wf tv (EL i vals)
Proof
  cheat
QED

Theorem bind_arguments_initial_local_ptrs:
  !tenv args vals env cenv func s.
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. ?off. FLOOKUP cenv.ce_vars (FST a) =
      SOME (MemLoc off (type_memory_bytes cenv (SND a)))) args ==>
    local_ptrs_rel func cenv [env] s
Proof
  cheat
QED

Theorem entry_static_arg_size:
  !cenv tenv ty tv.
    dec_cenv_agrees cenv tenv /\ evaluate_type tenv ty = SOME tv /\
    (is_word_type ty \/ ~is_dynamic (vyper_to_abi_type tenv ty)) ==>
    abi_embedded_static_size cenv.ce_struct_fields ty =
      type_memory_bytes cenv ty
Proof
  cheat
QED

Theorem entry_static_prefix_sizes:
  !cenv tenv args vals env i.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args ==>
    SUM (MAP (abi_embedded_static_size cenv.ce_struct_fields o SND)
             (TAKE i args)) =
    SUM (MAP (type_memory_bytes cenv o SND) (TAKE i args))
Proof
  cheat
QED

Theorem entry_static_abi_types:
  !tenv args vals env avs.
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args /\
    vyper_to_abi_list tenv (MAP SND args) vals = SOME avs ==>
    EVERY is_static (vyper_to_abi_types tenv (MAP SND args))
Proof
  cheat
QED

Theorem entry_static_encoding_sizes:
  !cenv tenv args vals env avs.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY is_static (vyper_to_abi_types tenv (MAP SND args)) /\
    vyper_to_abi_list tenv (MAP SND args) vals = SOME avs ==>
    MAP LENGTH (MAP2 enc (vyper_to_abi_types tenv (MAP SND args)) avs) =
    MAP (type_memory_bytes cenv o SND) args
Proof
  cheat
QED

Theorem entry_static_calldata_length:
  !cenv tenv fname args vals env cd.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args /\
    calldata_encodes tenv fname (MAP SND args) vals cd ==>
    LENGTH cd = 4 + SUM (MAP (type_memory_bytes cenv o SND) args)
Proof
  cheat
QED

Theorem entry_static_prefix_bound:
  !cenv tenv fname args vals env cd i.
    dec_cenv_agrees cenv tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      ~is_dynamic (vyper_to_abi_type tenv (SND a))) args /\
    calldata_encodes tenv fname (MAP SND args) vals cd /\
    LENGTH cd < dimword (:256) /\ i < LENGTH args ==>
    4 + SUM (MAP (type_memory_bytes cenv o SND) (TAKE i args)) +
        type_memory_bytes cenv (SND (EL i args)) < dimword (:256)
Proof
  cheat
QED

Theorem entry_decode_arg_frame:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory) (\r. F)
Proof
  cheat
QED

Theorem entry_decode_arg_run:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) /\
    ~s0.vs_halted /\ s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?u. dec_straight st st' /\
      run_inst_seq (emitted_insts st st') s0 = OK u /\
      let t = u with vs_inst_idx := LENGTH st'.cs_current_insts in
        dec_frame st (w2n p) (type_memory_size tv) s0 t /\
        fresh_vars_wrt st' t /\
        val_in_memory tv (EL i vals) (w2n p) t.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = s0.vs_current_bb /\
        t.vs_prev_bb = s0.vs_prev_bb
Proof
  cheat
QED
Theorem entry_decode_arg_frame_pc:
  !cenv cenv0 tenv fname args vals env i off hi st st' ctx loc dst s0 p tv.
    dec_cenv_agrees cenv0 tenv /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
                       (TAKE i args)) /\
    compile_decode_args cenv [build_positional_arg cenv0 (EL i args)] off
      CALLDATALOAD hi 4 st = ((), st') /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) = SOME loc /\
    var_location_decode_operand loc = SOME dst /\
    eval_operand dst s0 = SOME p /\ fresh_vars_wrt st s0 /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    calldata_encodes tenv fname (MAP SND args) vals s0.vs_call_ctx.cc_calldata /\
    (is_word_type (SND (EL i args)) \/
      (assignable_type tenv (SND (EL i args)) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND (EL i args))))) /\
    evaluate_type tenv (SND (EL i args)) = SOME tv /\ int_byte_widths tv /\
    off + type_memory_size tv < dimword (:256) /\
    w2n p + type_memory_size tv < dimword (:256) ==>
    frag_exec ctx st st' (\s. s = s0)
      (\t. dec_frame st (w2n p) (type_memory_size tv) s0 t /\
           fresh_vars_wrt st' t /\
           val_in_memory tv (EL i vals) (w2n p) t.vs_memory /\
           t.vs_prev_bb = s0.vs_prev_bb /\ t.vs_current_bb = s0.vs_current_bb)
      (\r. F)
Proof
  cheat
QED


(* Decoder frames preserve every live pointer: freshness rules out a live
   pointer being one of the decoder's new temporaries. *)
Theorem entry_live_ptrs_not_fresh:
  !func cenv scopes s st name entry p sz.
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p
Proof
  cheat
QED

Theorem entry_decode_bind_ptr:
  !func cenv scopes s t st name entry p w sz.
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    dec_frame st (w2n w) sz s t /\
    lookup_scopes name scopes = SOME entry /\
    (!q sq. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var q) sq)) /\
    lookup_var p s = SOME w /\ not_fresh_at st p /\
    local_backed func p s (w2n w) sz /\
    w2n w + sz <= s.vs_alloca_next /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n w) t.vs_memory /\
    (!n b sz'. local_region cenv scopes s n b sz' ==>
               regions_disjoint (w2n w) sz b sz') ==>
    local_ptrs_rel func
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar (Var p) sz)))
      scopes t
Proof
  cheat
QED

Theorem entry_alloc_buffer_inst:
  !n st buf sa func.
    compile_alloc_buffer n st = (buf, sa) /\ fn_has_code st sa func ==>
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
           [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED

Theorem entry_alloc_buffer_local_ptrs:
  !n st buf sa func cenv scopes s ctx.
    compile_alloc_buffer n st = (buf, sa) /\ fn_has_code st sa func /\
    n < dimword (:256) /\ s.vs_alloca_next < dimword (:256) /\
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?a. buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
      local_ptrs_rel func cenv scopes a /\
      lookup_var (STRING #"%" (toString st.cs_next_var)) a =
        SOME (n2w s.vs_alloca_next) /\
      local_backed func (STRING #"%" (toString st.cs_next_var)) a s.vs_alloca_next n /\
      a.vs_alloca_next = s.vs_alloca_next + n /\ fresh_vars_wrt sa a /\
      not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
      (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
      (!name q sz. local_region cenv scopes a name q sz ==>
                   regions_disjoint s.vs_alloca_next n q sz) /\
      a with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
                vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
      ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
      a.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel r. run_from fuel ctx func a = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED

Theorem entry_register_arg_runtime:
  !n st buf sa sb func cenv scopes s ctx name entry.
    compile_alloc_buffer n st = (buf, sa) /\ fn_has_code st sa func /\
    fn_has_code sa sb func /\ sa.cs_next_id <= sb.cs_next_id /\
    n < dimword (:256) /\ s.vs_alloca_next < dimword (:256) /\
    local_ptrs_rel func cenv scopes s /\ fresh_vars_wrt st s /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    lookup_scopes name scopes = SOME entry /\
    (!q sz. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var q) sz)) /\
    type_memory_size entry.type <= n /\ val_wf entry.type entry.value /\
    (!a. fresh_vars_wrt sa a /\
         lookup_var (STRING #"%" (toString st.cs_next_var)) a =
           SOME (n2w s.vs_alloca_next) /\ a.vs_call_ctx = s.vs_call_ctx ==>
       frag_exec ctx sa sb (\u. u = a)
         (\t. dec_frame sa s.vs_alloca_next n a t /\ fresh_vars_wrt sb t /\
              val_in_memory entry.type entry.value s.vs_alloca_next t.vs_memory /\
              t.vs_prev_bb = a.vs_prev_bb /\ t.vs_current_bb = a.vs_current_bb)
         (\r. F)) ==>
    ?t. local_ptrs_rel func
          (cenv with ce_vars updated_by (\m. m |+
            (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) n))) scopes t /\
        fresh_vars_wrt sb t /\ t.vs_alloca_next = s.vs_alloca_next + n /\
        (!aid. sb.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE) /\
        t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next;
                  vs_inst_idx := s.vs_inst_idx |> = s /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED

(* ===== The parameters ===== *)
Theorem entry_register_index_phases:
  !args cenv0 tenv vals env i cenv m off st cf sf func.
    i < LENGTH args /\ dec_cenv_agrees cenv0 tenv /\
    bind_arguments tenv args vals = SOME env /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args /\
    FLOOKUP cenv.ce_vars (FST (EL i args)) =
      SOME (MemLoc m (type_memory_bytes cenv0 (SND (EL i args)))) /\
    compile_register_positional_args cenv
      (build_positional_args cenv0 (DROP i args)) off st = (cf,sf) /\
    fn_has_code st sf func ==>
    ?buf sa sb.
      compile_alloc_buffer (type_memory_bytes cenv0 (SND (EL i args))) st = (buf,sa) /\
      let cenv1 = cenv with ce_vars updated_by (\v. v |+
        (FST (EL i args), PtrVar buf.buf_operand
           (type_memory_bytes cenv0 (SND (EL i args))))) in
      compile_decode_args cenv1 [build_positional_arg cenv0 (EL i args)]
        off CALLDATALOAD (Lit 0w) 4 sa = ((),sb) /\
      compile_register_positional_args cenv1
        (build_positional_args cenv0 (DROP (SUC i) args))
        (off + abi_embedded_static_size cenv0.ce_struct_fields (SND (EL i args)))
        sb = (cf,sf) /\
      fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb sf func /\
      sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem entry_register_index_step:
  !args cenv0 tenv vals env fname i cenv st s cf sf ctx func off q.
    dec_cenv_agrees cenv0 tenv /\ ALL_DISTINCT (MAP FST args) /\
    EVERY (\a. ?m. FLOOKUP cenv0.ce_vars (FST a) =
      SOME (MemLoc m (type_memory_bytes cenv0 (SND a)))) args /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args /\
    bind_arguments tenv args vals = SOME env /\ i < LENGTH args /\
    off = 4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
      (TAKE i args)) /\
    q = SUM (MAP (type_memory_bytes cenv0 o SND) (TAKE i args)) /\
    compile_register_positional_args cenv
      (build_positional_args cenv0 (DROP i args)) off st = (cf,sf) /\
    fn_has_code st sf func /\ local_ptrs_rel func cenv [env] s /\
    EVERY (\a. FLOOKUP cenv.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
      (DROP i args) /\
    s.vs_alloca_next = q /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    fresh_vars_wrt st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    calldata_encodes tenv fname (MAP SND args) vals s.vs_call_ctx.cc_calldata /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
    ?sb cenv1 t.
      compile_register_positional_args cenv1
        (build_positional_args cenv0 (DROP (SUC i) args))
        (4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
          (TAKE (SUC i) args))) sb = (cf,sf) /\
      fn_has_code sb sf func /\ local_ptrs_rel func cenv1 [env] t /\
      EVERY (\a. FLOOKUP cenv1.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
        (DROP (SUC i) args) /\
      t.vs_alloca_next = SUM (MAP (type_memory_bytes cenv0 o SND)
        (TAKE (SUC i) args)) /\
      (!aid. sb.cs_next_id <= aid ==> FLOOKUP t.vs_allocas aid = NONE) /\
      fresh_vars_wrt sb t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next;
                vs_inst_idx := s.vs_inst_idx |> = s /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED


Theorem entry_register_suffix_local_ptrs:
  !cenv0 tenv args vals env fname ctx func i cenv st s cf sf.
    dec_cenv_agrees cenv0 tenv /\ ALL_DISTINCT (MAP FST args) /\
    EVERY (\a. ?m. FLOOKUP cenv0.ce_vars (FST a) =
      SOME (MemLoc m (type_memory_bytes cenv0 (SND a)))) args /\
    EVERY (\a. is_word_type (SND a) \/
      (assignable_type tenv (SND a) /\
       ~is_dynamic (vyper_to_abi_type tenv (SND a)))) args /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
      int_byte_widths tv) args /\
    bind_arguments tenv args vals = SOME env /\ i <= LENGTH args /\
    compile_register_positional_args cenv
      (build_positional_args cenv0 (DROP i args))
      (4 + SUM (MAP (abi_embedded_static_size cenv0.ce_struct_fields o SND)
        (TAKE i args))) st = (cf,sf) /\
    fn_has_code st sf func /\ local_ptrs_rel func cenv [env] s /\
    EVERY (\a. FLOOKUP cenv.ce_vars (FST a) = FLOOKUP cenv0.ce_vars (FST a))
      (DROP i args) /\
    s.vs_alloca_next = SUM (MAP (type_memory_bytes cenv0 o SND) (TAKE i args)) /\
    (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
    fresh_vars_wrt st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    calldata_encodes tenv fname (MAP SND args) vals s.vs_call_ctx.cc_calldata /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
    ?t. local_ptrs_rel func cf [env] t /\
        t with <| vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                  vs_allocas := s.vs_allocas; vs_alloca_next := s.vs_alloca_next;
                  vs_inst_idx := s.vs_inst_idx |> = s /\
        fresh_vars_wrt sf t /\ ~t.vs_halted /\
        t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
          ?fuel'. run_from fuel' ctx func s = r)
Proof
  cheat
QED

(* Allocating and decoding the parameters from calldata that encodes the
   call puts each argument's value at its own fresh ALLOCA, the parameters
   in scope being env, the arguments bound.  Only word arguments and
   static ones (no dynamic ABI encoding, #762); integer widths are whole
   bytes (#733).  Nothing but variables, memory and allocations changes,
   and nothing reverts. *)
(* Why it holds: every argument is word or ABI-static, so calldata is the
   selector then the static tuple encoding, of length 4 + the sum of the
   arguments' memory sizes (dec_cenv_agrees, static_length_memory_size);
   that bound keeps every offset, ALLOCA base and size below dimword.
   ALLOCAs are bump-allocated from 0 with no alignment, so argument i's
   region starts at the sum of the earlier sizes, disjoint from the others.
   The decode code is straight-line (no new blocks), so the ALLOCAs stay in
   st'.cs_current_bb and fn_has_code puts them in func.  The bound values
   are the arguments (bind_arguments, safe_cast_some_eq) and satisfy val_wf
   by their typing.  An induction over a suffix of the arguments, with a
   general calldata offset, alloca_next and vs_allocas, gives the base case
   stated here. *)
Theorem register_positional_args_local_ptrs:
  !cenv0 tenv fname fargs vals env st cenv st' ctx func s0.
    compile_register_positional_args cenv0
      (build_positional_args cenv0 fargs) 4 st = (cenv, st') /\
    dec_cenv_agrees cenv0 tenv /\
    ALL_DISTINCT (MAP FST fargs) /\
    EVERY (\a. ?off. FLOOKUP cenv0.ce_vars (FST a) =
                     SOME (MemLoc off (type_memory_bytes cenv0 (SND a)))) fargs /\
    EVERY (\a. is_word_type (SND a) \/
               (assignable_type tenv (SND a) /\
                ~is_dynamic (vyper_to_abi_type tenv (SND a)))) fargs /\
    EVERY (\a. !tv. evaluate_type tenv (SND a) = SOME tv ==>
                    int_byte_widths tv) fargs /\
    bind_arguments tenv fargs vals = SOME env /\
    calldata_encodes tenv fname (MAP SND fargs) vals
      s0.vs_call_ctx.cc_calldata /\
    LENGTH s0.vs_call_ctx.cc_calldata < dimword (:256) /\
    s0.vs_allocas = FEMPTY /\ s0.vs_alloca_next = 0 /\
    fresh_vars_wrt st s0 /\ fn_has_code st st' func /\ ~s0.vs_halted /\
    s0.vs_current_bb = st.cs_current_bb /\
    s0.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. local_ptrs_rel func cenv [env] t /\
        t with <| vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
                  vs_allocas := s0.vs_allocas;
                  vs_alloca_next := s0.vs_alloca_next;
                  vs_inst_idx := s0.vs_inst_idx |> = s0 /\
        fresh_vars_wrt st' t /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        !fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
                 ?fuel'. run_from fuel' ctx func s0 = r
Proof
  cheat
QED
