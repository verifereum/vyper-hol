Theory bodyFullAbiDecodeCallerFull
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeSemantic bodySimFull
  gasOutcomeFullCompose abiBoundaryChecks exprSimProps bodyPtrDefs
  exprSimAbiDecodeEntryLayout exprSimAbiDecodeEntryTyping
  abiEncoderObserver fragGasPath fragGasOriginPtrLoop
  valueEncodingProps valueTypingMemoryProps venomState words finite_map
  exprSimMemDefs loweringPosts exprLowering vyperAST context vyperState
  exprSimAbiGasBridge venomExecSemantics exprOpenFirstOperand exprSimHyps stateRelProj
  bodyFullAbiDecodeCallerCollisionInterface vyperTyping
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs
  markerLib

Theorem abi_decode_caller_pointer_actual[local]:
  ann = ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv <= cap /\ d + cap < dimword (:256) /\
  d + cap <= t.vs_alloca_next /\ out = Var output /\
  lookup_var output t = SOME (n2w d) /\ FLOOKUP G output = SOME (d,cap) /\
  op_taint tn out = {} /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory tv v d mem) ==>
  ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    (Value v) (LocatedValue ann (mk_ptr out LocMemory)) es G tn t /\
  ptr_buf_ok ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]) out G t /\
  vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) es
    (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, vv_store_bound_def,
       post_value_type_def, lowered_value_type_def, expr_type_def, mk_ptr_def,
       read_result_def, return_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> simp[wordsTheory.w2n_n2w] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_REFL,
            arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.ADD_ASSOC]
QED

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H:(bool # 256 word # type_value) list # num list.
    V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
     h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\ write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
    write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^owned_decoder_state) start s G tn``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
       h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

val caller_setup_pre = ``\data min_size max_size outsz st ready ops s G tn b data_var d.
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ (?H. V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H:(bool # 256 word # type_value) list # num list.
    V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz))``;

val caller_setup_success = ``\st ready ops s G tn b min_size max_size outsz t G' tn' d.
  ?output input.
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    FST ops = Var output /\ FST (SND ops) = Var input /\
    eval_operand (SND (SND ops)) t = SOME (n2w (LENGTH input_bytes)) /\
    min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size /\
    (\live protected input_word output_base output_cap output_id.
       (^owned_decoder_state) ready t G' tn')
      [] [] (n2w (b+32)) d outsz
      (abi_builtin_decode_output_site st min_size max_size) /\
    FLOOKUP G' output = SOME (d,outsz) /\
    (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
       SOME (d,outsz)) /\
    op_prov G' (SND (SND ops)) = NONE /\
    op_taint tn' (FST ops) = {} /\ op_taint tn' (FST (SND ops)) = {} /\
    op_taint tn' (SND (SND ops)) = {} /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))``;

val caller_guarded_root_entry = ``\ready finish ops t G' tn' env sf ty tv outsz b st min_size max_size (s:venom_state) d.
  (\live protected input output input_word output_base output_cap output_id.
    (^guarded_to_buf_entry) (FST ops) (Lit 0w) MLOAD (FST (SND ops))
      (SND (SND ops)) (type_to_abi_dec_info sf ce ty) env sf ty tv
      live protected ready finish t G' tn' output_base)
    [] [] (THE (case FST (SND ops) of Var x => SOME x | _ => NONE))
    (THE (case FST ops of Var x => SOME x | _ => NONE))
    (n2w (b+32)) d outsz
    (abi_builtin_decode_output_site st min_size max_size)``;

(* These ML terms are syntax only. All producer parameters are universally
   closed independently of the particular caller being proved below. *)
val caller_input_origin = ``\s (input_word:256 word) output_id.
  (?aid ib isz. aid < output_id /\
    FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
    ib <= w2n input_word /\ w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
  (?name ib isz. local_region ce es.scopes s name ib isz /\
    ib <= w2n input_word /\ w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz)``;

val caller_protected_contained = ``\output_base output_cap (protected:(num # word8 list) list).
  EVERY (\(a,bytes). output_base <= a /\
    a + LENGTH bytes <= output_base + output_cap) protected``;

val caller_output_robust = ``\tv d t tn.
  !v. value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v d t.vs_memory ==>
    !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem``;

val caller_setup_input_origin = ``\st b min_size max_size u.
  (^caller_input_origin) u (n2w (b+32):256 word)
    (abi_builtin_decode_output_site st min_size max_size)``;

val caller_setup_post = ``\st ready ops s G tn b min_size max_size outsz d r G' tn'.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,G',tn')) /\
    (!obs. fn_has_code st ready obs ==> gas_path ctx obs s 0 r) /\
    ((?u. r = Abort Revert_abort u) \/
     (?t. r = OK t /\ (^caller_setup_success)
       st ready ops s G tn b min_size max_size outsz t G' tn' d /\
       (^caller_setup_input_origin) st b min_size max_size t))``;

val caller_guarded_post = ``\start cut s G tn tv d r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    (!obs. fn_has_code start cut obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = cut.cs_current_bb /\
       t.vs_inst_idx = LENGTH cut.cs_current_insts /\
       (^owned_decoder_state) cut t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
       (^caller_input_origin) t input_word output_id /\
       (!i. output_base <= i /\ i < output_base+output_cap /\
         i IN tn'.t_mem ==> i IN tn.t_mem) /\
       (^caller_output_robust) tv d t tn') \/
     (?t. r = Abort Revert_abort t))``;

val caller_full_setup_producer = boolSyntax.list_mk_forall o
  (fn tm => (free_vars tm,tm)) $ ``
  (^caller_setup_pre) data min_size max_size outsz st ready ops s G tn b data_var d /\
  (^caller_setup_input_origin) st b min_size max_size s ==>
  ?r G' tn'. (^caller_setup_post) st ready ops s G tn b min_size max_size outsz d r G' tn'``;

val caller_full_guarded_producer = boolSyntax.list_mk_forall o
  (fn tm => (free_vars tm,tm)) $ ``
  (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
    start cut s G tn d /\
  (^caller_protected_contained) output_base output_cap protected /\
  (^caller_input_origin) s input_word output_id ==>
  ?r G' tn'. (^caller_guarded_post) start cut s G tn tv d r G' tn'``;

val caller_collision = ``\start final.
  start.cs_blocks <> final.cs_blocks /\ start.cs_current_bb = final.cs_current_bb``;

val caller_cut_certificate = ``\start final func ctx s r.
  ?L ids id.
    let obs = frag_relabel_observer start final L ids func id;
        sL = s with vs_current_bb := L
    in
      LENGTH ids = LENGTH start.cs_current_insts /\ L <> final.cs_current_bb /\
      ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) /\
      EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) /\
      frag_gas_free (start_relabel L ids start) (start_swap start L ids final) /\
      fn_has_code (start_relabel L ids start) (start_swap start L ids final) obs /\
      fn_inst_ids_distinct obs /\
      (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
        MEM i (fn_insts func)) /\
      (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
      (!bb. lookup_block final.cs_current_bb obs.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
      ((?t u k. r = OK t /\ ~u.vs_halted /\
         (u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut final /\
         frag_relabel_state L start.cs_current_bb u t /\
         run_from k ctx obs sL = Halt (stop_view u)) \/
       (?t u k. r = Abort Revert_abort t /\
         frag_relabel_state L start.cs_current_bb u t /\
         run_from k ctx obs sL = Abort Revert_abort u))``;

val caller_endpoint_pre = ``\ce env ty tv data start out final limit_st p n bs d ctx func cx es s r.
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) start = (out,final) /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    assignable_type env ty /\ abi_decode_bytes_widths env ty /\
    abi_decoder_operand_live start.cs_next_var data /\
    start.cs_next_var <= limit_st.cs_next_var /\
    final.cs_next_var <= limit_st.cs_next_var /\
    eval_operand data s = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
    abi_builtin_decode_site_resources ctx func start final.cs_next_id
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (LENGTH bs) p d s /\
    cs_extends start final /\ fn_has_code start final func /\
    fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
    s.vs_inst_idx = LENGTH start.cs_current_insts /\
    immutable_alloca_sep func ce cx es s /\
    (!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
      t.vs_current_bb = final.cs_current_bb /\
      t.vs_inst_idx = LENGTH final.cs_current_insts) \/
     (?u. r = Abort Revert_abort u))``;

val caller_endpoint_post = ``\ce env ty tv bs out d start final ctx func cx es s r.
    (?t. r = OK t /\
      abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t) \/
    ((?u. r = Abort Revert_abort u) /\
     ?err. evaluate_abi_decode env ty bs = INR err)``;

val caller_full_endpoint_producer = ``
  !ce env ty tv data start out final limit_st p n bs d ctx func cx es s r.
    (^caller_endpoint_pre) ce env ty tv data start out final limit_st p n bs d ctx func cx es s r /\
    (~((^caller_collision) start final) ==> data <> Label start.cs_current_bb) /\
    ((^caller_collision) start final ==> (^caller_cut_certificate) start final func ctx s r) ==>
    (^caller_endpoint_post) ce env ty tv bs out d start final ctx func cx es s r``;

val caller_endpoint_here_pre = ``\wty wtv r. (^caller_endpoint_pre)
  ce (get_tenv cx) wty wtv data start out final final b n bs d ctx func cx es1 s r``;
val caller_endpoint_here_post = ``\wty wtv r. (^caller_endpoint_post)
  ce (get_tenv cx) wty wtv bs out d start final ctx func cx es1 s r``;

val caller_full_open_entry = ``\fn origin es0 es input_bytes V b data_var d ops ready.
    ((^caller_setup_pre) data min_size max_size cap start ready ops s G tn b data_var d /\
     (^caller_setup_input_origin) start b min_size max_size s) /\
    (!t Gs ts.
      (^caller_setup_success) start ready ops s G tn b min_size max_size cap t Gs ts d /\
      (^caller_setup_input_origin) start b min_size max_size t ==>
      (^caller_guarded_root_entry) ready final ops t Gs ts (get_tenv cx)
        ce.ce_struct_fields wty wtv cap b start min_size max_size s d /\
      (^caller_protected_contained) d cap [] /\
      (^caller_setup_input_origin) start b min_size max_size t) /\
    FST ops = out``;

val caller_full_entry = ``\fn origin es0 es input_bytes V wty wtv min_size max_size cap.
  ?b data_var d ops ready.
    (^caller_full_open_entry) fn origin es0 es input_bytes V b data_var d ops ready``;

val caller_full_context = ``\ewhole info min_size max_size cap
    (V:(bool # 256 word # type_value) list # num list -> bool).
    body_inv (cx_tops cx) ctx ce cx /\ MEM func ctx.ctx_functions /\
    expr_body_pre ce cx env ewhole es /\
    expr_type e = BaseT (BytesT (Dynamic n)) /\
    lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
    lower_abi_decode data info min_size max_size cap start = (out,final) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    fn_has_code start final func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    storage_trace_domain cx st0 es1.storage_trace /\
    (!H. V H ==> expr_post H ctx func ce cx e es sa start s0
      es1 (BytesV bs) data s)``;

val caller_joint_posts = ``\fn origin es0 es input_bytes V wtv min_size max_size cap
                            b d ops ready r0 Gs ts r Gf tnf.
  (^caller_setup_post) start ready ops s G tn b min_size max_size cap d r0 Gs ts /\
  ((?a. r0 = Abort Revert_abort a /\ r = r0 /\ Gf = Gs /\ tnf = ts) \/
   (?u. r0 = OK u /\
     (\live protected input output input_word output_base output_cap output_id.
       (^caller_guarded_post) ready final u Gs ts wtv d r Gf tnf)
         [] [] (THE (case FST (SND ops) of Var x => SOME x | _ => NONE))
         (THE (case FST ops of Var x => SOME x | _ => NONE))
         (n2w (b+32)) d cap (abi_builtin_decode_output_site start min_size max_size)))``;

val caller_full_cut_selector = boolSyntax.list_mk_forall o
  (fn tm => (free_vars tm,tm)) $ ``
    let ewhole = TypeBuiltin ann (AbiDecode unwrap) ty [e];
        wrapped = (unwrap /\ needs_external_call_wrap ty);
        wty = if wrapped then TupleT [ty] else ty;
        wtv = if wrapped then TupleTV [tv] else tv;
        min_size = abi_static_size ce.ce_struct_fields wty;
        max_size = abi_size_bound ce.ce_struct_fields wty;
        cap = type_memory_bytes ce wty;
        info = type_to_abi_dec_info ce.ce_struct_fields ce wty;
        V = \(H:(bool # 256 word # type_value) list # num list). valid_horizon cx st0 H es1.storage_trace
    in
      ((^caller_full_context) ewhole info min_size max_size cap V /\
       (^caller_full_open_entry) func sa es es1 bs V b data_var d ops ready) /\
      (^caller_collision) start final ==>
      ?r0 Gs ts r Gf tnf.
        (^caller_joint_posts) func sa es es1 bs V wtv min_size max_size cap
          b d ops ready r0 Gs ts r Gf tnf /\
        (^caller_cut_certificate) start final func ctx s r``;

val caller_full_hyps = ``
  (^caller_full_setup_producer) /\ (^caller_full_guarded_producer) /\
  (^caller_full_cut_selector) /\ (^caller_full_endpoint_producer) /\
  (^caller_full_context) (TypeBuiltin ann (AbiDecode unwrap) ty [e]) (type_to_abi_dec_info
    ce.ce_struct_fields ce (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else
    ty)) (abi_size_bound ce.ce_struct_fields (if unwrap /\ needs_external_call_wrap ty then TupleT [ty]
    else ty)) (type_memory_bytes ce (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (\(H:(bool # 256 word # type_value) list # num list).
      valid_horizon cx st0 H es1.storage_trace) /\
  (^caller_full_entry) func sa es es1 bs
    (\(H:(bool # 256 word # type_value) list # num list). valid_horizon cx st0 H es1.storage_trace)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))``;

val caller_decode_source = ``bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty
  [expr_type e] [BytesV bs])) (\v. return (Value v))``;

val caller_decode_normal = ``\H (res:eval_result + vyperState$exception) ee G' tn' t.
  ?v. res = INL v /\
  vv_post H ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0 ee v
    (LocatedValue ann (mk_ptr out LocMemory)) t /\
  vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    ee v (LocatedValue ann (mk_ptr out LocMemory)) t /\
  t.vs_current_bb = final.cs_current_bb /\
  t.vs_inst_idx = LENGTH final.cs_current_insts /\
  alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at ((DF : (bool # 256 word # type_value) list # num list -> dead) H)
    lo delta ce cx ee G' tn' t /\
  ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) v (LocatedValue ann
    (mk_ptr out LocMemory)) ee G' tn' t /\
  (!w. v = Value w /\ ~is_word_type (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    /\
    ~is_bytestring_type (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) ==>
    vv_own ce cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) sa final ee v
      (LocatedValue ann (mk_ptr out LocMemory)) t /\
    (!t' p. (LocatedValue ann (mk_ptr out LocMemory)) = LocatedValue t' p ==> p.ptr_location =
      LocMemory)) /\
  (ce.ce_is_ctor /\ vv_location (LocatedValue ann (mk_ptr out LocMemory)) = SOME LocCode ==>
    ?val. read_result cx v ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty
        [e])) = SOME rt /\
        eval_operand (vv_operand (LocatedValue ann (mk_ptr out LocMemory))) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  (!t' op. (LocatedValue ann (mk_ptr out LocMemory)) = StackValue t' op /\ ~is_word_type
    (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) ==>
    ptr_buf_ok ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]) op G' t) /\
  (!t' p. (LocatedValue ann (mk_ptr out LocMemory)) = LocatedValue t' p /\ p.ptr_location = LocMemory
    ==>
    ptr_buf_ok ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]) p.ptr_operand G' t) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G' tn'``;

val caller_decode_exit = ``\(H:(bool # 256 word # type_value) list # num list)
    (res:eval_result + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

(* Keep the stopped-observer run attached to the same answer and ghosts
   as the origin path used by the full simulation. *)
Theorem abi_decode_caller_full_observed:
  (^caller_full_hyps) ==>
  ?res r Gf tnf.
    (!tail. (^caller_decode_source) (es1 with gas_obs := tail) =
      (res, es1 with gas_obs := tail)) /\
    storage_trace_domain cx st0 es1.storage_trace /\
    data <> Label start.cs_current_bb /\
    (!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
          t.vs_inst_idx = LENGTH final.cs_current_insts) \/
     (?a. r = Abort Revert_abort a)) /\
    !H. valid_horizon cx st0 H es1.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tnf) /\
      ((?t. r = OK t /\ (^caller_decode_normal) H res (es1 with gas_obs := []) Gf tnf t) \/
       (exit_result r /\ (^caller_decode_exit) H res (es1 with gas_obs := []) (Gf,tnf) r))
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  qabbrev_tac `V = \(H:(bool # 256 word # type_value) list # num list). valid_horizon cx st0 H es1.storage_trace` >>
  DISCH_THEN (CONJUNCTS_THEN2 (mk_asm "setup")
    (CONJUNCTS_THEN2 (mk_asm "decoder")
      (CONJUNCTS_THEN2 (mk_asm "selector")
        (CONJUNCTS_THEN2 (mk_asm "endpoint")
          (CONJUNCTS_THEN2 (mk_asm "context") assume_tac))))) >>
  qpat_x_assum `?b data_var d ops ready. _`
    (qx_choose_then `b` $ qx_choose_then `data_var` $ qx_choose_then `d` $
     qx_choose_then `ops` $ qx_choose_then `ready` $ mk_asm "entry") >>
  `data <> Label start.cs_current_bb` by
    (asm "entry" (CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN assume_tac) kall_tac) >>
     simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm (mk_asm "interpret"))
    `!r. let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty;
             wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv
         in (^caller_endpoint_here_pre) wty wtv r /\
            ((^caller_collision) start final ==> (^caller_cut_certificate) start final func ctx s r) ==>
            (^caller_endpoint_here_post) wty wtv r`
  >- (PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> qx_gen_tac `r` >>
      DISCH_THEN (CONJUNCTS_THEN2
        (REPEAT_TCL CONJUNCTS_THEN assume_tac) (mk_asm "observation")) >>
      asm "endpoint" (irule o BETA_RULE) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (qexists `final` >> simp[]) >>
      simp[L "observation"] >>
      qexistsl [`data`,`n`,`b`] >> simp[]) >>
  Q_TAC KNOW_TAC `let wrapped = (unwrap /\ needs_external_call_wrap ty);
                     wty = if wrapped then TupleT [ty] else ty;
                     wtv = if wrapped then TupleTV [tv] else tv;
                     min_size = abi_static_size ce.ce_struct_fields wty;
                     max_size = abi_size_bound ce.ce_struct_fields wty;
                     cap = type_memory_bytes ce wty
                 in ?r0 Gs ts r Gf tnf.
                      (^caller_joint_posts) func sa es es1 bs V wtv min_size max_size cap
                        b d ops ready r0 Gs ts r Gf tnf /\
                      ((^caller_collision) start final ==>
                        (^caller_cut_certificate) start final func ctx s r) /\
                      ((^caller_endpoint_here_pre) wty wtv r ==>
                       (^caller_endpoint_here_post) wty wtv r)`
  >- (PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
      Cases_on `start.cs_blocks <> final.cs_blocks /\
                start.cs_current_bb = final.cs_current_bb`
      >- (unabbrev_all_tac >> BETA_TAC >> rule_assum_tac BETA_RULE >>
          qpat_assum `start.cs_blocks <> final.cs_blocks /\
                       start.cs_current_bb = final.cs_current_bb`
            (fn th => PURE_REWRITE_TAC [EQT_INTRO th, boolTheory.IMP_CLAUSES]) >>
          ho_match_mp_tac (Q.SPECL
            [`start.cs_blocks <> final.cs_blocks /\ start.cs_current_bb = final.cs_current_bb`,
             `T`, `data <> Label start.cs_current_bb`]
            abi_decode_caller_collision_selected) >>
          rpt conj_tac
          >- (strip_tac >>
          asm "selector" (irule o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
          asm_x "context" (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
          asm_x "entry" (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
          qpat_x_assum `start.cs_blocks <> final.cs_blocks /\
                       start.cs_current_bb = final.cs_current_bb`
            (CONJUNCTS_THEN assume_tac) >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          qexistsl [`ann`,`data`,`data_var`,`e`,`env`,`n`,`out`] >>
          rpt conj_tac >> first_assum ACCEPT_TAC)
          >- (qx_gen_tac `r` >>
              DISCH_THEN (CONJUNCTS_THEN2 (mk_asm "B")
                (CONJUNCTS_THEN2 kall_tac (mk_asm "S"))) >>
              asm "interpret" (MATCH_MP_TAC o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
              conj_tac >- asm "B" ACCEPT_TAC >>
              asm "S" ACCEPT_TAC) >>
          simp[]) >>
      Q_TAC (fn tm => SUBGOAL_THEN tm (mk_asm "regular" o BETA_RULE o PURE_REWRITE_RULE [LET_THM]))
        `!r. let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty;
                 wtv = if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv
             in (^caller_endpoint_here_pre) wty wtv r ==>
                (^caller_endpoint_here_post) wty wtv r`
      >- (PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> qx_gen_tac `r` >> disch_tac >>
          asm "interpret" (MATCH_MP_TAC o BETA_RULE o PURE_REWRITE_RULE [LET_THM]) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          simp[]) >>
      asm "entry" (CONJUNCTS_THEN2 (mk_asm "setup_pre") $
        CONJUNCTS_THEN2 (mk_asm "handoff") assume_tac) >>
      asm "setup" (qspecl_then [`PG`,`explicit`] (fn producer =>
        asm "setup_pre" (mp_tac o MATCH_MP producer))) >>
      DISCH_THEN (qx_choose_then `r0` $ qx_choose_then `Gs` $ qx_choose_then `ts` $
        (fn post => mk_asm "setup_post" post >>
          (CONJUNCTS_THEN2 kall_tac $ CONJUNCTS_THEN2 kall_tac $
           DISJ_CASES_THEN2
             (qx_choose_then `a` assume_tac)
             (qx_choose_then `u` $ CONJUNCTS_THEN2 (mk_asm "setup_normal") (mk_asm "setup_ok"))) post))
      >- (qexistsl [`r0`,`Gs`,`ts`,`r0`,`Gs`,`ts`] >>
          conj_tac >- (conj_tac >- asm "setup_post" ACCEPT_TAC >>
                        disj1_tac >> qexists `a` >> simp[]) >>
          conj_tac >- simp[] >> asm "regular" MATCH_ACCEPT_TAC) >>
      asm "handoff" (qspecl_then [`u`,`Gs`,`ts`] (fn handoff =>
        asm "setup_ok" (mp_tac o MATCH_MP handoff))) >>
      DISCH_THEN (mk_asm "guarded_pre") >>
      asm "decoder" (qspecl_then [`PG`,`explicit`] (fn producer =>
        asm_x "guarded_pre" (mp_tac o MATCH_MP producer))) >>
      DISCH_THEN (qx_choose_then `r` $ qx_choose_then `Gf` $ qx_choose_then `tnf` $
        mk_asm "guarded_post") >>
      qexistsl [`r0`,`Gs`,`ts`,`r`,`Gf`,`tnf`] >>
      conj_tac >- (conj_tac >- asm "setup_post" ACCEPT_TAC >>
        disj2_tac >> qexists `u` >>
        conj_tac >- asm "setup_normal" ACCEPT_TAC >>
        asm "guarded_post" ACCEPT_TAC) >>
      conj_tac >- simp[] >> asm "regular" MATCH_ACCEPT_TAC) >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  DISCH_THEN (qx_choose_then `r0` $ qx_choose_then `Gs` $ qx_choose_then `ts` $
    qx_choose_then `r` $ qx_choose_then `Gf` $ qx_choose_then `tnf` $
    CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (mk_asm "setup_post") (mk_asm "phase"))
      (CONJUNCTS_THEN2 kall_tac (mk_asm "selected_endpoint"))) >>
  asm_x "context" (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  asm_x "entry" (CONJUNCTS_THEN2 (REPEAT_TCL CONJUNCTS_THEN assume_tac) $
    CONJUNCTS_THEN2 kall_tac assume_tac) >>
  `cs_extends start ready` by
    (drule abiBuiltinDecodeSetupTheory.abi_builtin_decode_setup_shape >>
     strip_tac >> irule abiEncoderChildContextTheory.abi_encoder_straight_extends >>
     simp[]) >>
  `cs_extends ready final` by
    (drule abiBuiltinDecodeCorrectTheory.lower_abi_decode_setup_trace >>
     simp[pairTheory.PAIR_EQ] >> strip_tac >>
     drule abiDecoderAppendTheory.cs_extends_abi_decode >> simp[]) >>
  `cs_extends start final` by
    (drule exprSimAbiDecodeObliviousTheory.lower_abi_decode_frag_facts >> simp[]) >>
  `start.cs_next_var <= final.cs_next_var` by
    (drule abiBuiltinDecodeCorrectTheory.lower_abi_decode_setup_trace >>
     simp[pairTheory.PAIR_EQ] >> strip_tac >>
     drule abiBuiltinDecodeSetupTheory.abi_builtin_decode_setup_shape >> strip_tac >>
     drule abiDecoderCountersTheory.abi_decoder_variable_counter >> decide_tac) >>
  `abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
      (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)` by
    (drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_coherent >> strip_tac >>
     drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >> strip_tac >>
     `evaluate_type (get_tenv cx)
        (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) =
        SOME (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)` by
       simp[exprSimAbiDecodeEntryTypingTheory.abi_decode_wrapped_type] >>
     fs[abiDecoderCoherenceTheory.abi_decoder_header_def]) >>
  drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_assignable >> strip_tac >>
  drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_widths >> strip_tac >>
  qpat_assum `?H. V H` (qx_choose_then `hh` assume_tac) >>
  `expr_post hh ctx func ce cx e es sa start s0 es1 (BytesV bs) data s` by
    (qpat_assum `!H. V H ==> expr_post H ctx func ce cx e es sa start s0 es1 (BytesV bs) data s`
       (qspec_then `hh` mp_tac) >> simp[]) >>
  `stmt_state_rel hh ctx func ce cx es1 s` by
    (drule exprSimWordArgsTheory.expr_post_state >> simp[]) >>
  `immutable_alloca_sep func ce cx es1 s` by
    (qpat_assum `stmt_state_rel hh ctx func ce cx es1 s`
       (mp_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def]) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))` by
    (`IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
       (qpat_assum `expr_body_pre ce cx _ (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es`
          (mp_tac o MATCH_MP expr_body_pre_type_builtin_head) >>
        disch_then (ACCEPT_TAC o MATCH_MP expr_body_pre_type_evaluates)) >>
     qpat_assum `expr_type e = BaseT (BytesT (Dynamic n))` SUBST1_TAC >>
     qpat_x_assum `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `~is_word_type (expr_type e)` by simp[compileEnvTheory.is_word_type_def] >>
  drule_all exprSimAbiDecodeResourcesTheory.abi_decode_caller_resources >>
  disch_then (qx_choose_then `p` (qx_choose_then `d'`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `p = b /\ d' = d` by
    (qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ p d' s`
       (mp_tac o REWRITE_RULE [exprSimAbiDecodeBuiltinTheory.abi_builtin_decode_site_resources_def]) >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     conj_tac
     >- (`s.vs_alloca_next < dimword (:256)` by
           (qpat_assum `stmt_state_rel hh ctx func ce cx es1 s`
              (ACCEPT_TAC o MATCH_MP exprLoweringPropsTheory.alloca_room_next_lt o
               MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room)) >>
         `p < dimword (:256) /\ b < dimword (:256)` by (simp[]) >>
         `n2w p = (n2w b : 256 word)` by
           (qpat_assum `eval_operand data s = SOME (n2w p)` mp_tac >>
            qpat_assum `eval_operand data s = SOME (n2w b)`
              (fn th => rewrite_tac[th]) >> simp[]) >>
         pop_assum mp_tac >> simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
     qpat_assum `(FLOOKUP s.vs_allocas _ = NONE /\ d = _) \/ _`
       mp_tac >>
     qpat_assum `(FLOOKUP s.vs_allocas _ = NONE /\ d' = _) \/ _`
       (DISJ_CASES_THEN2
         (CONJUNCTS_THEN2 (fn th => PURE_REWRITE_TAC [th])
                          (fn th => PURE_REWRITE_TAC [th]))
         (fn th => PURE_REWRITE_TAC [th])) >>
     simp[NoAsms, pairTheory.PAIR_EQ]) >>
  qpat_x_assum `p = b` SUBST_ALL_TAC >>
  qpat_x_assum `d' = d` SUBST_ALL_TAC >>
  asm_x "setup_post" (CONJUNCTS_THEN2 (mk_asm "setup_path") $
    CONJUNCTS_THEN2 (mk_asm "setup_obs") (mk_asm "setup_result")) >>
  asm_x "phase" (DISJ_CASES_THEN2
    (qx_choose_then `a` $ REPEAT_TCL CONJUNCTS_THEN assume_tac)
    (qx_choose_then `u` $ CONJUNCTS_THEN2 (mk_asm "setup_normal") $
      CONJUNCTS_THEN2 (mk_asm "dec_path") $
      CONJUNCTS_THEN2 (mk_asm "dec_obs") (mk_asm "dec_result")))
  >- suspend "setup_abort" >>
  Q_TAC (fn tm => SUBGOAL_THEN tm (mk_asm "joint_path"))
    `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
                 (s,G,tn) [] (r,Gf,tnf)`
  >- (rpt strip_tac >>
     `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gs,ts)` by
       (asm "setup_normal" (SUBST1_TAC o SYM) >> simp[L "setup_path"]) >>
     `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gs,ts) [] (r,Gf,tnf)` by
       simp[L "dec_path"] >>
     drule_all gas_origin_ptr_path_trans >> simp[]) >>
  `!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r` by
    (rpt strip_tac >> qspecl_then [`start`,`ready`,`final`,`obs`] mp_tac
       fragExecTheory.fn_has_code_split >> simp[] >> strip_tac >>
     `gas_path ctx obs s 0 (OK u)` by
       (asm "setup_normal" (SUBST1_TAC o SYM) >> simp[L "setup_obs"]) >>
     `gas_path ctx obs u 0 r` by simp[L "dec_obs"] >>
     drule_all gas_path_then >> simp[]) >>
  asm_x "dec_result" (DISJ_CASES_THEN2
    (qx_choose_then `t` $ REPEAT_TCL CONJUNCTS_THEN assume_tac)
    (qx_choose_then `a` assume_tac))
  >- suspend "normal_post" >> suspend "decoder_abort"
QED

Resume abi_decode_caller_full_observed[normal_post]:
  Q_TAC (fn tm => SUBGOAL_THEN tm (mk_asm "control"))
    `(?z. r = OK z /\ ~z.vs_halted /\
        z.vs_current_bb = final.cs_current_bb /\ z.vs_inst_idx = LENGTH final.cs_current_insts) \/
     (?z. r = Abort Revert_abort z)`
  >- (disj1_tac >> qexists `t` >> simp[]) >>
  Q_TAC KNOW_TAC
    `(?z. r = OK z /\ abi_decode_immutable_success ce (get_tenv cx)
       (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
       (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)
       bs out d start final ctx func cx es1 s z) \/
     ((?z. r = Abort Revert_abort z) /\ ?err. evaluate_abi_decode (get_tenv cx)
       (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) bs = INR err)`
  >- (asm "selected_endpoint" MATCH_MP_TAC >>
      rpt (conj_tac >- simp[L "control"]) >> simp[L "control"]) >>
  DISCH_THEN (DISJ_CASES_THEN2
    (qx_choose_then `z` (CONJUNCTS_THEN2 (mk_asm "semantic_normal") assume_tac))
    (CONJUNCTS_THEN2 (qx_choose_then `z` assume_tac) kall_tac))
  >- (`z = t` by
        (asm "semantic_normal" mp_tac >> simp[]) >>
      qpat_x_assum `z = t` SUBST_ALL_TAC >>
      asm_x "setup" kall_tac >> asm_x "decoder" kall_tac >>
      asm_x "selector" kall_tac >> asm_x "endpoint" kall_tac >>
      drule_all abi_decode_body_caller_success_horizons >>
      disch_then (qx_choose_then `v` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
      asm_x "setup_result" (DISJ_CASES_THEN2
        (qx_choose_then `z` mp_tac)
        (qx_choose_then `z` $ CONJUNCTS_THEN2 assume_tac (mk_asm "setup_success")))
      >- simp[L "setup_normal"] >>
      `z = u` by
        (asm "setup_normal" (fn hu =>
           qpat_assum `r0 = OK z` (mp_tac o REWRITE_RULE [hu])) >>
         simp[NoAsms]) >>
      qpat_x_assum `z = u` SUBST_ALL_TAC >>
      asm_x "setup_success" (CONJUNCTS_THEN2
        (qx_choose_then `output` $ qx_choose_then `input_var` $
          REPEAT_TCL CONJUNCTS_THEN assume_tac) kall_tac) >>
      `out = Var output` by
        (qpat_assum `FST ops = out` (SUBST1_TAC o SYM) >>
         qpat_assum `FST ops = Var output` ACCEPT_TAC) >>
      qpat_assum `!x. not_fresh_at ready x ==> lookup_var x t = lookup_var x u /\ _`
        (qspec_then `output` (fn th =>
          qpat_assum `not_fresh_at ready output`
            (REPEAT_TCL CONJUNCTS_THEN assume_tac o MATCH_MP th))) >>
      `FLOOKUP Gf output = SOME (d,type_memory_bytes ce
        (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))` by simp[] >>
      `op_taint tnf out = {}` by
        (qpat_assum `out = Var output` SUBST1_TAC >>
         qpat_assum `op_taint tnf (Var output) = op_taint ts (Var output)` SUBST1_TAC >>
         qpat_assum `FST ops = Var output` (fn h =>
           qpat_assum `op_taint ts (FST ops) = {}`
             (ACCEPT_TAC o PURE_REWRITE_RULE [h]))) >>
      `lookup_var output t = SOME (n2w d)` by
        (qpat_assum `FST ops = Var output` (fn h =>
           qpat_assum `lookup_var (THE (case FST ops of _ => _)) t = SOME (n2w d)`
             (mp_tac o REWRITE_RULE [h])) >> simp[NoAsms]) >>
      `stmt_state_rel hh ctx func ce cx es1 t` by simp[] >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
        (qpat_assum `stmt_state_rel hh ctx func ce cx es1 t`
           (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
      `alloca_inv t` by
        (qpat_assum `stmt_state_rel hh ctx func ce cx es1 t`
           (ACCEPT_TAC o CONJUNCT2 o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
      `d + type_memory_bytes ce
        (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) <= t.vs_alloca_next` by
        (drule_all allocaSiteResourceTheory.alloca_site_registered_below >> simp[]) >>
      `ann = ty` by
        (drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_target >> simp[]) >>
      `abi_decode_root_metadata ce (get_tenv cx)` by
        (irule exprSimAbiDecodeEntryMetadataTheory.abi_decode_root_metadata_inv >>
         qexistsl [`env`, `es`] >> fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
      `type_memory_bytes ce ty = type_memory_size tv` by
        (irule abi_decode_descended_memory_size >>
         qexistsl [`get_tenv cx`, `get_tenv cx`] >> simp[]) >>
      `type_memory_size tv <= type_memory_bytes ce
        (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
        simp[abiDecodeUnwrapCaseTheory.abi_decode_output_size] >>
      qabbrev_tac `wrapped = (unwrap /\ needs_external_call_wrap ty)` >>
      `evaluate_type (get_tenv cx) (if wrapped then TupleT [ty] else ty) =
       SOME (if wrapped then TupleTV [tv] else tv)` by
        simp[Abbr `wrapped`, exprSimAbiDecodeEntryTypingTheory.abi_decode_wrapped_type] >>
      `evaluate_abi_decode (get_tenv cx) (if wrapped then TupleT [ty] else ty) bs =
       INL (if wrapped then ArrayV (TupleV [v]) else v)` by
        (qpat_assum `evaluate_type_builtin cx (AbiDecode unwrap) ty _ _ = INL v`
           (mp_tac o MATCH_MP (iffLR abiValidBytesUnwrapTheory.abi_source_decode_wrapping_iff)) >>
         simp[Abbr `wrapped`]) >>
      `val_wf tv v /\ val_in_memory tv v d t.vs_memory /\
       (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==> val_in_memory tv v d mem)` by
        (qpat_assum `abi_decode_immutable_success ce (get_tenv cx) _ _ bs out d start final ctx func cx es1 s t`
           (assume_tac o CONJUNCT1 o REWRITE_RULE
             [exprSimAbiDecodeImmutableOutcomeTheory.abi_decode_immutable_success_def]) >>
         drule exprSimAbiDecodeValueFrameTheory.abi_decode_success_value >>
         disch_then (qx_choose_then `value` $ REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
         `value = if wrapped then ArrayV (TupleV [v]) else v` by
           (qpat_assum `evaluate_abi_decode (get_tenv cx) (if wrapped then TupleT [ty] else ty) bs =
               INL (if wrapped then ArrayV (TupleV [v]) else v)` (fn h =>
              qpat_assum `evaluate_abi_decode _ _ bs = INL value`
                (mp_tac o PURE_REWRITE_RULE [h])) >> simp[NoAsms, EQ_SYM_EQ]) >>
         qpat_x_assum `value = _` SUBST_ALL_TAC >>
         drule_all vyperTypeABITheory.evaluate_abi_decode_well_typed >>
         disch_then (fn th => assume_tac th >>
           assume_tac (MATCH_MP (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) th)) >>
         qpat_assum `!x. value_has_type (if wrapped then TupleTV [tv] else tv) x /\ _ ==> _`
           (qspec_then `if wrapped then ArrayV (TupleV [v]) else v` mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `val_wf (if wrapped then TupleTV [tv] else tv) _` mp_tac >>
         qpat_assum `val_in_memory (if wrapped then TupleTV [tv] else tv) _ d t.vs_memory` mp_tac >>
         Cases_on `wrapped` >>
         simp[NoAsms, valueEncodingDefsTheory.val_wf_def, val_in_memory_singleton_tuple] >>
         rpt strip_tac >> simp[]) >>
      `ptr_vv_ok cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
         (Value v) (LocatedValue ann (mk_ptr out LocMemory)) es1 Gf tnf t /\
       ptr_buf_ok ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]) out Gf t /\
       vv_store_bound cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
         (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) es1
         (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t` by
        (irule abi_decode_caller_pointer_actual >> simp[]) >>
      `sa.cs_next_id <= start.cs_next_id` by
        (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
      drule exprSimAbiDecodeSetupExecTheory.abi_decode_output_site_interval >> strip_tac >>
      `d < dimword (:256)` by simp[] >>
      qabbrev_tac `cap = type_memory_bytes ce (if wrapped then TupleT [ty] else ty)` >>
      `val_footprint tv v <= cap` by
        (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `type_memory_size tv` >>
         simp[val_footprint_le]) >>
      `vv_own ce cx (post_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
         sa final es1 (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t` by
        ((simp[vv_own_def, post_value_type_def, expr_type_def, mk_ptr_def, read_result_def,
              return_def, eval_operand_def, w2n_n2w] >>
         disj1_tac >>
         qexistsl [`abi_builtin_decode_output_site start
           (abi_static_size ce.ce_struct_fields (if wrapped then TupleT [ty] else ty))
           (abi_size_bound ce.ce_struct_fields (if wrapped then TupleT [ty] else ty))`,
           `d`, `cap`] >> simp[] >> (gvs[]))) >>
      qexistsl [`INL (Value v)`, `r`, `Gf`, `tnf`] >>
      conj_tac >- simp[lift_sum_def, bind_def, return_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- asm "control" ACCEPT_TAC >>
      qx_gen_tac `H` >> strip_tac >>
      `V H` by fs[Abbr `V`] >>
      conj_tac >- simp[L "joint_path"] >>
      disj1_tac >> qexists `t` >>
      conj_tac >- asm "semantic_normal" ACCEPT_TAC >>
      qexists `Value v` >>
      simp[exprSimSubscriptArrayComposeTheory.vv_post_final_gas, vv_location_def] >>
      conj_tac >-
        ((qpat_assum `vv_store_bound cx _ _ es1 (Value v) _ t` mp_tac >>
         simp[NoAsms, vv_store_bound_def, post_value_type_def, read_result_def, return_def] >> (simp[]))) >>
      conj_tac >-
        ((`ghost_inv_at (DF H) lo delta ce cx es1 Gf tnf t` by
           (qpat_assum `!h. V h ==> stmt_state_rel h ctx func ce cx es1 t /\
                ghost_inv_at (DF h) lo delta ce cx es1 Gf tnf t /\ _`
              (qspec_then `H` mp_tac) >> simp[]) >>
         qpat_assum `ghost_inv_at (DF H) lo delta ce cx es1 Gf tnf t` mp_tac >>
         simp[NoAsms, ghost_inv_at_def] >> (metis_tac[NoAsms, ghost_inv_at_def]))) >>
      conj_tac >-
        (qpat_assum `ptr_vv_ok cx _ (Value v) _ es1 Gf tnf t` mp_tac >>
         simp[NoAsms, ptr_vv_ok_def, post_value_type_def, read_result_def,
              return_def, mk_ptr_def, expr_type_def] >>
         qpat_assum `out = Var output` SUBST1_TAC >> simp[]) >>
      conj_tac >-
        (qpat_assum `vv_own ce cx _ sa final es1 (Value v) _ t` mp_tac >>
         simp[NoAsms, vv_own_def, post_value_type_def, read_result_def,
              return_def, mk_ptr_def, expr_type_def] >>
         qpat_assum `out = Var output` SUBST1_TAC >> simp[]) >>
      qpat_assum `ptr_buf_ok ce (TypeBuiltin ann (AbiDecode unwrap) ty [e]) out Gf t` mp_tac >>
      qpat_assum `out = Var output` SUBST1_TAC >>
      qpat_assum `ann = ty` SUBST1_TAC >> simp[mk_ptr_def]) >>
  qpat_x_assum `r = Abort Revert_abort z` mp_tac >> simp[]
QED

(* Both rejection cases interpret the selected Revert and keep its ghosts. *)
val caller_revert_post =
  (Q_TAC KNOW_TAC
     `?err. evaluate_abi_decode (get_tenv cx)
        (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) bs = INR err`
   >- (asm "selected_endpoint" mp_tac >> simp[]) >>
   DISCH_THEN (qx_choose_then `err` assume_tac) >>
   `evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] =
      INR (RuntimeError err)` by
     (irule (cj 1 exprSimAbiDecodeRejectTheory.abi_decode_builtin_reject) >> simp[]) >>
   qexistsl [`INR (Error (RuntimeError err))`, `r`, `Gf`, `tnf`] >>
   conj_tac >- simp[lift_sum_def, bind_def, vyperStateTheory.raise_def] >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac >- (disj2_tac >> qexists `a` >> first_assum ACCEPT_TAC) >>
   qx_gen_tac `H` >> disch_tac >>
   `V H` by fs[Abbr `V`] >>
   conj_tac >- simp[L "joint_path"] >>
   disj2_tac >>
   simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def,
        exprSimDefsTheory.halt_exit_def]);

Resume abi_decode_caller_full_observed[decoder_abort]:
  caller_revert_post
QED

Resume abi_decode_caller_full_observed[setup_abort]:
  qpat_assum `r0 = Abort Revert_abort a` (fn th =>
    qpat_assum `r = r0` (assume_tac o PURE_REWRITE_RULE [th])) >>
  asm "setup_path" (fn th =>
    qpat_assum `r = r0` (fn hr =>
      qpat_assum `Gf = Gs` (fn hG =>
        qpat_assum `tnf = ts` (fn ht =>
          mk_asm "joint_path" (PURE_REWRITE_RULE (map SYM [hr,hG,ht]) th))))) >>
  `!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r` by
    (qx_gen_tac `obs` >> disch_tac >>
     `fn_has_code start ready obs` by
       (irule (cj 1 fragExecTheory.fn_has_code_split) >>
        conj_tac >- first_assum ACCEPT_TAC >> qexists `final` >> simp[]) >>
     qpat_assum `r = r0` SUBST1_TAC >>
     asm "setup_obs" (qspec_then `obs` mp_tac) >> simp[]) >>
  caller_revert_post
QED

Finalise abi_decode_caller_full_observed

Theorem abi_decode_caller_full_conditional:
  (^caller_full_hyps) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (^caller_decode_source) (es1,s,G,tn) (^caller_decode_normal) (^caller_decode_exit)
Proof
  disch_then (strip_assume_tac o MATCH_MP abi_decode_caller_full_observed) >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gf`, `es1`, `[]`, `r`, `res`, `tnf`] >> simp[]
QED
