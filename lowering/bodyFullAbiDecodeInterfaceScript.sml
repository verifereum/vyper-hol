(* Syntactic interfaces only: no recursive execution premise is proved here.
   The owned quotations reproduce LeafCases:170-200,254-307.  MotiveProbe
   remains unchanged; the independent expansion checks below relate its
   original state to the extra ownership conjuncts in LeafCases. *)
Theory bodyFullAbiDecodeInterface
Ancestors
  bodyFullAbiDecodeMotiveProbe abiBuiltinDecodeSetup

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
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
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

val owned_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
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
     eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\
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

val owned_decoder_post = ``\start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

val owned_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h /\
       h <= LENGTH input_bytes) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

val owned_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^owned_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==>
    (^owned_decoder_post) start finish s G tn``;

(* These are merely the additional owned-state conjuncts in LeafCases. *)
val owned_extras = ``\st s.
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

(* Independent source expansion of the pre-ownership MotiveProbe state. *)
val source_joint_state = ``\st s G tn.
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
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn)``;

val source_joint_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
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
     eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\
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
  (^source_joint_state) start s G tn``;

val source_owned_post = ``\start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       ((^source_joint_state) finish t G' tn' /\ (^owned_extras) finish t) /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

Theorem abi_decode_owned_interface_agrees:
  !finish size.
  ((^owned_decoder_state) st s G tn <=>
    (^source_joint_state) st s G tn /\
    (^owned_extras) st s) /\
  ((^owned_decoder_pre) start finish dst src opc base_op hi d write_start size s G tn <=>
    (^source_joint_pre)
      start finish dst src opc base_op hi d write_start size s G tn /\
    (^owned_extras) start s) /\
  ((^owned_decoder_post) start finish s G tn <=>
    (^source_owned_post) start finish s G tn)
Proof
  simp[GSYM CONJ_ASSOC]
QED

(* Unlike owned pre, guarded pre does not require off<=h.  Every other
   conjunct is retained, and hi is syntactically bounded. *)
val guarded_decoder_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\ (?H. V H) /\
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

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==>
    (^owned_decoder_post) start finish s G tn``;

val bounded_complex_elems_motive = ``\dst src opc base_op hi elems ao vo.
  !env sf pretys pretvs tys tvs live protected start finish s G tn d.
    LIST_REL (abi_decoder_coherent ce env sf) (pretys++tys) (pretvs++tvs) /\
    LENGTH pretys = LENGTH pretvs /\
    elems = abi_decoder_member_infos sf ce tys /\
    ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pretys) /\
    vo = SUM (MAP (type_memory_bytes ce) pretys) /\
    hi <> Lit 0w /\
    (?off h. eval_operand src s = SOME (n2w off) /\
      eval_operand hi s = SOME (n2w h) /\
      off+ao+SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) <= h /\
      h <= LENGTH input_bytes) /\
    compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo start =
      ((),finish) /\
    eval_operand dst s = SOME (n2w d) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d (d+vo)
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn ==>
    (^owned_decoder_post) start finish s G tn``;

val owned_dyn_loop_motive = ``\dst src opc base_op hi ei asz msz ip cnt.
  !env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h.
    abi_decoder_coherent ce env sf ty tv /\
    ei = type_to_abi_dec_info sf ce ty /\
    asz = abi_embedded_static_size ce.ce_struct_fields ty /\
    msz = type_memory_size tv /\ n < dimword (:256) /\ j <= n /\
    hi <> Lit 0w /\
    eval_operand base_op s = SOME (n2w srcbase) /\
    eval_operand src s = SOME (n2w srcoff) /\
    eval_operand hi s = SOME (n2w h) /\
    srcoff + 32 + n * asz <= h /\ h <= LENGTH input_bytes /\
    mem_word_at (srcbase+srcoff) s.vs_memory = n2w n /\
    eval_operand cnt s = SOME (n2w n) /\ op_taint tn cnt = {} /\
    ip = Var counter /\ lookup_var counter s = SOME (n2w cell) /\
    FLOOKUP s.vs_allocas aid = SOME (cell,32) /\
    (?ci cp. MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
      ci.inst_outputs = [cp] /\ ci.inst_id = aid /\
      not_local_ptr ce es.scopes cp) /\
    lo <= cell /\
    (!name b k. local_region ce es.scopes s name b k ==>
      cell+32 <= b \/ b+k <= cell) /\
    aid < start.cs_next_id /\ ptr_covers G tn counter s 32 /\
    op_taint tn ip = {} /\ mem_word_at cell s.vs_memory = n2w j /\
    (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
    cell+32 <= s.vs_alloca_next /\
    (cell+32 <= d \/ d+32+n*msz <= cell) /\
    (cell+32 <= w2n input_word \/
       w2n input_word+LENGTH input_bytes <= cell) /\
    EVERY (\(id,p,b,k,bytes). id <> aid /\ (b+k <= cell \/ cell+32 <= b)) live /\
    EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) protected /\
    compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt
      start = ((),finish) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d d (32+n*msz)
      s G tn ==>
    (^owned_decoder_post) start finish s G tn``;

(* This has open induction premises.  It is not a recursion certificate. *)
val _ = ISPECL [guarded_to_buf_motive, bounded_complex_elems_motive,
  owned_dyn_loop_motive] abiEncoderTheory.compile_abi_decode_to_buf_ind;
val _ = List.app (fn motive =>
  if List.exists (fn v => List.exists (fn n => fst (dest_var v) = n)
    ["env", "sf", "live", "protected"]) (free_vars motive)
  then raise Fail "descent parameters escaped motive quantifiers"
  else ()) [guarded_to_buf_motive, bounded_complex_elems_motive, owned_dyn_loop_motive];

Theorem abi_decode_guarded_primitive_entry:
  !finish.
  (^guarded_to_buf_entry) dst src opc base_op hi (DecPrimWord clamp)
    env sf ty tv live protected start finish s G tn d ==>
  (^owned_to_buf_entry) dst src opc base_op hi (DecPrimWord clamp)
    env sf ty tv live protected start finish s G tn d
Proof
  BETA_TAC >> rpt strip_tac >>
  pure_asm_rewrite_tac[] >>
  metis_tac[arithmeticTheory.LESS_EQ_ADD, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem abi_decode_bounded_root_entry:
  !finish.
  (^owned_to_buf_entry) dst (Lit 0w) opc base_op hi info
    env sf ty tv live protected start finish s G tn d /\ hi <> Lit 0w ==>
  (^guarded_to_buf_entry) dst (Lit 0w) opc base_op hi info
    env sf ty tv live protected start finish s G tn d
Proof
  BETA_TAC >> gen_tac >> strip_tac >>
  `LENGTH input_bytes < dimword (:256)` by decide_tac >>
  `off < dimword (:256) /\ off' < dimword (:256)` by decide_tac >>
  `h < dimword (:256) /\ h' < dimword (:256)` by decide_tac >>
  `off = off'` by
    (qpat_x_assum `eval_operand (Lit 0w) s = SOME (n2w off)` mp_tac >>
     asm_rewrite_tac[] >> simp[wordsTheory.n2w_11]) >>
  `h = h'` by
    (qpat_x_assum `eval_operand hi s = SOME (n2w h)` mp_tac >>
     asm_rewrite_tac[] >> simp[wordsTheory.n2w_11]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* CallerEntry preparation (.13).  These terms describe resources to be
   constructed, NOT extra hypotheses for the frozen expression theorem.
   In particular no bound on the actual length, nor setup success, is
   assumed by caller_setup_pre. *)
val caller_setup_pre = ``\data min_size max_size outsz st ready ops s G tn b data_var.
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
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
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
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
  s.vs_alloca_next+outsz < dimword (:256)``;

val caller_setup_success = ``\st ready ops s G tn b min_size max_size outsz t G' tn'.
  ?output input.
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    FST ops = Var output /\ FST (SND ops) = Var input /\
    eval_operand (SND (SND ops)) t = SOME (n2w (LENGTH input_bytes)) /\
    min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size /\
    (\live protected input_word output_base output_cap output_id.
       (^owned_decoder_state) ready t G' tn')
      [] [] (n2w (b+32)) s.vs_alloca_next outsz
      (abi_builtin_decode_output_site st min_size max_size) /\
    op_prov G' (SND (SND ops)) = NONE /\
    op_taint tn' (FST ops) = {} /\ op_taint tn' (FST (SND ops)) = {} /\
    op_taint tn' (SND (SND ops)) = {} /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))``;

val caller_setup_post = ``\st ready ops s G tn b min_size max_size outsz.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r,G',tn')) /\
    ((?u. r = Abort Revert_abort u) \/
     (?t. r = OK t /\ (^caller_setup_success)
       st ready ops s G tn b min_size max_size outsz t G' tn'))``;

val caller_guarded_root_entry = ``\ready finish ops t G' tn' env sf ty tv outsz b st min_size max_size s.
  (\live protected input output input_word output_base output_cap output_id.
    (^guarded_to_buf_entry) (FST ops) (Lit 0w) MLOAD (FST (SND ops))
      (SND (SND ops)) (type_to_abi_dec_info sf ce ty) env sf ty tv
      live protected ready finish t G' tn' output_base)
    [] [] (THE (case FST (SND ops) of Var x => SOME x | _ => NONE))
    (THE (case FST ops of Var x => SOME x | _ => NONE))
    (n2w (b+32)) s.vs_alloca_next outsz
    (abi_builtin_decode_output_site st min_size max_size)``;
