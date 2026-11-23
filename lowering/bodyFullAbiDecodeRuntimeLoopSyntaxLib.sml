(* Shared term quotations for the fixed-anchor runtime loop. These declare
   no HOL constants and do not depend on the unfinished LoopBody theorem. *)
structure bodyFullAbiDecodeRuntimeLoopSyntaxLib =
struct
open HolKernel boolLib bossLib
open bodyFullAbiDecodeInterfaceTheory abiDecoderLoopSetupTheory abiEncoderTheory
     compileEnvTheory venomInstTheory venomExecSemanticsTheory venomStateTheory
     loweringStateRelDefsTheory wordsTheory listTheory rich_listTheory
     finite_mapTheory arithmeticTheory valueEncodingPropsTheory ptrDisciplineTheory
     abiDecoderCoherenceTheory abiDecoderMemberInfosTheory abiDecoderReentryTheory
     abiDecoderOffsetTheory abiDecoderExecutionTheory

val owned_decoder_state = ``\live protected st s G tn.
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

val frame = ``\anchor s (G:string |-> num # num) tn t Gf tnf.
  !x. not_fresh_at anchor x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)``;

val owned_decoder_post = ``\live protected start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) live protected finish t G' tn' /\
       (^frame) start s G tn t G' tn') \/
     (?t. r = Abort Revert_abort t))``;

val loop_resource = ``\anchor j s G tn.
  (^owned_decoder_state) live protected anchor s G tn /\ allocas_from lo s /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  ptr_covers G tn dst s (32+n*msz) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\
  eval_operand src s = SOME (n2w srcoff) /\
  eval_operand hi s = SOME (n2w h) /\
  srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  mem_word_at (w2n input_word+srcoff) s.vs_memory = n2w n /\
  lookup_var counter s = SOME (n2w cell) /\
  FLOOKUP s.vs_allocas aid = SOME (cell,32) /\ aid < anchor.cs_next_id /\
  ptr_covers G tn counter s 32 /\ mem_word_at cell s.vs_memory = n2w j /\
  cell+32 <= s.vs_alloca_next /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  (?ci cp. MEM ci (fn_insts fn) /\ ci.inst_opcode = ALLOCA /\
    ci.inst_outputs = [cp] /\ ci.inst_id = aid /\ not_local_ptr ce es.scopes cp) /\
  lo <= cell /\
  (!name b k. local_region ce es.scopes s name b k ==>
    cell+32 <= b \/ b+k <= cell) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn src = {} /\ op_taint tn hi = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var counter) = {} /\ j <= n /\
  (w2n input_word+LENGTH input_bytes <= d \/ d+32+n*msz <= w2n input_word) /\
  (cell+32 <= d \/ d+32+n*msz <= cell) /\
  (cell+32 <= w2n input_word \/ w2n input_word+LENGTH input_bytes <= cell) /\
  EVERY (\(id,p,b,k,bytes). id <> aid /\ (b+k <= cell \/ cell+32 <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= cell \/ cell+32 <= a) protected /\
  EVERY (\(id,p,b,k,bytes). id < anchor.cs_next_id /\
    (b+k <= d \/ d+32+n*msz <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+32+n*msz <= a) protected``;

val loop_inv = ``\anchor hdr sin Gin tnin k s G tn.
  (^loop_resource) anchor k s G tn /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  (^frame) anchor sin Gin tnin s G tn``;

(* Pass the tail of the conjunction to the offset check so that both
   expansions retain Interface's original conjunction structure. *)
val decoder_pre = ``\offset_ok live protected start finish dst src opc base_op hi d write_start size s G tn.
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
  base_op = Var input /\ offset_ok src hi s
    (op_prov G src = NONE /\ op_prov G hi = NONE /\
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
     (^owned_decoder_state) live protected start s G tn)``;

val owned_decoder_pre = ``(^decoder_pre) (\src hi s rest.
  (?off h. eval_operand src s = SOME (n2w off) /\
    eval_operand hi s = SOME (n2w h) /\ off <= h /\ h <= LENGTH input_bytes) /\ rest)``;

val guarded_decoder_pre = ``(^decoder_pre) (\src hi s rest.
  (?off h. eval_operand src s = SOME (n2w off) /\
    eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
    h <= LENGTH input_bytes) /\ hi <> Lit 0w /\ rest)``;

val guarded_to_buf_entry = ``\dst src opc base_op hi info env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\ off < dimword (:256) /\
       h <= LENGTH input_bytes /\
       ((?clamp. info = DecPrimWord clamp) ==>
         off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^guarded_decoder_pre) live protected start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn``;

val guarded_to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    (^guarded_to_buf_entry) dst src opc base_op hi info env sf ty tv live protected
      start finish s G tn d ==>
    (^owned_decoder_post) live protected start finish s G tn``;

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
    (^owned_decoder_pre) live protected start finish dst src opc base_op hi d (d+vo)
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn ==>
    (^owned_decoder_post) live protected start finish s G tn``;

val old_loop_entry = ``\dst src opc base_op hi ei asz msz ip cnt
                        env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h.
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
    (^owned_decoder_pre) live protected start finish dst src opc base_op hi d d (32+n*msz)
      s G tn``;

val repaired_loop_entry = ``\dst src opc base_op hi ei asz msz ip cnt
                             env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h.
    (^old_loop_entry) dst src opc base_op hi ei asz msz ip cnt
      env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h /\
    abi_decoder_operand_live start.cs_next_var ip /\ srcbase = w2n input_word``;

val repaired_loop_motive = ``\dst src opc base_op hi ei asz msz ip cnt.
  !env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h.
    (^repaired_loop_entry) dst src opc base_op hi ei asz msz ip cnt
      env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h ==>
    (^owned_decoder_post) live protected start finish s G tn``;

(* The generated induction theorem, rather than the monadic expansion,
   determines the hypotheses of the loop constructor. *)
fun generated_loop_clause motives =
  abiEncoderTheory.compile_abi_decode_to_buf_ind
  |> ISPECL motives |> BETA_RULE |> concl |> dest_imp |> fst |> strip_conj |> List.last;

val loop_clause = generated_loop_clause
  [guarded_to_buf_motive, bounded_complex_elems_motive, repaired_loop_motive];

val loop_ih =
  let
    val (formals, implication) = strip_forall loop_clause
    val (args, _) = strip_abs repaired_loop_motive
  in
    subst (ListPair.mapEq (fn (v,a) => v |-> a) (formals,args))
      (fst (dest_imp implication))
  end;

(* The loop-body interface is closed when used as a conditional hypothesis. *)
val body_statement = snd (dest_abs ``\(s:venom_state).
  abi_decoder_coherent ce env sf ty tv /\
  ei = type_to_abi_dec_info sf ce ty /\
  asz = abi_embedded_static_size ce.ce_struct_fields ty /\
  msz = type_memory_size tv /\ n < dimword (:256) /\ hi <> Lit 0w /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (?H. V H) /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce anchor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  abi_decoder_operand_live anchor.cs_next_var src /\
  abi_decoder_operand_live anchor.cs_next_var hi /\
  abi_decoder_operand_live anchor.cs_next_var (Var dst) /\
  abi_decoder_operand_live anchor.cs_next_var (Var counter) /\
  abi_decoder_operand_live anchor.cs_next_var (Var input) /\
  anchor.cs_next_var <= loop_body.cs_next_var /\ anchor.cs_next_id <= loop_body.cs_next_id /\
  abi_decode_array_element_setup (Var counter) src (Var dst) MLOAD
    (Var input) hi ei asz msz loop_body = ((idx,child_src,child_dst),child) /\
  compile_abi_decode_to_buf child_dst child_src MLOAD (Var input) hi ei child =
    ((),returned) /\
  fn_has_code loop_body child fn /\ fn_has_code child returned fn /\
  idx = Var iv /\ loop_body.cs_next_var <= child.cs_next_var /\
  child.cs_next_var <= returned.cs_next_var /\ ~not_fresh_at returned nv /\
  lookup_block returned.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := returned.cs_current_bb; bb_instructions :=
      returned.cs_current_insts ++
        abi_decode_backedge_insts returned.cs_next_id iv nv (Var counter) hdr|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  (^guarded_to_buf_motive) child_dst child_src MLOAD (Var input) hi ei /\
  (^loop_resource) anchor j s G tn /\ j<n /\ ~s.vs_halted /\
  s.vs_current_bb = loop_body.cs_current_bb /\
  s.vs_inst_idx = LENGTH loop_body.cs_current_insts ==>
  (?t Gf tnf. !H. V H ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) \/
  (?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    (^loop_resource) anchor (SUC j) t Gf tnf /\
    (^frame) anchor s G tn t Gf tnf)``);

val closed_body_statement = list_mk_forall (free_vars body_statement, body_statement);
end
