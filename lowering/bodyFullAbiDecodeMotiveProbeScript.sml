(* An interface checkpoint, NOT a recursive execution certificate.
   The ML quotations below expand to HOL conjunctions; they introduce no
   constants, axioms or definitions.  Runtime preservation is still open. *)
Theory bodyFullAbiDecodeMotiveProbe
Ancestors
  bodyFullAbiDecodeDecoderBase abiDecoderCoherence abiDecoderMemberInfos
  abiDecoderRecursiveArray abiEncoder abiDecodePtrMemberFrame
  exprSimAbiDecodeEntryCoherence exprSimAbiDecodeBodyEntry
  bodyFullAllocGeneric allocaHistory gasOutcomeFull
  exprSimAbiDecodeArrayInvariant finite_map list rich_list pair words

(* All enclosing scratch is named by (allocation id, pointer variable,
   base address, size, actual contents).  Coverage alone is insufficient.
   'protected' contains completed output prefixes; it is distinct from live
   scratch and need not be a separate allocation.  Neither family includes
   the current loop's mutable counter while that loop is running. *)
val decoder_joint_state = ``\st s G tn.
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
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next)
    live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes)
    protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn)``;

(* The frame's unmodified operands are precisely those older than this
   compilation entry.  Child allocation sites may already occur in s; no
   universal freshness premise is imposed.  The live site ids must be
   outside the child's allocated interval -- a descent obligation. *)
val decoder_joint_pre = ``\start finish dst src opc base_op hi d write_start size s G tn.
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved ce start /\
  (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (write_start-d+size) /\
     FLOOKUP G p = SOME (output_base,output_cap)) /\
  base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\
     eval_operand hi s = SOME (n2w h) /\ off <= h /\
     h <= LENGTH input_bytes) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= write_start /\
  write_start+size <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= write_start \/
     write_start+size <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < start.cs_next_id /\
    (b+k <= write_start \/ write_start+size <= b)) live /\
  EVERY (\(a,bytes).
    a+LENGTH bytes <= write_start \/ write_start+size <= a) protected /\
  (^decoder_joint_state) start s G tn``;

(* r,G',tn' precede H.  Even rejection has a checked path with these same
   ghosts.  Successful runs preserve actual scratch and prefix contents,
   not a quantified arbitrary Frame predicate. *)
val decoder_joint_post = ``\start finish s G tn.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^decoder_joint_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))) \/
     (?t. r = Abort Revert_abort t))``;

val to_buf_motive = ``\dst src opc base_op hi info.
  !env sf ty tv live protected start finish s G tn d.
    abi_decoder_coherent ce env sf ty tv /\
    info = type_to_abi_dec_info sf ce ty /\
    (?off h. eval_operand src s = SOME (n2w off) /\
       eval_operand hi s = SOME (n2w h) /\
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h) /\
    compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
    (^decoder_joint_pre) start finish dst src opc base_op hi d d
      (type_memory_size tv) s G tn ==>
    (^decoder_joint_post) start finish s G tn``;

(* Prefix type lists determine BOTH offsets; remaining types and values
   descend together.  This is valid for tuple, fixed-array and struct views. *)
val complex_elems_motive = ``\dst src opc base_op hi elems ao vo.
  !env sf pretys pretvs tys tvs live protected start finish s G tn d.
    LIST_REL (abi_decoder_coherent ce env sf) (pretys++tys) (pretvs++tvs) /\
    LENGTH pretys = LENGTH pretvs /\
    elems = abi_decoder_member_infos sf ce tys /\
    ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pretys) /\
    vo = SUM (MAP (type_memory_bytes ce) pretys) /\
    compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo start =
      ((),finish) /\
    eval_operand dst s = SOME (n2w d) /\
    (^decoder_joint_pre) start finish dst src opc base_op hi d (d+vo)
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn ==>
    (^decoder_joint_post) start finish s G tn``;

(* Compiler induction visits the body ONCE.  Runtime induction must quantify
   j and preserve this loop's cell around each nested child; on the backedge
   the cell changes from j to SUC j.  It must not be in live for the whole
   loop.  The source count is reloaded at every header. *)
val dyn_loop_motive = ``\dst src opc base_op hi ei asz msz ip cnt.
  !env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff.
    abi_decoder_coherent ce env sf ty tv /\
    ei = type_to_abi_dec_info sf ce ty /\
    asz = abi_embedded_static_size ce.ce_struct_fields ty /\
    msz = type_memory_size tv /\ n < dimword (:256) /\ j <= n /\
    eval_operand base_op s = SOME (n2w srcbase) /\
    eval_operand src s = SOME (n2w srcoff) /\
    mem_word_at (srcbase+srcoff) s.vs_memory = n2w n /\
    eval_operand cnt s = SOME (n2w n) /\ op_taint tn cnt = {} /\
    ip = Var counter /\ lookup_var counter s = SOME (n2w cell) /\
    FLOOKUP s.vs_allocas aid = SOME (cell,32) /\
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
    (^decoder_joint_pre) start finish dst src opc base_op hi d d (32+n*msz)
      s G tn ==>
    (^decoder_joint_post) start finish s G tn``;

(* Typecheck all three arguments against the ACTUAL generated mutual
   principle.  This unnamed instantiation is an interface check only; no
   theorem is exported and no induction premise is claimed discharged. *)
val _ = ISPECL [to_buf_motive, complex_elems_motive, dyn_loop_motive]
  compile_abi_decode_to_buf_ind;

val _ = List.app (fn motive =>
  if List.exists (fn v => List.exists (fn n => fst (dest_var v) = n)
    ["env", "sf", "live", "protected"]) (free_vars motive)
  then raise Fail "descent parameters escaped motive quantifiers"
  else ()) [to_buf_motive, complex_elems_motive, dyn_loop_motive];

(* Checked struct adapter: the compiler's sf deletion and typing's env
   deletion must occur together.  Neither can be left at its root value. *)
Theorem motive_struct_descent[local]:
  abi_decoder_coherent ce env sf (StructT nsid) atv ==>
  ?args fields tvs.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP (FST o SND) fields = MAP SND args /\
    LIST_REL (abi_decoder_coherent ce (env \\ nsid)
      (sf \\ nsid_to_string nsid)) (MAP (FST o SND) fields) tvs /\
    type_to_abi_dec_info sf ce (StructT nsid) =
      DecComplex (EXISTS (is_abi_dynamic ce.ce_struct_fields) (MAP SND args))
        (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))
Proof
  strip_tac >> gvs[abi_decoder_coherent_struct_iff] >>
  qexists_tac `tvs` >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
  drule abi_decoder_struct_infos >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
QED

(* Checked member step: exact head/tail typing and the simultaneous offset
   advance needed at abiEncoder:607 and :610. *)
Theorem motive_member_descent[local]:
  LIST_REL (abi_decoder_coherent ce env sf) (pre++ty::tys) (prev++tv::tvs) /\
  LENGTH pre = LENGTH prev ==>
  abi_decoder_coherent ce env sf ty tv /\
  LIST_REL (abi_decoder_coherent ce env sf)
    (pre++[ty]++tys) (prev++[tv]++tvs) /\
  SUM (MAP (type_memory_bytes ce) (pre++[ty])) =
    SUM (MAP (type_memory_bytes ce) pre) + type_memory_bytes ce ty /\
  SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) (pre++[ty])) =
    SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre) +
      abi_embedded_static_size ce.ce_struct_fields ty
Proof
  strip_tac >> gvs[LIST_REL_APPEND_EQ, SUM_APPEND]
QED

(* Checked nested-loop adaptation.  The current outer cell is snapshotted
   into the child's live family, not presumed fresh at the inner site. *)
Theorem motive_nested_counter_push[local]:
  EVERY (\(aid,p,b,k,bytes). aid < st.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    k = LENGTH bytes /\ mem_bytes_at b k s.vs_memory = bytes) live /\
  st.cs_next_id <= child.cs_next_id /\
  FLOOKUP s.vs_allocas id = SOME (cell,32) /\ id < child.cs_next_id /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 ==>
  EVERY (\(aid,p,b,k,bytes). aid < child.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    k = LENGTH bytes /\ mem_bytes_at b k s.vs_memory = bytes)
    ((id,counter,cell,32,mem_bytes_at cell 32 s.vs_memory)::live)
Proof
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

(* Compiler-body induction cannot discharge this runtime backedge by itself.
   This checked arithmetic substitution is all that follows without a
   preservation proof for the child, the header and the counter store. *)
Theorem motive_counter_backedge[local]:
  j < n /\ n < dimword (:256) ==>
  SUC j <= n /\ (n2w j : 256 word) + 1w = n2w (SUC j)
Proof
  simp[arithmeticTheory.ADD1, wordsTheory.word_add_n2w] >> decide_tac
QED

(* Exact residual goals, checked as HOL terms, NOT asserted as theorems.
   The finite source/code entry mapping is lower_abi_decode_setup together
   with abi_builtin_decode_setup_trace/shape.  Typing entry is the existing
   abi_decode_body_wrapped_coherent; it chooses env=get_tenv cx and
   sf=ce.ce_struct_fields.  Runtime entry below still needs a joint setup
   proof carrying the input window, output allocation and all-H ghosts. *)
val caller_entry_goal = ``
  (\live protected. (^decoder_joint_pre) ready compile_last (FST ops) (Lit 0w)
    MLOAD (FST (SND ops)) (SND (SND ops)) output_base output_base
    (type_memory_size tv) t G' tn') [] []``;

(* At abiEncoder:607 substitute the selected type/value and actual child
   operands; at :610 keep dst/src but append the head to BOTH prefixes.
   motive_struct_descent gives env\\nsid and sf\\string together before
   either call; motive_member_descent supplies the head and tail types. *)
val member_child_entry_goal = ``
  (^decoder_joint_pre) child_start child_finish child_dst child_src MLOAD
    base_op hi (d+vo) (d+vo) (type_memory_size tv) u Gu tnu``;
val member_tail_entry_goal = ``
  (^decoder_joint_pre) child_finish compile_last dst src MLOAD base_op hi d
    (d+vo+type_memory_bytes ce ty)
    (SUM (MAP (type_memory_bytes ce) tys)) t G_after tnt``;

(* Runtime descent at abiEncoder:643 must push the OUTER counter snapshot
   and protect completed elements.  Crucially live/protected are universally
   quantified INSIDE all three motives, so the IH accepts these instances.
   A nested dynamic element retains env,sf and decreases the coherent type;
   abi_decoder_coherent_array_iff applies at both the outer and inner levels.
   The current counter id is older than child_start but need not be globally
   absent from the allocation map; motive_nested_counter_push checks this. *)
val loop_child_entry_goal = ``
  (\live protected. (^decoder_joint_pre) child_start child_finish elem_dst
    actual_src MLOAD base_op hi (d+32+j*msz) (d+32+j*msz) msz u Gu tnu)
    ((aid,counter,cell,32,mem_bytes_at cell 32 u.vs_memory)::live)
    ((d,mem_bytes_at d (32+j*msz) u.vs_memory)::protected)``;

(* What must survive that child, before executing new_i / MSTORE / JMP.
   This is content preservation, not a consequence of ptr_covers.  Once
   established, the loop header must re-read the same n from source, load
   SUC j from cell, and preserve the same enclosing live/protected family. *)
val loop_child_return_goal = ``
  FLOOKUP t.vs_allocas aid = SOME (cell,32) /\
  lookup_var counter t = SOME (n2w cell) /\ ptr_covers G_after tnt counter t 32 /\
  mem_bytes_at cell 32 t.vs_memory = mem_bytes_at cell 32 u.vs_memory /\
  mem_word_at cell t.vs_memory = n2w j /\
  mem_bytes_at d (32+j*msz) t.vs_memory = mem_bytes_at d (32+j*msz) u.vs_memory /\
  (^decoder_joint_state) child_finish t G_after tnt``;

(* Separate boundary still required for bytestring and bulk-array MCOPY
   (abiEncoder:527, :568).  Existing abi_decode_ptr_copy_windows supplies
   pointers/clean bytes but not these all-H ghosts or caller relation.
   This goal is deliberately not attributed to the finite MSTORE boundary. *)
val copy_return_goal = ``
  (^decoder_joint_state) sb (mcopy dest source byte_count s)
    (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
      (mcopy dest source byte_count s))
    (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy dest source byte_count s) tn)``;

(* Entry/descent matrix (no constructor execution is certified here):
   caller -> P:
     checked syntax: abiBuiltinDecodeSetup:24-29, caller_entry_goal above;
     checked typing: abi_decode_body_wrapped_coherent;
     residual: joint header/output-ALLOCA entry, history, frontier and ghosts.
   DecPrimWord/DecBytestring:
     no compiler recursion; primitive reads need a typed readable-head bound;
     residual: finite path; bytestring MCOPY requires copy_return_goal.
   DecComplex -> Q (both hi branches, abiEncoder:586/:592):
     prefix=[]; offsets=0; tuple/fixed/struct member_infos equations;
     residual: preserve joint state through head guard, then call Q.
   DecDynArray -> R (nonbulk abiEncoder:574):
     child coherent by abi_decoder_coherent_array_iff; asz from header,
     msz=type_memory_size child; counter initialized j=0;
     residual: ALLOCA/zero-store entry, source-count equality and clean cell.
   Q cons -> P (abiEncoder:607):
     env/sf retained (already deleted together for structs), head ty/tv;
     checked: motive_struct_descent, motive_member_descent;
     residual: getelemptr path/ghosts, member_child_entry_goal.
   Q cons -> Q (abiEncoder:610):
     checked: pre++[ty],prev++[tv],ao+asz,vo+msz;
     residual: member_tail_entry_goal, preserving actual earlier contents.
   R -> P (abiEncoder:643):
     env/sf retained; nested coherent array descent uses array_iff twice;
     live extended by snapshot of OUTER cell, protected by completed prefix;
     checked: motive_nested_counter_push;
     residual: loop_child_entry_goal and loop_child_return_goal.
   R runtime backedge (abiEncoder:645-647):
     checked: motive_counter_backedge (j -> SUC j);
     residual: child preserves outer cell, store updates ONLY current cell,
     header source count reload unchanged, enclosing cells/contents preserved.
   Q NIL: no recursive call; existing abi_decode_complex_nil_joint is only
     a NIL boundary and does not discharge ANY residual above.

   Further certification is required before constructor proofs: these
   quotations are candidate interfaces, not recursive closure.  In particular
   the general typed readable-head premise and allocation-site separation
   must be derived at caller/descent sites, not silently assumed external.
*)
