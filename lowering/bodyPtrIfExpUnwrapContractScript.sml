Theory bodyPtrIfExpUnwrapContract
Ancestors
  bodyPtrDefs loweringPosts exprLowering context compileEnv
  exprSimUnwrap bodyPtrIfExpUnwrapNoop

(* LocatedValue carries its annotation exactly; StackValue deliberately
   does not. This is a semantic boundary, independent of source layout. *)
Theorem vv_post_located_type:
  !ctx fn cenv cx e es sa sc s0 es' tv ty p s.
    vv_post ctx fn cenv cx e es sa sc s0 es' tv (LocatedValue ty p) s ==>
    ty = expr_type e
Proof
  simp[vv_post_def, vv_holds_def]
QED

(* The allocating IfExp arm has a non-word result annotation. Therefore
   every word LocatedValue load is unreachable at this particular caller,
   including memory, storage, transient and both immutable load modes. *)
Theorem ifexp_allocated_unwrap_dispatch:
  !ctx fn cenv cx e es sa sc s0 es' tv ty p s.
    vv_post ctx fn cenv cx e es sa sc s0 es' tv (LocatedValue ty p) s /\
    ~is_word_type (expr_type e) ==>
    ~is_word_type ty /\ p.ptr_location <> LocCalldata /\
    unwrap_value cenv (LocatedValue ty p) =
      (case p.ptr_location of
         LocMemory => comp_return p.ptr_operand
       | _ => compile_ensure_in_memory p.ptr_operand p.ptr_location
                (type_memory_bytes cenv ty)
                ((type_memory_bytes cenv ty + 31) DIV 32)
                cenv.ce_is_ctor cenv.ce_imm_alloca)
Proof
  rpt gen_tac >> strip_tac >>
  `ty = expr_type e` by metis_tac[vv_post_located_type] >>
  `p.ptr_location <> LocCalldata` by metis_tac[vv_post_calldata] >>
  simp[unwrap_value_def]
QED

(* UNWRAP CONTRACT AUDIT (not an admission of the proposed theorem).

   Full dispatch at contextScript.sml:134 and :508:
   word Memory: MLOAD; Storage: SLOAD; Transient: TLOAD;
   word Calldata: CALLDATALOAD;
   word Code: runtime DLOAD, constructor ILOAD, with optional base ADD.
   These word branches are excluded at the allocating caller by the checked
   ifexp_allocated_unwrap_dispatch, once result/arm annotation equality is
   supplied. Calldata is excluded even without a non-word assumption, by
   the existing vv_post_calldata. No new load theorem is required here.

   Non-word Memory is the checked UnwrapNoop boundary. Remaining branches:
   Storage/Transient allocate type_memory_bytes ty, then a single SLOAD or
   TLOAD plus MSTORE when word_count=1; otherwise a word-copy CFG loop.
   Code allocates type_memory_bytes ty and recursively copies immutable
   words (DLOAD at runtime; ILOAD, with optional base ADD, in constructor).
   Calldata would load length, allocate mem_bytes+32, write header, ADD
   source/destination data pointers and CALLDATACOPY; it is unreachable.

   Proposed isolated materialization contract (implementation still needed):

   unwrap_value cenv (LocatedValue ty p) sc = (src,sn) /\
   (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
    p.ptr_location = LocCode) /\ ~is_word_type ty /\
   vv_post ctx fn cenv cx e es sa sc s0 es' raw (LocatedValue ty p) s /\
   read_result cx raw es' = (INL v,es') /\
   ptr_vv_ok cx (expr_type e) raw (LocatedValue ty p) es' G tn s /\
   ghost_inv d cenv cx es' G tn s /\
   ghost_kept cenv es sa G0 tn0 s0 G tn /\
   ptr_covers G tn out s n /\ not_fresh_at sc out /\
   local_ptrs_reserved cenv sa /\
   MAP FDOM es.scopes = MAP FDOM es'.scopes /\
   sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
   fn_has_code sc sn fn /\ fn_inst_ids_distinct fn /\
   (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
   (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
      type_memory_bytes cenv ty = type_memory_size tvt /\
      type_memory_size tvt < 2 ** 64) /\
   ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
   s.vs_current_bb = sc.cs_current_bb /\
   s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
   ?G1 tn1 t.
     gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
     expr_post ctx fn cenv cx e es sa sn s0 es' v src t /\
     ptr_val_ok cx (expr_type e) v src G1 tn1 t /\
     ghost_inv d cenv cx es' G1 tn1 t /\
     ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
     ptr_covers G1 tn1 out t n /\ lookup_var out t = lookup_var out s /\
     (!w. eval_operand src t = SOME w ==>
        ?x. src = Var x /\
            ptr_covers G1 tn1 x t (type_memory_bytes cenv ty)) /\
     ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
     t.vs_inst_idx = LENGTH sn.cs_current_insts

   Source-to-consumer premise table:
   - vv_post, ptr_vv_ok, ghost_inv, original ghost_kept, destination
     ptr_covers and control position: AllocResources outputs, unchanged.
   - own-type non-word and non-calldata: checked dispatch above, together
     with actual result/arm annotation equality (not physical-layout eq).
   - source operand oldness, scope domains, sa<=sb next_var: AllocCaller;
     transport sb->sc via allocation ci_mono. Destination out old at sc:
     compile_alloc_buffer_parts. Allocation does NOT make it old at sa.
   - local reservation, sa<=sc next_id, code suffix, size/evaluate_type,
     no dynamic allocation context: require actual expression precondition
     and compiler monotonicity facts; not implied by AllocResources alone.
   - successful read v: vv_post's vv_holds gives it at every reachable
     location (storage_holds/immutable_holds), not an arbitrary new input.
   - full output capacity is at ty (=expr_type e), not automatically at
     lowered_value_type cenv e. Bridging that distinction for the store
     remains a separate caller/representation obligation.

   Materialization interface test: existing ensure_storage_memory_layout
   has precisely the allocation/one-word/loop split above, and
   ensure_storage_memory_defined_frag preserves all sc-old variables,
   hence out's value. But it is fixed-run semantic execution, NOT counted
   pointer execution. unwrap_storage_copy_path and runtime/constructor
   code copy paths in S1 provide gas_path with expr_post, not gas_path_ptr
   or a ghost frame. No existing counted materialization summary was
   found. For Storage/Transient, ptr_vv_ok supplies only dead-byte taint
   restrictions; each loop load/store must transfer that taint and prove
   robust destination interpretation, rather than require every source
   slot clean. For Code, the optional constructor base ADD must retain
   provenance for staged memory, and runtime DLOAD must keep out intact.
   Each path also needs original-sa ghost_kept and an explicit out lookup
   frame at sc. ghost_kept alone is not a machine-variable value frame.
   These missing counted/robust interfaces are not proved by this audit.
*)
