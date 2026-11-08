(* Explicit-resource allocation for the external ABI output prefix. *)
Theory externalReturnAllocPtr
Ancestors protectedAllocCorePtr
Theorem compile_alloc_buffer_protected_source_frag_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword(:256) /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  p+cap <= s.vs_alloca_next /\ val_wf tv v /\ val_footprint tv v <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = n /\ (p+cap <= b \/ b+n <= p)) ==>
  ?out b G1 tn1 sf.
    buf.buf_operand = Var out /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g = G /\ t = tn /\ w = s)
      (\g t w. g = G1 /\ t = tn1 /\ w = sf) R /\
    eval_operand (Var out) sf = SOME (n2w b) /\ ptr_covers G1 tn1 out sf n /\
    (p+cap <= b \/ b+n <= p) /\ eval_operand (Var src) sf = SOME (n2w p) /\
    (!mem. mem_agree_outside tn1.t_mem sf.vs_memory mem ==> val_in_memory tv v p mem) /\
    (!q k. not_fresh_at sa q /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q sf k) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
    alloca_inv sf /\ alloca_room ctx func sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (b,n) /\
    b+n <= sf.vs_alloca_next /\ s.vs_alloca_next <= sf.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (q,sz))
Proof
  strip_tac >> drule_all compile_alloc_buffer_protected_source_core_ptr >>
  disch_then (qspecl_then [`cx`, `R`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`out`, `b`, `G1`, `tn1`, `sf`] >> asm_rewrite_tac[]
QED

(* The actual complex-return prefix, stopping before the encoder executes. *)
Theorem compile_external_return_tuple_bytes_alloc_prefix_ptr:
  compile_external_return (SOME (Var src)) F F next.ce_ret_enc_info n nr key ut iv sa = (x,sc) /\
  (nr ==> iv) /\ fn_has_code sa sc func /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr0,rr,name,args,defaults,TupleT ts,(fbody:stmt list))) =
      (lbl,cenv0,pos,cds,payable,nr',key0,ut0,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa0) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (TupleT ts) /\ ts <> [] /\
  EVERY (\t. (?k. t = BaseT (BytesT (Dynamic k))) \/
             (?k. t = BaseT (StringT k))) ts /\
  evaluate_type (type_env tops) (TupleT ts) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi_list (type_env tops) ts vs = SOME avs /\
  alloca_inv s /\ alloca_room ctx func s /\ n < dimword(:256) /\
  not_fresh_at sa src /\ eval_operand (Var src) s = SOME (n2w p) /\
  p+cap <= s.vs_alloca_next /\ val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p mem) /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
    sz = n /\ (p+cap <= b \/ b+n <= p)) ==>
  ?buf sb len sd out b G1 tn1 sf.
    compile_alloc_buffer n sa = (buf,sb) /\
    compile_abi_encode_to_buf buf.buf_operand (Var src) next.ce_ret_enc_info sb = (len,sd) /\
    emit_inst RETURN [buf.buf_operand;len] [] sd = (x,sc) /\
    buf.buf_operand = Var out /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g = G /\ t = tn /\ w = s)
      (\g t w. g = G1 /\ t = tn1 /\ w = sf) R /\
    eval_operand (Var out) sf = SOME (n2w b) /\ ptr_covers G1 tn1 out sf n /\
    (p+cap <= b \/ b+n <= p) /\ eval_operand (Var src) sf = SOME (n2w p) /\
    (!mem. mem_agree_outside tn1.t_mem sf.vs_memory mem ==>
      abi_encoder_window_input next.ce_ret_enc_info
        (if needs_external_call_wrap (TupleT ts)
         then Tuple [vyper_to_abi_type (type_env tops) (TupleT ts)]
         else vyper_to_abi_type (type_env tops) (TupleT ts))
        (if needs_external_call_wrap (TupleT ts) then ListV [ListV avs] else ListV avs)
        p (SUM (MAP type_memory_size tvs)) mem) /\
    (!q k. not_fresh_at sa q /\ ptr_covers G tn q s k ==> ptr_covers G1 tn1 q sf k) /\
    (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
    alloca_inv sf /\ alloca_room ctx func sf /\
    FLOOKUP sf.vs_allocas sa.cs_next_id = SOME (b,n) /\
    b+n <= sf.vs_alloca_next /\ s.vs_alloca_next <= sf.vs_alloca_next /\
    b+n < dimword(:256) /\
    (!aid q sz. FLOOKUP s.vs_allocas aid = SOME (q,sz) ==>
      FLOOKUP sf.vs_allocas aid = SOME (q,sz))
Proof
  strip_tac >> drule_all loweringHaltTheory.compile_external_return_abi_parts >> strip_tac >>
  qmatch_asmsub_rename_tac `compile_alloc_buffer n sa = (buf,alloc_st)` >>
  qmatch_asmsub_rename_tac `compile_abi_encode_to_buf _ _ _ alloc_st = (len,enc_st)` >>
  `cs_extends sa alloc_st` by (drule loweringHaltTheory.compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends alloc_st sc` by
    (drule loweringHaltTheory.compile_abi_encode_to_buf_extends >> strip_tac >>
     drule fragExecTheory.cs_extends_emit_inst >> strip_tac >>
     metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code sa alloc_st func` by (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  drule_all compile_alloc_buffer_protected_source_frag_ptr >>
  disch_then (qspecl_then [`cx`, `R`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`buf`, `alloc_st`, `len`, `enc_st`, `out`, `b`, `G1`, `tn1`, `sf`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> drule_all externalReturnTupleWindowPtrTheory.external_frame_tuple_bytes_robust_window >> simp[]
QED
