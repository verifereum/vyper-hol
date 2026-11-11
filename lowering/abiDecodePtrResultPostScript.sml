(* Result-post boundaries for freshly decoded memory values. *)
Theory abiDecodePtrResultPost
Ancestors
  abiDecodePtrOutcome bodyPtrDefs exprSimProps loweringPosts
  valueEncoding vyperInterpreter context venomState venomExecSemantics
  ptrDiscipline finite_map words vyperState exprSimHash abiDecoderContract
  compileEnv arithmetic abiDecoderCoherence valueEncodingProps
  vyperValue vyperAST

Theorem memory_located_pointer_posts:
  evaluate_type (get_tenv cx) t = SOME tv /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s cap /\
  val_store_size tv v <= cap /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= cap /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_vv_ok cx t (Value v) (LocatedValue t' (mk_ptr (Var p) LocMemory)) es G tn s /\
  ptr_buf_ok cenv e (Var p) G s
Proof
  strip_tac >>
  `ptr_mem_ok cx t v (Var p) G tn s` by
    (gvs[ptr_mem_ok_def, ptr_covers_def, eval_operand_def] >>
     rpt strip_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  gvs[ptr_vv_ok_def, ptr_buf_ok_def, ptr_covers_def, mk_ptr_def,
      read_result_def, return_def, eval_operand_def] >>
  rpt strip_tac >> goal_assum (drule_at Any) >> decide_tac
QED

(* Ordinary bytes are framed by the decoder's physical write window,
   independently of its ghost frame.  The setup has not changed memory. *)
Theorem abi_decode_result_wb_frame:
  wb_frame cenv es sa s0 s /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  u.vs_memory = s.vs_memory /\ abi_decode_frame d cap u t /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
    regions_disjoint d cap b k) /\
  (!name b k. local_region cenv ee.scopes s name b k ==>
    regions_disjoint d cap b k) ==>
  wb_frame cenv es sa s0 t
Proof
  strip_tac >> irule wb_frame_allocating_tail >>
  simp[] >> qexistsl [`s`, `ee.scopes`, `sm`] >> simp[] >>
  fs[abi_decode_frame_def, regions_disjoint_def] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p k. _ ==> mem_bytes_at p k _ = _` (qspecl_then [`b`, `sz`] mp_tac) >>
  (impl_tac >- (first_x_assum drule_all >> decide_tac)) >> simp[]
QED

(* Allocation and physical frames, not ghost_kept, discharge vv_post. *)
Theorem abi_decode_tuple_result_posts:
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT tys /\
  abi_decoder_coherent cenv (get_tenv cx) cenv.ce_struct_fields
    (TupleT tys) (TupleTV tvs) /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  lookup_var dst t = SOME d /\
  ptr_covers H tk dst t (type_memory_bytes cenv (TupleT tys)) /\
  (!mem. mem_agree_outside tk.t_mem t.vs_memory mem ==>
    tuple_in_memory vs tvs (w2n d) mem) /\
  stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es sa s0 t /\
  FLOOKUP t.vs_allocas aid = SOME (w2n d,type_memory_bytes cenv (TupleT tys)) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b k. local_region cenv ee.scopes t name b k ==>
    regions_disjoint (w2n d) (type_memory_bytes cenv (TupleT tys)) b k) ==>
  vv_post ctx func cenv cx e es sa sb s0 ee (Value (ArrayV (TupleV vs)))
    (LocatedValue (TupleT tys) (mk_ptr (Var dst) LocMemory)) t /\
  ptr_vv_ok cx (TupleT tys) (Value (ArrayV (TupleV vs)))
    (LocatedValue (TupleT tys) (mk_ptr (Var dst) LocMemory)) ee H tk t /\
  ptr_buf_ok cenv e (Var dst) H t
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  `!mem. mem_agree_outside tk.t_mem t.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n d) mem` by
    simp[val_in_memory_tuple] >>
  conj_tac
  >- (qpat_assum `expr_type e = TupleT tys` (SUBST1_TAC o GSYM) >>
      irule vv_post_allocated_memory_intro >>
      simp[mk_ptr_def, eval_operand_def, is_word_type_def] >>
      qexistsl [`aid`, `w2n d`, `type_memory_bytes cenv (TupleT tys)`] >>
      simp[val_footprint_def, regions_disjoint_def] >>
      conj_tac >- (rpt strip_tac >>
        qpat_x_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >>
        simp[regions_disjoint_def]) >>
      first_x_assum irule >> simp[mem_agree_outside_def]) >>
  irule memory_located_pointer_posts >>
  qexistsl [`type_memory_bytes cenv (TupleT tys)`, `TupleTV tvs`, `d`] >>
  simp[val_store_size_def]
QED
