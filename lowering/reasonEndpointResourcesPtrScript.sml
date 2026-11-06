(* Projections of expression endpoints used by checked revert consumers.
   Placement is a semantic expression postcondition, independent of provenance. *)
Theory reasonEndpointResourcesPtr
Ancestors
  reasonRepresentationPtr reasonCopySourcePtr stringUnwrapLayout
  loweringPosts exprOperandVar exprSimCopy exprSimHyps exprLoweringProps
  compileEnv valueEncoding exprSimProps vyperInterpreter vyperValue
  venomState words arithmetic finite_map list context contractABI allocLimits vyperState
  vfmConstants

Theorem expr_val_at_region_prefix:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty /\
  eval_operand op s = SOME A /\ 0 < n /\ n <= val_footprint tvt v ==>
  (?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sb.cs_next_id /\
     a <= w2n A /\ w2n A+n <= a+sz) \/
  (?name a sz. local_region cenv es.scopes s name a sz /\
     a <= w2n A /\ w2n A+n <= a+sz)
Proof
  simp[expr_val_at_def] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[] >> `n+w2n A <= b+sz` by decide_tac >> metis_tac[]
QED

Theorem vv_at_memory_region_prefix:
  vv_at cenv cx ty sa sb es tv vv s /\
  (vv = StackValue ty' op \/
   (vv = LocatedValue ty' p /\ p.ptr_location = LocMemory /\ p.ptr_operand = op)) /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty /\
  eval_operand op s = SOME A /\ 0 < n /\ n <= val_footprint tvt v ==>
  (?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sb.cs_next_id /\
     a <= w2n A /\ w2n A+n <= a+sz) \/
  (?name a sz. local_region cenv es.scopes s name a sz /\
     a <= w2n A /\ w2n A+n <= a+sz)
Proof
  strip_tac
  >- (fs[vv_at_def] >> drule_all expr_val_at_region_prefix >> simp[]) >>
  fs[vv_at_def] >> gvs[] >> `n+w2n A <= b+sz` by decide_tac >> metis_tac[]
QED

Theorem immutable_holds_read_value:
  immutable_holds cenv cx ty tv A es s /\ read_result cx tv es = (INL v,es) ==>
  immutable_holds cenv cx ty (Value v) A es s
Proof
  simp[immutable_holds_def, read_result_def, return_def] >>
  rpt strip_tac >> gvs[] >> qexistsl [`name`,`off`,`itv`,`iv`,`k`] >> simp[]
QED

Theorem compile_expr_old_operand:
  compile_expr cenv ty e sa = (vv,sb) /\ local_ptrs_reserved cenv sa ==>
  copy_old_operand sb (vv_operand vv)
Proof
  simp[copy_old_operand_def] >> metis_tac[cj 1 compiler_compile_var]
QED

Theorem string_encoder_size_bounds:
  val_wf (BaseTV (StringT max)) (StringV str) /\
  type_alloc_ok cenv (BaseT (StringT max)) ==>
  32+contractABI$ceil32 (LENGTH str) <= type_memory_bytes cenv (BaseT (StringT max)) /\
  LENGTH str+63 < dimword(:256) /\
  64+type_memory_bytes cenv (BaseT (StringT max)) < dimword(:256) /\
  32*type_slot_size (BaseTV (StringT max)) < dimword(:256)
Proof
  strip_tac >> drule string_store_size_slots >> strip_tac >>
  `LENGTH str+32 <= type_memory_size (BaseTV (StringT max))` by fs[val_wf_def] >>
  fs[type_alloc_ok_def, is_word_type_def, string_memory_bytes_slots,
     val_store_size_def, contractABITheory.ceil32_def, word_size_def] >>
  fs[type_slot_size_def, type_memory_size_def, word_size_def, dimword_def] >>
  decide_tac
QED
