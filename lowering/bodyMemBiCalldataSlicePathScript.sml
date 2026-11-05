(* Located slice results and counted memory paths. *)
Theory bodyMemBiCalldataSlicePath
Ancestors
  bodyMemBiCalldataSliceRun bodyMemBiCalldataSliceFacts
  exprSimCalldataSlice exprSimDefs exprSimMemDefs exprSimProps
  exprSimVVFrame exprSimAlloc loweringPosts instMemFrontier
  valueEncoding valueEncodingProps valueTypingMemoryProps
  venomState venomExecSemantics words list finite_map
  vyperAST vyperState vyperContext vyperValue vyperTypeSystem
  vyperInterpreter exprLoweringProps freshWrites localPtrsProps exprLowering
  valueCopy compileEnv venomMemDefs

(* Original: exprSimCalldataSlice.slice_calldata_vv_post [local]. *)
Theorem slice_calldata_vv_post:
  !func cenv cx e es sa sb s t p a n w ctx.
  expr_type e = BaseT (BytesT (Dynamic n)) /\ p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand t = SOME w /\ a+n <= LENGTH cx.txn.calldata /\
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + 32 * word_size n) /\
  sa.cs_next_id < sb.cs_next_id /\
  val_in_memory (BaseTV (BytesT (Dynamic n)))
    (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!nm lb len. local_region cenv es.scopes t nm lb len ==>
     regions_disjoint (w2n w) (32 + 32 * word_size n) lb len) /\
  locals_kept cenv es s t ==>
  !k. vv_post ctx func cenv cx e es sa sb s es
    (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
    (LocatedValue (expr_type e) p) (t with vs_inst_idx := k)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by simp[LENGTH_TAKE_EQ] >>
  `n <= 32 * word_size n` by simp[word_size_capacity] >>
  `eval_operand p.ptr_operand (t with vs_inst_idx := k) = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def,
       read_result_def, return_def, evaluate_type_def, is_word_type_def,
       eval_operand_def, lookup_var_def, val_wf_def, val_footprint_def,
       locals_kept_inst_idx] >>
  conj_tac
  >- (strip_tac >> conj_tac
      >- simp[type_memory_size_def, word_size_capacity] >>
      disj1_tac >> qexistsl_tac [`sa.cs_next_id`,`w2n w`,`32 + 32 * word_size n`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!nm lb len. local_region _ _ t _ _ _ ==> _` drule >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[]
QED

Theorem slice_calldata_vv_capacity:
  vv_post ctx func cenv cx e es sa sb s es tv
    (LocatedValue (expr_type e) p) t /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  stmt_state_rel ctx func cenv cx es t /\
  eval_operand p.ptr_operand t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,32 + 32 * word_size n) ==>
  vv_store_bound cx (expr_type e) (expr_type e) es tv
    (LocatedValue (expr_type e) p) t
Proof
  strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type e)`
  >- simp[vv_store_bound_def] >>
  drule vv_store_bound_capacity >> simp[] >> disch_then irule >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  simp[type_memory_size_def] >>
  irule alloca_region_below_frontier >> conj_tac
  >- gvs[stmt_state_rel_def, alloca_inv_def] >>
  qexistsl_tac [`aid`, `w2n w`, `32 * word_size n + 32`] >> simp[]
QED
