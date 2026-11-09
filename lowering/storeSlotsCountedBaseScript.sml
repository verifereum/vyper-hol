(* Counted live-slot stores with their normalized storage effect. *)
Theory storeSlotsCountedBase
Ancestors
  storeSlotsMemoryFootprint bodyMemAssignTopCopySuffix placeStoreSlots
  placeStoreCopyPath stmtSimStoreCopy storeSlotsMemoryPaths typedMemoryCopy
  context compileEnv fragExec fragGasMode venomState venomInst
  valueEncoding valueEncodingProps vyperTyping words arithmetic list rich_list

val _ = diminish_srw_ss ["sizes"]

Theorem store_slots_copy_op_mem:
  compile_word_copy_loop_op src dst cnt LocMemory
    (if tr then LocTransient else LocStorage) F sa = (result,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand cnt s = SOME (n2w n) /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) /\
  w2n sw + 32*n <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32*j) s) q) s (COUNT_LIST n) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_alloca_next = s.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa (if tr then LocTransient else LocStorage) sw dw s n t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule store_slots_runtime_copy_path_mem >>
     Cases_on `tr` >> simp[] >> metis_tac[]) >>
  drule place_store_copy_frame_observations >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (fs[store_copy_frame_def] >> drule topcopy_normalize_allocations >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  fs[store_copy_frame_def, store_copy_prefix_def] >>
  irule FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by decide_tac >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    (pure_rewrite_tac[GSYM word_add_n2w, GSYM word_mul_n2w, n2w_w2n] >>
     wordsLib.WORD_DECIDE_TAC) >>
  Cases_on `tr` >> simp[w2n_n2w, LESS_MOD] >> gvs[]
QED
