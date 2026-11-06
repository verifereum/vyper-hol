(* Input intervals for raw_call; reuse the dynamic-bytes memory boundary. *)
Theory bodyMemRawCallBounds
Ancestors
  bodyMemBiKeccakBounds exprSimMemDefs exprLoweringProps loweringPosts
  exprSimProps compileEnv words instMemFrontier venomInst venomMemDefs

Theorem raw_call_input_bounds:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx ee t ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 + LENGTH bs < dimword (:256) /\
    LENGTH bs < dimword (:256) /\
    b + 32 <= t.vs_alloca_next /\
    (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= t.vs_alloca_next)
Proof
  strip_tac >> drule_all keccak_dynamic_post_bounds >> strip_tac >>
  `alloca_room ctx func t` by fs[stmt_state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  Cases_on `LENGTH bs = 0` >> gvs[] >> decide_tac
QED

Theorem raw_call_input_output_frontier:
  eval_operand off s = SOME ao /\ eval_operand len s = SOME az /\
  eval_operand roff s = SOME ro /\ eval_operand rlen s = SOME rz /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (w2n rz = 0 \/ w2n ro + w2n rz <= s.vs_alloca_next) ==>
  inst_mem_below_frontier
    (mk_inst id (if stat then STATICCALL else CALL)
      (if stat then [gas;addr;off;len;roff;rlen]
       else [gas;addr;vl;off;len;roff;rlen]) outs) s
Proof
  Cases_on `stat` >>
  simp[below_frontier_CALL, below_frontier_STATICCALL] >>
  rpt strip_tac >> gvs[]
QED

Theorem raw_call_output_allocated_bounds:
  alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (b, ((cap + 31) DIV 32) * 32 + 32) /\
  b + (((cap + 31) DIV 32) * 32 + 32) < dimword (:256) ==>
  b + 32 <= s.vs_alloca_next /\
  b + 32 + cap <= s.vs_alloca_next /\
  w2n (n2w b + 32w : bytes32) = b + 32 /\
  w2n (n2w b + 32w : bytes32) + cap <= s.vs_alloca_next
Proof
  strip_tac >>
  `b + (((cap + 31) DIV 32) * 32 + 32) <= s.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  qspec_then `cap` mp_tac le_word_size_mul >>
  simp[vfmConstantsTheory.word_size_def] >> strip_tac >>
  `b + 32 < dimword (:256)` by decide_tac >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >> decide_tac
QED
