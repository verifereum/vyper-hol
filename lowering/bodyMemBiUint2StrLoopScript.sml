(* Same-run composition of uint2str memory paths and value invariants. *)
Theory bodyMemBiUint2StrLoop
Ancestors
  bodyMemBiUint2StrBlocks bodyMemBiUint2StrBounds arithmeticProps exprSimUint2Str words
  venomInst venomState venomExecSemantics finite_map
  bodyMemBopRestWordPath fragGasPathMem arithmetic list

Theorem u2s_cond_mem_transition[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a buf b sz inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b sz inst s0 t /\
      u2s_digits a b n X x str t /\
      t.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `u2s_digits a b n X x str s` >>
  `lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256)` by
    fs[u2s_digits_def] >>
  qabbrev_tac `v = update_var (u2s_var a 4) (bool_to_word (x = 0)) s` >>
  `run_inst_seq (TAKE 1 (u2s_cond a)) s = OK v` by
    (irule (cj 1 u2s_cond_run) >> qexists_tac `x` >> simp[Abbr `v`]) >>
  `step_inst_base (LAST (u2s_cond a)) (v with vs_inst_idx := 1) =
    OK (jump_to (u2s_label a (if x = 0 then 4 else 2))
          (v with vs_inst_idx := 1))` by
    (simp[u2s_cond_def, Abbr `v`, u2s_inst_def, mk_inst_def,
          step_inst_base_def, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     Cases_on `x = 0` >> simp[]) >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `v`, update_var_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` by simp[] >>
  drule_all u2s_cond_memory_path >> strip_tac >>
  `u2s_safe ctx fn cenv cx es a buf b sz inst s0 v` by
    (simp[Abbr `v`] >> irule u2s_safe_update >> metis_tac[]) >>
  `u2s_digits a b n X x str v` by
    simp[Abbr `v`, u2s_digits_update] >>
  qexists_tac `jump_to (u2s_label a (if x = 0 then 4 else 2)) v` >>
  simp[u2s_safe_jump, u2s_digits_jump] >> simp[jump_to_def]
QED

Theorem u2s_store_bound[local]:
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  i <= n /\ 32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  w2n ((n2w b : bytes32)+n2w n-n2w i)+32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `(n2w b : bytes32)+n2w n-n2w i = n2w (b+n-i)` by
    (mp_tac (Q.INST [`x` |-> `0`] (cj 4 u2s_word_arithmetic)) >> simp[]) >>
  `b+n-i < dimword (:256)` by decide_tac >>
  `b+n-i+sz <= s.vs_alloca_next` by
    (irule u2s_safe_result_region >> metis_tac[]) >>
  simp[] >> decide_tac
QED

Theorem u2s_body_mem_transition[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  u2s_digits a b n X x str s /\ 0 < x /\ LENGTH str < n /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 t /\
      u2s_digits a b n X (x DIV 10) (CHR (48+x MOD 10)::str) t /\
      t.vs_current_bb = u2s_label a 1 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `n+32 <= sz+n` by decide_tac >>
  drule u2s_body_iteration >>
  disch_then (qspecl_then [`x`, `str`, `n`, `X`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `w2n ((n2w b : bytes32)+n2w n-n2w (LENGTH str))+32 <= s.vs_alloca_next` by
    (irule u2s_store_bound >>
     `LENGTH str <= n` by fs[u2s_digits_def] >> metis_tac[]) >>
  `eval_operand buf s = SOME (n2w b)` by fs[u2s_safe_def] >>
  `eval_operand (Var (u2s_var a 0)) s = SOME (n2w x) /\
   eval_operand (Var (u2s_var a 1)) s = SOME (n2w (LENGTH str))` by
    fs[u2s_digits_def, eval_operand_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|>` by simp[] >>
  `!z. buf = Var z ==> not_fresh_at a z` by simp[] >>
  `~t.vs_halted` by simp[] >>
  drule_all u2s_body_memory_path >> strip_tac >>
  qexists_tac `jump_to (u2s_label a 1) t` >>
  simp[u2s_safe_jump, u2s_digits_jump] >> simp[jump_to_def]
QED

Theorem u2s_final_mem_exit[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block (u2s_label a 4) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|> /\
  s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  u2s_digits a b n X 0 str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH str)) /\
      val_in_memory ty (StringV str) (b+n-LENGTH str) t.vs_memory /\
      b+n-LENGTH str+sz <= t.vs_alloca_next /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `n+32 <= sz+n` by decide_tac >>
  mp_tac (Q.INST [`sz` |-> `sz+n`] u2s_final_result) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `w2n ((n2w b : bytes32)+n2w n-n2w (LENGTH str))+32 <= s.vs_alloca_next` by
    (irule u2s_store_bound >>
     `LENGTH str <= n` by fs[u2s_digits_def] >> metis_tac[]) >>
  `eval_operand buf s = SOME (n2w b)` by fs[u2s_safe_def] >>
  `eval_operand (Var (u2s_var a 1)) s = SOME (n2w (LENGTH str))` by
    fs[u2s_digits_def, eval_operand_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|>` by simp[] >>
  `!z. buf = Var z ==> not_fresh_at a z` by simp[] >>
  `~t.vs_halted` by simp[] >>
  `b+n-LENGTH str+sz <= s.vs_alloca_next` by
    (irule u2s_safe_result_region >> metis_tac[]) >>
  drule_all u2s_final_memory_path >> strip_tac >>
  qexists_tac `jump_to (u2s_label a 5) t` >>
  simp[u2s_safe_jump] >>
  simp[jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem u2s_loop_mem_path[local]:
  !x s str.
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  u2s_digits a b n X x str s /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ 32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b+n-LENGTH (num_to_dec_string X)+sz <= t.vs_alloca_next /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  completeInduct_on `x` >> rpt gen_tac >> strip_tac >>
  `lookup_block (u2s_label a 1) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _`
       (qspec_then `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  mp_tac (Q.INST [`sz` |-> `sz+n`] u2s_cond_mem_transition) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `s1` strip_assume_tac) >>
  `alloca_inv s1` by
    (irule rest_word_state_alloca_inv >> fs[u2s_safe_def] >> metis_tac[]) >>
  Cases_on `x = 0`
  >- (gvs[] >>
      `lookup_block (u2s_label a 4) fn.fn_blocks =
        SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a (Var p) n|>` by
        (qpat_x_assum `!bb. MEM bb _ ==> _`
          (qspec_then `<|bb_label := u2s_label a 4;
                        bb_instructions := u2s_final a (Var p) n|>` mp_tac) >>
         simp[u2s_blocks_def]) >>
      mp_tac (Q.INST [`s` |-> `s1`, `buf` |-> `Var p`] u2s_final_mem_exit) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `str = num_to_dec_string X` by fs[u2s_digits_def] >>
      qexists_tac `t` >> gvs[] >>
      drule_all gas_path_mem_then >> simp[]) >>
  `0 < x` by decide_tac >>
  `LENGTH str < n` by (irule u2s_digits_room >> metis_tac[]) >>
  `lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _`
      (qspec_then `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  mp_tac (Q.INST [`s` |-> `s1`] u2s_body_mem_transition) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `alloca_inv s2` by
    (irule rest_word_state_alloca_inv >> fs[u2s_safe_def] >> metis_tac[]) >>
  `x DIV 10 < x` by simp[DIV_LESS] >>
  qpat_x_assum `!m. m < x ==> _` (qspec_then `x DIV 10` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`s2`, `CHR (48+x MOD 10)::str`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexists_tac `t` >> gvs[] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Theorem u2s_zero_mem_exit[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|> /\
  s.vs_current_bb = u2s_label a 3 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  1 <= n /\ 32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-1)) /\
      val_in_memory ty (StringV "0") (b+n-1) t.vs_memory /\
      b+n-1+sz <= t.vs_alloca_next /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `n+32 <= sz+n` by decide_tac >>
  mp_tac (Q.INST [`sz` |-> `sz+n`] u2s_zero_result) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `w2n ((n2w b : bytes32)+n2w n)+32 <= s.vs_alloca_next` by
    (mp_tac (Q.INST [`i` |-> `0`] u2s_store_bound) >> simp[] >> metis_tac[]) >>
  `w2n ((n2w b : bytes32)+n2w n-1w)+32 <= s.vs_alloca_next` by
    (mp_tac (Q.INST [`i` |-> `1`] u2s_store_bound) >> simp[] >> metis_tac[]) >>
  `eval_operand buf s = SOME (n2w b)` by fs[u2s_safe_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|>` by simp[] >>
  `!z. buf = Var z ==> not_fresh_at a z` by simp[] >>
  `~t.vs_halted` by simp[] >>
  `b+n-1+sz <= s.vs_alloca_next` by
    (irule u2s_safe_result_region >> metis_tac[]) >>
  drule_all u2s_zero_memory_path >> strip_tac >>
  qexists_tac `jump_to (u2s_label a 5) t` >>
  simp[u2s_safe_jump] >>
  simp[jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem u2s_check_mem_exit[local]:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  lookup_var (u2s_var a 0) s = SOME (n2w X) /\
  lookup_var (u2s_var a 1) s = SOME 0w /\ local_ptrs_reserved cenv a /\
  (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ 32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b+n-LENGTH (num_to_dec_string X)+sz <= t.vs_alloca_next /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks =
    SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _`
      (qspec_then `<|bb_label := u2s_label a 0; bb_instructions := u2s_check a|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  qabbrev_tac `v = update_var (u2s_var a 3) (bool_to_word (X = 0)) s` >>
  `run_inst_seq (TAKE 1 (u2s_check a)) s = OK v` by
    (irule (cj 1 u2s_check_run) >> qexists_tac `X` >> simp[Abbr `v`]) >>
  `step_inst_base (LAST (u2s_check a)) (v with vs_inst_idx := 1) =
    OK (jump_to (u2s_label a (if X = 0 then 3 else 1))
          (v with vs_inst_idx := 1))` by
    (simp[u2s_check_def, Abbr `v`, u2s_inst_def, mk_inst_def,
          step_inst_base_def, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
     Cases_on `X = 0` >> simp[]) >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `v`, update_var_def] >>
  drule_all u2s_check_memory_path >> strip_tac >>
  qabbrev_tac `s1 = jump_to (u2s_label a (if X = 0 then 3 else 1)) v` >>
  `u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s1` by
    (simp[Abbr `s1`] >> irule u2s_safe_jump >> simp[Abbr `v`] >>
     irule u2s_safe_update >> gvs[]) >>
  `alloca_inv s1` by
    (irule rest_word_state_alloca_inv >> fs[u2s_safe_def] >> metis_tac[]) >>
  Cases_on `X = 0` >- suspend "zero" >> suspend "nonzero"
QED

Resume u2s_check_mem_exit[zero]:
  `s1.vs_current_bb = u2s_label a 3 /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted` by
    simp[Abbr `s1`, jump_to_def] >>
  `lookup_block (u2s_label a 3) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|>` by
    (qpat_x_assum `!bb. MEM bb _ ==> _`
      (qspec_then `<|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|>` mp_tac) >>
     simp[u2s_blocks_def]) >>
  mp_tac (Q.INST [`s` |-> `s1`] u2s_zero_mem_exit) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  qexists_tac `t` >> gvs[EVAL ``num_to_dec_string 0``] >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_path_mem_then >> simp[]
QED

Resume u2s_check_mem_exit[nonzero]:
  `s1.vs_current_bb = u2s_label a 1 /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted` by
    simp[Abbr `s1`, jump_to_def] >>
  `u2s_digits a b n X X [] s1` by
    (simp[Abbr `s1`, Once u2s_digits_jump] >>
     simp[Abbr `v`, u2s_digits_update] >>
     irule u2s_digits_initial >> simp[] >> decide_tac) >>
  mp_tac (Q.SPECL [`X`, `s1`, `[]`] u2s_loop_mem_path) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `t` >> gvs[] >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_path_mem_then >> simp[]
QED

Finalise u2s_check_mem_exit

Theorem u2s_setup_mem_exit:
  fn_inst_ids_distinct fn /\ alloca_history fn s /\ alloca_inv s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ u2s_setup a op buf /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  (!blk. MEM blk (u2s_blocks a op buf n) ==>
         lookup_block blk.bb_label fn.fn_blocks = SOME blk) /\
  u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s /\
  eval_operand op s = SOME (n2w X) /\ eval_operand buf s = SOME (n2w b) /\
  local_ptrs_reserved cenv a /\ (?p. buf = Var p /\ not_fresh_at a p) /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  X < dimword (:256) /\ 78 <= n /\ 32 <= sz /\ b+(sz+n) < dimword (:256) ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
      alloca_history fn t /\ t.vs_alloca_next = s.vs_alloca_next /\
      u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 t /\
      eval_operand (Var (u2s_var a 2)) t = SOME (n2w (b+n-LENGTH (num_to_dec_string X))) /\
      val_in_memory ty (StringV (num_to_dec_string X))
        (b+n-LENGTH (num_to_dec_string X)) t.vs_memory /\
      b+n-LENGTH (num_to_dec_string X)+sz <= t.vs_alloca_next /\
      t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  strip_tac >>
  qabbrev_tac `v = update_var (u2s_var a 2) (n2w b)
    (update_var (u2s_var a 1) 0w (update_var (u2s_var a 0) (n2w X) s))` >>
  `run_inst_seq (TAKE 3 (u2s_setup a op buf)) s = OK v` by
    (simp[Abbr `v`] >> irule u2s_setup_run >> gvs[]) >>
  `lookup_var (u2s_var a 0) v = SOME (n2w X) /\
   lookup_var (u2s_var a 1) v = SOME 0w /\
   v.vs_current_bb = s.vs_current_bb /\ ~v.vs_halted` by
    (mp_tac (Q.INST [`t` |-> `v`, `p` |-> `n2w b`, `w` |-> `n2w X`] u2s_setup_values) >>
     simp[Abbr `v`]) >>
  `u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 v` by
    (simp[Abbr `v`] >> irule u2s_setup_safe >> gvs[]) >>
  drule_all u2s_setup_memory_path >> strip_tac >>
  qabbrev_tac `s1 = jump_to (u2s_label a 0) v` >>
  `u2s_safe ctx fn cenv cx es a buf b (sz+n) inst s0 s1` by
    (simp[Abbr `s1`] >> irule u2s_safe_jump >> gvs[]) >>
  `alloca_inv s1` by
    (irule rest_word_state_alloca_inv >> fs[u2s_safe_def] >> metis_tac[]) >>
  `s1.vs_current_bb = u2s_label a 0 /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
   lookup_var (u2s_var a 0) s1 = SOME (n2w X) /\
   lookup_var (u2s_var a 1) s1 = SOME 0w` by
    (simp[Abbr `s1`, jump_to_def, lookup_var_def] >> fs[lookup_var_def]) >>
  mp_tac (Q.INST [`s` |-> `s1`] u2s_check_mem_exit) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `t` >> gvs[] >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_path_mem_then >> simp[]
QED
