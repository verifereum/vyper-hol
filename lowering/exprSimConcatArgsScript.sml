(*
 * Concat case: compile_concat's operand loop as counted execution.
 *
 * TOP-LEVEL:
 *   concat_args_sim — from the operands' case judgments, the operand loop
 *     appends each operand's bytes to the data window and bumps the offset
 *     word by their length
 *)
Theory exprSimConcatArgs
Ancestors
  exprSimConcatPath exprSimConcatStore exprSimConcatStep exprSimAlloc
  exprSimWordArgs exprSimSource exprSimHypsDefs exprSimProps exprSimDefs
  exprBopSimProps exprOperandVar loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath freshWrites fragExec exprLowering
  exprLoweringProps compileEnv loweringStateRelDefs valueEncoding valueEncodingDefs valueEncodingProps valueEncodingProofs venomState
  vyperValue vyperTyping vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  vyperInterpreter vyperState venomMemProps venomExecSemantics words arithmetic list rich_list
Libs
  monadsyntax dep_rewrite

Theorem concat_mstore_local_region[local]:
  !cenv sc a w s nm lo len.
    local_region cenv sc (mstore a w s) nm lo len <=> local_region cenv sc s nm lo len
Proof
  simp[local_region_def, lookup_var_def, mstore_def]
QED

Theorem concat_mcopy_local_region[local]:
  !cenv sc d src n s nm lo len.
    local_region cenv sc (mcopy d src n s) nm lo len <=> local_region cenv sc s nm lo len
Proof
  simp[local_region_def, lookup_var_def, mcopy_def,
       write_memory_with_expansion_def, LET_THM]
QED

Theorem concat_mstore_fields[local]:
  !a w s.
    (mstore a w s).vs_current_bb = s.vs_current_bb /\
    (mstore a w s).vs_halted = s.vs_halted /\
    (mstore a w s).vs_allocas = s.vs_allocas /\
    (mstore a w s).vs_vars = s.vs_vars /\
    (mstore a w s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[mstore_def]
QED

Theorem concat_mcopy_fields[local]:
  !d src n s.
    (mcopy d src n s).vs_current_bb = s.vs_current_bb /\
    (mcopy d src n s).vs_halted = s.vs_halted /\
    (mcopy d src n s).vs_allocas = s.vs_allocas /\
    (mcopy d src n s).vs_vars = s.vs_vars /\
    (mcopy d src n s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[mcopy_def, write_memory_with_expansion_def, LET_THM]
QED

Theorem concat_mload_fields[local]:
  !a s V n. mload a (s with <|vs_vars := V; vs_inst_idx := n|>) = mload a s
Proof
  simp[mload_def]
QED

(* The offset store and the step's fresh registers keep the relation. *)
Theorem concat_offset_store_state_rel[local]:
  !ctx func cenv cx es s oinst o' w V n sx.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sx /\
    (!z. not_fresh_at sx z ==> FLOOKUP V z = FLOOKUP s.vs_vars z) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas oinst.inst_id = SOME (o',64) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       o' + 64 <= lb \/ lb + lsz <= o') ==>
    stmt_state_rel ctx func cenv cx es
      (mstore o' w s with <|vs_vars := V; vs_inst_idx := n|>)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es (mstore o' w s)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`o'`, `oinst`, `64`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `mstore o' w s with <|vs_vars := V; vs_inst_idx := n|> =
   (mstore o' w s with vs_vars := V) with vs_inst_idx := n` by simp[] >>
  pop_assum SUBST1_TAC >> rewrite_tac[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[local_ptrs_reserved_def, lookup_var_def, mstore_def] >>
  metis_tac[]
QED

(* A bytesM operand's store at the running offset, then the offset bump. *)
Theorem concat_fixed_arm:
  !ctx func cenv cx es t sx s2 data_ptr off_ptr x m bs ow k binst B bsz oinst.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; x];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) sx = ((), s2) /\
    fn_has_code sx s2 func /\ ~t.vs_halted /\
    t.vs_current_bb = sx.cs_current_bb /\
    t.vs_inst_idx = LENGTH sx.cs_current_insts /\
    local_ptrs_reserved cenv sx /\ stmt_state_rel ctx func cenv cx es t /\
    eval_operand data_ptr t = SOME (n2w (B + 32)) /\
    eval_operand off_ptr t = SOME ow /\
    eval_operand x t = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs)) /\
    (!z. data_ptr = Var z ==> not_fresh_at sx z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sx z) /\
    (!z. x = Var z ==> not_fresh_at sx z) /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
    mload (w2n ow) t = n2w k /\ LENGTH bs = m /\ m <= 32 /\
    32 + k + 32 <= bsz ==>
    ?t2. gas_path ctx func t 0 (OK t2) /\
      stmt_state_rel ctx func cenv cx es t2 /\ ~t2.vs_halted /\
      t2.vs_current_bb = s2.cs_current_bb /\
      t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
      t2.vs_allocas = t.vs_allocas /\
      (!z. not_fresh_at sx z ==> lookup_var z t2 = lookup_var z t) /\
      mem_bytes_at (B + 32) (k + m) t2.vs_memory =
        mem_bytes_at (B + 32) k t.vs_memory ++ bs /\
      mload (w2n ow) t2 = n2w (k + m) /\
      (!p n. (p + n <= B \/ B + bsz <= p) /\
             (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
             mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all concat_fixed_step_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule concat_fixed_code_shape >> strip_tac >>
  qabbrev_tac `a = B + 32 + k` >>
  `w2n (n2w (B + 32) + mload (w2n ow) t) = a` by
    (simp[word_add_n2w, Abbr `a`] >> irule LESS_MOD >> fs[dimword_def]) >>
  `mload (w2n ow) t + n2w m = n2w (k + m) : bytes32` by simp[word_add_n2w] >>
  qabbrev_tac `wd = word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32` >>
  qabbrev_tac `t2 = mstore (w2n ow) (n2w (k + m)) (mstore a wd t) with
    <|vs_vars := V; vs_inst_idx := LENGTH s2.cs_current_insts|>` >>
  `gas_path ctx func t 0 (OK t2)` by
    (qunabbrev_tac `t2` >>
     qpat_x_assum `gas_path _ _ _ _ _` mp_tac >> asm_rewrite_tac[]) >>
  `!p n. (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
     mem_bytes_at p n (mstore (w2n ow) (n2w (k + m)) (mstore a wd t)).vs_memory =
     mem_bytes_at p n t.vs_memory` by
    (rpt gen_tac >> disch_tac >> irule EQ_TRANS >>
     qexists_tac `mem_bytes_at p n (mstore a wd t).vs_memory` >> conj_tac
     >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
     irule mstore_mem_bytes_at_disjoint >> qunabbrev_tac `a` >> decide_tac) >>
  qexists_tac `t2` >> asm_rewrite_tac[] >>
  `stmt_state_rel ctx func cenv cx es (mstore a wd t)` by
    (irule literal_mstore_state_rel >> conj_tac
     >- (qexistsl_tac [`B`, `binst`, `bsz`] >> simp[Abbr `a`] >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  rpt conj_tac
  >- (qunabbrev_tac `t2` >> irule concat_offset_store_state_rel >>
      rpt conj_tac
      >~ [`local_region`] >- (simp[concat_mstore_local_region] >> metis_tac[])
      >~ [`ALLOCA`] >- (qexists_tac `oinst` >> simp[mstore_def])
      >~ [`local_ptrs_reserved`] >- (qexists_tac `sx` >> simp[mstore_def]) >>
      first_assum ACCEPT_TAC)
  >- simp[Abbr `t2`, concat_mstore_fields]
  >- simp[Abbr `t2`, concat_mstore_fields]
  >- simp[Abbr `t2`, concat_mstore_fields]
  >- simp[Abbr `t2`, concat_mstore_fields]
  >- simp[Abbr `t2`, concat_mstore_fields, lookup_var_def]
  >- (`mem_bytes_at (B + 32) (k + LENGTH bs)
         (mstore (w2n ow) (n2w (k + LENGTH bs)) (mstore a wd t)).vs_memory =
       mem_bytes_at (B + 32) k t.vs_memory ++ bs` by
        (qunabbrev_tac `wd` >> qunabbrev_tac `a` >>
         irule concat_fixed_mem >> simp[]) >>
      simp[Abbr `t2`] >> metis_tac[])
  >- simp[Abbr `t2`, concat_mload_fields, mload_mstore_same] >>
  rpt gen_tac >> disch_tac >> simp[Abbr `t2`] >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem concat_bytes_arm:
  !ctx func cenv cx es t sx s2 mem_ptr data_ptr off_ptr sw bs ow k binst B bsz
   oinst.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) sx = ((), s2) /\
    fn_has_code sx s2 func /\ ~t.vs_halted /\
    t.vs_current_bb = sx.cs_current_bb /\
    t.vs_inst_idx = LENGTH sx.cs_current_insts /\
    local_ptrs_reserved cenv sx /\ stmt_state_rel ctx func cenv cx es t /\
    eval_operand mem_ptr t = SOME sw /\
    eval_operand data_ptr t = SOME (n2w (B + 32)) /\
    eval_operand off_ptr t = SOME ow /\
    (!z. mem_ptr = Var z ==> not_fresh_at sx z) /\
    (!z. data_ptr = Var z ==> not_fresh_at sx z) /\
    (!z. off_ptr = Var z ==> not_fresh_at sx z) /\
    mload (w2n sw) t = n2w (LENGTH bs) /\
    mem_bytes_at (w2n sw + 32) (LENGTH bs) t.vs_memory = bs /\
    w2n sw + 32 < dimword (:256) /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
    mload (w2n ow) t = n2w k /\ 32 + k + LENGTH bs <= bsz ==>
    ?t2. gas_path ctx func t 0 (OK t2) /\
      stmt_state_rel ctx func cenv cx es t2 /\ ~t2.vs_halted /\
      t2.vs_current_bb = s2.cs_current_bb /\
      t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
      t2.vs_allocas = t.vs_allocas /\
      (!z. not_fresh_at sx z ==> lookup_var z t2 = lookup_var z t) /\
      mem_bytes_at (B + 32) (k + LENGTH bs) t2.vs_memory =
        mem_bytes_at (B + 32) k t.vs_memory ++ bs /\
      mload (w2n ow) t2 = n2w (k + LENGTH bs) /\
      (!p n. (p + n <= B \/ B + bsz <= p) /\
             (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
             mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all concat_bytes_step_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule concat_bytes_code_shape >> strip_tac >>
  qabbrev_tac `a = B + 32 + k` >>
  `w2n (n2w (B + 32) + mload (w2n ow) t) = a` by
    (simp[word_add_n2w, Abbr `a`] >> irule LESS_MOD >> fs[dimword_def]) >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (simp[word_add_def] >> irule LESS_MOD >> fs[dimword_def]) >>
  `w2n (mload (w2n sw) t) = LENGTH bs` by
    (asm_rewrite_tac[w2n_n2w] >> irule LESS_MOD >> fs[dimword_def]) >>
  `mload (w2n ow) t + mload (w2n sw) t = n2w (k + LENGTH bs) : bytes32` by
    asm_rewrite_tac[word_add_n2w] >>
  qabbrev_tac `t1 = mcopy a (w2n sw + 32) (LENGTH bs) t` >>
  qabbrev_tac `t2 = mstore (w2n ow) (n2w (k + LENGTH bs)) t1 with
    <|vs_vars := V; vs_inst_idx := LENGTH s2.cs_current_insts|>` >>
  `gas_path ctx func t 0 (OK t2)` by
    (qunabbrev_tac `t2` >> qunabbrev_tac `t1` >>
     qpat_x_assum `gas_path _ _ _ _ _` mp_tac >> asm_rewrite_tac[]) >>
  `B <= a /\ a + LENGTH bs <= B + bsz` by (qunabbrev_tac `a` >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es t1` by
    (qunabbrev_tac `t1` >>
     qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `t`, `binst`, `B`, `bsz`,
                  `a`, `w2n sw + 32`, `LENGTH bs`]
       mp_tac alloca_mcopy_state_rel >>
     impl_tac >- metis_tac[] >>
     disch_then ACCEPT_TAC) >>
  `!p n. (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
     mem_bytes_at p n (mstore (w2n ow) (n2w (k + LENGTH bs)) t1).vs_memory =
     mem_bytes_at p n t.vs_memory` by
    (rpt gen_tac >> disch_tac >> irule EQ_TRANS >>
     qexists_tac `mem_bytes_at p n t1.vs_memory` >> conj_tac
     >- (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
     qunabbrev_tac `t1` >> irule mcopy_mem_bytes_at_disjoint >>
     qunabbrev_tac `a` >> decide_tac) >>
  qexists_tac `t2` >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qunabbrev_tac `t2` >> irule concat_offset_store_state_rel >>
      rpt conj_tac
      >~ [`local_region`]
      >- (simp[Abbr `t1`, concat_mcopy_local_region] >> metis_tac[])
      >~ [`ALLOCA`]
      >- (qexists_tac `oinst` >> simp[Abbr `t1`, concat_mcopy_fields])
      >~ [`local_ptrs_reserved`]
      >- (qexists_tac `sx` >> simp[Abbr `t1`, concat_mcopy_fields]) >>
      first_assum ACCEPT_TAC)
  >- simp[Abbr `t2`, Abbr `t1`, concat_mstore_fields, concat_mcopy_fields]
  >- (simp[Abbr `t2`, Abbr `t1`, concat_mstore_fields, concat_mcopy_fields] >>
      fs[])
  >- (simp[Abbr `t2`, Abbr `t1`, concat_mstore_fields, concat_mcopy_fields] >>
      fs[])
  >- simp[Abbr `t2`, Abbr `t1`, concat_mstore_fields, concat_mcopy_fields]
  >- (simp[Abbr `t2`, Abbr `t1`, concat_mstore_fields, concat_mcopy_fields,
           lookup_var_def] >> metis_tac[])
  >- (`mem_bytes_at (B + 32) (k + LENGTH bs)
         (mstore (w2n ow) (n2w (k + LENGTH bs)) t1).vs_memory =
       mem_bytes_at (B + 32) k t.vs_memory ++ bs` by
        (qunabbrev_tac `t1` >> qunabbrev_tac `a` >>
         irule concat_bytes_mem >> asm_rewrite_tac[] >> decide_tac) >>
      simp[Abbr `t2`] >> metis_tac[])
  >- simp[Abbr `t2`, concat_mload_fields, mload_mstore_same] >>
  rpt gen_tac >> disch_tac >> simp[Abbr `t2`] >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

(* Frame composition for one operand: the head's expr_post (s0 to t), the
   arm's store (t to t2) and the tail's frames (t2 to u) give the loop's
   frames from s0 to u. *)
Theorem concat_args_glue:
  !ctx func cenv cx e es sa s1 s2 s0 es1 es2 v op t t2 u B bsz ow k bv bvs.
    expr_post ctx func cenv cx e es sa s1 s0 es1 v op t /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s2.cs_next_id /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    t2.vs_allocas = t.vs_allocas /\
    (!z. not_fresh_at s1 z ==> lookup_var z t2 = lookup_var z t) /\
    mem_bytes_at (B + 32) (k + LENGTH bv) t2.vs_memory =
      mem_bytes_at (B + 32) k t.vs_memory ++ bv /\
    (!p n. (p + n <= B \/ B + bsz <= p) /\
           (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
           mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory) /\
    mem_bytes_at (B + 32) k t.vs_memory = mem_bytes_at (B + 32) k s0.vs_memory /\
    mem_bytes_at (B + 32) (k + LENGTH bv + LENGTH bvs) u.vs_memory =
      mem_bytes_at (B + 32) (k + LENGTH bv) t2.vs_memory ++ bvs /\
    (!z w. not_fresh_at s2 z /\ lookup_var z t2 = SOME w ==>
           lookup_var z u = SOME w) /\
    (!aid a. FLOOKUP t2.vs_allocas aid = SOME a ==>
             FLOOKUP u.vs_allocas aid = SOME a) /\
    (!aid p n. FLOOKUP t2.vs_allocas aid = SOME (p,n) /\ aid < s2.cs_next_id /\
       (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) /\
       (!name lo sz. local_region cenv es1.scopes t2 name lo sz ==>
                     p + n <= lo \/ lo + sz <= p) ==>
       mem_bytes_at p n u.vs_memory = mem_bytes_at p n t2.vs_memory) /\
    locals_kept cenv es1 es2 t2 u ==>
    mem_bytes_at (B + 32) (k + LENGTH (bv ++ bvs)) u.vs_memory =
      mem_bytes_at (B + 32) k s0.vs_memory ++ (bv ++ bvs) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
           lookup_var z u = SOME w) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
             FLOOKUP u.vs_allocas aid = SOME a) /\
    (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
       (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) /\
       (!name lo sz. local_region cenv es.scopes s0 name lo sz ==>
                     p + n <= lo \/ lo + sz <= p) ==>
       mem_bytes_at p n u.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    locals_kept cenv es es2 s0 u
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `sa.cs_next_var <= s2.cs_next_var` by decide_tac >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
         lookup_var z t2 = SOME w` by
    (rpt strip_tac >> `not_fresh_at s1 z` by metis_tac[not_fresh_at_mono] >>
     metis_tac[]) >>
  `!name lb lsz. local_region cenv es1.scopes t name lb lsz ==>
     local_region cenv es.scopes s0 name lb lsz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[]) >>
  `!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
     local_region cenv es.scopes s0 name lb lsz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`sa`, `es1.scopes`, `t2`] >> asm_rewrite_tac[]) >>
  `locals_kept cenv es1 es1 t t2` by
    (irule locals_kept_regions >> rpt strip_tac >>
     first_x_assum irule >>
     `local_region cenv es.scopes s0 n b sz` by metis_tac[] >>
     metis_tac[]) >>
  `locals_kept cenv es es1 s0 t2` by
    (irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t`] >>
     asm_rewrite_tac[]) >>
  rpt conj_tac
  >- (`k + LENGTH (bv ++ bvs) = k + LENGTH bv + LENGTH bvs` by simp[] >>
      asm_rewrite_tac[] >> simp[])
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[]
  >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
           (qspecl_then [`aid`, `p`, `n`] mp_tac) >>
         impl_tac >- asm_rewrite_tac[] >> simp[]) >>
      `mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory` by
        (qpat_x_assum `!p n. _ ==> mem_bytes_at p n t2.vs_memory = _` irule >>
         asm_rewrite_tac[]) >>
      `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t2.vs_memory` by
        (qpat_x_assum `!aid p n. FLOOKUP t2.vs_allocas aid = SOME (p,n) /\ _ ==> _`
           (qspecl_then [`aid`, `p`, `n`] mp_tac) >>
         impl_tac
         >- (rpt conj_tac
             >- metis_tac[]
             >- decide_tac
             >- asm_rewrite_tac[]
             >- asm_rewrite_tac[] >>
             rpt strip_tac >> metis_tac[]) >>
         simp[]) >>
      asm_rewrite_tac[]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t2`] >>
  asm_rewrite_tac[]
QED

Theorem concat_mem_bytes_at_sub[local]:
  !b sz p n m1 m2.
    mem_bytes_at b sz m1 = mem_bytes_at b sz m2 /\ b <= p /\ p + n <= b + sz ==>
    mem_bytes_at p n m1 = mem_bytes_at p n m2
Proof
  rpt strip_tac >>
  qabbrev_tac `d = p - b` >> qabbrev_tac `r = b + sz - (p + n)` >>
  `sz = d + (n + r) /\ p = b + d` by (unabbrev_all_tac >> decide_tac) >>
  qpat_x_assum `mem_bytes_at b sz _ = _` mp_tac >>
  qpat_x_assum `sz = _` SUBST1_TAC >>
  qpat_x_assum `p = _` SUBST1_TAC >>
  rewrite_tac[mem_bytes_at_split_padded] >>
  strip_tac >> fs[APPEND_11_LENGTH]
QED

Theorem concat_mload_bytes[local]:
  !a s t.
    mem_bytes_at a 32 t.vs_memory = mem_bytes_at a 32 s.vs_memory ==>
    mload a t = mload a s
Proof
  rpt strip_tac >> rewrite_tac[GSYM mem_word_at_eq_mload] >>
  fs[mem_word_at_def, mem_bytes_at_def]
QED

(* The head operand's frame keeps the loop's registers, allocas, offset slot
   and written prefix, and the regions disjoint from the buffer stay so. *)
Theorem concat_args_pre:
  !ctx func cenv cx e es sa s1 s0 es1 v op t B bsz ow k binst oinst dv ov.
    expr_post ctx func cenv cx e es sa s1 s0 es1 v op t /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    lookup_var dv s0 = SOME (n2w (B + 32)) /\ lookup_var ov s0 = SOME ow /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    oinst.inst_id < sa.cs_next_id /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    32 + k <= bsz ==>
    lookup_var dv t = SOME (n2w (B + 32)) /\ lookup_var ov t = SOME ow /\
    FLOOKUP t.vs_allocas binst.inst_id = SOME (B,bsz) /\
    FLOOKUP t.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es1.scopes t name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    mload (w2n ow) t = mload (w2n ow) s0 /\
    mem_bytes_at (B + 32) k t.vs_memory = mem_bytes_at (B + 32) k s0.vs_memory
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `mem_bytes_at B bsz t.vs_memory = mem_bytes_at B bsz s0.vs_memory` by
    (qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (qspecl_then [`binst.inst_id`, `B`, `bsz`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >> simp[]) >>
  `mem_bytes_at (w2n ow) 64 t.vs_memory = mem_bytes_at (w2n ow) 64 s0.vs_memory` by
    (qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
       (qspecl_then [`oinst.inst_id`, `w2n ow`, `64`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >> simp[]) >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (rpt gen_tac >> strip_tac >>
      `local_region cenv es.scopes s0 name lb lsz` by
        (irule local_region_frame >>
         conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
         qexistsl_tac [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[]) >>
      metis_tac[])
  >- (irule concat_mload_bytes >> irule concat_mem_bytes_at_sub >>
      qexistsl_tac [`w2n ow`, `64`] >> asm_rewrite_tac[] >> decide_tac) >>
  irule concat_mem_bytes_at_sub >>
  qexistsl_tac [`B`, `bsz`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem concat_fixed_value[local]:
  !cx m v op s tv.
    expr_val_rel cx (BaseT (BytesT (Fixed m))) v op s /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
    value_has_type tv v ==>
    ?bs. v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
         eval_operand op s = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bs))
Proof
  rpt strip_tac >>
  `m <= 32 /\ tv = BaseTV (BytesT (Fixed m))` by
    gvs[evaluate_type_def, AllCaseEqs()] >>
  gvs[] >> Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[expr_val_rel_def, is_word_type_def, typed_val_to_w256_def, evaluate_type_def]
QED

Theorem concat_bytes_value[local]:
  !ctx func cenv cx ty v op s sa sb es tv.
    expr_val_rel cx ty v op s /\ expr_val_at cenv cx ty sa sb es v op s /\
    stmt_state_rel ctx func cenv cx es s /\ is_bytestring_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
    ?sw. eval_operand op s = SOME sw /\
      mload (w2n sw) s = n2w (LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) /\
      mem_bytes_at (w2n sw + 32) (LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) s.vs_memory = (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
      w2n sw + 32 < dimword (:256) /\
      LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= concat_payload_capacity ty
Proof
  rpt strip_tac >>
  `~is_word_type ty` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def, is_word_type_def]) >>
  `?w. eval_operand op s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory` by
    (fs[expr_val_rel_def] >> first_x_assum drule >> gvs[]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_val_at_def]) >>
  disch_then (qspec_then `tv` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  gvs[] >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  Cases_on `ty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[val_in_memory_def, val_footprint_def, mem_word_at_eq_mload,
      concat_payload_capacity_def, LET_THM] >>
  res_tac >> decide_tac
QED

Theorem concat_head_typed[local]:
  !cenv cx env e es v es'.
    expr_body_pre cenv cx env e es /\
    bind (eval_expr cx e) (read_result cx) es = (INL v, es') ==>
    expr_sim_inv cenv cx env es' /\
    (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
          value_has_type tv v) /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    ?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                     read_result cx tv s1 = (INL v, t1)
Proof
  rpt gen_tac >> strip_tac >>
  `(\r. read_result cx r) = read_result cx` by simp[FUN_EQ_THM] >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v, es')` by
    asm_rewrite_tac[] >>
  `?tv0 t0. eval_expr cx e es = (INL tv0, t0) /\
            read_result cx tv0 t0 = (INL v, es')` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
     Cases_on `eval_expr cx e es` >> rename1 `(r0, st0)` >>
     Cases_on `r0` >> simp[]) >>
  drule forced_eval_expr_preserves_scopes_dom >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
  >- first_assum ACCEPT_TAC >>
  metis_tac[]
QED

Theorem concat_fixed_step_mono[local]:
  !data_ptr off_ptr x m s1 s2.
    (do offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MSTORE [dst; x];
        new_offset <- emit_op ADD [offset_op; Lit (n2w m)];
        emit_void MSTORE [off_ptr; new_offset]
     od) s1 = ((), s2) ==> ci_mono s1 s2
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `stp s1 = ((),s2) ==> _` >>
  `ci_mono s1 (SND (stp s1))` suffices_by (rpt strip_tac >> gvs[]) >>
  qunabbrev_tac `stp` >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE gen_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem concat_bytes_step_mono[local]:
  !mem_ptr data_ptr off_ptr s1 s2.
    (do arg_len <- emit_op MLOAD [mem_ptr];
        arg_data <- emit_op ADD [mem_ptr; Lit 32w];
        offset_op <- emit_op MLOAD [off_ptr];
        dst <- emit_op ADD [data_ptr; offset_op];
        emit_void MCOPY [dst; arg_data; arg_len];
        new_offset <- emit_op ADD [offset_op; arg_len];
        emit_void MSTORE [off_ptr; new_offset]
     od) s1 = ((), s2) ==> ci_mono s1 s2
Proof
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `stp s1 = ((),s2) ==> _` >>
  `ci_mono s1 (SND (stp s1))` suffices_by (rpt strip_tac >> gvs[]) >>
  qunabbrev_tac `stp` >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE gen_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void]
QED

(* One operand: after the head's code, its arm stores the operand's bytes
   at the running offset; the facts the tail and the frame composition
   need. *)
Theorem concat_head_arm:
  !ctx func cenv cx e args es sa s1 sb s0 es1 v op t B bsz ow k P binst
   oinst dv ov tv.
    compile_concat compile_expr cenv (e::args) (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) (e::args))
      (Var ov) sa = ((), sb) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, s1) /\
    (is_bytestring_type (expr_type e) \/
     ?m. expr_type e = BaseT (BytesT (Fixed m))) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
    expr_post ctx func cenv cx e es sa s1 s0 es1 v op t /\
    ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    lookup_var dv s0 = SOME (n2w (B + 32)) /\ lookup_var ov s0 = SOME ow /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\ B + bsz < dimword (:256) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32 + P + SUM (MAP concat_payload_capacity (MAP expr_type (e::args))) <= bsz /\
    32 + concat_data_bound P (MAP expr_type (e::args)) <= bsz ==>
    ?s2 t2.
      compile_concat compile_expr cenv args (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) args)
        (Var ov) s2 = ((), sb) /\
      ci_mono sa s1 /\ ci_mono s1 s2 /\ fn_has_code s2 sb func /\
      gas_path ctx func t 0 (OK t2) /\
      stmt_state_rel ctx func cenv cx es1 t2 /\ ~t2.vs_halted /\
      t2.vs_current_bb = s2.cs_current_bb /\
      t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
      lookup_var dv t2 = SOME (n2w (B + 32)) /\ lookup_var ov t2 = SOME ow /\
      FLOOKUP t2.vs_allocas binst.inst_id = SOME (B, bsz) /\
      FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
      (!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
         (B + bsz <= lb \/ lb + lsz <= B) /\
         (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
      mload (w2n ow) t2 = n2w (k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) /\
      k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= P + concat_payload_capacity (expr_type e) /\
      t2.vs_allocas = t.vs_allocas /\
      (!z. not_fresh_at s1 z ==> lookup_var z t2 = lookup_var z t) /\
      mem_bytes_at (B + 32) (k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) t2.vs_memory =
        mem_bytes_at (B + 32) k t.vs_memory ++ (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
      (!p n. (p + n <= B \/ B + bsz <= p) /\
             (p + n <= w2n ow \/ w2n ow + 64 <= p) ==>
             mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory) /\
      mem_bytes_at (B + 32) k t.vs_memory = mem_bytes_at (B + 32) k s0.vs_memory
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `ci_mono sa s1` by
    (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `sa.cs_next_var <= s1.cs_next_var /\ cs_extends sa s1` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  `not_fresh_at s1 dv /\ not_fresh_at s1 ov` by metis_tac[not_fresh_at_mono] >>
  `32 + P + (concat_payload_capacity (expr_type e) +
     SUM (MAP concat_payload_capacity (MAP expr_type args))) <= bsz` by
    (qpat_x_assum `32 + P + SUM _ <= _` mp_tac >> simp[]) >>
  `32 + k <= bsz` by decide_tac >>
  `expr_post ctx func cenv cx e es sa s1 s0 es1 v op t` by first_assum ACCEPT_TAC >>
  drule_all concat_args_pre >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (qpat_x_assum `is_bytestring_type (expr_type e) \/ _` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type e) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[evaluate_type_def, is_word_type_def]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `post_value_type cenv e = expr_type e`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `mload (w2n ow) t = n2w k` by metis_tac[] >>
  `eval_operand (Var dv) t = SOME (n2w (B + 32)) /\
   eval_operand (Var ov) t = SOME ow` by
    (rewrite_tac[eval_operand_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `(!z. Var dv = Var z ==> not_fresh_at s1 z) /\
   (!z. Var ov = Var z ==> not_fresh_at s1 z)` by
    (rw[] >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv es1.scopes t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  Cases_on `is_bytestring_type (expr_type e)` >> asm_rewrite_tac[] >> strip_tac
  >- suspend "bytes"
  >> suspend "fixed"
QED

Resume concat_head_arm[bytes]:
  drule compile_concat_bytes_cons >> strip_tac >>
  `mem_ptr = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (mem_ptr, _)` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `mem_ptr = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule concat_bytes_step_mono >> strip_tac >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     `cs_extends sb sb` by rewrite_tac[cs_extends_refl] >>
     metis_tac[fn_has_code_mid]) >>
  drule_all concat_bytes_value >> strip_tac >>
  `32 + k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= bsz` by decide_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es1`, `t`, `s1`, `s2`, `op`,
               `Var dv`, `Var ov`, `sw`, `(case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])`, `ow`, `k`, `binst`, `B`,
               `bsz`, `oinst`] mp_tac concat_bytes_arm >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >> suspend "common_b"
QED

Resume concat_head_arm[fixed]:
  `?m. expr_type e = BaseT (BytesT (Fixed m))` by fs[] >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[] >> strip_tac >>
  drule compile_concat_fixed_cons >> strip_tac >>
  `v' = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (v', _)` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `v' = op` SUBST_ALL_TAC >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule concat_fixed_step_mono >> strip_tac >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (fs[ci_mono_def] >>
     `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
     `cs_extends sb sb` by rewrite_tac[cs_extends_refl] >>
     metis_tac[fn_has_code_mid]) >>
  `expr_val_rel cx (BaseT (BytesT (Fixed m))) v op t` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv` by metis_tac[] >>
  drule_all concat_fixed_value >> strip_tac >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `32 + k + 32 <= bsz` by
    (qpat_x_assum `32 + concat_data_bound _ _ <= _` mp_tac >>
     asm_simp_tac (srw_ss()) [concat_data_bound_def, LET_THM,
                              is_bytestring_type_def] >>
     rewrite_tac[arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
  `concat_payload_capacity (expr_type e) = m` by
    asm_simp_tac (srw_ss()) [concat_payload_capacity_def] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es1`, `t`, `s1`, `s2`,
               `Var dv`, `Var ov`, `op`, `m`, `bs`, `ow`, `k`, `binst`, `B`,
               `bsz`, `oinst`] mp_tac concat_fixed_arm >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >> suspend "common_f"
QED

Resume concat_head_arm[common_b]:
  qexistsl_tac [`s2`, `t2`] >>
  `lookup_var dv t2 = SOME (n2w (B + 32)) /\ lookup_var ov t2 = SOME ow` by
    (conj_tac >>
     qpat_assum `!z. not_fresh_at s1 z ==> _` (fn th => DEP_REWRITE_TAC[th]) >>
     asm_rewrite_tac[]) >>
  `FLOOKUP t2.vs_allocas binst.inst_id = SOME (B, bsz) /\
   FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow, 64)` by
    (qpat_assum `t2.vs_allocas = _` (fn th => rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
         (B + bsz <= lb \/ lb + lsz <= B) /\
         (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)` by
     (rpt gen_tac >> strip_tac >>
      `local_region cenv es1.scopes t name lb lsz` by
        (irule local_region_frame >>
         conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
         qexistsl_tac [`s1`, `es1.scopes`, `t2`] >> asm_rewrite_tac[] >>
         metis_tac[]) >>
      metis_tac[]) >>
  `k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= P + concat_payload_capacity (expr_type e)` by decide_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `compile_concat _ _ args _ _ _ _ = _` mp_tac >> simp[LET_THM]
QED

Resume concat_head_arm[common_f]:
  qexistsl_tac [`s2`, `t2`] >>
  `lookup_var dv t2 = SOME (n2w (B + 32)) /\ lookup_var ov t2 = SOME ow` by
    (conj_tac >>
     qpat_assum `!z. not_fresh_at s1 z ==> _` (fn th => DEP_REWRITE_TAC[th]) >>
     asm_rewrite_tac[]) >>
  `FLOOKUP t2.vs_allocas binst.inst_id = SOME (B, bsz) /\
   FLOOKUP t2.vs_allocas oinst.inst_id = SOME (w2n ow, 64)` by
    (qpat_assum `t2.vs_allocas = _` (fn th => rewrite_tac[th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `(case BytesV bs of BytesV bs => bs | StringV str => MAP (n2w o ORD) str
                    | _ => []) = bs` by simp[] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  qpat_x_assum `LENGTH bs = m` (fn th => rewrite_tac[th]) >>
  `!name lb lsz. local_region cenv es1.scopes t2 name lb lsz ==>
         (B + bsz <= lb \/ lb + lsz <= B) /\
         (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)` by
     (rpt gen_tac >> strip_tac >>
      `local_region cenv es1.scopes t name lb lsz` by
        (irule local_region_frame >>
         conj_tac >- (qexists_tac `func` >> first_assum ACCEPT_TAC) >>
         qexistsl_tac [`s1`, `es1.scopes`, `t2`] >> asm_rewrite_tac[] >>
         metis_tac[]) >>
      metis_tac[]) >>
  `k + m <= P + concat_payload_capacity (BaseT (BytesT (Fixed m)))` by
    (simp[concat_payload_capacity_def] >> decide_tac) >>
  `!p n. (n + p <= B \/ B + bsz <= p) /\ (n + p <= w2n ow \/ w2n ow + 64 <= p) ==>
         mem_bytes_at p n t2.vs_memory = mem_bytes_at p n t.vs_memory` by
    (rpt strip_tac >>
     qpat_x_assum `!p n. _ ==> mem_bytes_at p n t2.vs_memory = _` irule >>
     decide_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `compile_concat _ _ args _ _ _ _ = _` mp_tac >> simp[LET_THM]
QED

Finalise concat_head_arm

Theorem concat_cons_mono[local]:
  !cenv e args dv ov sa sb op s1.
    compile_concat compile_expr cenv (e::args) (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) (e::args))
      (Var ov) sa = ((), sb) /\
    lower_value compile_expr cenv (expr_type e) e sa = (op, s1) /\
    (is_bytestring_type (expr_type e) \/
     ?m. expr_type e = BaseT (BytesT (Fixed m))) ==>
    ci_mono s1 sb
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  Cases_on `is_bytestring_type (expr_type e)` >> asm_rewrite_tac[] >> strip_tac
  >- (drule compile_concat_bytes_cons >> strip_tac >>
      `mem_ptr = op /\ s1' = s1` by
        (qpat_x_assum `lower_value _ _ _ _ _ = (mem_ptr, _)` mp_tac >>
         asm_rewrite_tac[] >> simp[]) >>
      qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
      drule concat_bytes_step_mono >> strip_tac >>
      `ci_mono s2 sb` by
        metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
      fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `?m. expr_type e = BaseT (BytesT (Fixed m))` by fs[] >>
  qpat_x_assum `compile_concat _ _ (_::_) _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> simp[] >> strip_tac >>
  drule compile_concat_fixed_cons >> strip_tac >>
  `v = op /\ s1' = s1` by
    (qpat_x_assum `lower_value _ _ _ _ _ = (v, _)` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  qpat_x_assum `s1' = s1` SUBST_ALL_TAC >>
  drule concat_fixed_step_mono >> strip_tac >>
  `ci_mono s2 sb` by
    metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND] >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Theorem concat_args_sim:
  !args P k ctx func cenv cx env nocalls es sa sb s0 dv ov ow
   binst B bsz oinst.
    compile_concat compile_expr cenv args (Var dv) (MAP (\e. let ety = expr_type e in
                if is_bytestring_type ety then (T, 0:num)
                else case ety of
                       BaseT (BytesT (Fixed m)) => (F, m)
                     | _ => (F, 32:num)) args)
      (Var ov) sa = ((), sb) /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
               ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
    expr_sim_inv cenv cx env es /\
    (!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
       expr_body_pre cenv cx env e st /\ (nocalls ==> int_calls_expr e = [])) /\
    exprs_case nocalls ctx func cenv cx args /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var dv s0 = SOME (n2w (B + 32)) /\ lookup_var ov s0 = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B, bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow, 64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B + bsz <= lb \/ lb + lsz <= B) /\
       (w2n ow + 64 <= lb \/ lb + lsz <= w2n ow)) /\
    (B + bsz <= w2n ow \/ w2n ow + 64 <= B) /\
    B + bsz < dimword (:256) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32 + P + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
    32 + concat_data_bound P (MAP expr_type args) <= bsz ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee t /\
         LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                              value_has_type tv v) args vs /\
         mem_bytes_at (B + 32) (k + LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs))) t.vs_memory =
           mem_bytes_at (B + 32) k s0.vs_memory ++ FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs) /\
         mload (w2n ow) t = n2w (k + LENGTH (FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs))) /\
         (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
                lookup_var z t = SOME w) /\
         (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
                  FLOOKUP t.vs_allocas aid = SOME a) /\
         (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
            aid < sa.cs_next_id /\
            (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) /\
            (!name lo sz. local_region cenv es.scopes s0 name lo sz ==>
                          p + n <= lo \/ lo + sz <= p) ==>
            mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
         locals_kept cenv es ee s0 t /\
         (~EXISTS expr_has_effect args ==>
            (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
               mem_bytes_at lb lsz t.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
            !p n. (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) /\
              (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                 sa.cs_next_id <= inst.inst_id /\
                 FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                 regions_disjoint p n b sz) ==>
              mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory))
      (\rr ee r. ?exc. rr = INR exc /\
         expr_exit (INR exc : eval_result + exception) r)
Proof
  Induct
  >- (rpt strip_tac >>
      gvs[compile_concat_def, comp_return_def] >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def, gas_marked_exec_def, gas_explicit_def,
           eval_exprs_nil, gas_marked_path_def] >>
      qexistsl_tac [`INL []`, `es`, `OK s0`] >>
      simp[cj 1 gas_path_rules, locals_kept_refl] >> gvs[]) >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rename1 `exprs_case nocalls ctx func cenv cx (e::args)` >>
  qpat_x_assum `exprs_case _ _ _ _ _ (_::_)`
    (strip_assume_tac o REWRITE_RULE [exprs_case_def]) >>
  `expr_body_pre cenv cx env e es /\ (nocalls ==> int_calls_expr e = [])` by
    (qpat_assum `!e st. MEM _ _ /\ _ ==> _` (qspecl_then [`e`, `es`] mp_tac) >>
     simp[]) >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
     disch_then (qspecl_then [`env`, `expr_type e`, `es`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `EVERY _ (e::args)`
    (CONJUNCTS_THEN assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ _ sa = (op, s1)` >>
  `ci_mono sa s1` by
    (drule (cj 2 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono s1 sb` by
    (qspecl_then [`cenv`, `e`, `args`, `dv`, `ov`, `sa`, `sb`, `op`, `s1`]
       mp_tac concat_cons_mono >>
     impl_tac >- (rpt conj_tac >- first_assum ACCEPT_TAC
                  >- first_assum ACCEPT_TAC >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `fn_has_code sa s1 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_refl]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  drule_all expr_sim_apply >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume concat_args_sim[head_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
   (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    asm_simp_tac (srw_ss()) [expr_body_pre_gas_obs] >>
  drule_all concat_head_typed >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by fs[] >>
  `EVERY (\e. is_bytestring_type (expr_type e) \/
              ?m. expr_type e = BaseT (BytesT (Fixed m))) args` by fs[] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `args`, `es`, `sa`, `s1`, `sb`,
               `s0`, `es_end with gas_obs := []`, `v`, `op`, `t`, `B`, `bsz`,
               `ow`, `k`, `P`, `binst`, `oinst`, `dv`, `ov`, `tv`]
    mp_tac concat_head_arm >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  `gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
     (es,s0) marks (INL v) es_end (OK t2)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ (OK t)` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     mp_tac (Q.INST [`fn` |-> `func`, `s` |-> `s0`, `n` |-> `LENGTH (marks : bool list)`,
                     `m` |-> `0`, `r` |-> `OK t2`] gas_path_then) >>
     simp[]) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ (OK t)` kall_tac >>
  `exprs_case nocalls ctx func cenv cx args` by metis_tac[] >>
  `!e' st. MEM e' args /\ expr_sim_inv cenv cx env st ==>
     expr_body_pre cenv cx env e' st /\ (nocalls ==> int_calls_expr e' = [])` by
    metis_tac[MEM] >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
   sa.cs_next_id <= s2.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `not_fresh_at s2 dv /\ not_fresh_at s2 ov` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `binst.inst_id < s2.cs_next_id /\ oinst.inst_id < s2.cs_next_id` by decide_tac >>
  `32 + (P + concat_payload_capacity (expr_type e)) +
     SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz` by
    decide_tac >>
  `32 + concat_data_bound (P + concat_payload_capacity (expr_type e))
     (MAP expr_type args) <= bsz` by
    (qpat_x_assum `concat_data_bound P (_::_) + 32 <= bsz` mp_tac >>
     simp[concat_data_bound_def, LET_THM] >> rw[MAX_DEF]) >>
  first_x_assum (qspecl_then
    [`P + concat_payload_capacity (expr_type e)`, `k + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])`,
     `ctx`, `func`, `cenv`, `cx`, `env`, `nocalls`, `es_end with gas_obs := []`,
     `s2`, `sb`, `t2`, `dv`, `ov`, `ow`, `binst`, `B`, `bsz`, `oinst`] mp_tac) >>
  qpat_x_assum `compile_concat _ _ args _ _ _ s2 = _`
    (assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED

Resume concat_args_sim[head_exit]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  qpat_x_assum `(\res ee r. expr_exit res r) _ _ _` (mp_tac o BETA_RULE) >>
  qpat_x_assum `exit_result r` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `y` >> Cases_on `r` >> simp[expr_exit_def, exit_result_def] >>
  TRY (rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def])
QED

Resume concat_args_sim[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any wb_args_head_exempt_cert >> goal_assum (drule_at Any)
QED

Resume concat_args_sim[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `gas_marked_exec _ _ (eval_exprs cx args) _ _ (INL vs) es_end' (OK tu)` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK tu`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >>
  `!aid p n. FLOOKUP t2.vs_allocas aid = SOME (p,n) /\ aid < s2.cs_next_id /\
     (p + n <= B \/ B + bsz <= p) /\ (p + n <= w2n ow \/ w2n ow + 64 <= p) /\
     (!name lo sz. local_region cenv (es_end with gas_obs := []).scopes t2 name lo sz ==>
                   p + n <= lo \/ lo + sz <= p) ==>
     mem_bytes_at p n tu.vs_memory = mem_bytes_at p n t2.vs_memory` by
    (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_x_assum `!aid p n. FLOOKUP t2.vs_allocas aid = SOME (p,n) /\ _ ==>
                     mem_bytes_at _ _ tu.vs_memory = _` irule >>
     rpt conj_tac
     >- (rpt strip_tac >> first_x_assum drule >> decide_tac)
     >- (qexists_tac `aid` >> conj_tac >> first_assum ACCEPT_TAC)
     >- decide_tac >>
     decide_tac) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `e`, `es`, `sa`, `s1`, `s2`, `s0`,
               `es_end with gas_obs := []`, `es_end' with gas_obs := []`,
               `v`, `op`, `t`, `t2`, `tu`, `B`,
               `bsz`, `ow`, `k`, `(case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])`, `FLAT (MAP (\v. case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) vs)`]
    mp_tac concat_args_glue >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >> suspend "post"
QED

Resume concat_args_sim[post]:
  qexists_tac `tu` >> conj_tac >- REFL_TAC >>
  qexists_tac `v::vs` >> conj_tac >- REFL_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_x_assum `expr_sim_inv _ _ _ (es_end' with gas_obs := [])` mp_tac >>
      simp[])
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (es_end' with gas_obs := []) tu` mp_tac >>
      simp[])
  >- (qexistsl_tac [`v`, `vs`] >> simp[])
  >- (rewrite_tac[listTheory.MAP, listTheory.FLAT] >> BETA_TAC >>
      first_assum ACCEPT_TAC)
  >- (qpat_x_assum `mload (w2n ow) tu = _` (fn th => rewrite_tac[th]) >>
      simp[])
  >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ _ ==>
                      mem_bytes_at _ _ tu.vs_memory = _` irule >>
      rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!name lo sz. local_region cenv es.scopes s0 name lo sz ==>
                          _ \/ _` drule >>
          decide_tac)
      >- (qexists_tac `aid` >> conj_tac >> first_assum ACCEPT_TAC)
      >- decide_tac >>
      decide_tac) >>
  (* the pure frame, clear of the two concat buffers *)
  strip_tac >>
  `~expr_has_effect e /\ ~EXISTS expr_has_effect args` by fs[] >>
  `pure_frame cenv func es sa s0 t` by
    (drule_all expr_post_pure_frame >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `_ ==> (!n lb lsz. local_region _ _ t2 _ _ _ ==>
                  mem_bytes_at _ _ tu.vs_memory = _) /\ _` mp_tac >>
  impl_tac >- fs[] >> strip_tac >>
  `wb_frame cenv es (es_end with gas_obs := []) sa s0 t` by
    (drule expr_post_frame >> disch_then ACCEPT_TAC) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t2 = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at s1 x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     `lookup_var x t = SOME w` by fs[wb_frame_def] >>
     metis_tac[]) >>
  qpat_x_assum `pure_frame _ _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE [pure_frame_def]) >>
  conj_tac
  >- (qx_genl_tac [`nm`, `lb`, `lsz`] >> strip_tac >>
      `local_region cenv (es_end with gas_obs := []).scopes t2 nm lb lsz` by
        (match_mp_tac local_region_frame_fwd >>
         qexistsl_tac [`es.scopes`, `sa`, `s0`] >> simp[]) >>
      `mem_bytes_at lb lsz t.vs_memory = mem_bytes_at lb lsz s0.vs_memory` by
        (qpat_x_assum `!n b sz. local_region cenv es.scopes s0 n b sz ==>
                         mem_bytes_at b sz t.vs_memory = _`
           (drule_then ACCEPT_TAC)) >>
      `mem_bytes_at lb lsz t2.vs_memory = mem_bytes_at lb lsz t.vs_memory` by
        (qpat_x_assum `!p n. _ /\ _ ==> mem_bytes_at p n t2.vs_memory = _` irule >>
         qpat_x_assum `!name lb lsz. local_region cenv es.scopes s0 _ _ _ ==> _ /\ _`
           drule >> decide_tac) >>
      `mem_bytes_at lb lsz tu.vs_memory = mem_bytes_at lb lsz t2.vs_memory` by
        (qpat_x_assum `!n lb lsz. local_region _ _ t2 _ _ _ ==>
                         mem_bytes_at _ _ tu.vs_memory = _`
           (drule_then ACCEPT_TAC)) >>
      simp[]) >>
  qx_genl_tac [`off`, `len`] >> strip_tac >>
  `mem_bytes_at off len tu.vs_memory = mem_bytes_at off len t2.vs_memory` by
    (qpat_x_assum `!p n. _ /\ _ /\ (!inst b sz. _ ==> _) ==>
                     mem_bytes_at p n tu.vs_memory = _` irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `mem_bytes_at off len t2.vs_memory = mem_bytes_at off len t.vs_memory` by
    (qpat_x_assum `!p n. _ /\ _ ==> mem_bytes_at p n t2.vs_memory = _` irule >>
     conj_tac >> decide_tac) >>
  `mem_bytes_at off len t.vs_memory = mem_bytes_at off len s0.vs_memory` by
    (qpat_x_assum `!off len. (!inst b sz. _ ==> _) ==>
                     mem_bytes_at off len t.vs_memory = _` irule >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [`inst`, `b`, `sz`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_x_assum `!aid a. FLOOKUP t2.vs_allocas aid = SOME a ==> _` irule >>
         qpat_x_assum `t2.vs_allocas = t.vs_allocas` (fn th => rewrite_tac[th]) >>
         first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  simp[]
QED

Resume concat_args_sim[tail_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[]
QED

Resume concat_args_sim[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED

Finalise concat_args_sim
