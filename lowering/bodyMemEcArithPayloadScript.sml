Theory bodyMemEcArithPayload
Ancestors
  bodyMemEcArithCode bodyMemEcArithTransfers exprSimCalldataSlice
  emitHelper emitHelperProps compileEnv context venomState venomInst
  venomExecSemantics exprLoweringProps exprSimWordBuiltins
  exprSimPrecompiles immutableMemoryFrame valueEncodingProps
  bodyMemEcArithPrefix fragExecMem

(* Restatement of private exprSimECArith.ecmul_input_stores_run;
   original: alan-ref/base/exprSimECArithScript.sml.txt, lines 951-1020.
   Uses the scalar boundary rather than repeating instruction execution. *)
Theorem ecmul_input_stores_run:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+64) wscalar
        (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
          (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  drule (Q.INST [`ops` |-> `[scalar]`, `len` |-> `96`]
    (SPEC_ALL ec_point_prefix_then_run)) >>
  disch_then (qspecl_then [`scalar`, `s`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  `eval_operand ib s1 = SOME bw /\ eval_operand scalar s1 = SOME wscalar` by
    (gvs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [ib;scalar] ==> not_fresh_at sc x` by
    (gvs[] >> metis_tac[]) >>
  drule_all ec_scalar_store_run >> strip_tac >>
  drule_then strip_assume_tac ec_scalar_store_shape >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  `w2n (bw+64w) = w2n bw+64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  qexists_tac `t` >> conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac
  >- (qpat_x_assum `t.vs_memory = _` SUBST1_TAC >> simp[] >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then [`w2n bw+64`, `wscalar`] mp_tac) >> simp[NoAsms]) >>
  conj_tac
  >- (qpat_assum `_ = s1`
       (mp_tac o Q.AP_TERM `\st. st with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>`) >>
      simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
   t.vs_labels = s.vs_labels` by gvs[venom_state_component_equality] >>
  simp[] >> rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]
QED

(* Restatement of private exprSimECArith.ec_point_words_scratch_store;
   original reference lines 563-573. *)
Theorem ec_point_words_scratch_store:
  !base sz point off w s.
  regions_disjoint base sz point 64 /\ off + 32 <= sz ==>
  mem_word_at point (mstore (base + off) w s).vs_memory =
    mem_word_at point s.vs_memory /\
  mem_word_at (point + 32) (mstore (base + off) w s).vs_memory =
    mem_word_at (point + 32) s.vs_memory
Proof
  rpt gen_tac >> simp[regions_disjoint_def] >>
  strip_tac >> conj_tac >>
  irule valueEncodingPropsTheory.mstore_mem_word_at_disjoint >> decide_tac
QED

(* Restatement of private exprSimECArith.ecadd_input_stores_run;
   original reference lines 1023-1112. *)
Theorem ecadd_input_stores_run:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+96) (mem_word_at (w2n point2+32) s.vs_memory)
        (mstore (w2n bw+64) (mem_word_at (w2n point2) s.vs_memory)
          (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
            (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  drule (Q.INST [`ops` |-> `[q]`, `len` |-> `128`]
    (SPEC_ALL ec_point_prefix_then_run)) >>
  disch_then (qspecl_then [`s`, `q`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  `eval_operand q s1 = SOME point2 /\ eval_operand ib s1 = SOME bw` by
    (gvs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [q;ib] ==> not_fresh_at sc x` by
    (gvs[] >> metis_tac[]) >>
  `w2n (bw+64w) = w2n bw+64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `w2n (bw+64w) + 64 < dimword (:256) /\
   regions_disjoint (w2n (bw+64w)) 64 (w2n point2) 64` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  drule (Q.INST [`boff` |-> `64w`] (SPEC_ALL ec_point_pair_transfer_run)
    |> SRULE [wordsTheory.word_add_n2w]) >>
  disch_then (qspecl_then [`s1`, `point2`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` by
    (qpat_x_assum `_ sc = ((),sb)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[NoAsms, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  `mem_word_at (w2n point2) s1.vs_memory = mem_word_at (w2n point2) s.vs_memory /\
   mem_word_at (w2n point2+32) s1.vs_memory =
     mem_word_at (w2n point2+32) s.vs_memory` by
    (qspecl_then [`w2n bw`, `128`, `w2n point2`, `32`] mp_tac ec_point_words_scratch_store >>
     simp[] >> disch_then assume_tac >>
     qspecl_then [`w2n bw`, `128`, `w2n point2`, `0`] mp_tac ec_point_words_scratch_store >>
     simp[] >> disch_then assume_tac >> simp[]) >>
  qexists_tac `t` >> conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac
  >- (qpat_x_assum `t.vs_memory = _` SUBST1_TAC >> simp[] >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then [`w2n bw+64`, `mem_word_at (w2n point2) s.vs_memory`]
        (mp_tac o Q.AP_TERM `\z. z.vs_memory`)) >> simp[] >> strip_tac >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then [`w2n bw+96`, `mem_word_at (w2n point2+32) s.vs_memory`]
        mp_tac) >> simp[NoAsms]) >>
  conj_tac
  >- (qpat_assum `_ = s1`
       (mp_tac o Q.AP_TERM `\st. st with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>`) >>
      simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- metis_tac[] >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
   t.vs_labels = s.vs_labels` by gvs[venom_state_component_equality] >>
  simp[] >> rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]
QED

(* Restatements of private exprSimECArith.ec_scratch_stores_memory,
   ec_scratch_stores_capacity and ec_scratch_stores_frame;
   original reference lines 1114-1173. *)
Theorem ec_scratch_stores_memory:
  !stores s.
  (!off w. MEM (off,w) stores ==> off + 32 <= len) /\
  regions_disjoint a len b sz ==>
  mem_bytes_at b sz
    (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory =
  mem_bytes_at b sz s.vs_memory
Proof
  Induct_on `stores` >> simp[] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt strip_tac >>
  `mem_bytes_at b sz
     (FOLDL (\u (off,w). mstore (a+off) w u)
       (mstore (a+h0) h1 s) stores).vs_memory =
   mem_bytes_at b sz (mstore (a+h0) h1 s).vs_memory` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[] >> irule mstore_mem_bytes_at_disjoint >>
  gvs[regions_disjoint_def] >>
  qpat_x_assum `!off w. _` (qspecl_then [`h0`, `h1`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem ec_scratch_stores_capacity:
  !stores s. LENGTH s.vs_memory <=
    LENGTH (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory
Proof
  Induct_on `stores` >> simp[] >>
  qx_gen_tac `h` >> PairCases_on `h` >> gen_tac >>
  first_x_assum (qspec_then `mstore (a+h0) h1 s` mp_tac) >>
  simp[immutable_mstore_capacity] >> decide_tac
QED

Theorem ec_scratch_stores_frame:
  t.vs_memory =
    (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory /\
  (!off w. MEM (off,w) stores ==> off + 32 <= len) /\
  stmt_state_rel ctx func cenv cx es s /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint a len b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint a len b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint a len off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t
Proof
  strip_tac >>
  `!b sz. regions_disjoint a len b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule ec_scratch_stores_memory >>
     qexists_tac `len` >> metis_tac[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[] >> irule ec_scratch_stores_capacity) >>
  drule_all scratch_memory_frame >> simp[]
QED

(* Family-specific restatement of private exprSimECArith.ec_input_stores_sim,
   first conjunct, original reference lines 1175-1210. *)
Theorem ecmul_input_stores_sim:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 96 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 96 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes wscalar T
Proof
  strip_tac >> drule_all ecmul_input_stores_run >> strip_tac >>
  `?stores. t.vs_memory =
     (FOLDL (\u (off,w). mstore (w2n bw+off) w u) s stores).vs_memory /\
     (!off w. MEM (off,w) stores ==> off+32 <= 96)` by
    (qexists_tac `[(0,mem_word_at (w2n point) s.vs_memory);
                  (32,mem_word_at (w2n point+32) s.vs_memory);
                  (64,wscalar)]` >>
     simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  qexists_tac `t` >>
  simp[IgnAsm `t.vs_memory = (FOLDL _ _ _).vs_memory`, scratch_three_word_stores] >>
  drule_all ec_scratch_stores_frame >> simp[]
QED

(* Family-specific restatement of private exprSimECArith.ec_input_stores_sim,
   second conjunct, original reference lines 1211-1287. *)
Theorem ecadd_input_stores_sim:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 128 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 128 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T
Proof
  strip_tac >> drule_all ecadd_input_stores_run >> strip_tac >>
  `?stores. t.vs_memory =
     (FOLDL (\u (off,w). mstore (w2n bw+off) w u) s stores).vs_memory /\
     (!off w. MEM (off,w) stores ==> off+32 <= 128)` by
    (qexists_tac `[(0,mem_word_at (w2n point) s.vs_memory);
                  (32,mem_word_at (w2n point+32) s.vs_memory);
                  (64,mem_word_at (w2n point2) s.vs_memory);
                  (96,mem_word_at (w2n point2+32) s.vs_memory)]` >>
     simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  qexists_tac `t` >>
  simp[IgnAsm `t.vs_memory = (FOLDL _ _ _).vs_memory`, scratch_four_word_stores] >>
  drule_all ec_scratch_stores_frame >> simp[]
QED

Theorem ec_point_transfers_mem:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  w2n point + 64 <= s.vs_alloca_next /\
  w2n (bword+boff) + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb ++ emitted_insts sb sc) s
Proof
  strip_tac >>
  `w2n (point+32w) = w2n point+32 /\
   w2n ((bword+boff)+32w) = w2n (bword+boff)+32` by
    (conj_tac >> irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `w2n (point+0w) + 32 <= s.vs_alloca_next /\
   w2n (bword+boff) + 32 <= s.vs_alloca_next` by
    (simp[wordsTheory.WORD_ADD_0] >> decide_tac) >>
  drule_all ec_point_word_transfer_mem >> strip_tac >>
  drule_all ec_point_word_transfer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK s1` >>
  rev_drule_then strip_assume_tac ec_point_word_transfer_shape >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `_ = s` (mp_tac o Q.AP_TERM `\st. st.vs_labels`) >> simp[]) >>
  `eval_operand point_op s1 = SOME point /\ eval_operand base_op s1 = SOME bword` by
    (conj_tac >> Cases_on `point_op` >> Cases_on `base_op` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sb x` by metis_tac[] >>
  `s1.vs_alloca_next = s.vs_alloca_next` by metis_tac[] >>
  `w2n (point+32w) + 32 <= s1.vs_alloca_next /\
   w2n (bword+(boff+32w)) + 32 <= s1.vs_alloca_next` by
    simp[wordsTheory.WORD_ADD_ASSOC] >>
  drule_all ec_point_word_transfer_mem >> strip_tac >>
  irule run_inst_seq_mem_ok_append >> simp[]
QED

Theorem ec_point_pair_transfer_mem:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value];
      src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sa = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  w2n point + 64 <= s.vs_alloca_next /\
  w2n (bword+boff) + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sc) s
Proof
  strip_tac >>
  `(do (do src <- emit_op ADD [point_op; Lit 0w];
           value <- emit_op MLOAD [src];
           dst <- emit_op ADD [base_op; Lit boff];
           emit_void MSTORE [dst; value] od);
       src <- emit_op ADD [point_op; Lit 32w];
       value <- emit_op MLOAD [src];
       dst <- emit_op ADD [base_op; Lit (boff+32w)];
       emit_void MSTORE [dst; value] od) sa = ((),sc)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `_ sa = (u,sb)` >>
  Cases_on `u` >> strip_tac >>
  drule_all ec_point_transfers_mem >>
  rev_drule_then strip_assume_tac ec_point_word_transfer_shape >>
  drule_then strip_assume_tac ec_point_word_transfer_shape >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  simp[]
QED

Theorem ecmul_input_stores_mem:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 /\
  w2n point + 64 <= s.vs_alloca_next /\
  w2n bw + 96 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  drule (Q.INST [`ops` |-> `[scalar]`, `len` |-> `96`]
    (SPEC_ALL ec_point_prefix_then_run)) >>
  disch_then (qspecl_then [`scalar`, `s`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  `!x. MEM (Var x) [p;ib] ==> not_fresh_at sa x` by (gvs[] >> metis_tac[]) >>
  `w2n bw + 64 < dimword (:256) /\ w2n bw + 64 <= s.vs_alloca_next` by decide_tac >>
  drule (Q.INST [`boff` |-> `0w`] (SPEC_ALL ec_point_pair_transfer_mem)
    |> SRULE [wordsTheory.WORD_ADD_0]) >>
  disch_then (qspecl_then [`s`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `eval_operand ib s1 = SOME bw /\ eval_operand scalar s1 = SOME wscalar` by
    (gvs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [ib;scalar] ==> not_fresh_at sc x` by (gvs[] >> metis_tac[]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `_ = s` (mp_tac o Q.AP_TERM `\st. st.vs_alloca_next`) >> simp[]) >>
  `w2n (bw+64w) = w2n bw+64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `w2n (bw+64w)+32 <= s1.vs_alloca_next` by (simp[] >> decide_tac) >>
  drule_all ec_scalar_store_mem_ok >> strip_tac >>
  drule_then strip_assume_tac ec_scalar_store_shape >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  pure_asm_rewrite_tac [] >> irule run_inst_seq_mem_ok_append >>
  conj_tac >- (rpt strip_tac >> gvs[]) >> simp[]
QED

Theorem ecadd_input_stores_mem:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 /\
  w2n point + 64 <= s.vs_alloca_next /\
  w2n point2 + 64 <= s.vs_alloca_next /\
  w2n bw + 128 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  drule (Q.INST [`ops` |-> `[q]`, `len` |-> `128`]
    (SPEC_ALL ec_point_prefix_then_run)) >>
  disch_then (qspecl_then [`s`, `q`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  `!x. MEM (Var x) [p;ib] ==> not_fresh_at sa x` by (gvs[] >> metis_tac[]) >>
  `w2n bw + 64 < dimword (:256) /\ w2n bw + 64 <= s.vs_alloca_next` by decide_tac >>
  drule (Q.INST [`boff` |-> `0w`] (SPEC_ALL ec_point_pair_transfer_mem)
    |> SRULE [wordsTheory.WORD_ADD_0]) >>
  disch_then (qspecl_then [`s`, `point`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `eval_operand q s1 = SOME point2 /\ eval_operand ib s1 = SOME bw` by
    (gvs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [q;ib] ==> not_fresh_at sc x` by (gvs[] >> metis_tac[]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `_ = s` (mp_tac o Q.AP_TERM `\st. st.vs_alloca_next`) >> simp[]) >>
  `w2n (bw+64w) = w2n bw+64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `w2n (bw+64w)+64 < dimword (:256) /\
   w2n (bw+64w)+64 <= s1.vs_alloca_next /\
   w2n point2+64 <= s1.vs_alloca_next` by (simp[] >> decide_tac) >>
  drule (Q.INST [`boff` |-> `64w`] (SPEC_ALL ec_point_pair_transfer_mem)
    |> SRULE [wordsTheory.word_add_n2w]) >>
  disch_then (qspecl_then [`s1`, `point2`, `bw`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` by
    (qpat_x_assum `_ sc = ((),sb)` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[NoAsms, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  pure_asm_rewrite_tac [] >> irule run_inst_seq_mem_ok_append >>
  conj_tac >- (rpt strip_tac >> gvs[]) >> simp[]
QED
