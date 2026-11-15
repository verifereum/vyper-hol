(* The relative-memory runtime loop header uses one operational and ghost run. *)
Theory abiDecodePtrLoopHeaderJoint
Ancestors
 abiDecoderExecution abiDecoderContract abiDecoderArrayBackedge instMemFrontier
 abiDecodePtrRead abiDecodePtrMemberFrame
 abiDecodePtrScalarFrame bodyPtrBopScalarSeq bodyPtrBopScalarCompile
 bodyPtrBopScalarOutcome wordLoadStorePtr typedCopyPtr decoderGhostFramePtr
 fragGasCopyLoop fragGasOriginPtr fragGasOriginPtrDead fragGasEmitCtrl fragGasSeqPtr fragExecMem fragExec
 instSeqComposePtr ghostPcTransportPtr abiDecoderVarExtend abiDecoderVarSequence ssaOperandFrame
 emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
 bodyPtrDefs ptrDiscipline venomExecSemantics venomState venomInst venomMemDefs
 instIdxIndep finite_map pred_set words list rich_list arithmetic

Theorem position_header_prefix_joint[local]:
 abi_decoder_operand_live first (Var index) /\
 abi_decoder_operand_live first (Var source) /\ abi_decoder_operand_live first pos /\
 ~ctx_has_dalloca ctx /\ s.vs_inst_idx = 0 /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn index s 32 /\ lookup_var index s = SOME (n2w slot) /\
 slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
 (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
 mload slot s = n2w j /\
 eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
 p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
 mload (B+p) s = n2w ncount /\ j <= ncount /\ ncount < dimword (:256) ==>
 ?G' tm.
 inst_seq_ptr D 0 ctx func PG G tn
   (TAKE 5 (abi_decode_position_header_insts id (Var index) pos MLOAD
     (Var source) first body_lbl exit_lbl)) s G' tm /\
 run_inst_seq_mem_ok
   (TAKE 5 (abi_decode_position_header_insts id (Var index) pos MLOAD
     (Var source) first body_lbl exit_lbl)) s /\
 run_inst_seq
   (TAKE 5 (abi_decode_position_header_insts id (Var index) pos MLOAD
     (Var source) first body_lbl exit_lbl)) s =
   OK (abi_decode_position_header_state (Var source) first B p j ncount s) /\
 abi_decode_ptr_window G' tm
   (abi_decode_position_header_state (Var source) first B p j ncount s)
   source (n2w B) L /\
 ptr_covers G' tm index
   (abi_decode_position_header_state (Var source) first B p j ncount s) 32 /\
 tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
 tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
 (!x. abi_decoder_operand_live first (Var x) ==>
   lookup_var x (abi_decode_position_header_state (Var source) first B p j ncount s) =
     lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)) /\
 (!k. MEM k [first;first+2;first+3;first+4] ==>
   op_prov G' (Var (STRING #"%" (toString k))) = NONE /\
   op_taint tm (Var (STRING #"%" (toString k))) = {})
Proof
 strip_tac >>
 qabbrev_tac `iv = STRING #"%" (toString first)` >>
 qabbrev_tac `ar = STRING #"%" (toString (first+1))` >>
 qabbrev_tac `cv = STRING #"%" (toString (first+2))` >>
 qabbrev_tac `cmp = STRING #"%" (toString (first+3))` >>
 qabbrev_tac `done = STRING #"%" (toString (first+4))` >>
 `ALL_DISTINCT [iv;ar;cv;cmp;done]` by
   simp[Abbr `iv`,Abbr `ar`,Abbr `cv`,Abbr `cmp`,Abbr `done`,
     ASCIInumbersTheory.toString_inj] >>
 `!x k. abi_decoder_operand_live first (Var x) /\ first <= k ==>
   x <> STRING #"%" (toString k)` by
   metis_tac[abi_decoder_live_excludes_output] >>
 `index <> iv /\ source <> iv /\ source <> ar /\
  index <> ar /\ index <> cv /\ source <> cv /\
  pos <> Var iv` by
   (simp[Abbr `iv`,Abbr `ar`,Abbr `cv`] >> rpt conj_tac >>
    metis_tac[abi_decoder_live_excludes_output,LESS_EQ_REFL,LESS_EQ_ADD]) >>
 `B < dimword (:256) /\ B+p < dimword (:256) /\
  slot < dimword (:256) /\ j < dimword (:256)` by decide_tac >>
 `lookup_var source s = SOME (n2w B) /\ op_taint tn (Var source) = {}` by
   gvs[abi_decode_ptr_window_def,ptr_covers_def] >>
 qabbrev_tac `a = update_var iv (n2w j) s` >>
 qabbrev_tac `b = update_var ar (n2w (B+p)) a` >>
 qabbrev_tac `c = update_var cv (n2w ncount) b` >>
 qabbrev_tac `e = abi_decode_position_header_state (Var source) first B p j ncount s` >>
 qabbrev_tac `i0 = mk_inst id MLOAD [Var index] [iv]` >>
 qabbrev_tac `i1 = mk_inst (id+1) ADD [Var source;pos] [ar]` >>
 qabbrev_tac `i2 = mk_inst (id+2) MLOAD [Var ar] [cv]` >>
 qabbrev_tac `tail = [mk_inst (id+3) LT [Var iv;Var cv] [cmp];
   mk_inst (id+4) ISZERO [Var cmp] [done]]` >>
 qabbrev_tac `G1 = step_prov PG G i0 a` >>
 qabbrev_tac `tm1 = step_taint i0 s a tn` >>
 qabbrev_tac `G2 = step_prov PG G1 i1 b` >>
 qabbrev_tac `tm2 = step_taint i1 a b tm1` >>
 qabbrev_tac `G3 = step_prov PG G2 i2 c` >>
 qabbrev_tac `tm3 = step_taint i2 b c tm2` >>
 `TAKE 5 (abi_decode_position_header_insts id (Var index) pos MLOAD
   (Var source) first body_lbl exit_lbl) = [i0;i1;i2] ++ tail` by
   simp[abi_decode_position_header_insts_def,abi_decode_position_header_delta_def,
     Abbr `i0`,Abbr `i1`,Abbr `i2`,Abbr `tail`,
     Abbr `iv`,Abbr `ar`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
 `run_inst_seq ([i0;i1;i2] ++ tail) s = OK e` by
   (qpat_assum `TAKE 5 _ = _` (fn th => rewrite_tac[GSYM th]) >>
    simp[Abbr `e`] >>
    mp_tac (abi_decode_position_header_prefix |> Q.INST [`p` |-> `n2w slot`] |> Q.INST
      [`opc` |-> `MLOAD`, `ip` |-> `Var index`, `base_op` |-> `Var source`,
       `src` |-> `pos`, `sb` |-> `p`, `i` |-> `j`, `ncount` |-> `ncount`,
       `exit` |-> `exit_lbl`]) >>
    (impl_tac >- simp[abi_decode_source_opcode_def,eval_operand_def,
      abi_decode_load_def,abi_decode_source_def,w2n_n2w]) >>
    simp[abi_decode_position_header_delta_def]) >>
 `step_inst_base i0 s = OK a /\ step_inst_base i1 a = OK b /\
  step_inst_base i2 b = OK c` by
   (simp[Abbr `i0`,Abbr `i1`,Abbr `i2`,Abbr `a`,Abbr `b`,Abbr `c`,
     step_inst_base_opcode_eqs,mk_inst_def,exec_read1_def,exec_pure2_def,
     eval_operand_def,lookup_var_update_var,word_add_n2w,w2n_n2w,
     mload_update_var] >>
    Cases_on `pos` >> gvs[eval_operand_def,lookup_var_def,FLOOKUP_UPDATE,
      mload_update_var,word_add_n2w]) >>
 `run_inst_seq tail c = OK e` by
   (qpat_x_assum `run_inst_seq ([i0;i1;i2] ++ tail) s = OK e` mp_tac >>
    simp[run_inst_seq_def]) >>
 `op_taint tm1 (Var iv) = {} /\ op_prov G1 (Var iv) = NONE /\
  tm1.t_mem = tn.t_mem /\ tm1.t_stor = tn.t_stor /\
  tm1.t_trans = tn.t_trans /\ tm1.t_imm = tn.t_imm` by
   (mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`id`,`Var index`,`iv`,`n2w slot`]
     mload_ghost_clean) >>
    simp[eval_operand_def,w2n_n2w,Abbr `tm1`,Abbr `G1`,Abbr `i0`,
      Abbr `a`,step_prov_def,set_prov_def,out_prov_def,op_prov_def,
      mk_inst_def,FLOOKUP_DRESTRICT] >>
    strip_tac >> simp[step_taint_def,imm_taint_def,mk_inst_def]) >>
 `!x. x <> iv ==> lookup_var x a = lookup_var x s /\
   FLOOKUP G1 x = FLOOKUP G x /\ op_taint tm1 (Var x) = op_taint tn (Var x)` by
   (simp[Abbr `a`,Abbr `G1`,Abbr `tm1`,Abbr `i0`,
     lookup_var_update_var,step_prov_def,set_prov_def,out_prov_def,
     step_taint_def,set_var_taint_def,op_taint_def,mk_inst_def,
     FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]) >>
 `abi_decode_ptr_window G1 tm1 a source (n2w B) L /\
  ptr_covers G1 tm1 index a 32` by
   (conj_tac >- (irule abi_decode_ptr_window_frame >>
       qexistsl_tac [`G`,`s`,`tn`] >> simp[Abbr `a`,update_var_def]) >>
    irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
 `eval_operand pos a = SOME (n2w p) /\ op_taint tm1 pos = {}` by
   (Cases_on `pos` >> fs[eval_operand_def,op_taint_def,Abbr `a`,
     lookup_var_update_var] >> metis_tac[]) >>
 `abi_decode_ptr_window G2 tm2 b ar (n2w (B+p)) (L-p)` by
   (mp_tac (abi_decode_ptr_relative_window |> Q.INST [`b` |-> `n2w B`] |> Q.INST
     [`G` |-> `G1`,`tn` |-> `tm1`,`s` |-> `a`,`src` |-> `source`,
      `h` |-> `L`,`out` |-> `ar`,`idx` |-> `b.vs_inst_idx`,
      `id` |-> `id+1`]) >>
    (impl_tac >- simp[w2n_n2w]) >>
    simp[word_add_n2w,Abbr `G2`,Abbr `tm2`,Abbr `i1`,Abbr `b`,update_var_def]) >>
 `tm2.t_mem = tm1.t_mem /\ tm2.t_stor = tm1.t_stor /\
  tm2.t_trans = tm1.t_trans /\ tm2.t_imm = tm1.t_imm /\
  (!x. x <> ar ==> FLOOKUP G2 x = FLOOKUP G1 x /\
    op_taint tm2 (Var x) = op_taint tm1 (Var x))` by
   simp[Abbr `G2`,Abbr `tm2`,Abbr `i1`,Abbr `b`,copy_len_binop_ghost_frame,
     step_taint_def,imm_taint_def,mk_inst_def] >>
 `ptr_covers G2 tm2 ar b 32 /\ lookup_var ar b = SOME (n2w (B+p)) /\
  (!i. B+p <= i /\ i < B+p+32 ==> i NOTIN tm2.t_mem)` by
   (`32 <= L-p` by decide_tac >>
    fs[abi_decode_ptr_window_def,w2n_n2w] >>
    fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS,LESS_EQ_MONO_ADD_EQ]) >>
 `op_taint tm3 (Var cv) = {} /\ op_prov G3 (Var cv) = NONE /\
  tm3.t_mem = tm2.t_mem /\ tm3.t_stor = tm2.t_stor /\
  tm3.t_trans = tm2.t_trans /\ tm3.t_imm = tm2.t_imm` by
   (mp_tac (Q.SPECL [`PG`,`G2`,`tm2`,`b`,`id+2`,`Var ar`,`cv`,`n2w (B+p)`]
     mload_ghost_clean) >>
    simp[eval_operand_def,w2n_n2w,Abbr `tm3`,Abbr `G3`,Abbr `i2`,
      Abbr `c`,Abbr `b`,Abbr `a`,mload_update_var,
      step_prov_def,set_prov_def,out_prov_def,op_prov_def,mk_inst_def,
      FLOOKUP_DRESTRICT] >>
    strip_tac >> simp[step_taint_def,imm_taint_def,mk_inst_def]) >>
 `!x. x <> cv ==> lookup_var x c = lookup_var x b /\
   FLOOKUP G3 x = FLOOKUP G2 x /\ op_taint tm3 (Var x) = op_taint tm2 (Var x)` by
   simp[Abbr `c`,Abbr `G3`,Abbr `tm3`,Abbr `i2`,lookup_var_update_var,
     step_prov_def,set_prov_def,out_prov_def,step_taint_def,set_var_taint_def,
     op_taint_def,mk_inst_def,FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] >>
 `!x. abi_decoder_operand_live first (Var x) ==>
   lookup_var x c = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
   op_taint tm3 (Var x) = op_taint tn (Var x)` by
   (rpt strip_tac >> `x <> iv /\ x <> ar /\ x <> cv` by
      (simp[Abbr `iv`,Abbr `ar`,Abbr `cv`] >> metis_tac[LESS_EQ_ADD]) >>
    simp[Abbr `c`,Abbr `b`,lookup_var_update_var] >> metis_tac[]) >>
 `abi_decode_ptr_window G3 tm3 c source (n2w B) L /\
  ptr_covers G3 tm3 index c 32` by
   (conj_tac >- (irule abi_decode_ptr_window_frame >>
       qexistsl_tac [`G`,`s`,`tn`] >> simp[Abbr `c`,Abbr `b`,Abbr `a`,update_var_def]) >>
    irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
 `op_prov G3 (Var iv) = NONE /\ op_taint tm3 (Var iv) = {}` by
   (fs[ALL_DISTINCT,op_prov_def] >> metis_tac[]) >>
 `bop_scalar_seq {x | abi_decoder_operand_live first (Var x)} {Var iv;Var cv}
   tail (Var done INSERT Var cmp INSERT {Var iv;Var cv})` by
   (`tail = [mk_inst (id+3) LT [Var iv;Var cv] [cmp]] ++
      [mk_inst (id+4) ISZERO [Var cmp] [done]]` by simp[Abbr `tail`] >>
    pop_assum SUBST1_TAC >> irule bop_scalar_seq_append >>
    qexists_tac `Var cmp INSERT {Var iv;Var cv}` >> conj_tac >>
    irule bop_scalar_seq_single >> simp[Abbr `cmp`,Abbr `done`] >> metis_tac[LESS_EQ_ADD]) >>
 `!op. op IN {Var iv;Var cv} ==> op_prov G3 op = NONE /\ op_taint tm3 op = {}` by
   (rpt strip_tac >> gvs[]) >>
 `run_inst_seq tail (c with vs_inst_idx := 3) = OK (e with vs_inst_idx := 3)` by
   (simp[run_inst_seq_inst_idx,exec_result_map_def,Abbr `tail`,mk_inst_def,
     is_terminator_def] >> metis_tac[]) >>
 mp_tac (abi_decode_scalar_success_frame |> Q.INST
   [`s` |-> `c with vs_inst_idx := 3`, `u` |-> `e with vs_inst_idx := 3`,
    `G` |-> `G3`, `tn` |-> `tm3`, `code` |-> `tail`,
    `R` |-> `{x | abi_decoder_operand_live first (Var x)}`,
    `A` |-> `{Var iv;Var cv}`,
    `B` |-> `Var done INSERT Var cmp INSERT {Var iv;Var cv}`,
    `j` |-> `0`, `fn` |-> `func`, `PG` |-> `PG`, `D` |-> `D`]) >>
 (impl_tac >- simp[]) >>
 strip_tac >>
 rename1 `inst_seq_ptr D 0 ctx func PG G3 tm3 tail (c with vs_inst_idx := 3) H tm` >>
 `!k. step_inst_base i1 (a with vs_inst_idx := k) = OK (b with vs_inst_idx := k)` by
   simp[step_inst_inst_idx_indep,exec_result_map_def,Abbr `i1`,mk_inst_def,
     is_terminator_def] >>
 `!k. step_inst_base i2 (b with vs_inst_idx := k) = OK (c with vs_inst_idx := k)` by
   simp[step_inst_inst_idx_indep,exec_result_map_def,Abbr `i2`,mk_inst_def,
     is_terminator_def] >>
 `ptr_inst_ok D 0 0 ctx func G tn i0 s` by
   (simp[Abbr `i0`] >> irule ptr_inst_ok_mload >> simp[]) >>
 `!k. ptr_inst_ok D 0 0 ctx func G1 tm1 i1 (a with vs_inst_idx := k)` by
   (gen_tac >> simp[Abbr `i1`] >> irule ptr_inst_ok_copy_len_binop >>
    simp[] >> fs[abi_decode_ptr_window_def,ptr_covers_def]) >>
 `!k. ptr_inst_ok D 0 0 ctx func G2 tm2 i2 (b with vs_inst_idx := k)` by
   (gen_tac >> simp[Abbr `i2`] >> irule ptr_inst_ok_mload >> simp[]) >>
 `inst_seq_ptr D 0 ctx func PG G tn ([i0;i1;i2] ++ tail) s H tm` by
   (gvs[inst_seq_ptr_def,Abbr `G1`,Abbr `tm1`,Abbr `G2`,Abbr `tm2`,
      Abbr `G3`,Abbr `tm3`]) >>
 `inst_mem_below_frontier i0 s /\ inst_dload_in_section i0 s /\
  inst_mem_below_frontier i1 a /\ inst_dload_in_section i1 a /\
  inst_mem_below_frontier i2 b /\ inst_dload_in_section i2 b` by
   (simp[Abbr `i0`,Abbr `i1`,Abbr `i2`,
     below_frontier_MLOAD,below_frontier_no_ranges,memSafeRunTheory.inst_dload_in_section_other,
     mk_inst_def,eval_operand_def,Abbr `a`,Abbr `b`,
     lookup_var_update_var,w2n_n2w,update_var_def] >> decide_tac) >>
 `run_inst_seq_mem_ok tail c` by
   (irule bop_scalar_seq_mem_ok >> metis_tac[]) >>
 `run_inst_seq_mem_ok ([i0;i1;i2] ++ tail) s` by
   simp[run_inst_seq_mem_ok_def] >>
 `e.vs_inst_idx = s.vs_inst_idx /\ e.vs_memory = s.vs_memory` by
   simp[Abbr `e`,abi_decode_position_header_state_def,
     abi_decode_position_header_delta_def,LET_THM,update_var_def] >>
 `e with vs_inst_idx := 0 = e` by simp[venom_state_component_equality] >>
 `abi_decode_ptr_window H tm e source (n2w B) L` by
   (qpat_assum `!x b h. _ ==> abi_decode_ptr_window H tm _ _ _ _`
      (qspecl_then [`source`,`n2w B`,`L`] mp_tac) >>
    simp[abi_decode_ptr_window_def,lookup_var_def] >>
    fs[abi_decode_ptr_window_def,lookup_var_def]) >>
 `ptr_covers H tm index e 32` by
   (qpat_assum `!x cap. _ ==> ptr_covers H tm _ _ _`
      (qspecl_then [`index`,`32`] mp_tac) >>
    qpat_assum `ptr_covers G3 tm3 index c 32` mp_tac >>
    qpat_assum `abi_decoder_operand_live first (Var index)` mp_tac >>
    qpat_assum `e with vs_inst_idx := 0 = e` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_covers_def,lookup_var_def]) >>
 `!x. abi_decoder_operand_live first (Var x) ==>
   lookup_var x e = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
   op_taint tm (Var x) = op_taint tn (Var x)` by
   (qpat_assum `!x. x IN _ ==> lookup_var x _ = _ /\ _` mp_tac >>
    qpat_assum `!x. abi_decoder_operand_live first (Var x) ==>
      lookup_var x c = _ /\ _` mp_tac >>
    qpat_assum `e with vs_inst_idx := 0 = e` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def] >> metis_tac[]) >>
 `tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm` by simp[] >>
 `!k. MEM k [first;first+2;first+3;first+4] ==>
   op_prov H (Var (STRING #"%" (toString k))) = NONE /\
   op_taint tm (Var (STRING #"%" (toString k))) = {}` by
   (qpat_assum `!op. op IN Var done INSERT _ ==> _` mp_tac >>
    simp[Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
 `e = abi_decode_position_header_state (Var source) first B p j ncount s` by
   simp[Abbr `e`] >>
 qexistsl_tac [`H`,`tm`] >>
 qpat_assum `e = abi_decode_position_header_state _ _ _ _ _ _ _`
   (fn th => rewrite_tac[GSYM th]) >> asm_rewrite_tac[]
QED

Theorem abi_decode_position_header_success_joint:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = abi_decode_position_header_insts id (Var index) pos MLOAD
    (Var source) first body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  abi_decoder_operand_live first (Var index) /\
  abi_decoder_operand_live first (Var source) /\
  abi_decoder_operand_live first pos /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn index s 32 /\ lookup_var index s = SOME (n2w slot) /\
  slot+32 < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  mload slot s = n2w j /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  mload (B+p) s = n2w ncount /\ j <= ncount /\ ncount < dimword (:256) /\
  allocas_from lo s ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      (OK (jump_to (if j < ncount then body_lbl else exit_lbl)
        (abi_decode_position_header_state (Var source) first B p j ncount s)),G',tn')) /\
    abi_decode_ptr_window G' tn'
      (jump_to (if j < ncount then body_lbl else exit_lbl)
        (abi_decode_position_header_state (Var source) first B p j ncount s))
      source (n2w B) L /\
    ptr_covers G' tn' index
      (jump_to (if j < ncount then body_lbl else exit_lbl)
        (abi_decode_position_header_state (Var source) first B p j ncount s)) 32 /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live first (Var x) ==>
      lookup_var x (abi_decode_position_header_state (Var source) first B p j ncount s) =
        lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!k. MEM k [first;first+2;first+3;first+4] ==>
      op_prov G' (Var (STRING #"%" (toString k))) = NONE /\
      op_taint tn' (Var (STRING #"%" (toString k))) = {})
Proof
 strip_tac >>
 mp_tac (position_header_prefix_joint |> Q.INST
   [`D` |-> `<|d_stor := K (K {});d_trans := K (K {});d_imm := K {};d_ret := K {}|>`]) >>
 (impl_tac >- simp[]) >> strip_tac >>
 qabbrev_tac `h = abi_decode_position_header_state (Var source) first B p j ncount s` >>
 qabbrev_tac `prepared = h with vs_inst_idx := 5` >>
 qabbrev_tac `sa = (ARB:compile_state) with
   <|cs_current_bb := s.vs_current_bb;cs_current_insts := TAKE 5 bb.bb_instructions;
     cs_next_id := id+5|>` >>
 qabbrev_tac `sb = sa with
   <|cs_current_insts := bb.bb_instructions;cs_next_id := id+6|>` >>
 `emit_inst JNZ [Var (STRING #"%" (toString (first+4)));Label exit_lbl;Label body_lbl]
   [] sa = ((),sb)` by
   simp[Abbr `sa`,Abbr `sb`,emit_inst_def,comp_bind_def,fresh_id_def,
     emit_def,comp_return_def,abi_decode_position_header_insts_def,
     abi_decode_position_header_delta_def] >>
 `fn_has_code sa sb func` by
   (simp[fn_has_code_def,emitted_blocks_def,Abbr `sa`,Abbr `sb`] >> metis_tac[]) >>
 `allocas_from lo h /\ ~h.vs_halted /\ h.vs_current_bb = s.vs_current_bb` by
   (qpat_assum `allocas_from lo s` mp_tac >>
    qpat_assum `~s.vs_halted` mp_tac >>
    simp_tac (srw_ss()) [Abbr `h`,abi_decode_position_header_state_def,
      abi_decode_position_header_delta_def,LET_THM,update_var_def,allocas_from_def] >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
 `allocas_from lo prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = sa.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH sa.cs_current_insts /\
  op_taint tm (Var (STRING #"%" (toString (first+4)))) = {}` by
   (fs[Abbr `prepared`,Abbr `sa`,abi_decode_position_header_insts_def,
      abi_decode_position_header_delta_def,allocas_from_def] >> metis_tac[]) >>
 `eval_operand (Var (STRING #"%" (toString (first+4)))) prepared =
   SOME (if ~(j < ncount) then 1w else 0w)` by
   (Cases_on `j < ncount` >>
    simp[Abbr `prepared`,Abbr `h`,abi_decode_position_header_state_def,
     abi_decode_position_header_delta_def,LET_THM,eval_operand_def,lookup_var_update_var,
     lookup_var_def,update_var_def,FLOOKUP_UPDATE,
     ASCIInumbersTheory.toString_inj,bool_to_word_def]) >>
 qexistsl_tac [`G'`,`tm`] >> conj_tac
 >- (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
     `LENGTH (TAKE 5 bb.bb_instructions) = 5 /\
      isPREFIX (TAKE 5 bb.bb_instructions) (DROP s.vs_inst_idx bb.bb_instructions) /\
      EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
        (TAKE 5 bb.bb_instructions)` by
       simp[abi_decode_position_header_insts_def,abi_decode_position_header_delta_def,
         mk_inst_def,is_terminator_def,IS_PREFIX_APPEND] >>
     `gas_origin_ptr_path
       (<|d_stor := K (K {});d_trans := K (K {});d_imm := K {};d_ret := K {}|>,
        lo,explicit,ctx,func,PG) (s,G,tn) [] (OK prepared,G',tm)` by
       (mp_tac (run_inst_seq_origin_ptr_lift |> Q.INST
         [`code` |-> `TAKE 5 bb.bb_instructions`,`t` |-> `h`, `s` |-> `s`,
          `G` |-> `G`, `tn` |-> `tn`, `G'` |-> `G'`, `tn'` |-> `tm`,
          `D` |-> `<|d_stor := K (K {});d_trans := K (K {});d_imm := K {};d_ret := K {}|>`]) >>
        (impl_tac >- (simp[Abbr `h`] >> metis_tac[])) >>
        simp[Abbr `prepared`,Abbr `h`]) >>
     mp_tac (emit_jnz_origin_ptr |> Q.INST
       [`sa` |-> `sa`, `sb` |-> `sb`, `s` |-> `prepared`,
        `op` |-> `Var (STRING #"%" (toString ((first:num)+4)))`,
        `lt` |-> `exit_lbl`, `lf` |-> `body_lbl`, `b` |-> `~(j < ncount)`,
        `D` |-> `<|d_stor := K (K {});d_trans := K (K {});d_imm := K {};d_ret := K {}|>`,
        `G` |-> `G'`, `tn` |-> `tm`]) >>
     (impl_tac >- simp[]) >> strip_tac >>
     Cases_on `j < ncount` >>
     fs[Abbr `prepared`,jump_to_def] >>
     metis_tac[gas_origin_ptr_path_append,APPEND]) >>
 gvs[Abbr `h`,jump_to_def,abi_decode_ptr_window_def,ptr_covers_def,lookup_var_def] >>
 metis_tac[]
QED
