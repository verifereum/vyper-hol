Theory extRetSemanticComplexOuterPtr
Ancestors
  extRetSemanticComplexMembersPtr extRetSemanticResultPtr
  extRetComplexMemberStatePtr extRetFramedChildPtr extRetDynamicBodyPtr
  extRetRecursiveResourcePtr extRetRecursiveFramePtr
  abiEncoder abiEncoderComplexCode compileEnv emitHelper
  fragGasPathPtr bodyPtrDefs venomState ptrDiscipline
  contractABI vyperValue words finite_map list rich_list arithmetic

Theorem encoder_complex_static_cursor_irrelevant:
  !infos dst src so ho dp dq.
  EVERY (\(_,_,_,dy). ~dy) infos ==>
  compile_abi_encode_complex_elems dst src infos so ho dp =
  compile_abi_encode_complex_elems dst src infos so ho dq
Proof
  Induct >- simp[compile_abi_encode_child_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[Ntimes compile_abi_encode_child_def 2] >>
  simp[Ntimes compile_abi_encode_child_def 2, FUN_EQ_THM,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  first_x_assum (qspecl_then [`dst`, `src`, `h2+so`, `h1+ho`, `dp`, `dq`] assume_tac) >>
  simp[]
QED

Theorem encoder_semantic_complex_empty_counted_ptr:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (out,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  encoder_resource ctx fn sites q source_len protected s /\
  vyper_to_abi env ty v = SOME av /\
  LENGTH (enc (vyper_to_abi_type env ty) av) = 0 ==>
  encoder_semantic_framed_result env ty v D ctx fn PG sa sb
    sites q source_len protected b cap out 0 0 G tn s G tn s
Proof
  simp[Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >>
  gvs[encoder_semantic_framed_result_def] >>
  irule encoder_framed_child_result_identity >>
  simp[eval_operand_def, op_taint_def]
QED

Theorem encoder_complex_infos_flags:
  LENGTH dyn = LENGTH ms ==>
  EXISTS (\(_,_,_,dy). dy) (encoder_complex_infos eis hs ms dyn) = EXISTS I dyn
Proof
  strip_tac >> simp_tac bool_ss [encoder_complex_infos_def, listTheory.EXISTS_GENLIST] >>
  simp[EXISTS_MEM, MEM_EL]
QED

Theorem encoder_complex_infos_heads:
  LENGTH hs = LENGTH ms ==>
  SUM (MAP (\(_,h,_,_). h) (encoder_complex_infos eis hs ms dyn)) = SUM hs
Proof
  simp[encoder_complex_infos_def, MAP_GENLIST] >> strip_tac >>
  `GENLIST (\j. EL j hs) (LENGTH ms) = hs` by metis_tac[GENLIST_ID] >>
  fs[combinTheory.o_DEF]
QED

Theorem encoder_semantic_complex_static_counted_ptr:
  encoder_complex_layout 0 0 ms hs tails dyn ns caps children
    sites a scap b dcap protected F cid cursor /\
  compile_abi_encode_to_buf (Var dst) (Var src)
    (AbiComplex (encoder_complex_infos eis hs ms dyn)) sa = (out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    F cid cursor 0 0 ms hs tails tv v 0 sa G tn s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (!i. i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset 0 ms i + val_footprint (tv i) (v i) <= scap /\
    vyper_to_abi env (tys i) (v i) = SOME (avs i) /\
    EL i ns = LENGTH (enc (vyper_to_abi_type env (tys i)) (avs i))) /\
  encoder_complex_semantic_children env tys tv v eis ms hs tails dyn caps children
    cost 0 0 a scap b protected cid cursor D ctx fn PG /\
  vyper_to_abi env ty value = SOME av /\
  LENGTH (enc (vyper_to_abi_type env ty) av) = SUM hs + SUM tails ==>
  (?Gf tnf sf. encoder_semantic_framed_result env ty value
    D ctx fn PG sa sb sites a scap protected b dcap out (SUM hs+SUM tails)
    (SUM (GENLIST cost (LENGTH ms))) G tn s Gf tnf sf) /\
  SUM hs+SUM tails <= dcap
Proof
  strip_tac >>
  `LENGTH hs = LENGTH ms /\ LENGTH dyn = LENGTH ms /\
   ~EXISTS I dyn /\ SUM hs+SUM tails <= dcap` by
    gvs[encoder_complex_layout_def] >>
  `~EXISTS (\(_,_,_,dy). dy) (encoder_complex_infos eis hs ms dyn)` by
    metis_tac[encoder_complex_infos_flags] >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  `EVERY (\(_,_,_,dy). ~dy) (encoder_complex_infos eis hs ms dyn)` by
    (simp[EVERY_MEM] >> qx_gen_tac `e` >> PairCases_on `e` >>
     fs[EXISTS_MEM, EVERY_MEM, combinTheory.o_DEF] >> strip_tac >>
     qpat_x_assum `!e. MEM e (encoder_complex_infos _ _ _ _) ==> _`
       (qspec_then `(e0,e1,e2,e3)` mp_tac) >> simp[]) >>
  `compile_abi_encode_complex_elems (Var dst) (Var src)
    (encoder_complex_infos eis hs ms dyn) 0 0 (Var ip) sa = (ignored,sb)` by
    metis_tac[encoder_complex_static_cursor_irrelevant] >>
  `EVERY ($= F) dyn` by (gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `tails = REPLICATE (LENGTH ms) 0` by
    metis_tac[encoder_complex_static_no_cursor] >>
  `SUM tails = 0` by simp[SUM_REPLICATE] >>
  `SUM (MAP (\(_,h,_,_). h) (encoder_complex_infos eis hs ms dyn)) = SUM hs` by
    metis_tac[encoder_complex_infos_heads] >>
  drule_all encoder_semantic_complex_members_counted_ptr >> strip_tac >>
  simp[] >> qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  simp[encoder_semantic_framed_result_def, encoder_framed_child_result_def,
       encoder_dynamic_effect_def, encoder_complex_member_inv_def,
       eval_operand_def, op_taint_def] >>
  fs[encoder_dynamic_effect_def, encoder_complex_member_inv_def, op_taint_def]
QED
