Theory bodyAbiDecodeGuardedMemberSelectConditionalMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods bodyFullAbiDecodeMemberPrefix
  bodyFullAbiDecodeOwnedStateProps bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeScalarObserved bodyFullAbiDecodeRelativeLoadExact
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq bodyPtrBopScalarCompile
  fragGasPath fragGasOriginPtrDead fragGasOriginPtrLoop fragExec instSeqPtrLo gasOriginPtrLabels
  bodyFullAbiDecodeClampMemory bodyFullAbiDecodeFiniteGuardEffect
  abiDecodePtrPrims abiDecodePtrHead abiDecodePtrPosition abiDecoderGuard
  abiDecoderCoherence abiDecoderMemberInfos abiDecoderReentry abiDecoderDynamic
  abiDecoderOffset abiDecodeRanges externalEntryShape
  bodyPtrDefs stateFrame loweringStateRelDefs freshWrites compileEnv emitHelper
  loweringShapeRules emitHelperProps abiEncoder vyperABI valueEncoding
  exprLoweringProps venomExecSemantics venomInst venomState ptrDiscipline
  words list rich_list finite_map pred_set pair
Libs
  bodyAbiDecodeGuardedEffectSyntaxLib bodyFullAbiDecodeComplexPrefixSyntaxLib

val owned_decoder_state = bodyFullAbiDecodeComplexPrefixSyntaxLib.owned_decoder_state;
val owned_decoder_pre = bodyFullAbiDecodeComplexPrefixSyntaxLib.owned_decoder_pre;

(* The address load retains precisely the packet that the selector consumes. *)
val load_all = let
  val (pre,post) = dest_imp (concl (BETA_RULE abi_decode_owned_relative_load_exact))
  val (ws,body) = strip_exists post
  val extra = ``tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t))``
  val tm = mk_imp (pre, list_mk_exists (ws,mk_conj (body,extra)))
in list_mk_forall (free_vars tm,tm) end;

(* The exact post at the cut, with the compiler's intermediate address
   cursor still determined by the entry equations. *)
fun cut_post tm names = let
  val (_,core) = strip_forall tm
  val (pre,post) = dest_imp core
  val args = map (bodyAbiDecodeGuardedEffectSyntaxLib.param (free_vars pre)) names
in list_mk_abs (args,post) end;

val load_post = cut_post load_all ["sa","sc","v","s","G","tn","p"];

(* Retain scalar effects at the finite run that also fixes the pointer ghosts. *)
val scalar_retained = let
  val (pre,post) = dest_imp (concl abi_decode_scalar_guard_success_joint_effect)
  val (ws,body) = strip_exists post
  val extra = ``abi_decode_guarded_effect_core s tn u tnf``
in mk_imp (pre,list_mk_exists (ws,mk_conj (body,extra))) end;

Theorem member_scalar_success_retained[local]:
  ^scalar_retained
Proof
  strip_tac >>
  `lo <= s.vs_alloca_next /\ alloca_history fn s` by fs[] >>
  drule_all (bop_scalar_seq_run |> Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[abi_decode_scalar_seq_mem_ok] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >> simp[] >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[]) >>
  drule_all emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `u`] >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`, lookup_var_def, op_taint_def] >> gvs[]) >>
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[] >> gvs[inst_extends_def]) >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `abi_decode_guarded_effect_core s tn u tn'` by
    simp[abi_decode_guarded_effect_core_def] >>
  qexistsl_tac [`u`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> asm_rewrite_tac[]
QED

Theorem member_scalar_normal_observed[local]:
  bop_scalar_seq R A (emitted_insts sa sb) B /\
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  u = t with vs_inst_idx := LENGTH sb.cs_current_insts ==>
  (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
  u.vs_allocas = s.vs_allocas
Proof
  strip_tac >> conj_tac
  >- (drule_then assume_tac bop_scalar_seq_opcodes >> rpt strip_tac >>
      qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
      irule abi_decode_finite_success_observed >> simp[] >>
      qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
      simp[GSYM inst_extends_def] >>
      gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem member_slot_retained[local]:
  emit_op ADD [src;Lit (n2w ao)] sa = (pos,sb) /\
  eval_operand src s = SOME (n2w off) /\
  off+ao+head_size <= h /\ h < dimword (:256) /\
  op_prov G src = NONE /\ op_taint tn src = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    eval_operand pos u = SOME (n2w (off+ao)) /\
    op_prov Gf pos = NONE /\ op_taint tnf pos = {} /\
    off+ao < dimword (:256) /\ off+ao+head_size <= h /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    tnf.t_mem = tn.t_mem /\ u.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    abi_decode_guarded_effect_core s tn u tnf
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all buffer_emit_add_run >> strip_tac >>
  `bop_scalar_seq {x | not_fresh_at sa x} {src;Lit (n2w ao)}
     (emitted_insts sa sb) (pos INSERT {src;Lit (n2w ao)})` by
    (irule bop_scalar_seq_emit_op >>
     conj_tac >- simp[] >> qexistsl_tac [`ADD`, `[src;Lit (n2w ao)]`] >> simp[]) >>
  `!op. op IN {src;Lit (n2w ao)} ==>
      op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac[IN_INSERT, NOT_IN_EMPTY] >> rpt strip_tac >>
     gvs[op_prov_def, op_taint_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `inst_extends sa sb` by metis_tac[inst_extends_emit_op] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by simp[mk_inst_def] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (drule emit_op_facts >> simp[]) >>
  drule_all (BETA_RULE member_scalar_success_retained) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `(!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
   u.vs_allocas = s.vs_allocas` by
    (drule_all member_scalar_normal_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  `pos = Var (STRING #"%" (toString sa.cs_next_var))` by
    gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `off+ao < dimword (:256)` by decide_tac >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, word_add_n2w]
QED

Theorem member_actual_retained[local]:
  emit_op ADD [src;offset] sa = (actual,sm) /\
  abi_decode_ge_guard actual src sm = ((),sb) /\
  eval_operand src s = SOME sw /\ eval_operand offset s = SOME ow /\
  abi_decoder_operand_live sa.cs_next_var src /\
  op_prov G src = NONE /\ op_prov G offset = NONE /\
  op_taint tn src = {} /\ op_taint tn offset = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort t))) \/
  (?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    eval_operand actual u = SOME (sw+ow) /\ w2n sw <= w2n (sw+ow) /\
    op_prov Gf actual = NONE /\ op_taint tnf actual = {} /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    tnf.t_mem = tn.t_mem /\ u.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    abi_decode_guarded_effect_core s tn u tnf)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {src;offset}
     (emitted_insts sa sb) B /\ actual IN B` by
    (irule abi_decode_position_suffix_scalar >>
     conj_tac >- simp[] >>
     qexistsl_tac [`Lit 1w`, `sm`, `offset`, `src`] >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!op. op IN {src;offset} ==>
      op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac[IN_INSERT, NOT_IN_EMPTY] >> rpt strip_tac >> gvs[]) >>
  `inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp_tac (srw_ss()) [inst_extends_def, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule_all abi_decode_member_actual_run >> strip_tac
  >- (disj1_tac >> drule_all member_scalar_revert_observed >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`u`, `Gf`, `tnf`] >> asm_rewrite_tac[]) >>
  disj2_tac >>
  drule_all (BETA_RULE member_scalar_success_retained) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `(!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
   u.vs_allocas = s.vs_allocas` by
    (drule_all member_scalar_normal_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  qexistsl_tac [`u`, `Gf`, `tnf`] >> asm_rewrite_tac[] >>
  qpat_x_assum `u = _` (fn th => rewrite_tac[th]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

val bounded_member_entry = ``\dst src opc base_op hi elems ao vo env sf pretys pretvs tys tvs live protected start finish s G tn d.
    LIST_REL (abi_decoder_coherent ce env sf) (pretys++tys) (pretvs++tvs) /\
    LENGTH pretys = LENGTH pretvs /\
    elems = abi_decoder_member_infos sf ce tys /\
    ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pretys) /\
    vo = SUM (MAP (type_memory_bytes ce) pretys) /\
    hi <> Lit 0w /\
    (?off h. eval_operand src s = SOME (n2w off) /\
      eval_operand hi s = SOME (n2w h) /\
      off+ao+SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys) <= h /\
      h <= LENGTH input_bytes) /\
    compile_abi_decode_complex_elems dst src opc base_op hi elems ao vo start =
      ((),finish) /\
    eval_operand dst s = SOME (n2w d) /\
    (^owned_decoder_pre) start finish dst src opc base_op hi d (d+vo)
      (SUM (MAP (type_memory_bytes ce) tys)) s G tn``;

fun member_alloca_bound state =
  strip_tac >> irule owned_decoder_allocas_below_fmp >>
  qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ ^state /\ _`
    (drule_then (ACCEPT_TAC o CONJUNCT1));

Theorem member_select_observed_then[local]:
  !sa sb sc u.
  cs_extends sa sb ==> cs_extends sb sc ==>
  (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) ==>
  (!obs. fn_has_code sb sc obs ==> gas_path ctx obs u 0 r) ==>
  !obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 r
Proof
  rpt strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  irule (gas_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
  qexists_tac `u` >> simp[]
QED

Theorem member_select_live_operand[local]:
  u.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
     FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)) /\
  abi_decoder_operand_live sa.cs_next_var op ==>
  eval_operand op u = eval_operand op s /\
  op_prov Gu op = op_prov G op /\ op_taint tnu op = op_taint tn op
Proof
  Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, op_prov_def, op_taint_def, GSYM not_fresh_at_def] >>
  metis_tac[]
QED

val slot_post = cut_post (concl member_slot_retained) ["sa","sb","pos","head_size"];
val actual_post = cut_post (concl member_actual_retained)
  ["sa","sb","actual","s","G","tn","sw","ow"];

val select_open = ``!finish.
  (^bounded_member_entry) dst src opc base_op hi elems ao vo env sf
    pretys pretvs (ty::tys) (tv::tvs) live protected start finish s G tn d /\
  compile_getelemptr_abi src
    (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao opc base_op hi
    start = (elem_src,select_end) /\ fn_has_code start select_end fn ==>
  ((?rstate Gr tnr. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort rstate,Gr,tnr)) /\
      (!obs. fn_has_code start select_end obs ==>
        gas_path ctx obs s 0 (Abort Revert_abort rstate))) \/
   (?u Gu tnu q h.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
      (!obs. fn_has_code start select_end obs ==> gas_path ctx obs s 0 (OK u)) /\
      tnu.t_mem = tn.t_mem /\ u.vs_allocas = s.vs_allocas /\
      ~u.vs_halted /\ u.vs_current_bb = select_end.cs_current_bb /\
      u.vs_inst_idx = LENGTH select_end.cs_current_insts /\
      (^owned_decoder_state) select_end u Gu tnu /\
      eval_operand elem_src u = SOME (n2w q) /\ q < dimword(:256) /\
      eval_operand hi u = SOME (n2w h) /\ h <= LENGTH input_bytes /\
      op_prov Gu elem_src = NONE /\ op_taint tnu elem_src = {} /\
      ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) ==>
        q + abi_member_head_size (vyper_to_abi_type env ty) <= h) /\
      (!x. not_fresh_at start x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
        op_taint tnu (Var x) = op_taint tn (Var x))))``;

val select_all = let
  open bodyAbiDecodeGuardedEffectSyntaxLib
  val (binders,core) = strip_forall select_open
  val (pre,post) = dest_imp core
  val (early,normal) = dest_disj post
  val (ws,body) = strip_exists normal
  val vs = free_vars pre
  val E = effect (param vs "s") (param vs "tn") (param ws "u") (param ws "tnu")
  val tm = list_mk_forall (binders,
    mk_imp (pre,mk_disj (early,list_mk_exists (ws,mk_conj (body,E)))))
  val _ = checked "member select" select_open tm
in list_mk_forall (free_vars tm, tm) end;

Theorem abi_decode_member_select_observed_effect_from_load_mods:
  ^load_all ==> ^select_all
Proof
  disch_then (mk_asm "load") >> rpt gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by (member_alloca_bound ``s``) >>
  `allocas_from lo s` by
    (qpat_assum `?H. V H` (qx_choose_then `H` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     qpat_assum `ghost_inv_at _ lo _ ce cx es G tn s`
       (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp_tac bool_ss []) >>
  `not_fresh_at start input` by
    gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `?off h. _ /\ _ /\ off+ao+_ <= h /\ _` strip_assume_tac >>
  `h < dimword(:256)` by decide_tac >>
  `off+ao+abi_embedded_static_size ce.ce_struct_fields ty <= h` by
    (qpat_x_assum `off+ao+_ <= h` mp_tac >> simp[MAP,SUM]) >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_getelemptr_abi_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  reverse (Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)`)
  >- suspend "static_slot"
  >> suspend "dynamic_slot"
QED

Resume abi_decode_member_select_observed_effect_from_load_mods[static_slot]:
  asm_x "load" kall_tac >>
  asm_simp_tac bool_ss [comp_return_def, pairTheory.PAIR_EQ] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  drule_all (BETA_RULE member_slot_retained) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `u.vs_labels = s.vs_labels` by
    metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `eval_operand hi u = SOME (n2w h)` by
    (drule_all member_select_live_operand >> simp[]) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[LIST_REL_APPEND_EQ]) >>
  `abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type env ty)` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  disj2_tac >> qexistsl_tac [`u`,`Gf`,`tnf`,`off+ao`,`h`] >>
  asm_rewrite_tac[] >> strip_tac >> decide_tac
QED

Resume abi_decode_member_select_observed_effect_from_load_mods[dynamic_slot]:
  asm_simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [] >>
  pure_rewrite_tac [GSYM (REWRITE_RULE [comp_bind_def, comp_ignore_bind_def]
    abi_decode_ge_guard_def)] >>
  pairarg_tac >>
  first_assum (fn th => CONV_TAC (LAND_CONV (REWRITE_CONV [th]))) >>
  simp_tac std_ss [comp_return_def] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] start = (head_ptr,slot_end)` >>
  rename1 `compile_abi_dec_addr (Var input) head_ptr slot_end = (head_addr,addr_end)` >>
  rename1 `emit_op MLOAD [head_addr] addr_end = (offset_val,load_end)` >>
  rename1 `emit_op ADD [src;offset_val] load_end = (elem_src,actual_end)` >>
  `abi_decode_ge_guard elem_src src actual_end = ((),select_end)` by
    (simp_tac std_ss [abi_decode_ge_guard_def,
       comp_bind_def, comp_ignore_bind_def, LET_THM] >> simp[]) >>
  `cs_extends start slot_end /\ cs_extends slot_end addr_end /\
   cs_extends addr_end load_end /\ cs_extends load_end actual_end /\
   cs_extends actual_end select_end` by
    (qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [src;offset_val] _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD [src;Lit _] _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[exprSimAccountsTheory.emit_op_extends_next_var,
       externalEntryShapeTheory.compile_abi_dec_addr_labels,
       exprSimConvertTheory.straight_fresh_extends,
       abiDecodePtrPositionTheory.abi_decode_ge_guard_straight_fresh,
       pairTheory.SND]) >>
  `cs_extends slot_end load_end /\ cs_extends load_end select_end` by
    (conj_tac >> irule cs_extends_trans >- (qexists `addr_end` >> simp[]) >>
     qexists `actual_end` >> simp[]) >>
  `cs_extends slot_end select_end` by
    (irule cs_extends_trans >> qexists `load_end` >> simp[]) >>
  qspecl_then [`start`,`slot_end`,`select_end`,`fn`] mp_tac fn_has_code_split >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qspecl_then [`slot_end`,`load_end`,`select_end`,`fn`] mp_tac fn_has_code_split >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `(^slot_post) start slot_end head_ptr (abi_embedded_static_size ce.ce_struct_fields ty)` by
    (BETA_TAC >> irule (BETA_RULE member_slot_retained) >> asm_rewrite_tac[] >>
     qexists `src` >> asm_rewrite_tac[] >>
     qpat_assum `ao = _` (fn th => pure_once_rewrite_tac [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  suspend "offset_load"
QED

Resume abi_decode_member_select_observed_effect_from_load_mods[offset_load]:
  `start.cs_next_var <= slot_end.cs_next_var` by
    (qpat_assum `emit_op ADD [src;Lit _] start = _`
       (mp_then Any strip_assume_tac emit_op_facts) >> simp[]) >>
  `not_fresh_at slot_end input /\ local_ptrs_reserved ce slot_end /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at slot_end x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at slot_end x)` by
    (qpat_assum `start.cs_next_var <= slot_end.cs_next_var` mp_tac >>
     qpat_x_assum `not_fresh_at start input` mp_tac >>
     qpat_x_assum `local_ptrs_reserved ce start` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at start x` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at start x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var]) >>
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => simp[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >> simp[LIST_REL_APPEND_EQ]) >>
  `off+ao+32 <= LENGTH input_bytes` by
    (`is_dynamic (vyper_to_abi_type env ty)` by
       (drule_then (fn th => fs[abi_decoder_needs_offset_iff, th])
          abi_decoder_coherent_dynamic) >>
     `abi_embedded_static_size ce.ce_struct_fields ty = 32` by
       (drule abi_decoder_coherent_header >>
        simp[abi_decoder_header_def, abi_member_head_size_def]) >>
     qpat_assum `off+ao+abi_embedded_static_size _ ty <= h` mp_tac >>
     qpat_assum `h <= LENGTH input_bytes` mp_tac >>
     qpat_assum `abi_embedded_static_size _ ty = 32` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by (member_alloca_bound ``u``) >>
  `(^load_post) slot_end load_end offset_val u Gf tnf (off+ao)` by
    (BETA_TAC >> asm "load" irule >> asm_rewrite_tac[] >>
     qexistsl [`head_addr`,`head_ptr`,`addr_end`] >> asm_rewrite_tac[]) >>
  pop_assum (qx_choose_then `out` (qx_choose_then `t` (qx_choose_then `Gl`
      (qx_choose_then `tnl` (map_every assume_tac o CONJUNCTS)))) o BETA_RULE) >>
  asm_x "load" kall_tac >>
  `abi_decode_guarded_effect_core u tnf t tnl` by
    simp[abi_decode_guarded_effect_core_def] >>
  suspend "actual_guard"
QED

Resume abi_decode_member_select_observed_effect_from_load_mods[actual_guard]:
  `cs_extends start load_end` by
    (irule cs_extends_trans >> qexists `slot_end` >> simp[]) >>
  `!obs. fn_has_code start load_end obs ==> gas_path ctx obs s 0 (OK t)` by
    (qpat_x_assum `!obs. fn_has_code slot_end load_end obs ==> _` mp_tac >>
     qpat_x_assum `!obs. fn_has_code start slot_end obs ==> _` mp_tac >>
     qpat_assum `cs_extends slot_end load_end` mp_tac >>
     qpat_assum `cs_extends start slot_end` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     MATCH_ACCEPT_TAC member_select_observed_then) >>
  `slot_end.cs_next_var <= load_end.cs_next_var` by
    (`emit_op ADD [Var input;head_ptr] slot_end = (head_addr,addr_end)` by
       fs[compile_abi_dec_addr_def] >>
     qpat_assum `emit_op ADD _ slot_end = _` (mp_then Any strip_assume_tac emit_op_facts) >>
     qpat_assum `emit_op MLOAD _ addr_end = _` (mp_then Any strip_assume_tac emit_op_facts) >>
     simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gl x = FLOOKUP G x /\ op_taint tnl (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at slot_end x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_assum `start.cs_next_var <= slot_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[not_fresh_at_mono]) >>
  `t.vs_labels = s.vs_labels` by metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `eval_operand src t = eval_operand src s /\
    op_prov Gl src = op_prov G src /\ op_taint tnl src = op_taint tn src` by
    (irule member_select_live_operand >> asm_rewrite_tac[] >>
     qexists `start` >> asm_rewrite_tac[]) >>
  `eval_operand src t = SOME (n2w off) /\ op_prov Gl src = NONE /\
    op_taint tnl src = {}` by asm_rewrite_tac[] >>
  `abi_decoder_operand_live load_end.cs_next_var src` by
    (qpat_x_assum `abi_decoder_operand_live start.cs_next_var src` mp_tac >>
     qpat_assum `start.cs_next_var <= slot_end.cs_next_var` mp_tac >>
     qpat_assum `slot_end.cs_next_var <= load_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at load_end input /\ local_ptrs_reserved ce load_end /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at load_end x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at load_end x)` by
    (qpat_assum `slot_end.cs_next_var <= load_end.cs_next_var` mp_tac >>
     qpat_x_assum `not_fresh_at slot_end input` mp_tac >>
     qpat_x_assum `local_ptrs_reserved ce slot_end` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_buf = _ ==> not_fresh_at slot_end x` mp_tac >>
     qpat_x_assum `!x sz. ce.ce_return_pc = _ ==> not_fresh_at slot_end x` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var]) >>
  `allocas_from lo t` by
    (qpat_assum `t.vs_allocas = u.vs_allocas`
       (fn th => pure_rewrite_tac[allocas_from_def,th]) >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by (member_alloca_bound ``t``) >>
  `(^actual_post) load_end select_end elem_src t Gl tnl (n2w off)
     (mload (w2n input_word+(off+ao)) u)` by
    (BETA_TAC >> irule (BETA_RULE member_actual_retained) >> asm_rewrite_tac[] >>
     qexistsl [`offset_val`,`actual_end`,`src`] >> asm_rewrite_tac[] >>
     qpat_assum `ao = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  pop_assum (DISJ_CASES_THEN (qx_choose_then `z` (qx_choose_then `Gz`
      (qx_choose_then `tnz` (map_every assume_tac o CONJUNCTS)))) o BETA_RULE)
  >- suspend "actual_reject"
  >> suspend "actual_success"
QED

Resume abi_decode_member_select_observed_effect_from_load_mods[actual_reject]:
  disj1_tac >> qexistsl_tac [`z`,`Gz`,`tnz`] >>
  reverse conj_tac >-
    (qpat_x_assum `!obs. fn_has_code load_end select_end obs ==> _` mp_tac >>
     qpat_x_assum `!obs. fn_has_code start load_end obs ==> _` mp_tac >>
     qpat_x_assum `cs_extends load_end select_end` mp_tac >>
     qpat_x_assum `cs_extends start load_end` mp_tac >>
     MATCH_ACCEPT_TAC member_select_observed_then) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (u,Gf,tnf) _ _` mp_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ (t,Gl,tnl) _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_trans]
QED

Resume abi_decode_member_select_observed_effect_from_load_mods[actual_success]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK z,Gz,tnz)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Gf,tnf) _ _` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (t,Gl,tnl) _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_origin_ptr_path_trans]) >>
  `start.cs_next_var <= load_end.cs_next_var` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists `slot_end.cs_next_var` >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gz x = FLOOKUP G x /\ op_taint tnz (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at start x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at load_end x ==> lookup_var x z = _ /\ _` mp_tac >>
     qpat_assum `start.cs_next_var <= load_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[not_fresh_at_mono]) >>
  `z.vs_labels = s.vs_labels` by metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `eval_operand hi z = eval_operand hi s /\
    op_prov Gz hi = op_prov G hi /\ op_taint tnz hi = op_taint tn hi` by
    (irule member_select_live_operand >> asm_rewrite_tac[] >>
     qexists `start` >> asm_rewrite_tac[]) >>
  `!obs. fn_has_code start select_end obs ==> gas_path ctx obs s 0 (OK z)` by
    (qpat_x_assum `!obs. fn_has_code load_end select_end obs ==> _` mp_tac >>
     qpat_x_assum `!obs. fn_has_code start load_end obs ==> _` mp_tac >>
     qpat_x_assum `cs_extends load_end select_end` mp_tac >>
     qpat_x_assum `cs_extends start load_end` mp_tac >>
     MATCH_ACCEPT_TAC member_select_observed_then) >>
  `tnz.t_mem = tn.t_mem /\ z.vs_allocas = s.vs_allocas` by
    (MAP_EVERY (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC[th]))
       [`tnz.t_mem = tnl.t_mem`, `tnl.t_mem = tnf.t_mem`, `tnf.t_mem = tn.t_mem`,
        `z.vs_allocas = t.vs_allocas`, `t.vs_allocas = u.vs_allocas`,
        `u.vs_allocas = s.vs_allocas`] >> REWRITE_TAC[]) >>
  `abi_decode_guarded_effect_core s tn t tnl` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tnf`,`u`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_guarded_effect_core s tn z tnz` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl [`tnl`,`t`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `~(?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp)` by
    (qpat_assum `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> fs[dec_info_needs_offset_def]) >>
  disj2_tac >> qexistsl_tac [`z`,`Gz`,`tnz`,
    `w2n (n2w off+mload (w2n input_word+(off+ao)) u:bytes32)`,`h`] >>
  asm_rewrite_tac[wordsTheory.n2w_w2n, wordsTheory.w2n_lt] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_decode_member_select_observed_effect_from_load_mods
