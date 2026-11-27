Theory bodyAbiDecodeLoopBodyNormalMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods bodyFullAbiDecodeLoopPhasesObserved
  bodyFullAbiDecodeLoopResource gasOriginPtrLabels fragGasOriginPtr fragGasPath
  venomState venomExecSemantics allocaHistory valueEncodingProps freshWrites
  pred_set list rich_list pair arithmetic
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib bodyFullAbiDecodeLoopObservedSyntaxLib
  bodyAbiDecodeGuardedEffectSyntaxLib

(* Take all cuts from the checked syntax or the observed phase statements.
   The preparation and content results are logical inputs, not imports. *)
val (body_params, body_imp) = strip_forall (beta (guarded_effect_length_body_typed ()));
val (entry, body_result) = dest_imp body_imp;
val (body_ws, normal_post) = strip_exists (snd (dest_disj body_result));
val (b, Gb, tb) = (``b:venom_state``,
  mk_var ("Gb", type_of (List.nth (body_ws,1))),
  mk_var ("tb", type_of (List.nth (body_ws,2))));
val final_post = subst (ListPair.mapEq (fn (x,y) => x |-> y) (body_ws,[b,Gb,tb])) normal_post;
val p = param body_params;
val s = p "s" and G = p "G" and tn = p "tn";
val k = p "k" and ca = p "loop_body" and child = p "child" and ret = p "returned";
val (u,Gu,tu) = (``u:venom_state``, mk_var ("Gu",type_of G), mk_var ("tu",type_of tn));
val (t,Gr,tr) = (``t:venom_state``, mk_var ("Gr",type_of G), mk_var ("tr",type_of tn));
val q = ``q:num`` and child_ptr = ``child_ptr:string``;
val lc = ``(aid:num,counter:string,cell,32:num,mem_bytes_at cell 32 (^s).vs_memory)::live``;
val pc = ``(d,mem_bytes_at d (32+ ^k*msz) (^s).vs_memory)::protected``;

val setup_post =
  let
    val old = concl (BETA_RULE abi_decode_loop_setup_observed)
    val (ws, post) = strip_exists (snd (dest_disj (snd (strip_imp old))))
    val v = param (free_vars old)
    val at_cut = subst
      ([v "j" |-> k, v "sa" |-> ca, v "sb" |-> child,
        v "live" |-> lc, v "protected" |-> pc] @
       ListPair.mapEq (fn (x,y) => x |-> y) (ws,[u,Gu,tu,q,child_ptr])) post
  in mk_conj (mk_conj (at_cut, effect s tn u tu), ``
    not_fresh_at anchor counter /\ not_fresh_at anchor input /\
    local_ptrs_reserved ce loop_body /\ not_fresh_at loop_body input /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at loop_body x) /\
    abi_decoder_operand_live loop_body.cs_next_var hi /\ SUC ^k * msz <= n * msz``) end;

val child_post =
  let
    val motive = beta ``(^(guarded_effect_motive_typed ())) child_dst child_src MLOAD (Var input) hi ei``
    val (vs, imp) = strip_forall motive
    val v = param vs
    val (ws, packet) = strip_exists (snd (dest_imp imp))
    val (r, Gf, tf) = triple "child" ws
    val (orig,tail) = dest_conj packet
    val (obs,res) = dest_conj tail
    val (ts,witness) = strip_exists (fst (dest_disj res))
    val (physical, child_effect) = dest_conj witness
    val post = list_mk_conj [orig, obs, mk_conj (snd (dest_conj physical), child_effect)]
  in beta (subst [v "live" |-> lc, v "protected" |-> pc,
      v "start" |-> child, v "finish" |-> ret, v "s" |-> u, v "G" |-> Gu,
      v "tn" |-> tu, v "d" |-> ``d+32+ ^k*msz``,
      r |-> ``OK ^t``, Gf |-> Gr, tf |-> tr, hd ts |-> t] post) end;

val snapshots = ``(w2n (^(p "input_word")),input_bytes)::
  (d,mem_bytes_at d (32+SUC ^k*msz) (^t).vs_memory)::
  (MAP (\(id:num,p:string,b:num,l:num,bytes:word8 list). (b,bytes)) live ++ protected)``;
val backedge_block = ``<|bb_label := (^ret).cs_current_bb;
  bb_instructions := (^ret).cs_current_insts ++
    abi_decode_backedge_insts (^ret).cs_next_id iv nv (Var counter) hdr|>``;
val (back_pre, back_post) =
  let
    val old = concl (BETA_RULE abi_decode_loop_backedge_observed)
    val v = param (free_vars old)
    val common = [v "s" |-> t, v "G" |-> Gr, v "tn" |-> tr,
      v "sa" |-> ret, v "j" |-> k, v "id" |-> ``(^ret).cs_next_id``,
      v "prefix" |-> ``(^ret).cs_current_insts``, v "bb" |-> backedge_block,
      v "start" |-> p "anchor", v "end_st" |-> p "finish", v "snapshots" |-> snapshots]
    val (pres, res) = strip_imp old
    val (ws, post) = strip_exists res
  in (subst common (list_mk_conj pres),
      mk_conj (subst (common @ ListPair.mapEq (fn (x,y) => x |-> y) (ws,[b,Gb,tb])) post,
               effect t tr b tb)) end;

val back_support = ``
  (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (^s,^G,^tn) [] (OK ^t,^Gr,^tr)) /\
  (^frame) anchor ^s ^G ^tn ^t ^Gr ^tr /\ (^t).vs_labels = (^s).vs_labels /\
  (^owned_decoder_state) live protected returned ^t ^Gr ^tr /\
  mem_bytes_at d (32+ ^k*msz) (^t).vs_memory = mem_bytes_at d (32+ ^k*msz) (^s).vs_memory /\
  anchor.cs_next_var <= returned.cs_next_var``;

val content_all = beta (close_statement ``
  msz = type_memory_size tv /\ SUC ^k*msz <= n*msz /\
  output_base <= d /\ d+32+n*msz <= output_base+output_cap /\
  (^completed_robust_typed) j0 ^k ^s ^tn /\
  (^robust_at_typed) tv (d+32+ ^k*msz) ^t ^tr /\
  mem_bytes_at d (32+ ^k*msz) (^t).vs_memory = mem_bytes_at d (32+ ^k*msz) (^s).vs_memory /\
  mem_bytes_at d (32+SUC ^k*msz) (^b).vs_memory = mem_bytes_at d (32+SUC ^k*msz) (^t).vs_memory /\
  (^tb).t_mem SUBSET (^tr).t_mem /\ (^taint_decreases) ^tn ^tb /\
  mem_word_at d (^s).vs_memory = (w:256 word) ==>
  (^completed_robust_typed) j0 (SUC ^k) ^b ^tb /\ mem_word_at d (^b).vs_memory = w``);

val normal_packet_statement =
  let
    val extra = [u,Gu,tu,q,child_ptr,t,Gr,tr,param (free_vars back_pre) "ci",
                 param (free_vars back_pre) "counter_owner",b,Gb,tb]
    val imp = beta (mk_imp (list_mk_conj [entry,setup_post,child_post,
      back_pre,back_support,back_post],final_post))
    val _ = if List.all (fn x => List.exists (aconv x) (body_params @ extra)) (free_vars imp)
            then () else raise Fail "normal loop body: unexpected free parameter"
  in mk_imp (content_all,list_mk_forall (body_params @ extra,imp)) end;

Theorem abi_decode_loop_body_normal_packet_conditional:
  ^normal_packet_statement
Proof
  disch_then (mk_asm "content") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (conj_asm1_tac >- suspend "origin" >>
      conj_tac >- suspend "observer" >>
      `~b.vs_halted /\ b.vs_current_bb = hdr /\ b.vs_inst_idx = 0` by
        (qpat_assum `b = jump_to hdr _` (fn th => rewrite_tac[th]) >>
         qpat_assum `~t.vs_halted` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[jump_to_def, venomStateTheory.mstore_def, update_var_def]) >>
      ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_asm2_tac >- suspend "resource" >>
      conj_tac >- suspend "frame" >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_asm1_tac >- suspend "taint" >>
      suspend "content") >>
  `abi_decode_guarded_effect_core s tn t tr` by
    (irule abi_decode_guarded_effect_compose_core >>
     qexistsl_tac [`tu`,`u`] >> asm_rewrite_tac[]) >>
  irule abi_decode_guarded_effect_compose_core >>
  qexistsl_tac [`tr`,`t`] >> asm_rewrite_tac[]
QED

Resume abi_decode_loop_body_normal_packet_conditional[origin]:
  qpat_assum `!H. V H ==> gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gr,tr)` mp_tac >>
  qpat_assum `!H. V H ==> gas_origin_ptr_path _ (t,Gr,tr) [] (OK b,Gb,tb)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]
QED

Resume abi_decode_loop_body_normal_packet_conditional[observer]:
  rpt strip_tac >>
  qpat_assum `!obs. fn_has_code anchor finish' obs ==> fn_has_code loop_body child obs /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!obs. fn_has_code loop_body child obs ==> gas_path ctx obs s 0 (OK u)`
    (drule_then mp_tac) >>
  qpat_assum `!obs. fn_has_code child returned obs ==> gas_path ctx obs u 0 (OK t)`
    (drule_then mp_tac) >>
  qpat_assum `!obs. fn_has_code anchor finish' obs ==> gas_path ctx obs t 0 (OK b)`
    (drule_then mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  metis_tac[REWRITE_RULE[ADD_CLAUSES] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)]
QED

Resume abi_decode_loop_body_normal_packet_conditional[resource]:
  `alloca_history fn b` by
    (qpat_assum `alloca_history fn t` mp_tac >>
     qpat_assum `b.vs_allocas = t.vs_allocas` mp_tac >>
     qpat_assum `b.vs_inst_idx = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[allocaHistoryTheory.alloca_history_jump]) >>
  `allocas_from lo b` by
    (qpat_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
     qpat_assum `!H. V H ==> gas_origin_ptr_path _ (s,G,tn) [] (OK b,Gb,tb)`
       (qspec_then `H0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_then Any (qspec_then `lo` mp_tac)
       gasOriginPtrLabelsTheory.member_origin_allocas_from) >>
     asm_rewrite_tac[LESS_EQ_REFL]) >>
  `b.vs_labels = s.vs_labels` by
    (qpat_assum `b.vs_labels = t.vs_labels` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) b.vs_memory = bytes)
    ((w2n input_word,input_bytes)::(MAP (\(id,p,b,k,bytes). (b,bytes)) live ++ protected))` by
    (qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) b.vs_memory = bytes) ^snapshots`
       mp_tac >> POP_ASSUM_LIST (K all_tac) >> simp[EVERY_DEF]) >>
  `abi_decode_ptr_window Gb tb b input input_word (LENGTH input_bytes) /\
   (!D. V D ==> stmt_state_rel D ctx fn ce cx es b /\
      ghost_inv_at (DF D) lo delta ce cx es Gb tb b /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 Gb tb)` by
    (qpat_assum `!D. V D ==> abi_decode_ptr_window Gb tb b input input_word (LENGTH input_bytes) /\ _`
       mp_tac >> qpat_assum `?H. V H` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  irule (BETA_RULE abi_decode_loop_resource_reconstruct) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`G`,`s`,`tn`] >> asm_rewrite_tac[]) >>
  conj_tac >- (qexistsl_tac [`Gr`,`returned`,`t`,`tr`] >> asm_rewrite_tac[]) >>
  first_assum ACCEPT_TAC
QED

Resume abi_decode_loop_body_normal_packet_conditional[frame]:
  qpat_assum `!x. not_fresh_at returned x ==> _` mp_tac >>
  qpat_assum `!x. not_fresh_at anchor x ==> _` mp_tac >>
  qpat_assum `anchor.cs_next_var <= returned.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Resume abi_decode_loop_body_normal_packet_conditional[taint]:
  qpat_assum `tb.t_mem SUBSET tr.t_mem` mp_tac >>
  qpat_assum `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tr.t_mem ==> _` mp_tac >>
  qpat_assum `tu.t_mem = tn.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[SUBSET_DEF] >> metis_tac[]
QED

Resume abi_decode_loop_body_normal_packet_conditional[content]:
  `mem_bytes_at d (32+SUC k*msz) b.vs_memory =
   mem_bytes_at d (32+SUC k*msz) t.vs_memory` by
    (qpat_assum `EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) b.vs_memory = bytes) ^snapshots`
       mp_tac >> POP_ASSUM_LIST (K all_tac) >> simp[EVERY_DEF, LENGTH_mem_bytes_at]) >>
  asm "content" irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`n`,`output_base`,`output_cap`,`s`,`t`,`tn`,`tr`] >>
  asm_rewrite_tac[]
QED

Finalise abi_decode_loop_body_normal_packet_conditional
