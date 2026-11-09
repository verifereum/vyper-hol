(* Task-owned sequential field-copy interfaces. *)
Theory externalReturnCopyFields
Ancestors
  externalReturnCopyTransport externalReturnCopyFrame fragExec
  exprLoweringProps valueEncoding valueEncodingProps valueEncodingProofs
  vyperTypeSystem vyperTyping list rich_list pair alist arithmetic words
  compileEnv context

Definition return_copy_entries_def:
  (return_copy_entries cenv ctx tenv [] stys dtvs stvs vs <=>
     stys = [] /\ dtvs = [] /\ stvs = [] /\ vs = []) /\
  (return_copy_entries cenv ctx tenv (dty::dtys) stys dtvs stvs vs <=>
     case (stys,dtvs,stvs,vs) of
       (sty::stys,dtv::dtvs,stv::stvs,v::vs) =>
         type_memory_bytes cenv dty = type_memory_size dtv /\
         type_memory_bytes cenv sty = type_memory_size stv /\
         evaluate_type tenv dty = SOME dtv /\
         evaluate_type tenv sty = SOME stv /\
         type_widens_to tenv sty dty /\
         value_has_type stv v /\ value_has_type dtv v /\
         return_copy_entry cenv ctx tenv dty sty dtv stv v /\
         return_copy_entries cenv ctx tenv dtys stys dtvs stvs vs
     | _ => F)
End

Theorem return_copy_entries_lengths:
  !dtys stys dtvs stvs vs.
    return_copy_entries cenv ctx tenv dtys stys dtvs stvs vs ==>
    LENGTH dtys = LENGTH vs /\ LENGTH stys = LENGTH vs /\
    LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs
Proof
  Induct >> simp[return_copy_entries_def] >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  simp[return_copy_entries_def] >> metis_tac[]
QED

Theorem return_copy_struct_fields_producer:
  !fs full cenv dst src doff soff.
    ALL_DISTINCT (MAP FST full) /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full /\
    EVERY (\f. MEM f full) fs ==>
    compile_struct_typed_copy cenv dst src fs full doff soff =
    compile_typed_copy_fields cenv dst src
      (MAP (\(name,ty,sz). ty) fs) (MAP (\(name,ty,sz). ty) fs) doff soff
Proof
  Induct
  >- simp[compile_store_memory_typed_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[EVERY_DEF] >> strip_tac >>
  `ALOOKUP full h0 = SOME (h1,h2)` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> gvs[]) >>
  `h2 = type_memory_bytes cenv h1` by
    (gvs[EVERY_MEM] >>
     qpat_x_assum `!e. MEM e full ==> _` (qspec_then `(h0,h1,h2)` mp_tac) >> simp[]) >>
  simp[Once compile_store_memory_typed_def] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  simp[]
QED

Theorem return_copy_struct_suffix_producer:
  ALL_DISTINCT (MAP FST full) /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full ==>
  !n dst src doff soff.
    compile_struct_typed_copy cenv dst src (DROP n full) full doff soff =
    compile_typed_copy_fields cenv dst src
      (MAP (\(name,ty,sz). ty) (DROP n full))
      (MAP (\(name,ty,sz). ty) (DROP n full)) doff soff
Proof
  rpt strip_tac >> irule return_copy_struct_fields_producer >>
  simp[EVERY_MEM] >> metis_tac[MEM_DROP_IMP]
QED

Theorem return_copy_fields_tuple_zip:
  !names vs tvs off mem.
    LENGTH names = LENGTH vs /\ LENGTH names = LENGTH tvs ==>
    (fields_in_memory (ZIP(names,vs)) (ZIP(names,tvs)) off mem <=>
     tuple_in_memory vs tvs off mem)
Proof
  Induct >> Cases_on `vs` >> Cases_on `tvs` >>
  simp[val_in_memory_def]
QED

Theorem return_copy_tuple_frame:
  LENGTH vs = LENGTH tvs /\ tuple_val_wf vs tvs /\
  tuple_in_memory vs tvs off mem /\ return_copy_memory_frame dst len mem mem' /\
  (off + type_memory_size_list tvs <= dst \/ dst + len <= off) ==>
  tuple_in_memory vs tvs off mem'
Proof
  rpt strip_tac >> irule (cj 5 val_in_memory_mem_agree_proof) >>
  simp[] >> qexists_tac `mem` >> gvs[return_copy_memory_frame_def]
QED

Theorem return_copy_entry_offset_frag:
  !cenv ctx tenv dty sty dtv stv v dst src doff soff sa s1 s2 sb dp sp s dw sw.
  return_copy_entry cenv ctx tenv dty sty dtv stv v /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  type_widens_to tenv sty dty /\ value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv <> 0 ==>
    w2n sw + soff + type_memory_size stv < dimword (:256) /\
    (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
     w2n dw + doff + type_memory_size dtv <= w2n sw + soff)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
         return_copy_frame sa (w2n dw + doff) (type_memory_size dtv) s t)
    (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono s2 sb` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by metis_tac[return_copy_offset_mono] >>
  `(!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x)` by
    metis_tac[return_copy_offset_fresh, return_copy_operand_fresh_mono] >>
  `w2n (dw + n2w doff) = w2n dw + doff` by
    (irule return_copy_offset_nonwrap >> decide_tac) >>
  `val_in_memory stv v (w2n (sw + n2w soff)) s.vs_memory` by
    (Cases_on `type_memory_size stv = 0`
     >- metis_tac[return_zero_layout_memory_address] >>
     `w2n (sw + n2w soff) = w2n sw + soff` by
       (irule return_copy_offset_nonwrap >> decide_tac) >> metis_tac[]) >>
  ho_match_mp_tac return_copy_two_offsets_frag >>
  qexistsl_tac [`dst`, `src`, `doff`, `soff`, `dp`, `s1`, `sp`, `s2`, `dw`, `sw`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `return_copy_entry _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [return_copy_entry_def]) >>
  disch_then drule >>
  disch_then (qspecl_then [`u`, `dw + n2w doff`, `sw + n2w soff`] mp_tac) >>
  simp[] >> disch_then irule >>
  Cases_on `type_memory_size stv = 0` >> simp[] >>
  `w2n (sw + n2w soff) = w2n sw + soff` by
    (irule return_copy_offset_nonwrap >> decide_tac) >> simp[]
QED

Theorem return_copy_tuple_zero_memory:
  tuple_val_wf vs tvs /\ type_memory_size_list tvs = 0 ==>
  (tuple_in_memory vs tvs src mem <=> tuple_in_memory vs tvs dst mem')
Proof
  strip_tac >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by simp[val_wf_def] >>
  `type_memory_size (TupleTV tvs) = 0` by simp[type_memory_size_def] >>
  drule_all return_zero_layout_memory_address >>
  simp[val_in_memory_def]
QED

Theorem return_copy_tuple_frame_cond:
  LENGTH vs = LENGTH tvs /\ tuple_val_wf vs tvs /\
  tuple_in_memory vs tvs off mem /\ return_copy_memory_frame dst len mem mem' /\
  (type_memory_size_list tvs <> 0 ==>
    off + type_memory_size_list tvs <= dst \/ dst + len <= off) ==>
  tuple_in_memory vs tvs off mem'
Proof
  strip_tac >> Cases_on `type_memory_size_list tvs = 0`
  >- metis_tac[return_copy_tuple_zero_memory] >>
  irule return_copy_tuple_frame >> metis_tac[]
QED

Theorem return_copy_tuple_suffix_frag:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw.
    return_copy_entries cenv ctx tenv dtys stys dtvs stvs vs /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (type_memory_size_list stvs <> 0 ==>
      w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
      (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
       w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff)) ==>
    frag_exec ctx sa sb (\u. u = s)
      (\t. tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
           return_copy_frame sa (w2n dw + doff)
             (type_memory_size_list dtvs) s t) (\r. F)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[return_copy_entries_def, compile_store_memory_typed_def,
          comp_return_def, val_in_memory_def, type_memory_size_def] >>
      irule frag_exec_refl >> simp[]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[return_copy_entries_def] >>
  rename1 `return_copy_entry cenv ctx tenv dty sty dtv stv v` >>
  rename1 `return_copy_entries cenv ctx tenv dtys stys dtvs stvs vs` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dst_ptr dty src_ptr sty cs'' = (u,sc)` >>
  Cases_on `u` >>
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs''` by metis_tac[return_copy_offset_mono] >>
     `ci_mono cs'' sc` by metis_tac[cj 1 ci_mono_typed_memory_family, SND] >>
     `ci_mono sc sb` by metis_tac[cj 2 ci_mono_typed_memory_family, SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
      return_copy_entry_offset_frag) >>
  disch_then (drule_at (Pat `compile_with_byte_offset src _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `return_copy_entry _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (simp[ADD_COMM] >> decide_tac)) >>
  disch_then (mp_then Any irule frag_exec_then) >>
  `cs_extends sa sc /\ cs_extends sc sb` by gvs[ci_mono_def] >>
  simp[] >> rpt strip_tac >> suspend "suffix"
QED

Resume return_copy_tuple_suffix_frag[suffix]:
  `LENGTH vs = LENGTH stvs` by metis_tac[return_copy_entries_lengths] >>
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `return_copy_entry _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule return_copy_tuple_frame_cond >> simp[] >>
     qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[return_copy_frame_def] >> decide_tac) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[return_copy_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[return_copy_operand_fresh_mono] >>
  qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` drule >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> decide_tac)) >>
  disch_then (mp_then Any irule frag_exec_conseq) >>
  simp[] >> rpt strip_tac
  >- suspend "preserve_head" >>
  suspend "frames"
QED

Resume return_copy_tuple_suffix_frag[preserve_head]:
  irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size dtv`, `t.vs_memory`] >>
  gvs[return_copy_frame_def, return_copy_memory_frame_def] >>
  first_x_assum irule >> decide_tac
QED

Resume return_copy_tuple_suffix_frag[frames]:
  irule return_copy_frame_trans >> qexists_tac `t` >>
  conj_tac
  >- (irule return_copy_frame_subinterval >>
      qexistsl_tac [`doff + w2n dw`, `type_memory_size dtv`] >> simp[]) >>
  irule return_copy_frame_mono >> qexists_tac `sc` >> simp[] >>
  irule return_copy_frame_subinterval >>
  qexistsl_tac [`doff + (type_memory_size dtv + w2n dw)`,
    `type_memory_size_list dtvs`] >> simp[]
QED

Finalise return_copy_tuple_suffix_frag

Theorem return_copy_struct_suffix_frag:
  !n tvs vs dst src doff soff sa sb s dw sw.
    ALL_DISTINCT (MAP FST full) /\
    EVERY (\(name,ty,sz). sz = type_memory_bytes cenv ty) full /\
    return_copy_entries cenv ctx tenv
      (MAP (\(name,ty,sz). ty) (DROP n full))
      (MAP (\(name,ty,sz). ty) (DROP n full)) tvs tvs vs /\
    tuple_val_wf vs tvs /\
    compile_struct_typed_copy cenv dst src (DROP n full) full doff soff sa = ((),sb) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
    tuple_in_memory vs tvs (w2n sw + soff) s.vs_memory /\
    w2n dw + doff + type_memory_size_list tvs < dimword (:256) /\
    (type_memory_size_list tvs <> 0 ==>
      w2n sw + soff + type_memory_size_list tvs < dimword (:256) /\
      (w2n sw + soff + type_memory_size_list tvs <= w2n dw + doff \/
       w2n dw + doff + type_memory_size_list tvs <= w2n sw + soff)) ==>
    frag_exec ctx sa sb (\u. u = s)
      (\t. tuple_in_memory vs tvs (w2n dw + doff) t.vs_memory /\
           return_copy_frame sa (w2n dw + doff)
             (type_memory_size_list tvs) s t) (\r. F)
Proof
  rpt strip_tac >>
  drule_all return_copy_struct_suffix_producer >> strip_tac >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule return_copy_tuple_suffix_frag >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`s`, `dw`, `sw`] mp_tac) >> simp[]
QED
