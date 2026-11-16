(* Retained compiler decomposition exported for uniform Slots control paths. *)
Theory fullStoreSlotsControlLayout
Ancestors
  placeStoreSlots stmtLoweringMono emitHelperProps fragExec
  typedMemoryCopy compileEnv loweringStateRelDefs arithmetic list
  context emitHelper exprLoweringProps

Theorem store_slots_elements_layout:
  compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) ==>
  ?hdr body exit cv a b c init p q h lt h1 done h2 hj body_start
   so b1 sp b2 doff b3 dp sc sd inc tail1 tail2 tail3.
    ci_mono sa sc /\ ci_mono sc sd /\ ci_mono sd sb /\
    not_fresh_at sc cv /\ ~not_fresh_at sa cv /\
    (fn_has_code sa sb func ==> fn_has_code sc sd func) /\
    fresh_label "dyn_cond" sa = (hdr,a) /\
    fresh_label "dyn_body" a = (body,b) /\
    fresh_label "dyn_exit" b = (exit,c) /\
    fresh_var c = (cv,init) /\
    emit_inst ASSIGN [Lit 0w] [cv] init = ((),p) /\
    emit_inst JMP [Label hdr] [] p = ((),q) /\
    new_block hdr q = (q.cs_current_bb,h) /\
    emit_op LT [Var cv;cnt] h = (lt,h1) /\
    emit_op ISZERO [lt] h1 = (done,h2) /\
    emit_inst JNZ [done;Label exit;Label body] [] h2 = ((),hj) /\
    new_block body hj = (hj.cs_current_bb,body_start) /\
    emit_op MUL [Var cv;Lit (n2w (type_memory_bytes cenv elem))]
      body_start = (so,b1) /\
    emit_op ADD [src;so] b1 = (sp,b2) /\
    emit_op MUL [Var cv;Lit (n2w (type_memory_bytes cenv elem DIV 32))]
      b2 = (doff,b3) /\
    emit_op ADD [slot;doff] b3 = (dp,sc) /\
    compile_store_slots cenv sp dp elem tr sc = ((),sd) /\
    emit_op ADD [Var cv;Lit 1w] sd = (inc,tail1) /\
    emit_inst ASSIGN [inc] [cv] tail1 = ((),tail2) /\
    emit_inst JMP [Label hdr] [] tail2 = ((),tail3) /\
    new_block exit tail3 = (tail3.cs_current_bb,sb)
Proof
  simp[Once compile_store_slots_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_store_slots cenv sp dp elem tr sc = ((),sd)` >>
  `ci_mono sc sd` by
    metis_tac[cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots,
              pairTheory.SND] >>
  rpt (goal_assum (drule_at Any)) >>
  gvs[fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
      fresh_id_def, emit_def, new_block_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `ci_mono sc sd` >>
  qmatch_goalsub_abbrev_tac `ci_mono sd sf` >>
  `ci_mono sa sc` by
    (simp[ci_mono_def, cs_extends_def, Abbr `sc`] >>
     qexists_tac `TAKE 2 sc.cs_blocks` >>
     simp[Abbr `sc`, APPEND_ASSOC]) >>
  `ci_mono sd sf` by
    (simp[ci_mono_def, cs_extends_def, Abbr `sf`] >>
     qexists_tac `TAKE 1 sf.cs_blocks` >>
     simp[Abbr `sf`, APPEND_ASSOC]) >>
  simp[] >>
  conj_tac
  >- simp[not_fresh_at_def, Abbr `sc`, emitHelperPropsTheory.fresh_var_distinct] >>
  conj_tac
  >- (simp[not_fresh_at_def] >> qexists_tac `sa.cs_next_var` >> simp[]) >>
  strip_tac >> irule fragExecTheory.fn_has_code_mid >>
  gvs[ci_mono_def] >> qexistsl_tac [`sf`, `sa`] >> simp[]
QED
