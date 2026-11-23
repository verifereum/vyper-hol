(* Installed compiler occurrences used by the StructLit normal and cut rules. *)
Theory entryCreateStructLitLayout
Ancestors
  createSizeCutRegion entryCreateFocusSpec exprSimAggregateLayout exprSimFullBundleProps
  exprLoweringProps gasShadowCompile gasShadowCompileContext gasShadowCompileHelpers
  gasShadowCompileConvert loweringHalt fragExec compileEnv pred_set
  exprLowering emitHelper gasShadowState gasShadow gasShadowCompilePure
  gasShadowCompileBase venomInst

(* The common relative-layout rule is a parameter: the installation gives
   the occurrence distinctness, and clients instantiate it with the common
   subinterval/left-stop laws.  In particular, no strict growth is needed. *)
Definition structlit_layout_laws_def:
  structlit_layout_laws L <=>
    (!a m n b. cs_extends a m /\ cs_extends m n /\ cs_extends n b /\
               L a b ==> L m n) /\
    (!a m b s. cs_extends a m /\ cs_extends m b /\ L a b /\
               create_cut_region a m s /\ ~create_operand_at m s ==>
               ~create_operand_at b s)
End

Definition structlit_split_layout_def:
  structlit_split_layout L f a m b <=>
    ci_mono a m /\ ci_mono m b /\
    fn_has_code a m f /\ fn_has_code m b f /\ L a m /\ L m b /\
    frag_ids a m SUBSET frag_ids a b /\
    (!s. create_cut_region a m s /\ ~create_operand_at m s ==>
         ~create_operand_at b s)
End

Theorem structlit_split_layout_intro[local]:
  structlit_layout_laws L /\
  ci_mono a m /\ ci_mono m b /\ fn_has_code a b f /\ L a b ==>
  structlit_split_layout L f a m b
Proof
  simp[structlit_layout_laws_def,structlit_split_layout_def,ci_mono_def] >> strip_tac >>
  `fn_has_code a m f /\ fn_has_code m b f` by metis_tac[fn_has_code_split] >>
  `L a m /\ L m b` by metis_tac[cs_extends_refl] >>
  simp[abiEncoderPropsTheory.frag_ids_def,SUBSET_DEF] >>
  metis_tac[]
QED

Theorem structlit_fields_ci_mono[local]:
  !a ce ty fs buf off.
    ci_mono a (SND (compile_struct_lit compile_expr ce ty fs buf off a))
Proof
  rpt gen_tac >> irule ci_mono_compile_struct_lit_cfn >> simp[compile_expr_ci_mono]
QED

Theorem structlit_shadow_result[local]:
  gas_shadow_compiles c d /\ gas_shadow_state a a' /\ c a = (x,b) ==>
  ?b'. d a' = (x,b') /\ gas_shadow_state b b'
Proof
  Cases_on `d a'` >> simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum (qspecl_then [`a`,`a'`] mp_tac) >> simp[]
QED

Theorem structlit_fields_cons_compiler:
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) nm =
    SOME (fty,fsz) /\
  compile_struct_lit compile_expr ce (StructT nsid) ((nm,e)::fs) buf off si =
    (out,sb) /\
  compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
    (MAP (I ## gas_shadow_expr) ((nm,e)::fs)) buf off hi = (out,hb) /\
  gas_shadow_state si hi ==>
  ?vv dst src u sm sn su ss hm hn hu hs.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (src,su) /\
    compile_store_memory ce src dst fty (lowered_value_type ce e) su = (u,ss) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs buf (off+fsz) ss = (out,sb) /\
    compile_expr (gas_shadow_env sd ce) (expr_type e) (gas_shadow_expr e) hi = (vv,hm) /\
    emit_op ADD [buf; Lit (n2w off)] hm = (dst,hn) /\
    unwrap_value ce vv hn = (src,hu) /\
    compile_store_memory ce src dst fty (lowered_value_type ce e) hu = (u,hs) /\
    compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) buf (off+fsz) hs = (out,hb) /\
    gas_shadow_state sm hm /\ gas_shadow_state sn hn /\
    gas_shadow_state su hu /\ gas_shadow_state ss hs
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e si` >>
  rename1 `compile_expr ce _ e si = (vv,sm)` >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (src,su)` >>
  Cases_on `compile_store_memory ce src dst fty (lowered_value_type ce e) su` >>
  rename1 `compile_store_memory ce src dst _ _ su = (u,ss)` >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
      (compile_expr (gas_shadow_env sd ce) (expr_type e) (gas_shadow_expr e))` by
    (mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`,`T`]
       (CONJUNCT1 gas_shadow_compile_expr_env)) >> simp[])
  >> `?hm. compile_expr (gas_shadow_env sd ce) (expr_type e) (gas_shadow_expr e) hi =
        (vv,hm) /\ gas_shadow_state sm hm` by metis_tac[structlit_shadow_result]
  >> `?hn. emit_op ADD [buf; Lit (n2w off)] hm = (dst,hn) /\ gas_shadow_state sn hn` by
    metis_tac[structlit_shadow_result,gas_shadow_compiles_emit_op_same]
  >> `?hu. unwrap_value ce vv hn = (src,hu) /\ gas_shadow_state su hu` by
    metis_tac[structlit_shadow_result,gas_shadow_compiles_unwrap_value]
  >> `?hs. compile_store_memory ce src dst fty (lowered_value_type ce e) hu =
        (u,hs) /\ gas_shadow_state ss hs` by
    metis_tac[structlit_shadow_result,gas_shadow_compiles_store_memory]
  >> map_every qexists_tac [`vv`,`dst`,`src`,`u`,`sm`,`sn`,`su`,`ss`,`hm`,`hn`,`hu`,`hs`]
  >> qpat_x_assum `compile_struct_lit _ ce _ ((nm,e)::_) _ _ _ = _` mp_tac
  >> qpat_x_assum `compile_struct_lit _ (gas_shadow_env _ _) _ _ _ _ _ = _` mp_tac
  >> simp[Once compile_struct_lit_def,comp_bind_def,comp_ignore_bind_def,
          gas_shadow_expr_type]
  >> simp[Once compile_struct_lit_def,comp_bind_def,comp_ignore_bind_def]
QED

Theorem structlit_field_chain_mono[local]:
  !ce e si vv sm buf off dst sn src su fty u ss ty fs off' out sb.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (src,su) /\
    compile_store_memory ce src dst fty (lowered_value_type ce e) su = (u,ss) /\
    compile_struct_lit compile_expr ce ty fs buf off' ss = (out,sb) ==>
    ci_mono si sm /\ ci_mono sm sn /\ ci_mono sn su /\
    ci_mono su ss /\ ci_mono ss sb
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ce`,`expr_type e`,`e`,`si`] mp_tac (CONJUNCT1 compile_expr_ci_mono) >>
  qspecl_then [`ADD`,`[buf;Lit (n2w off)]`,`sm`] mp_tac ci_mono_emit_op >>
  qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >>
  qspecl_then [`ce`,`src`,`dst`,`fty`,`lowered_value_type ce e`,`su`] mp_tac
    ci_mono_compile_store_memory >>
  qspecl_then [`ss`,`ce`,`ty`,`fs`,`buf`,`off'`] mp_tac (GEN_ALL structlit_fields_ci_mono) >>
  simp[]
QED

Theorem structlit_split_code[local]:
  expr_sim_full_code (ctx,hctx,f,hf) (a,b,ha,hb) /\
  ci_mono a m /\ ci_mono m b /\ ci_mono ha hm /\ ci_mono hm hb /\
  gas_shadow_state m hm ==>
  expr_sim_full_code (ctx,hctx,f,hf) (a,m,ha,hm) /\
  expr_sim_full_code (ctx,hctx,f,hf) (m,b,hm,hb)
Proof
  simp[expr_sim_full_code_def,ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem structlit_selected_intervals:
  structlit_layout_laws L /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) nm =
    SOME (fty,fsz) /\
  compile_struct_lit compile_expr ce (StructT nsid) ((nm,e)::fs) buf off si =
    (out,sb) /\
  compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
    (MAP (I ## gas_shadow_expr) ((nm,e)::fs)) buf off hi = (out,hb) /\
  expr_sim_full_code (ctx,hctx,f,hf) (si,sb,hi,hb) /\ L si sb ==>
  ?vv dst src u sm sn su ss hm hn hu hs.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
    unwrap_value ce vv sn = (src,su) /\
    compile_store_memory ce src dst fty (lowered_value_type ce e) su = (u,ss) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs buf (off+fsz) ss = (out,sb) /\
    compile_expr (gas_shadow_env sd ce) (expr_type e) (gas_shadow_expr e) hi = (vv,hm) /\
    emit_op ADD [buf; Lit (n2w off)] hm = (dst,hn) /\
    unwrap_value ce vv hn = (src,hu) /\
    compile_store_memory ce src dst fty (lowered_value_type ce e) hu = (u,hs) /\
    compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) buf (off+fsz) hs = (out,hb) /\
    expr_sim_full_code (ctx,hctx,f,hf) (si,sm,hi,hm) /\
    expr_sim_full_code (ctx,hctx,f,hf) (sm,sn,hm,hn) /\
    expr_sim_full_code (ctx,hctx,f,hf) (sn,su,hn,hu) /\
    expr_sim_full_code (ctx,hctx,f,hf) (su,ss,hu,hs) /\
    expr_sim_full_code (ctx,hctx,f,hf) (ss,sb,hs,hb) /\
    structlit_split_layout L f si sm sb /\ structlit_split_layout L f sm sn sb /\
    structlit_split_layout L f sn su sb /\ structlit_split_layout L f su ss sb
Proof
  strip_tac >>
  `gas_shadow_state si hi /\ fn_has_code si sb f` by fs[expr_sim_full_code_def] >>
  drule_all structlit_fields_cons_compiler >> strip_tac >>
  drule_all structlit_field_chain_mono >> strip_tac >>
  `ci_mono hi hm /\ ci_mono hm hn /\ ci_mono hn hu /\
   ci_mono hu hs /\ ci_mono hs hb` by
    (gvs[] >> drule_all (SIMP_RULE (srw_ss()) [gas_shadow_expr_type]
       (Q.SPECL [`gas_shadow_env sd ce`,`gas_shadow_expr e`] structlit_field_chain_mono)) >>
     simp[]) >>
  `ci_mono su sb /\ ci_mono sn sb /\ ci_mono sm sb` by metis_tac[ci_mono_trans] >>
  `ci_mono hu hb /\ ci_mono hn hb /\ ci_mono hm hb` by metis_tac[ci_mono_trans] >>
  `expr_sim_full_code (ctx,hctx,f,hf) (si,sm,hi,hm) /\
   expr_sim_full_code (ctx,hctx,f,hf) (sm,sb,hm,hb)` by
    (irule structlit_split_code >> simp[]) >>
  `expr_sim_full_code (ctx,hctx,f,hf) (sm,sn,hm,hn) /\
   expr_sim_full_code (ctx,hctx,f,hf) (sn,sb,hn,hb)` by
    (irule structlit_split_code >> simp[]) >>
  `expr_sim_full_code (ctx,hctx,f,hf) (sn,su,hn,hu) /\
   expr_sim_full_code (ctx,hctx,f,hf) (su,sb,hu,hb)` by
    (irule structlit_split_code >> simp[]) >>
  `expr_sim_full_code (ctx,hctx,f,hf) (su,ss,hu,hs) /\
   expr_sim_full_code (ctx,hctx,f,hf) (ss,sb,hs,hb)` by
    (irule structlit_split_code >> simp[]) >>
  map_every qexists_tac [`vv`,`dst`,`src`,`u`,`sm`,`sn`,`su`,`ss`,`hm`,`hn`,`hu`,`hs`] >>
  `structlit_split_layout L f si sm sb` by (irule structlit_split_layout_intro >> simp[]) >>
  drule_then strip_assume_tac (iffLR structlit_split_layout_def) >>
  `structlit_split_layout L f sm sn sb` by (irule structlit_split_layout_intro >> simp[]) >>
  qpat_assum `structlit_split_layout L f sm sn sb` (strip_assume_tac o REWRITE_RULE
    [structlit_split_layout_def]) >>
  `structlit_split_layout L f sn su sb` by (irule structlit_split_layout_intro >> simp[]) >>
  qpat_assum `structlit_split_layout L f sn su sb` (strip_assume_tac o REWRITE_RULE
    [structlit_split_layout_def]) >>
  simp[] >> irule structlit_split_layout_intro >> simp[]
QED

Theorem structlit_alloc_selected_interval:
  structlit_layout_laws L /\
  compile_expr ce ty (StructLit ann nsid fs) sa = (vv,sb) /\
  compile_expr (gas_shadow_env sd ce) ty (gas_shadow_expr (StructLit ann nsid fs)) ha =
    (vv,hb) /\
  expr_sim_full_code (ctx,hctx,f,hf) (sa,sb,ha,hb) /\ L sa sb ==>
  ?n buf u sm hm.
    n = SUM (MAP (SND o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
    compile_alloc_buffer n sa = (buf,sm) /\ compile_alloc_buffer n ha = (buf,hm) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs buf.buf_operand 0 sm = (u,sb) /\
    compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) buf.buf_operand 0 hm = (u,hb) /\
    vv = LocatedValue (expr_type (StructLit ann nsid fs)) (base_ptr buf) /\
    expr_sim_full_code (ctx,hctx,f,hf) (sa,sm,ha,hm) /\
    expr_sim_full_code (ctx,hctx,f,hf) (sm,sb,hm,hb) /\
    structlit_split_layout L f sa sm sb
Proof
  strip_tac >>
  `gas_shadow_state sa ha /\ fn_has_code sa sb f` by fs[expr_sim_full_code_def] >>
  drule compile_struct_literal_inv >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer n sa` >>
  rename1 `compile_alloc_buffer n sa = (buf,sm)` >>
  `?hm. compile_alloc_buffer n ha = (buf,hm) /\ gas_shadow_state sm hm` by
    metis_tac[structlit_shadow_result,gas_shadow_compiles_alloc_buffer] >>
  `gas_shadow_compiles (compile_struct_lit compile_expr ce (StructT nsid) fs buf.buf_operand 0)
      (compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
        (MAP (I ## gas_shadow_expr) fs) buf.buf_operand 0)` by
    (irule (MATCH_MP gas_shadow_compiles_struct_lit (CONJUNCT1 gas_shadow_compile_expr_env) |>
            Q.INST [`sh` |-> `T`] |> REWRITE_RULE [COND_CLAUSES])) >>
  `?hb'. compile_struct_lit compile_expr (gas_shadow_env sd ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) buf.buf_operand 0 hm = (u,hb') /\
      gas_shadow_state sb hb'` by metis_tac[structlit_shadow_result] >>
  `SND (compile_expr (gas_shadow_env sd ce) ty
          (gas_shadow_expr (StructLit ann nsid fs)) ha) = hb'` by
    (qpat_x_assum `compile_expr (gas_shadow_env _ _) _ _ ha = _` kall_tac >>
     qpat_assum `Abbrev (n = _)` (fn th =>
       simp[gas_shadow_expr_def,compile_struct_literal,
            GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  `hb' = hb` by (qpat_x_assum `SND _ = hb'` mp_tac >> simp[EQ_SYM_EQ]) >>
  qpat_x_assum `hb' = hb` SUBST_ALL_TAC >>
  `ci_mono sa sm /\ ci_mono ha hm` by
    (qspecl_then [`n`,`sa`] mp_tac ci_mono_compile_alloc_buffer >>
     qspecl_then [`n`,`ha`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sm sb /\ ci_mono hm hb` by
    (qspecl_then [`sm`,`ce`,`StructT nsid`,`fs`,`buf.buf_operand`,`0`]
       mp_tac structlit_fields_ci_mono >>
     qspecl_then [`hm`,`gas_shadow_env sd ce`,`StructT nsid`,
       `MAP (I ## gas_shadow_expr) fs`,`buf.buf_operand`,`0`]
       mp_tac structlit_fields_ci_mono >> simp[]) >>
  `expr_sim_full_code (ctx,hctx,f,hf) (sa,sm,ha,hm) /\
   expr_sim_full_code (ctx,hctx,f,hf) (sm,sb,hm,hb)` by
    (irule structlit_split_code >> simp[]) >>
  map_every qexists_tac [`n`,`buf`,`u`,`sm`,`hm`] >>
  simp[Abbr `n`] >> irule structlit_split_layout_intro >> simp[]
QED

Theorem structlit_fields_nil_interval:
  compile_struct_lit compile_expr ce ty [] buf off si = (out,sb) /\
  compile_struct_lit compile_expr (gas_shadow_env sd ce) ty
    (MAP (I ## gas_shadow_expr) []) buf off hi = (out,hb) ==>
  out = buf /\ sb = si /\ hb = hi
Proof
  simp[compile_struct_lit_def,comp_return_def]
QED
