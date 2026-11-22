(* Pair each observed compiler cut before constructing any machine path. *)
Theory createSizeRawPairedCode
Ancestors
  createSizeItinerary createSizeCtorCutSpine createSizeDispatch
  exprSimFullBundleProps exprSimSend externalEntryShape exprLoweringProps stmtLoweringMono
  exprLowering fragExec compileEnv builtinCreate
  gasShadow gasShadowCompile gasShadowCompileHelpers gasShadowCompileBase gasShadowState
  gasShadowCompileCallSupport gasShadowCompileContext gasShadowCompileConvert
  gasShadowCompileExternal gasShadowCompileBuiltinCreate gasShadowCompilePure
  list rich_list pair option arithmetic

(* Read the equal result and related end state from a paired compiler action. *)
fun raw_pair r sh th =
  Cases_on sh >>
  qspecl_then r (fn paired =>
    ASSUM_LIST (fn asms =>
      let val equations = List.filter (fn a => is_eq (concl a) andalso
            pairSyntax.is_pair (rhs (concl a))) asms
      in
        first_assum (fn state =>
          let val result = SIMP_RULE (srw_ss()) equations (MP paired state)
          in if is_conj (concl result) then
               CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) assume_tac result
             else assume_tac result
          end)
      end)) (REWRITE_RULE [gas_shadow_compiles_def] th);

Theorem raw_shadow_scalar_actions[local]:
  (!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr ce ty (gas_shadow_expr e))) /\
  (!ce e. gas_shadow_compiles (compile_create_salt compile_expr ce e)
    (compile_create_salt compile_expr ce (OPTION_MAP gas_shadow_expr e))) /\
  (!ce xs. gas_shadow_compiles (compile_create_ctor_args compile_expr ce xs)
    (compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs)))
Proof
  rpt conj_tac >> rpt gen_tac >>
  FIRST [irule (SRULE [] (Q.INST [`sh` |-> `T`] gas_shadow_compiles_lower_value)),
         irule (SRULE [gas_shadow_env_F]
           (Q.INST [`sd` |-> `F`, `sh` |-> `T`] gas_shadow_compiles_create_salt)),
         irule (SRULE [gas_shadow_env_F]
           (Q.INST [`sd` |-> `F`, `sh` |-> `T`] gas_shadow_compiles_create_ctor_args))] >>
  simp[gas_shadow_compile_expr]
QED

Theorem raw_compiler_extends[local]:
  (!ce ty e a. cs_extends a (SND (compile_expr ce ty e a))) /\
  (!ce ty e a. cs_extends a (SND (lower_value compile_expr ce ty e a))) /\
  (!ce cp v a. cs_extends a (SND (compile_snapshot_vv ce cp v a))) /\
  (!ce v ty a. cs_extends a (SND (compile_create_snapshot ce v ty a))) /\
  (!opc os a. cs_extends a (SND (emit_op opc os a))) /\
  (!ce xs a. cs_extends a (SND (compile_create_ctor_args compile_expr ce xs a))) /\
  (!sz a. cs_extends a (SND (compile_alloc_buffer sz a))) /\
  (!dst src lenop a. cs_extends a (SND (compile_copy_memory_dynamic dst src lenop a))) /\
  (!ce dst rows a. cs_extends a (SND (compile_abi_encode_values_to_buf ce dst rows a))) /\
  (!ce salt a. cs_extends a (SND (compile_create_salt compile_expr ce salt a))) /\
  (!buf sz v salt rof a. cs_extends a (SND (compile_create_dispatch buf sz v salt rof a)))
Proof
  simp[compile_expr_labels,lower_value_labels,compile_snapshot_vv_labels,
       compile_create_snapshot_labels,compile_create_ctor_args_labels,
       compile_alloc_buffer_labels,compile_copy_memory_dynamic_labels,
       compile_abi_encode_values_to_buf_labels,compile_create_salt_labels,
       compile_create_dispatch_labels] >>
  metis_tac[ci_mono_def,ci_mono_emit_op]
QED

(* Restrict the containing function to successive pieces of a known spine. *)
fun raw_code_spine f (a::b::(rest as _::_)) =
      [QUOTE ("cs_extends " ^ b ^ " " ^ List.last rest)] by
        (let fun tr [_] = first_assum ACCEPT_TAC
               | tr (y::ys) = irule cs_extends_trans >> qexists_tac [QUOTE y] >>
                    conj_tac >- first_assum ACCEPT_TAC >> tr ys
               | tr [] = NO_TAC
         in tr rest end) >>
      [QUOTE ("fn_has_code " ^ a ^ " " ^ b ^ " " ^ f ^ " /\\ fn_has_code " ^ b ^ " " ^ List.last rest ^ " " ^ f)] by
        (irule fn_has_code_split >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum strip_assume_tac >> raw_code_spine f (b::rest)
  | raw_code_spine f _ = all_tac;

fun raw_extends ths = FIRST (map (fn th => mp_tac th >> simp[] >> metis_tac[SND])
       (List.map (fn i => cj i raw_compiler_extends) ths));

Theorem raw_shadow_rows[local]:
  create_itinerary_ctor_rows ce xs vals a b cs mid vvs /\
  create_itinerary_ctor_rows ce (MAP gas_shadow_expr xs) vals ha hb hs hm hv /\
  gas_shadow_state a ha ==>
  (!i. i <= LENGTH xs ==> gas_shadow_state (EL i cs) (EL i hs)) /\
  (!i. i < LENGTH xs ==>
    EL i hv = EL i vvs /\ gas_shadow_state (EL i mid) (EL i hm))
Proof
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [create_itinerary_ctor_rows_def]) >>
  `cs <> [] /\ hs <> []` by (Cases_on `cs` >> Cases_on `hs` >> fs[]) >>
  `!i. i < LENGTH xs /\ gas_shadow_state (EL i cs) (EL i hs) ==>
     EL i hv = EL i vvs /\ gas_shadow_state (EL i mid) (EL i hm) /\
     gas_shadow_state (EL (SUC i) cs) (EL (SUC i) hs)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!j. j < LENGTH xs ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!j. j < LENGTH (MAP _ xs) ==> _ /\ _`
       (drule_then strip_assume_tac o SIMP_RULE (srw_ss()) [EL_MAP,GSYM MAP_DROP,gas_shadow_expr_can_mutate]) >>
     qspecl_then [`ce`,`expr_type (EL i xs)`,`EL i xs`,`T`] mp_tac
       (cj 1 gas_shadow_compile_expr) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[] >> strip_tac >>
     qpat_x_assum `EL i vvs = EL i hv` (SUBST_ALL_TAC o SYM) >>
     mp_tac (Q.INST [`cenv` |-> `ce`, `copy_flag` |-> `exprs_can_mutate ce (DROP (SUC i) xs)`,
                     `vv` |-> `ext_call_arg_value (lowered_value_type ce (EL i xs)) (EL i vvs)`]
               gas_shadow_compiles_snapshot_vv) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> gvs[]) >>
  conj_asm1_tac
  >- (Induct >> simp[EL] >> strip_tac >> first_assum (irule_at Any) >> decide_tac) >>
  rpt strip_tac >> first_x_assum (qspec_then `i` mp_tac) >> simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]
QED

Theorem raw_row_embedding[local]:
  create_itinerary_ctor_rows ce xs vals a b cs mid vvs /\ fn_has_code a b fn ==>
  !i. i < LENGTH xs ==>
    fn_has_code (EL i cs) (EL i mid) fn /\
    fn_has_code (EL i mid) (EL (SUC i) cs) fn /\
    fn_has_code (EL i cs) (EL (SUC i) cs) fn
Proof
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [create_itinerary_ctor_rows_def]) >>
  `cs <> []` by (Cases_on `cs` >> fs[]) >>
  `a = EL 0 cs /\ b = EL (LENGTH xs) cs` by (`PRE (LENGTH cs) = LENGTH xs` by decide_tac >> fs[EL,LAST_EL]) >>
  `!i. i < LENGTH xs ==> cs_extends (EL i cs) (EL i mid) /\
    cs_extends (EL i mid) (EL (SUC i) cs) /\ cs_extends (EL i cs) (EL (SUC i) cs)` by
    (rpt strip_tac >> qpat_assum `!j. j < LENGTH xs ==> _` (drule_then strip_assume_tac) >>
     metis_tac[cj 1 raw_compiler_extends,cj 3 raw_compiler_extends,SND,cs_extends_trans]) >>
  `!n i. i + n <= LENGTH xs ==> cs_extends (EL i cs) (EL (i+n) cs)` by
    (Induct >- simp[cs_extends_refl] >> rpt strip_tac >>
     `i+n <= LENGTH xs /\ i+n < LENGTH xs` by decide_tac >>
     simp[ADD_CLAUSES] >> irule cs_extends_trans >> qexists_tac `EL (i+n) cs` >> simp[]) >>
  `!i. i <= LENGTH xs ==> cs_extends a (EL i cs) /\ cs_extends (EL i cs) b` by
    (rpt strip_tac >> gvs[]
     >- (first_x_assum (qspecl_then [`i`,`0`] mp_tac) >> simp[]) >>
     first_x_assum (qspecl_then [`LENGTH xs-i`,`i`] mp_tac) >>
     `i+(LENGTH xs-i)=LENGTH xs` by decide_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `cs_extends a (EL i cs) /\ cs_extends (EL (SUC i) cs) b` by simp[] >>
  `fn_has_code (EL i cs) (EL (SUC i) cs) fn` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`b`,`a`] >> simp[]) >>
  `cs_extends (EL i cs) (EL i mid) /\ cs_extends (EL i mid) (EL (SUC i) cs)` by simp[] >>
  drule_all fn_has_code_split >> simp[]
QED

(* Statement of the pure prep action in the raw compiler, for the shadow run. *)
Theorem raw_shadow_prep_pair[local]:
  gas_shadow_state d hd /\
  (if xs = [] then bufop = data /\ sizeop = lenop /\ p = d else
   compile_create_ctor_args compile_expr ce xs d = (vals,k) /\
   compile_alloc_buffer cap k = (buf,j) /\
   compile_copy_memory_dynamic buf.buf_operand data lenop j = ((),m) /\
   emit_op ADD [buf.buf_operand;lenop] m = (dst,n) /\
   compile_abi_encode_values_to_buf ce dst (ZIP (vals,MAP (lowered_value_type ce) xs)) n = (alen,o') /\
   emit_op ADD [lenop;alen] o' = (sizeop,p) /\ bufop = buf.buf_operand) ==>
  ?hp hk.
    gas_shadow_state p hp /\ cs_extends d p /\ cs_extends hd hp /\
    (if xs = [] then hp = hd else
      compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hd = (vals,hk) /\
      gas_shadow_state k hk /\ cs_extends hd hk /\ cs_extends hk hp /\ cs_extends k p) /\
    (if xs = [] then comp_return (data,lenop) else
       comp_bind (compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs)) (\vals.
       comp_bind (compile_alloc_buffer cap) (\buf.
       comp_ignore_bind (compile_copy_memory_dynamic buf.buf_operand data lenop)
       (comp_bind (emit_op ADD [buf.buf_operand;lenop]) (\dst.
       comp_bind (compile_abi_encode_values_to_buf ce dst
                    (ZIP (vals,MAP (lowered_value_type ce) xs))) (\alen.
       comp_bind (emit_op ADD [lenop;alen]) (\sizeop.
       comp_return (buf.buf_operand,sizeop)))))))) hd = ((bufop,sizeop),hp)
Proof
  Cases_on `xs = []` >- simp[comp_return_def,cs_extends_refl] >>
  asm_simp_tac bool_ss [COND_CLAUSES] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  raw_pair [`d`,`hd`] `compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hd`
    (Q.SPECL [`ce`, `xs`] (cj 3 raw_shadow_scalar_actions)) >>
  rename1 `compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hd = (vals,hk)` >>
  raw_pair [`k`,`hk`] `compile_alloc_buffer cap hk`
    (Q.INST [`nbytes` |-> `cap`] gas_shadow_compiles_alloc_buffer) >>
  rename1 `compile_alloc_buffer cap hk = (buf,hj)` >>
  raw_pair [`j`,`hj`] `compile_copy_memory_dynamic buf.buf_operand data lenop hj`
    (Q.INST [`dst` |-> `buf.buf_operand`, `src` |-> `data`, `len` |-> `lenop`]
      gas_shadow_compiles_copy_memory_dynamic) >>
  rename1 `compile_copy_memory_dynamic buf.buf_operand data lenop hj = (unitval,hm)` >>
  raw_pair [`m`,`hm`] `emit_op ADD [buf.buf_operand;lenop] hm`
    (Q.INST [`opc` |-> `ADD`,`ops` |-> `[buf.buf_operand;lenop]`] gas_shadow_compiles_emit_op_same) >>
  rename1 `emit_op ADD [buf.buf_operand;lenop] hm = (dst,hn)` >>
  raw_pair [`n`,`hn`]
    `compile_abi_encode_values_to_buf ce dst (ZIP (vals,MAP (lowered_value_type ce) xs)) hn`
    (Q.INST [`cenv` |-> `ce`,`dst` |-> `dst`,
             `rows` |-> `ZIP (vals,MAP (lowered_value_type ce) xs)`]
      gas_shadow_compiles_abi_encode_values_to_buf) >>
  rename1 `compile_abi_encode_values_to_buf ce dst _ hn = (alen,ho')` >>
  raw_pair [`o'`,`ho'`] `emit_op ADD [lenop;alen] ho'`
    (Q.INST [`opc` |-> `ADD`,`ops` |-> `[lenop;alen]`] gas_shadow_compiles_emit_op_same) >>
  rename1 `emit_op ADD [lenop;alen] ho' = (sizeop,hp)` >>
  qexists_tac `hp` >> simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  `cs_extends d k /\ cs_extends hd hk /\ cs_extends k j /\ cs_extends hk hj /\
   cs_extends j m /\ cs_extends hj hm /\ cs_extends m n /\ cs_extends hm hn /\
   cs_extends n o' /\ cs_extends hn ho' /\ cs_extends o' p /\ cs_extends ho' hp` by
    (rpt conj_tac >> FIRST (map (fn th => mp_tac th >> simp[] >> metis_tac[SND])
       (CONJUNCTS raw_compiler_extends))) >>
  metis_tac[cs_extends_trans]
QED

Theorem raw_shadow_ctor_code:
  compile_create_ctor_args compile_expr ce (MAP gas_shadow_expr xs) hd = (vals,hk) /\
  create_itinerary_ctor_rows ce xs vals d k cs mid vvs /\ gas_shadow_state d hd /\
  fn_has_code d k fn /\ fn_has_code hd hk sfn /\
  gas_shadow_context ctx sctx /\ ctx_inst_ids_distinct ctx /\ gas_shadow_function fn sfn /\
  MEM fn ctx.ctx_functions /\ MEM sfn sctx.ctx_functions /\ fn_inst_ids_distinct fn ==>
  ?hcs hmid. LENGTH hcs = SUC (LENGTH xs) /\ HD hcs = hd /\ LAST hcs = hk /\ LENGTH hmid = LENGTH xs /\
    !i. i < LENGTH xs ==>
      compile_expr ce (expr_type (EL i xs)) (gas_shadow_expr (EL i xs)) (EL i hcs) =
        (EL i vvs,EL i hmid) /\
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) xs))
        (ext_call_arg_value (lowered_value_type ce (EL i xs)) (EL i vvs)) (EL i hmid) =
        (EL i vals, EL (SUC i) hcs) /\
      expr_sim_full_code (ctx,sctx,fn,sfn) (EL i cs,EL i mid,EL i hcs,EL i hmid) /\
      expr_sim_full_code (ctx,sctx,fn,sfn) (EL i mid,EL (SUC i) cs,EL i hmid,EL (SUC i) hcs) /\
      expr_sim_full_code (ctx,sctx,fn,sfn) (EL i cs,EL (SUC i) cs,EL i hcs,EL (SUC i) hcs)
Proof
  strip_tac >>
  `?hcs hmid hv. create_itinerary_ctor_rows ce (MAP gas_shadow_expr xs) vals hd hk hcs hmid hv` by
    (drule_all create_ctor_cut_spine >> simp[GSYM create_itinerary_ctor_rows_def]) >>
  drule_all raw_shadow_rows >> strip_tac >>
  let val restrict_rows = drule_then assume_tac o
        MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] raw_row_embedding)
  in
    qpat_assum `create_itinerary_ctor_rows ce xs vals d k _ _ _` restrict_rows >>
    qpat_assum `create_itinerary_ctor_rows ce (MAP _ xs) vals hd hk _ _ _` restrict_rows
  end >>
  qpat_x_assum `create_itinerary_ctor_rows ce (MAP _ _) _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_itinerary_ctor_rows_def]) >>
  qexistsl_tac [`hcs`,`hmid`] >> simp[] >> gen_tac >> strip_tac >>
  `SUC i <= LENGTH xs` by decide_tac >>
  qpat_assum `!i. i < LENGTH (MAP _ _) ==> compile_expr _ _ _ _ = _ /\ _`
    (drule_then strip_assume_tac o SIMP_RULE (srw_ss()) [EL_MAP,GSYM MAP_DROP,gas_shadow_expr_can_mutate]) >>
  qpat_assum `!i. i < LENGTH xs ==> EL i hv = EL i vvs /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `EL i hv = EL i vvs` SUBST_ALL_TAC >>
  simp[expr_sim_full_code_def,LESS_IMP_LESS_OR_EQ]
QED

Theorem raw_shadow_outer[local]:
  (hs ==> rest <> []) /\ xs = (if hs then FRONT rest else rest) /\
  salte = (if hs then SOME (LAST rest) else NONE) /\
  compile_expr ce ty (gas_shadow_expr (Call ann (CreateTarget RawCreate hs rof ks)
    (e::v::rest) dflt)) hsa = (parent_vv,hsb) ==>
  ?out. compile_raw_create compile_expr ce (gas_shadow_expr e) (gas_shadow_expr v)
    (MAP gas_shadow_expr xs) (OPTION_MAP gas_shadow_expr salte) rof hsa = (out,hsb)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  `~(LENGTH rest < (if hs then 1 else 0))` by (Cases_on `hs` >> Cases_on `rest` >> fs[]) >>
  simp[gas_shadow_expr_def,compile_expr_call,compile_call_def,compile_create_call_def,
       GSYM MAP_FRONT] >>
  Cases_on `hs` >> fs[] >>
  qmatch_goalsub_abbrev_tac `as_stack_val ann r` >>
  Cases_on `r` >> simp[as_stack_val_def]
QED

(* Both functions are the compiled whole call; all normal boundary variables
   here refer to the fixed cuts already chosen by the raw itinerary. *)
Theorem create_raw_paired_operand_code:
  (hs ==> rest <> []) /\ xs = (if hs then FRONT rest else rest) /\
  salte = (if hs then SOME (LAST rest) else NONE) /\
  cap = bytelike_type_bound (lowered_value_type ce e) +
    abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) xs)) /\
  compile_expr ce ty (gas_shadow_expr (Call ann (CreateTarget RawCreate hs rof ks)
    (e::v::rest) dflt)) hsa = (parent_vv,hsb) /\
  expr_sim_full_code (ctx,sctx,fn,sfn) (sa,sb,hsa,hsb) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (lenop,c) /\ emit_op ADD [snap;Lit 32w] c = (data,d) /\
  (if xs = [] then bufop = data /\ sizeop = lenop /\ p = d else
   compile_create_ctor_args compile_expr ce xs d = (vals,k) /\
   create_itinerary_ctor_rows ce xs vals d k cs mid vvs /\
   compile_alloc_buffer cap k = (buf,j) /\
   compile_copy_memory_dynamic buf.buf_operand data lenop j = ((),m) /\
   emit_op ADD [buf.buf_operand;lenop] m = (dst,n) /\
   compile_abi_encode_values_to_buf ce dst (ZIP (vals,MAP (lowered_value_type ce) xs)) n = (alen,o') /\
   emit_op ADD [lenop;alen] o' = (sizeop,p) /\ bufop = buf.buf_operand) /\
  lower_value compile_expr ce (expr_type v) v p = (value,q) /\
  create_itinerary_salt ce salte q salt sc /\
  create_size_dispatch_tail rof sc sd created bufop sizeop value salt result sb ==>
  ?ha hp hq hsc.
    compile_expr ce (expr_type e) (gas_shadow_expr e) hsa = (vv,ha) /\
    expr_sim_full_code (ctx,sctx,fn,sfn) (sa,a,hsa,ha) /\
    fn_has_code a d fn /\ fn_has_code a b fn /\ fn_has_code b c fn /\ fn_has_code c d fn /\
    lower_value compile_expr ce (expr_type v) (gas_shadow_expr v) hp = (value,hq) /\
    expr_sim_full_code (ctx,sctx,fn,sfn) (p,q,hp,hq) /\
    (case salte of
     NONE => q = sc /\ hq = hsc /\ salt = NONE
     | SOME se => ?sop. salt = SOME sop /\
         lower_value compile_expr ce (expr_type se) se q = (sop,sc) /\
         lower_value compile_expr ce (expr_type se) (gas_shadow_expr se) hq = (sop,hsc) /\
         expr_sim_full_code (ctx,sctx,fn,sfn) (q,sc,hq,hsc)) /\
    (xs <> [] ==>
      fn_has_code d k fn /\ fn_has_code k j fn /\ fn_has_code j m fn /\
      fn_has_code m n fn /\ fn_has_code n o' fn /\ fn_has_code o' p fn /\
      ?hd hk hcs hmid. LENGTH hcs = SUC (LENGTH xs) /\ HD hcs = hd /\ LAST hcs = hk /\
        LENGTH hmid = LENGTH xs /\
        !i. i < LENGTH xs ==>
          compile_expr ce (expr_type (EL i xs)) (gas_shadow_expr (EL i xs)) (EL i hcs) =
            (EL i vvs,EL i hmid) /\
          compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) xs))
            (ext_call_arg_value (lowered_value_type ce (EL i xs)) (EL i vvs)) (EL i hmid) =
            (EL i vals, EL (SUC i) hcs) /\
          expr_sim_full_code (ctx,sctx,fn,sfn) (EL i cs,EL i mid,EL i hcs,EL i hmid) /\
          expr_sim_full_code (ctx,sctx,fn,sfn) (EL i mid,EL (SUC i) cs,EL i hmid,EL (SUC i) hcs) /\
          expr_sim_full_code (ctx,sctx,fn,sfn) (EL i cs,EL (SUC i) cs,EL i hcs,EL (SUC i) hcs))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_shadow_outer >> strip_tac >>
  qpat_x_assum `expr_sim_full_code _ _` (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
  raw_pair [`sa`,`hsa`] `compile_expr ce (expr_type e) (gas_shadow_expr e) hsa`
    (Q.SPECL [`ce`,`expr_type e`,`e`,`T`] (cj 1 gas_shadow_compile_expr) |> SRULE []) >>
  rename1 `compile_expr ce (expr_type e) (gas_shadow_expr e) hsa = (vv,ha)` >>
  raw_pair [`a`,`ha`] `compile_create_snapshot ce vv (lowered_value_type ce e) ha`
    (Q.INST [`cenv` |-> `ce`,`vv` |-> `vv`,`bytecode_ty` |-> `lowered_value_type ce e`]
      gas_shadow_compiles_create_snapshot) >>
  rename1 `compile_create_snapshot ce vv (lowered_value_type ce e) ha = (snap,hb)` >>
  raw_pair [`b`,`hb`] `emit_op MLOAD [snap] hb`
    (Q.INST [`opc` |-> `MLOAD`,`ops` |-> `[snap]`] gas_shadow_compiles_emit_op_same) >>
  rename1 `emit_op MLOAD [snap] hb = (lenop,hc)` >>
  raw_pair [`c`,`hc`] `emit_op ADD [snap; Lit 32w] hc`
    (Q.INST [`opc` |-> `ADD`,`ops` |-> `[snap; Lit 32w]`] gas_shadow_compiles_emit_op_same) >>
  rename1 `emit_op ADD [snap; Lit 32w] hc = (data,hd)` >>
  suspend "prep"
QED

Resume create_raw_paired_operand_code[prep]:
  qpat_assum `gas_shadow_state d hd` (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] raw_shadow_prep_pair)) >>
  impl_tac >- (Cases_on `xs = []` >> fs[]) >>
  disch_then (qx_choosel_then [`hp`,`hk`] (map_every assume_tac o CONJUNCTS)) >>
  rename1 `compile_raw_create compile_expr ce _ _ _ _ _ hsa = (hout,hsb)` >>
  raw_pair [`p`,`hp`] `lower_value compile_expr ce (expr_type v) (gas_shadow_expr v) hp`
    (Q.SPECL [`ce`,`expr_type v`,`v`] (cj 1 raw_shadow_scalar_actions)) >>
  rename1 `lower_value compile_expr ce (expr_type v) (gas_shadow_expr v) hp = (value,hq)` >>
  `compile_create_salt compile_expr ce salte q = (salt,sc)` by
    (qpat_x_assum `create_itinerary_salt ce salte q salt sc` mp_tac >>
     Cases_on `salte` >> simp[create_itinerary_salt_def,compile_create_salt_def,
                             comp_bind_def,comp_return_def] >> strip_tac >> simp[]) >>
  raw_pair [`q`,`hq`] `compile_create_salt compile_expr ce (OPTION_MAP gas_shadow_expr salte) hq`
    (Q.SPECL [`ce`,`salte`] (cj 2 raw_shadow_scalar_actions)) >>
  rename1 `compile_create_salt compile_expr ce (OPTION_MAP gas_shadow_expr salte) hq = (salt,hsc)` >>
  suspend "finish"
QED

Resume create_raw_paired_operand_code[finish]:
  `MAP (lowered_value_type ce) (MAP gas_shadow_expr xs) = MAP (lowered_value_type ce) xs` by
    simp[MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
  `compile_create_dispatch bufop sizeop value salt rof hsc = (hout,hsb)` by
    (qpat_x_assum `xs = (if hs then _ else _)` kall_tac >>
     qpat_x_assum `salte = (if hs then _ else _)` kall_tac >>
     qpat_x_assum `compile_raw_create _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_raw_create_def,comp_bind_def,comp_return_def,comp_ignore_bind_def] >>
     Cases_on `xs = []` >> gvs[comp_bind_def,comp_return_def,comp_ignore_bind_def]) >>
  `compile_create_dispatch bufop sizeop value salt rof sc = (result,sb)` by
    (qpat_x_assum `create_size_dispatch_tail _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `salt` >> simp[create_size_dispatch_tail_def,compile_create_dispatch_def,comp_bind_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sa a /\ cs_extends a b /\ cs_extends b c /\ cs_extends c d /\
   cs_extends p q /\ cs_extends q sc /\ cs_extends sc sb /\
   cs_extends hsa ha /\ cs_extends ha hb /\ cs_extends hb hc /\ cs_extends hc hd /\
   cs_extends hp hq /\ cs_extends hq hsc /\ cs_extends hsc hsb` by
    (rpt conj_tac >> raw_extends [1,2,4,5,10,11]) >>
  `cs_extends a d /\ cs_extends ha hd` by metis_tac[cs_extends_trans] >>
  raw_code_spine "fn" ["sa","a","d","p","q","sc","sb"] >>
  raw_code_spine "fn" ["a","b","c","d"] >>
  raw_code_spine "sfn" ["hsa","ha","hd","hp","hq","hsc","hsb"] >>
  qexistsl_tac [`ha`,`hp`,`hq`,`hsc`] >> simp[expr_sim_full_code_def] >>
  conj_tac >- suspend "salt" >>
  suspend "rows"
QED

Resume create_raw_paired_operand_code[salt]:
  Cases_on `salte` >> fs[compile_create_salt_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> fs[]) >> gvs[]
QED

Resume create_raw_paired_operand_code[rows]:
  strip_tac >>
  `xs = [] <=> F` by simp[] >>
  ntac 2 (qpat_x_assum `if xs = [] then _ else _` mp_tac) >>
  asm_rewrite_tac[] >> rpt (disch_then (map_every assume_tac o CONJUNCTS)) >>
  `cs_extends d k /\ cs_extends k j /\ cs_extends j m /\
   cs_extends m n /\ cs_extends n o' /\ cs_extends o' p` by
    (rpt conj_tac >> raw_extends [5,6,7,8,9]) >>
  raw_code_spine "fn" ["d","k","j","m","n","o'","p"] >>
  raw_code_spine "sfn" ["hd","hk","hp"] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  drule_all raw_shadow_ctor_code >> strip_tac >>
  qexistsl_tac [`hcs`,`hmid`] >> simp[] >> rpt strip_tac >>
  qpat_assum `!i. i < LENGTH _ ==> compile_expr _ _ _ _ = _ /\ _` (drule_then strip_assume_tac) >>
  fs[expr_sim_full_code_def]
QED
Finalise create_raw_paired_operand_code
