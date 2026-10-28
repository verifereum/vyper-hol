(* Proof-producing original-syntax recursion. Runtime expressions are accepted
   ONLY by code(), after derive() has independently constructed the meaning. *)
structure sourceMeaningLocationWitnessLib = struct
open HolKernel Parse boolLib bossLib
open sourceMeaningLocationDefsTheory sourceMeaningLocationSourceTheory
open sourceMeaningLocationCodeTheory sourceMeaningLocationBodyTheory
open sourceMeaningDefsTheory sourceMeaningConstTheory sourceMeaningCodeTheory
open sourceExprDefsTheory sourceSyntaxTheory sourceResolveTheory
open sourceModuleDefsTheory sourceModuleDeclTheory sourceModuleStmtTheory
open sourceConstValueTheory vyperASTTheory alistTheory listTheory

fun fields expected tm = let val (h,args) = strip_comb tm in
  if is_const h andalso fst (dest_const h) = expected then SOME args else NONE end;
fun one expected tm = case fields expected tm of SOME [x] => SOME x | _ => NONE;
fun computed tm = rhs (concl (EVAL tm));
fun some tm = valOf (one "SOME" (computed tm));
fun ok tm = valOf (one "SM_Ok" (computed tm));
fun items tm = #1 (listSyntax.dest_list tm);
fun meanings xs = listSyntax.mk_list(xs,``:source_location_meaning``);
fun fail e = raise Fail ("independent source meaning: " ^ term_to_string e);
fun stage scopes table constants original = let
  val resolution = EVAL ``source_resolve_candidate ^scopes ^table ^original``
  val resolved = valOf (one "SOME" (rhs (concl resolution)))
  val value = EVAL ``source_meaning_const ^constants ^resolved``
  val result = rhs (concl value)
  in (result,prove (``source_meaning_stage ^scopes ^table ^constants ^original ^result``,
    simp[source_meaning_stage_def,resolution,value])) end;

fun derive refs type_ids scopes table constants ty original = let
  val (result,stage_th) = stage scopes table constants original
  fun relation m = ``source_location_source ^refs ^type_ids ^scopes ^table ^constants ^ty ^original ^m``
  fun child t e = derive refs type_ids scopes table constants t e
  fun mk rule term inst facts = let val term = computed term in (term,prove(relation term,
    irule (SIMP_RULE (srw_ss()) [source_location_type_def,source_meaning_type_def,source_location_boolean_def,
       source_expr_binary_def,source_expr_unary_def]
      (Q.INST inst (SPEC_ALL rule))) >>
    simp ([source_location_type_def,source_meaning_type_def,source_expr_binary_def,source_expr_unary_def,
      source_expr_compare_def] @ facts) >> EVAL_TAC)) end
  fun infer e = let val (res,_) = stage scopes table constants e in
    case one "SC_Value" res of SOME v => some ``source_expr_value_type ^v``
    | NONE => let val (h,args) = strip_comb e in
      case (fst (dest_const h),args) of
        ("SX_Name",_) => reference_type e
      | ("SX_Attribute",_) => reference_type e
      | ("SX_Unary",[oper,c]) => infer c
      | ("SX_Binary",[oper,l,r]) =>
          (case one "SC_Value" (#1 (stage scopes table constants l)) of
             SOME _ => infer r | _ => infer l)
      | ("SX_Compare",_) => ``BaseT BoolT``
      | ("SX_Boolean",_) => ``BaseT BoolT``
      | ("SX_IfExp",[c,l,r]) => infer l
      | ("SX_Tuple",[cs]) => let val ts = listSyntax.mk_list(map infer (items cs),``:type``)
          in ``TupleT ^ts`` end
      | ("SX_List",[cs]) => let val ts = items cs val et = infer (hd ts)
          val n = numSyntax.term_of_int (List.length ts) in ``ArrayT ^et (Fixed ^n)`` end
      | ("SX_Subscript",[a,i]) => (case fields "ArrayT" (infer a) of
          SOME [et,bd] => et | _ => let val ts = valOf (one "TupleT" (infer a))
            val n = valOf (one "SCV_Int" (valOf (one "SC_Value" (#1 (stage scopes table constants i)))))
            in computed ``EL (Num ^n) ^ts`` end)
      | ("SX_Call",[callee,as_,kws]) => let
          val names = some ``source_expr_path ^callee``
          val (path,kind) = pairSyntax.dest_pair (some ``source_resolve_name ^scopes ^table ^names``)
          val name = stringSyntax.fromHOLstring (computed ``LAST ^path``)
          in if name = "abi_encode" then let
              val ts = listSyntax.mk_list(map infer (items as_),``:type``)
              val ensure = flag kws "ensure_tuple" true
              val mid = selector kws
              in computed ``BaseT (BytesT (Dynamic (vyper_abi_size_bound FEMPTY
                (case ^ts of [t] => if ^ensure then TupleT ^ts else t | _ => TupleT ^ts) +
                  abi_encode_method_id_size ^mid)))`` end
            else if name = "abi_decode" then type_operand (List.nth(items as_,1))
            else if name = "raw_revert" orelse name = "raw_call" then ``NoneT``
            else if name = "len" then ``BaseT (UintT 256)``
            else if name = "keccak256" then ``BaseT (BytesT (Fixed 32))``
            else infer (hd (items as_)) end
      | _ => fail e end end
  and reference_type e = let
    val names = some ``source_expr_path ^e``
    val (path,kind) = pairSyntax.dest_pair (some ``source_resolve_name ^scopes ^table ^names``)
    in if aconv path ``["$builtin";"msg";"sender"]`` then ``BaseT AddressT``
      else #1 (pairSyntax.dest_pair (some ``ALOOKUP ^refs ^path``)) end
  and type_operand e = case fields "SX_Tuple" e of SOME [cs] =>
      let val ts = listSyntax.mk_list(map type_operand (items cs),``:type``) in ``TupleT ^ts`` end
    | _ => let val names = some ``source_expr_path ^e``
        val (path,kind) = pairSyntax.dest_pair (some ``source_resolve_name ^scopes ^table ^names``)
        in some ``ALOOKUP ^type_ids ^path`` end
  and flag kws key default = let val k = stringSyntax.fromMLstring key in
    case one "SOME" (computed ``ALOOKUP ^kws ^k``) of NONE => if default then T else F
    | SOME e => valOf (one "SCV_Bool" (valOf (one "SC_Value" (#1 (stage scopes table constants e))))) end
  and selector kws = case one "SOME" (computed ``ALOOKUP ^kws "method_id"``) of
      NONE => ``NONE:word8 list option``
    | SOME e => let val v = valOf (one "SC_Value" (#1 (stage scopes table constants e))) in
      case one "SCV_Bytes" v of SOME bs => computed ``SOME (MAP (n2w:num->word8) ^bs)``
      | NONE => let val s = valOf (one "SCV_Hex" v) in
          computed ``SOME (MAP (n2w:num->word8) (source_const_hex_decode (DROP 2 ^s)))`` end end
  fun metadata defs tm = prove(tm,simp defs >> EVAL_TAC)
  fun flag_th kws key default b = let val k = stringSyntax.fromMLstring key in
    case one "SOME" (computed ``ALOOKUP ^kws ^k``) of
      NONE => metadata [source_location_flag_def] ``source_location_flag ^scopes ^table ^constants ^kws ^k ^default ^b``
    | SOME e => let val th = #2(stage scopes table constants e) in
      metadata [source_location_flag_def,EVAL ``ALOOKUP ^kws ^k``,th]
        ``source_location_flag ^scopes ^table ^constants ^kws ^k ^default ^b`` end end
  fun selector_th kws mid = let
    val facts = case one "SOME" (computed ``ALOOKUP ^kws "method_id"``) of
      NONE => [] | SOME e => [MATCH_MP source_location_stage_unique (#2(stage scopes table constants e))]
    in metadata (source_location_selector_def :: EVAL ``ALOOKUP ^kws "method_id"`` :: facts)
      ``source_location_selector ^scopes ^table ^constants ^kws ^mid`` end
  fun intrinsic callee name = let val n = stringSyntax.fromMLstring name
    val names = some ``source_expr_path ^callee`` in
    metadata [source_location_intrinsic_def,EVAL ``source_expr_path ^callee``,
      EVAL ``source_resolve_name ^scopes ^table ^names``]
      ``source_location_intrinsic ^scopes ^table ^callee ^n`` end
  fun type_operand_th target ty = let
    val goal = ``source_location_type_operand ^scopes ^table ^constants ^type_ids ^target ^ty``
    in case fields "SX_Tuple" target of SOME [cs] => let
        val ts = items(valOf(one "TupleT" ty))
        val ths = ListPair.mapEq (fn (e,t) => type_operand_th e t) (items cs,ts)
        in prove(goal,simp(source_location_type_operand_def :: ths)) end
      | _ => let
          val ns = some ``source_expr_path ^target``
          val (path,kind) = pairSyntax.dest_pair(some ``source_resolve_name ^scopes ^table ^ns``)
        in prove(goal,simp[source_location_type_operand_def,
          EVAL ``source_resolve_name ^scopes ^table ^ns``,EVAL ``ALOOKUP ^type_ids ^path``]) end
    end
  fun calls callee as_ kws = let
    val args = items as_
    val names = some ``source_expr_path ^callee``
    val (path,kind) = pairSyntax.dest_pair (some ``source_resolve_name ^scopes ^table ^names``)
    val name = stringSyntax.fromHOLstring (computed ``LAST ^path``)
    fun children () = map (fn e => child (infer e) e) args
    in if name = "abi_encode" then let
        val results = children () val ms = meanings(map #1 results)
        val ensure = flag kws "ensure_tuple" true val mid = selector kws
        val term = ``SML_TypeApply ^ty (AbiEncode ^ensure ^mid) (TupleT (MAP source_location_type ^ms)) ^ms``
        in mk sourceMeaningLocationSourceTheory.encode term [`ms` |-> `^ms`]
          (intrinsic callee name :: flag_th kws "ensure_tuple" T ensure :: selector_th kws mid :: map #2 results) end
      else if name = "abi_decode" then let
        val data = hd args val target = List.nth(args,1) val dty = infer data
        val (m,th) = child dty data val unwrap = flag kws "unwrap_tuple" true
        val opty = type_operand_th target ty
        in mk sourceMeaningLocationSourceTheory.decode
          ``SML_TypeApply ^ty (AbiDecode ^unwrap) ^ty [^m]`` [`et` |-> `^dty`]
          [intrinsic callee name,flag_th kws "unwrap_tuple" T unwrap,opty,th] end
      else if name = "raw_revert" then let
        val d = hd args val dty = infer d val (m,th) = child dty d
        in mk sourceMeaningLocationSourceTheory.revert ``SML_Revert ^ty ^m``
          [`et` |-> `^dty`] [intrinsic callee name,th] end
      else if name = "raw_call" then let
        val target = hd args val data = List.nth(args,1) val dty = infer data
        val (tm,tt) = child ``BaseT AddressT`` target val (dm,dt) = child dty data
        val vm = ``SML_Core (SM_Literal (BaseT (UintT 256)) (IntL 0))``
        val flags = ``<|rcf_max_outsize := 0; rcf_is_delegate := F;
          rcf_is_static := F; rcf_revert_on_failure := T|>``
        in mk sourceMeaningLocationSourceTheory.raw_call ``SML_RawCall ^ty ^flags ^tm ^dm ^vm``
          [`et` |-> `^dty`] [intrinsic callee name,tt,dt,
            flag_th kws "is_delegate_call" F F,flag_th kws "is_static_call" F F,
            flag_th kws "revert_on_failure" T T] end
      else let
        val b = some ``source_expr_builtin_identity ^scopes ^table ^callee``
        val bt = some ``source_expr_builtin ^b``
        in if aconv bt ``Len`` then let
            val e = hd args val et = infer e val (m,th) = child et e
            in mk sourceMeaningLocationSourceTheory.length ``SML_Length ^ty ^m``
              [`et` |-> `^et`] [th,EVAL ``source_expr_builtin_identity ^scopes ^table ^callee``] end
          else let val results = children () val ms = meanings(map #1 results)
            in mk sourceMeaningLocationSourceTheory.builtin ``SML_Apply ^ty ^bt ^ms``
              [`ms` |-> `^ms`, `b` |-> `^b`]
              (stage_th :: EVAL ``source_expr_builtin_identity ^scopes ^table ^callee`` ::
                EVAL ``source_expr_builtin ^b`` :: map #2 results) end end
    end
  fun dynamic () = let val (h,args) = strip_comb original in
    case (fst(dest_const h),args) of
      ("SX_Unary",[oper,e]) => let val (m,th) = child ty e in
        mk sourceMeaningLocationSourceTheory.unary ``SML_Apply ^ty (source_expr_unary ^oper) [^m]`` [`uop` |-> `^oper`]
          [stage_th,th,EVAL ``source_expr_unary_domain ^oper ^ty``] end
    | ("SX_Binary",[oper,l,r]) => let val (lm,lt) = child ty l val (rm,rt) = child ty r in
        mk sourceMeaningLocationSourceTheory.binary ``SML_Apply ^ty (Bop (source_expr_binary ^oper)) [^lm;^rm]`` [`op` |-> `^oper`]
          [stage_th,lt,rt,EVAL ``source_expr_binary_domain ^oper ^ty``] end
    | ("SX_Compare",[oper,l,r]) => let
        val et = infer l val (lm,lt) = child et l val (rm,rt) = child et r
        val bop = some ``source_expr_compare ^oper``
        in mk sourceMeaningLocationSourceTheory.compare ``SML_Apply ^ty (Bop ^bop) [^lm;^rm]``
          [`et` |-> `^et`] [stage_th,lt,rt,EVAL ``source_expr_compare ^oper``] end
    | ("SX_IfExp",[c,l,r]) => let val (cm,ct) = child ``BaseT BoolT`` c
        val (lm,lt) = child ty l val (rm,rt) = child ty r
        in mk sourceMeaningLocationSourceTheory.conditional ``SML_If ^ty ^cm ^lm ^rm`` [] [ct,lt,rt] end
    | ("SX_Boolean",[oper,cs]) => let val results = map (child ``BaseT BoolT``) (items cs)
        val ms = meanings(map #1 results)
        in mk sourceMeaningLocationSourceTheory.boolean ``source_location_boolean ^oper ^ms``
          [`ms` |-> `^ms`,`boolop` |-> `^oper`] (stage_th :: map #2 results) end
    | ("SX_Tuple",[cs]) => let val ts = items (valOf(one "TupleT" ty))
        val results = ListPair.mapEq (fn (t,e) => child t e) (ts,items cs)
        val ms = meanings(map #1 results)
        in mk sourceMeaningLocationSourceTheory.tuple
          ``SML_Apply ^ty (MakeArray NONE (Fixed (LENGTH ^ms))) ^ms`` [`ms` |-> `^ms`] (map #2 results) end
    | ("SX_List",[cs]) => let val [et,bd] = valOf(fields "ArrayT" ty)
        val results = map (child et) (items cs) val ms = meanings(map #1 results)
        in mk sourceMeaningLocationSourceTheory.array ``SML_Apply ^ty (MakeArray (SOME ^et) ^bd) ^ms``
          [`ms` |-> `^ms`] (map #2 results) end
    | ("SX_Subscript",[a,i]) => let val aty = infer a val (am,at) = child aty a in
        case fields "ArrayT" aty of SOME [et,bd] => let val (im,it) = child ``BaseT (UintT 256)`` i in
          mk sourceMeaningLocationSourceTheory.array_subscript ``SML_Subscript ^ty ^am ^im``
            [`et` |-> `^et`,`bd` |-> `^bd`] [at,it] end
        | _ => let val ts = valOf(one "TupleT" aty)
            val (res,sth) = stage scopes table constants i
            val n = valOf(one "SCV_Int" (valOf(one "SC_Value" res)))
            val nn = computed ``Num ^n``
            val im = ``SML_Core (SM_Literal (BaseT (UintT 256)) (IntL ^n))``
          in mk sourceMeaningLocationSourceTheory.tuple_subscript ``SML_Subscript ^ty ^am ^im``
            [`ts` |-> `^ts`,`n` |-> `^nn`] [at,sth] end end
    | ("SX_Call",[c,as_,ks]) => calls c as_ ks
    | _ => let val ns = some ``source_expr_path ^original``
        val (path,kind) = pairSyntax.dest_pair(some ``source_resolve_name ^scopes ^table ^ns``)
        val pathth = EVAL ``source_expr_path ^original``
        val resth = EVAL ``source_resolve_name ^scopes ^table ^ns``
        in if aconv path ``["$builtin";"msg";"sender"]`` then
          mk sourceMeaningLocationSourceTheory.sender ``SML_Apply ^ty (Env Sender) []`` [] [pathth,resth]
        else let val (t,r) = pairSyntax.dest_pair(some ``ALOOKUP ^refs ^path``) in
          mk sourceMeaningLocationSourceTheory.reference ``SML_Reference ^ty ^r`` []
            [pathth,resth,EVAL ``ALOOKUP ^refs ^path``] end end
    end
  in case one "SC_Value" result of SOME sv => let
      val lit_eq = EVAL ``source_const_value_literal ^sv``
      val core = case one "SOME" (rhs(concl lit_eq)) of
        SOME lit => ``SM_Literal ^ty ^lit`` | NONE => ``SM_Constant ^ty ^sv``
      val core_th = prove (``source_meaning_source [] ^scopes ^table ^constants ^ty ^original ^core``,
        FIRST [irule (Q.INST [`sv` |-> `^sv`] (SPEC_ALL sourceMeaningDefsTheory.constant)),
          irule sourceMeaningDefsTheory.aggregate] >> simp[stage_th,lit_eq])
      in mk sourceMeaningLocationSourceTheory.staged ``SML_Core ^core`` [`sv` |-> `^sv`] [stage_th,core_th] end
    | NONE => dynamic () end;

(* Separate proof recursion checks the independent semantic term against code.
   It never invents a semantic term from runtime syntax. *)
fun code tenv m e = let
  fun relation m e = ``source_location_code ^tenv ^m ^e``
  fun codes ms es = prove(``source_location_codes ^tenv ^ms ^es``,
    MAP_EVERY (fn th => ASSUME_TAC th) (ListPair.mapEq (fn (m,e) => code tenv m e) (items ms,items es)) >>
    simp[source_location_code_rules])
  fun mk rule facts = prove(relation m e,irule rule >> simp facts >> EVAL_TAC)
  val m = computed m val e = computed e
  val (h,args) = strip_comb m val (_,es) = strip_comb e
  in case (fst(dest_const h),args) of
    ("SML_Core",[core]) => let
      val coreth = case fields "SM_Literal" core of SOME [ty,lit] =>
          let val (lh,la) = strip_comb lit
            val v = case fst(dest_const lh) of
                "IntL" => ``SCV_Int ^(hd la)`` | "BoolL" => ``SCV_Bool ^(hd la)``
              | "DecimalL" => ``SCV_Decimal ^(hd la)`` | "StringL" => ``SCV_String ^(hd la)``
              | "BytesL" => let val ns = computed ``MAP (w2n:word8->num) ^(hd la)`` in ``SCV_Bytes ^ns`` end
              | _ => fail lit
          in prove(``source_meaning_code ^tenv [] ^core ^e``,
            irule (Q.INST [`sv` |-> `^v`] (SPEC_ALL sourceMeaningCodeTheory.literal)) >> EVAL_TAC) end
        | _ => prove(``source_meaning_code ^tenv [] ^core ^e``,irule sourceMeaningCodeTheory.aggregate >> EVAL_TAC)
      in case fields "Literal" e of SOME _ => mk sourceMeaningLocationCodeTheory.core_literal [coreth]
        | _ => mk sourceMeaningLocationCodeTheory.core_builtin [coreth] end
  | ("SML_Reference",_) => (case fields "Name" e of SOME _ => mk sourceMeaningLocationCodeTheory.local_cell []
      | _ => mk sourceMeaningLocationCodeTheory.global [])
  | ("SML_Apply",[ty,b,ms]) => mk sourceMeaningLocationCodeTheory.apply [codes ms (List.nth(es,2))]
  | ("SML_Length",[ty,c]) => mk sourceMeaningLocationCodeTheory.length [code tenv c (hd(items(List.nth(es,2))))]
  | ("SML_If",[ty,c,l,r]) => mk sourceMeaningLocationCodeTheory.conditional
      [code tenv c (List.nth(es,1)),code tenv l (List.nth(es,2)),code tenv r (List.nth(es,3))]
  | ("SML_Subscript",[ty,a,i]) => mk sourceMeaningLocationCodeTheory.subscript
      [code tenv a (List.nth(es,1)),code tenv i (List.nth(es,2))]
  | ("SML_TypeApply",[ty,b,t,ms]) => mk sourceMeaningLocationCodeTheory.type_apply [codes ms (List.nth(es,3))]
  | ("SML_Revert",[ty,c]) => mk sourceMeaningLocationCodeTheory.revert [code tenv c (hd(items(List.nth(es,2))))]
  | ("SML_RawCall",[ty,f,t,d,v]) => let val [te,de,ve] = items(List.nth(es,2)) in
      mk sourceMeaningLocationCodeTheory.raw_call [code tenv t te,code tenv d de,code tenv v ve] end
  | _ => fail m end;

fun bodies refs type_ids ctx ret originals = let
  fun source refs ctx originals ms final_refs final_ctx =
    ``source_location_bodies_source ^refs ^type_ids ^ctx ^ret ^originals ^ms ^final_refs ^final_ctx``
  fun expr ctx refs ty original = derive refs type_ids
    (computed ``(^ctx).sm_scopes``) (computed ``(^ctx).sm_table``)
    (computed ``(^ctx).sm_constants``) ty original
  fun statement refs ctx s = let
    val (h,args) = strip_comb s
    fun mk rule m nr nc facts inst = (m,nr,nc,
      prove (``source_location_body_source ^refs ^type_ids ^ctx ^ret ^s ^m ^nr ^nc``,
        irule (SIMP_RULE (srw_ss()) facts
          (Q.INST ([`ctx` |-> `^ctx`,`refs` |-> `^refs`,`type_ids` |-> `^type_ids`,
            `ret` |-> `^ret`] @ inst) (SPEC_ALL rule))) >> simp facts >> EVAL_TAC))
    in case (fst(dest_const h),args) of
      ("SS_Pass",[]) => mk sourceMeaningLocationBodyTheory.pass_body ``SMLB_Pass`` refs ctx [] []
    | ("SS_Return",[option]) => (case one "SOME" option of NONE =>
        mk sourceMeaningLocationBodyTheory.return_none ``SMLB_Return NONE`` refs ctx [] []
      | SOME e => let val (m,th) = expr ctx refs ret e in
        mk sourceMeaningLocationBodyTheory.return_value ``SMLB_Return (SOME ^m)`` refs ctx [th] [] end)
    | ("SS_Expr",[e]) => let val (m,th) = expr ctx refs ``NoneT`` e in
        mk sourceMeaningLocationBodyTheory.expression_body ``SMLB_Expr ^m`` refs ctx [th] [`ty` |-> `NoneT`] end
    | ("SS_AnnAssign",[name,annotation,option]) => let
        val e = valOf(one "SOME" option) val ty = ok ``source_module_type ^ctx ^annotation``
        val (m,th) = expr ctx refs ty e
        val nr = computed ``(((^ctx).sm_owner ++ [^name],(^ty,SMR_Local ^name))::^refs)``
        val nc = computed ``source_module_local ^ctx ^name ^ty T``
        in mk sourceMeaningLocationBodyTheory.local_body ``SMLB_Local ^name ^ty ^m`` nr nc
          [th,EVAL ``source_module_type ^ctx ^annotation``,
            EVAL ``source_module_interface_fields ^ctx ^annotation``,
            EVAL ``source_module_local ^ctx ^name ^ty T``]
          [`ty` |-> `^ty`,`name` |-> `^name`,`annotation` |-> `^annotation`] end
    | ("SS_Assign",[target,e]) => let
        val scopes = computed ``(^ctx).sm_scopes`` val table = computed ``(^ctx).sm_table``
        val ns = some ``source_expr_path ^target``
        val (path,kind) = pairSyntax.dest_pair(some ``source_resolve_name ^scopes ^table ^ns``)
        val (ty,r) = pairSyntax.dest_pair(some ``ALOOKUP ^refs ^path``)
        val (m,th) = expr ctx refs ty e
        in mk sourceMeaningLocationBodyTheory.assign_body ``SMLB_Assign ^r ^m`` refs ctx
          [th,EVAL ``source_expr_path ^target``,EVAL ``source_resolve_name ^scopes ^table ^ns``,
            EVAL ``ALOOKUP ^refs ^path``,EVAL ``(^ctx).sm_scopes``,EVAL ``(^ctx).sm_table``]
          [`ty` |-> `^ty`] end
    | ("SS_If",[c,yes,no]) => let
        val (m,th) = expr ctx refs ``BaseT BoolT`` c
        val (ym,yr,yc,yt) = bodies refs type_ids ctx ret yes
        val (nm,nr,nc,nt) = bodies refs type_ids ctx ret no
        in mk sourceMeaningLocationBodyTheory.if_body ``SMLB_If ^m ^ym ^nm`` refs ctx [th,yt,nt]
          [`yr` |-> `^yr`,`yc` |-> `^yc`,`nr` |-> `^nr`,`nc` |-> `^nc`] end
    | _ => fail s end
  in case items originals of [] => let val ms = ``[]:source_location_body list`` in
      (ms,refs,ctx,prove(source refs ctx originals ms refs ctx,
        irule sourceMeaningLocationBodyTheory.empty_bodies)) end
  | s::ss => let
      val (m,nr,nc,st) = statement refs ctx s
      val rest = listSyntax.mk_list(ss,``:source_stmt``)
      val (ms,fr,fc,sts) = bodies nr type_ids nc ret rest
      val all = ``^m::^ms``
      val th = prove(source refs ctx originals all fr fc,
        irule (Q.INST [`next_ctx` |-> `^nc`,`next_refs` |-> `^nr`]
          (SPEC_ALL sourceMeaningLocationBodyTheory.cons_bodies)) >> simp[st,sts])
      in (all,fr,fc,th) end end;

fun body_code tenv ms ss = let
  fun statement m s = let
    fun mk rule facts = prove(``source_location_body_code ^tenv ^m ^s``,
      irule (SIMP_RULE (srw_ss()) [source_reference_code_def] rule) >>
      simp (source_reference_code_def :: facts) >> EVAL_TAC)
    val (h,args) = strip_comb m val (_,es) = strip_comb s
    in case (fst(dest_const h),args) of
      ("SMLB_Pass",[]) => mk sourceMeaningLocationBodyTheory.pass_code []
    | ("SMLB_Return",[option]) => (case one "SOME" option of NONE => mk sourceMeaningLocationBodyTheory.return_none_code []
      | SOME m => mk sourceMeaningLocationBodyTheory.return_value_code
          [code tenv m (valOf(one "SOME" (hd es)))])
    | ("SMLB_Expr",[m]) => mk sourceMeaningLocationBodyTheory.expression_code [code tenv m (hd es)]
    | ("SMLB_Local",[id,ty,m]) => mk sourceMeaningLocationBodyTheory.local_code [code tenv m (List.nth(es,2))]
    | ("SMLB_Assign",[r,m]) => mk (Q.INST [`r` |-> `^r`] (SPEC_ALL sourceMeaningLocationBodyTheory.assign_code))
        [code tenv m (List.nth(es,1))]
    | ("SMLB_If",[c,ym,nm]) => mk sourceMeaningLocationBodyTheory.if_code
        [code tenv c (hd es),body_code tenv ym (List.nth(es,1)),body_code tenv nm (List.nth(es,2))]
    | _ => fail m end
  val facts = ListPair.mapEq (fn (m,s) => statement m s) (items(computed ms),items ss)
  in prove(``source_location_bodies_code ^tenv ^ms ^ss``,
    MAP_EVERY ASSUME_TAC facts >> simp[source_location_body_code_rules]) end;
end
