Theory sourceExprWitnessDefs
Ancestors
  sourceExprElaborate sourceExprDefs sourceSyntax sourceResolve sourceConstValue
  sourceConstBuiltin sourceConstBuiltinTest vyperAST vyperTypeSystem finite_map
Libs
  cv_transLib

(* Test-only inputs, split from sourceExprTest to keep the test roots small.
   TOP-LEVEL: source_expr_witness_elaborate, source_expr_witnesses (37 rows).
   Helpers: resolved test bindings and kernel-computed hash equations. *)

(* Each witness supplies independently resolved runtime expressions/constants.
   Builtin/type spellings are introduced into this TEST scope only; production
   elaboration dispatches on SR_Builtin or an SE_Intrinsic declaration binding. *)
Definition source_expr_witness_builtins_def:
  source_expr_witness_builtins =
    [("len",SR_Builtin SCB_Len); ("keccak256",SR_Builtin SCB_Keccak256);
     ("method_id",SR_Builtin SCB_MethodId); ("min",SR_Builtin SCB_Min);
     ("max",SR_Builtin SCB_Max); ("abs",SR_Builtin SCB_Abs);
     ("pow_mod256",SR_Builtin SCB_PowMod256);
     ("uint256_addmod",SR_Builtin SCB_Uint256AddMod);
     ("uint256_mulmod",SR_Builtin SCB_Uint256MulMod);
     ("bytes4",SR_FixedBytes 4); ("Bytes",SR_Bytes);
     ("abi_encode",SR_Function); ("abi_decode",SR_Function);
     ("raw_call",SR_Function); ("raw_revert",SR_Function);
     ("uint256",SR_Type); ("bool",SR_Type)]
End

Definition source_expr_witness_bindings_def:
  source_expr_witness_bindings =
    [(["builtin";"abi_encode"],SE_Intrinsic SE_AbiEncode);
     (["builtin";"abi_decode"],SE_Intrinsic SE_AbiDecode);
     (["builtin";"raw_call"],SE_Intrinsic SE_RawCall);
     (["builtin";"raw_revert"],SE_Intrinsic SE_RawRevert);
     (["builtin";"uint256"],SE_Type (BaseT (UintT 256)));
     (["builtin";"bool"],SE_Type (BaseT BoolT))]
End

Definition source_expr_witness_env_def:
  source_expr_witness_env env runtime = env with <|
    type_defs := FEMPTY;
    var_types := FEMPTY |++ FLAT (MAP (\(path,e).
      case e of Name ty id => [(id,ty)] | _ => []) runtime);
    toplevel_vtypes := FEMPTY |++ FLAT (MAP (\(path,e).
      case e of TopLevelName ty id => [(id,Type ty)] | _ => []) runtime) |>
End

Definition source_expr_witness_elaborate_def:
  source_expr_witness_elaborate env runtime constants ty original =
    source_expr_elaborate 12 (source_expr_witness_env env runtime)
      [MAP (\(path,e). (HD path,path)) (FILTER (\(path,e). LENGTH path = 1) runtime) ++
       MAP (\(path,v). (HD path,path)) constants ++
       [("self",["self"]); ("msg",["msg"])] ++
       MAP (\(name,kind). (name,["builtin";name])) source_expr_witness_builtins]
      (MAP (\(path,e). (path,SR_Dynamic)) runtime ++
       MAP (\(path,v). (path,SR_Constant)) constants ++
       [(["self"],SR_Module); (["msg"],SR_Module)] ++
       MAP (\(name,kind). (["builtin";name],kind)) source_expr_witness_builtins)
      (MAP (\(path,v). (path,SC_Constant v)) constants)
      (MAP (\(path,e). (path,SE_Runtime e)) runtime ++ source_expr_witness_bindings)
      ty original
End

val source_expr_hash_transfer = save_thm ("source_expr_hash_transfer",
  cv_eval ``source_const_keccak [116;114;97;110;115;102;101;114;40;97;100;100;114;101;115;115;44;117;105;110;116;50;53;54;41]``);
val source_expr_hash_f = save_thm ("source_expr_hash_f",
  cv_eval ``source_const_keccak [102;40;117;105;110;116;50;53;54;41]``);
val source_expr_hash_E = save_thm ("source_expr_hash_E",
  cv_eval ``source_const_keccak [69;40;117;105;110;116;50;53;54;41]``);
val source_expr_hash_x = save_thm ("source_expr_hash_x",
  cv_eval ``source_const_keccak [120]``);

(* Original bodies/initializers for ALL 37 retained witnesses. Runtime pieces
   have exact expected ASTs, including ABI flags/prefixes and raw-call order.
   The one source rejection is method_id_var, never a successful valid fixture.
   Statements and module composition belong to the source-module owner. *)
Definition source_expr_witnesses_def:
  source_expr_witnesses =
    let u = BaseT (UintT 256); i = BaseT (IntT 256); b = BaseT BoolT;
        b4 = BaseT (BytesT (Fixed 4)); d4 = BaseT (BytesT (Dynamic 4));
        b32 = BaseT (BytesT (Fixed 32)); addr = BaseT AddressT;
        d36 = BaseT (BytesT (Dynamic 36)); d68 = BaseT (BytesT (Dynamic 68));
        ni = \n. SX_Literal (SCL_Int n); nb = \v. SX_Literal (SCL_Bool v);
        li = \ty n. Literal ty (IntL n); lb = \v. Literal b (BoolL v);
        call = \n args. SX_Call (SX_Name n) args [];
        mid = \s. SX_Call (SX_Name "method_id") [SX_Literal (SCL_String s)] [];
        fixed = \s. SX_Call (SX_Name "method_id") [s] [("output_type",SX_Name "bytes4")];
        enc = \a ks. SX_Call (SX_Name "abi_encode") [a] ks;
        dead = SX_Literal (SCL_Hex "0xdeadbeef");
        ks = [("ensure_tuple",nb F); ("method_id",dead)];
        transfer = BytesL [169w;5w;156w;187w]; foo = BytesL [194w;152w;85w;120w];
        enc_ast = \ty ensure prefix e. TypeBuiltin ty (AbiEncode ensure (SOME prefix))
          (TupleT [expr_type e]) [e];
        D = [222w;173w;190w;239w]; Fsel = [179w;222w;100w;139w];
        Esel = [0w;47w;240w;103w];
        x = Name u "x"; y = Name i "y"; a = Name u "a";
        X = [(["x"],x)]; Y = [(["y"],y)]; A = [(["a"],a)];
        iv = Name i "x"; bv = Name b "x"; ad = Name addr "a";
        st = BaseT (StringT 40); dt = BaseT (BytesT (Dynamic 64));
        tt = TupleT [BaseT (IntT 128);b]; v = Name tt "v";
        self_s = TopLevelName u (NONE,"s"); immX = TopLevelName u (NONE,"X");
        hhello = BytesL [28w;138w;255w;149w;6w;133w;194w;237w;75w;195w;23w;79w;
          52w;114w;40w;123w;86w;217w;81w;123w;156w;148w;129w;39w;49w;154w;9w;167w;163w;109w;234w;200w]
    in
    [("pow_folded_exp",X,[],u,SX_Binary SCB_Pow (SX_Name "x") (SX_Binary SCB_Add (ni 1) (ni 2)),
        SC_Value (Builtin u (Bop Exp) [x;li u 3]));
     ("pow_negfold_base",Y,[],i,SX_Binary SCB_Pow (SX_Binary SCB_Sub (ni 0) (ni 2)) (SX_Name "y"),
        SC_Value (Builtin i (Bop Exp) [li i (-2);y]));
     ("fold_add",X,[],u,SX_Binary SCB_Add (SX_Name "x") (SX_Binary SCB_Add (ni 1) (ni 2)),
        SC_Value (Builtin u (Bop Add) [x;li u 3]));
     ("fold_pow_lit",X,[],u,SX_Binary SCB_Mul (SX_Name "x") (SX_Binary SCB_Pow (ni 2) (ni 8)),
        SC_Value (Builtin u (Bop Mul) [x;li u 256]));
     ("fold_cmp",[],[],b,SX_Compare SCC_Lt (ni 1) (ni 2),SC_Value (lb T));
     ("fold_not",[(["x"],bv)],[],b,SX_Boolean SCB_And [SX_Name "x";SX_Unary SCU_Not (nb T)],
        SC_Value (IfExp b bv (lb F) (lb F)));
     ("fold_shift",X,[],u,SX_Binary SCB_BitAnd (SX_Name "x") (SX_Binary SCB_LShift (ni 1) (ni 4)),
        SC_Value (Builtin u (Bop And) [x;li u 16]));
     ("fold_minmax",X,[],u,SX_Binary SCB_Add (SX_Name "x") (call "min" [ni 3;ni 5]),
        SC_Value (Builtin u (Bop Add) [x;li u 3]));
     ("fold_powmod",[],[],u,call "pow_mod256" [ni 2;ni 10],SC_Value (li u 1024));
     ("fold_addmod",[],[],u,call "uint256_addmod" [ni 5;ni 6;ni 7],SC_Value (li u 4));
     ("fold_abs",[],[],i,call "abs" [SX_Unary SCU_Neg (ni 5)],SC_Value (li i 5));
     ("keccak_literal",[],[],b32,call "keccak256" [SX_Literal (SCL_String "hello")],
        SC_Value (Literal b32 hhello));
     ("len_string_lit",[],[],u,call "len" [SX_Literal (SCL_String "abcd")],SC_Value (li u 4));
     ("method_id_b4",[],[],b4,fixed (SX_Literal (SCL_String "transfer(address,uint256)")),
        SC_Value (Literal b4 transfer));
     ("method_id_bytes",[],[],d4,mid "transfer(address,uint256)",SC_Value (Literal d4 transfer));
     ("method_id_const",[],[(["SIG"],SCV_String "foo()")],b4,fixed (SX_Name "SIG"),
        SC_Value (Literal b4 foo));
     ("method_id_storage",[],[],b4,fixed (SX_Literal (SCL_String "foo()")),SC_Value (Literal b4 foo));
     ("method_id_var",[(["s"],Name (BaseT (StringT 30)) "s")],[],b4,fixed (SX_Name "s"),
        SC_Invalid SCErr_Domain);
     ("enc_mid_const",A,[(["M"],SCV_Hex "0xdeadbeef")],d36,
        enc (SX_Name "a") [("ensure_tuple",nb F);("method_id",SX_Name "M")],
        SC_Value (enc_ast d36 F D a));
     ("enc_mid_methodid_call",A,[],d36,
        enc (SX_Name "a") [("ensure_tuple",nb F);("method_id",mid "foo()")],
        SC_Value (enc_ast d36 F [194w;152w;85w;120w] a));
     ("enc_mid_bytes4lit",[(["v"],v)],[],d68,
        enc (SX_Name "v") [("ensure_tuple",nb F);("method_id",SX_Literal (SCL_Bytes [222;173;190;239]))],
        SC_Value (enc_ast d68 F D v));
     ("enc_ensF_string_mid",[(["a"],Name st "a")],[],BaseT (BytesT (Dynamic 132)),enc (SX_Name "a") ks,
        SC_Value (enc_ast (BaseT (BytesT (Dynamic 132))) F D (Name st "a")));
     ("enc_ensF_uint_mid",A,[],d36,enc (SX_Name "a") ks,SC_Value (enc_ast d36 F D a));
     ("enc_ensure_const",A,[(["E"],SCV_Bool F)],d36,
        enc (SX_Name "a") [("ensure_tuple",SX_Name "E");("method_id",dead)],SC_Value (enc_ast d36 F D a));
     ("dec_unwrap_const",[(["d"],Name dt "d")],[(["U"],SCV_Bool F)],TupleT [u;b],
        SX_Call (SX_Name "abi_decode") [SX_Name "d";SX_Tuple [SX_Name "uint256";SX_Name "bool"]]
          [("unwrap_tuple",SX_Name "U")],
        SC_Value (TypeBuiltin (TupleT [u;b]) (AbiDecode F) (TupleT [u;b]) [Name dt "d"]));
     ("ctl03_abi_method_id",X,[],d36,enc (SX_Name "x") [("method_id",mid "f(uint256)")],
        SC_Value (enc_ast d36 T Fsel x));
     ("enc_ensT_uint_mid",[(["a"],ad)],[],d36,enc (SX_Name "a") [("method_id",dead)],
        SC_Value (enc_ast d36 T D ad));
     ("neg_lit",[(["x"],iv)],[],i,SX_Binary SCB_Add (SX_Name "x") (SX_Unary SCU_Neg (ni 5)),
        SC_Value (Builtin i (Bop Add) [iv;li i (-5)]));
     ("pow_neglit_base",Y,[],i,SX_Binary SCB_Pow (SX_Unary SCU_Neg (ni 2)) (SX_Name "y"),
        SC_Value (Builtin i (Bop Exp) [li i (-2);y]));
     ("lt_mixed_lit",A,[],b,SX_Compare SCC_Lt (SX_Name "a") (ni 5),
        SC_Value (Builtin b (Bop Lt) [a;li u 5]));
     ("boolop_and3",[(["a"],Name b "a");(["b"],Name b "b");(["c"],Name b "c")],[],b,
        SX_Boolean SCB_Or [SX_Boolean SCB_And [SX_Name "a";SX_Name "b"];SX_Name "c"],
        SC_Value (IfExp b
          (IfExp b (Name b "a") (Name b "b") (lb F))
          (lb T) (Name b "c")));
     ("i12_immut_with_storage",[(["X"],immX);(["self";"s"],self_s)],[(["N"],SCV_Int 10)],u,
        SX_Binary SCB_Add (SX_Binary SCB_Add (SX_Name "X") (SX_Attribute (SX_Name "self") "s")) (SX_Name "N"),
        SC_Value (Builtin u (Bop Add) [Builtin u (Bop Add) [immX;self_s];li u 10]));
     ("p29_imm_multi",[(["C"],TopLevelName b32 (NONE,"C"))],[],b32,SX_Name "C",
        SC_Value (TopLevelName b32 (NONE,"C")));
     ("c16_const_string_in_expr",[],[(["S"],SCV_String "abc")],u,call "len" [SX_Name "S"],SC_Value (li u 3));
     ("c27_const_binop_fold",[],[(["A"],SCV_Int 3)],u,SX_Binary SCB_Mul (SX_Name "A") (ni 7),SC_Value (li u 21));
     ("rc09_abi_encode_data",X ++ [(["t"],Name addr "t")],[],NoneT,
        call "raw_call" [SX_Name "t";enc (SX_Name "x") [("method_id",mid "f(uint256)")]],
        SC_Value (Call NoneT (RawCallTarget <| rcf_max_outsize := 0;rcf_is_delegate := F;
          rcf_is_static := F;rcf_revert_on_failure := T |>)
          [Name addr "t";enc_ast d36 T Fsel x;li u 0] NONE));
     ("rr03_abi",X,[],NoneT,
        call "raw_revert" [enc (SX_Name "x") [("method_id",mid "E(uint256)")]],
        SC_Value (Call NoneT RawRevert [enc_ast d36 T Esel x] NONE))]
End

val source_expr_exists_equal = save_thm ("source_expr_exists_equal",
  CONV_RULE (DEPTH_CONV ETA_CONV)
    (prove (``?(x:'a). y = x``, qexists_tac `y` >> simp[])));
