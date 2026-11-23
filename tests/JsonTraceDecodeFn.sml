(* The authoritative exported-trace decoder, shared by HOL and standalone CV. *)
functor JsonTraceDecodeFn (
  structure B : jsonImportTerm
  structure AST : sig
    type term
    val wrapped_annotated_ast : term JSONDecode.decoder
    val storage_layout : term JSONDecode.decoder
  end
  sharing type AST.term = B.term
  val translate_annotated_ast : B.term -> B.term
) : sig
  val parse_abi_type : string -> B.term
  val fixture_decoder : B.term list JSONDecode.decoder
  val test_with_deps_decoder :
    (string list * B.term list) JSONDecode.decoder
  val fixture_name_of_dep : string -> string
  val resolve_fixtures :
    (string * JSON.value * 'a) list -> string list ->
    (string * JSON.value * 'a) list
  val decode_cases : JSON.value -> (string * B.term list) list
  val source_codes_json : JSON.value -> string list
  (* Complete-state checkpoint evidence, checked by StateCheckpoint traces. *)
  val state_checkpoint : B.term JSONDecode.decoder
  val checkpoint_address : B.term JSONDecode.decoder
  val checkpoint_bytes : B.term JSONDecode.decoder
  val checkpoint_topic : B.term JSONDecode.decoder
  val checkpoint_num : B.term JSONDecode.decoder
  val checkpoint_uint256 : IntInf.int JSONDecode.decoder
  val checkpoint_unique_array :
    (IntInf.int -> IntInf.int -> bool) ->
    (IntInf.int * 'a) JSONDecode.decoder -> 'a list JSONDecode.decoder
  val checkpoint_num_less : IntInf.int -> IntInf.int -> bool
  val checkpoint_address_less : string -> string -> bool
  val checkpoint_slot : (IntInf.int * B.term) JSONDecode.decoder
  val checkpoint_account : (string * B.term) JSONDecode.decoder
end = struct

open B JSONDecode
infixr 0 $
fun f $ x = f x
fun curry f x y = f (x,y)
fun equal x y = x = y
fun I x = x

type 'a decoder = 'a JSONDecode.decoder
fun runner_type name = named_type {Thy="vyperTestRunner", Tyop=name}
fun runner_const name = constant {Thy="vyperTestRunner", Name=name}
fun abi_const name = constant {Thy="contractABI", Name=name}
val abi_type_ty = named_type {Thy="contractABI", Tyop="abi_type"}
val bytes32_ty = word_ty 256
val bytes_ty = mk_type ("list", [word_ty 8])
val call_trace_ty = runner_type "call_trace"
val deployment_trace_ty = runner_type "deployment_trace"
val raw_deployment_trace_ty = runner_type "raw_deployment_trace"
val abi_function_ty = runner_type "abi_function"
val abi_entry_ty = runner_type "abi_entry"
val trace_ty = runner_type "trace"
val Nonpayable_tm = constant {Thy="vyperAST", Name="Nonpayable"}
val View_tm = constant {Thy="vyperAST", Name="View"}
val Payable_tm = constant {Thy="vyperAST", Name="Payable"}
val Pure_tm = constant {Thy="vyperAST", Name="Pure"}
val Array_tm = abi_const "Array"
val Tuple_tm = abi_const "Tuple"
val Uint_tm = abi_const "Uint"
val Int_tm = abi_const "Int"
val Bytes_tm = abi_const "Bytes"
val Bool_tm = abi_const "Bool"
val Address_tm = abi_const "Address"
val String_tm = abi_const "String"

fun translate_jsonast_to_vyper jsonast = let
  val result = translate_annotated_ast jsonast
in
  if is_some result then dest_some result
  else raise JSONError (Fail "imports not topologically sorted", JSON.OBJECT [])
end

val toplevels_via_jsonast : term decoder =
  JSONDecode.map translate_jsonast_to_vyper AST.wrapped_annotated_ast

fun from_term_option ty NONE = mk_none ty
  | from_term_option _ (SOME tm) = mk_some tm

(* Compatibility copy of the grammar in the pinned Verifereum dependency:
   .holbuild/src/verifereum/util/contractABISyntax.sml, from
   skip_to_matching_paren through parse_abi_type. Term construction is adapted
   to B and numeric values use IntInf to avoid host-dependent overflow. Keep
   syntax and inherited rejection/leniency behavior in sync when updating that
   pin; vyperTestLibTestScript.sml checks parity and arbitrary-precision bounds.
   The copy exists because Verifereum's parser builds HOL terms directly; it could
   be consolidated by moving that parser into a HOL-free function that takes the
   constructors as an argument, which both Verifereum and this functor would call. *)
  fun skip_to_matching_paren ss = let
    fun skip_to_close i = let
      val c = Substring.sub(ss, i)
      val i = i+1
    in
      if c = #"]" then i else skip_to_close i
    end
    fun loop n i = let
      val c = Substring.sub(ss, i)
      val i = i+1
    in
      if c = #"(" then loop (n+1) i else
      if c = #")" then
        if n = 1
        then if i < Substring.size ss andalso
                Substring.sub(ss, i) = #"["
             then skip_to_close (i+1)
             else i
        else loop (n-1) i
      else loop n i
    end
  in
    Substring.splitAt(ss, loop 0 0)
  end

  fun split_on_outer_commas ss = let
    val (x,ss) =
      (if Substring.sub(ss, 0) = #"("
       then skip_to_matching_paren
       else Substring.splitl (not o equal #",")) ss
  in
    if Substring.size ss = 0 then [x]
    else x :: split_on_outer_commas (Substring.triml 1 ss)
  end

  fun parse_optnum_ss ns =
    case IntInf.fromString $ Substring.string ns
      of SOME n => mk_some (natural n)
       | NONE => mk_none num_ty

  fun parse_abi_type_ss ss =
    if Substring.isSuffix "]" ss then let
      val (ps, ns) = Substring.splitr (not o equal #"[") ss
      val bt = parse_optnum_ss ns
      val ss = Substring.trimr 1 ps
      val t = parse_abi_type_ss ss
    in list_mk_comb(Array_tm, [bt, t]) end
    else if Substring.isPrefix "(" ss then let
      val ss = Substring.trimr 1 $ Substring.triml 1 $ ss
      val tss = split_on_outer_commas ss
      val ts = List.map parse_abi_type_ss tss
      val ls = mk_list(ts, abi_type_ty)
    in mk_comb(Tuple_tm, ls) end
    else if Substring.isPrefix "uint" ss then let
      val ns = Substring.triml 4 ss
      val SOME n = IntInf.fromString (Substring.string ns)
      val nt = natural n
    in mk_comb(Uint_tm, nt) end
    else if Substring.isPrefix "int" ss then let
      val ns = Substring.triml 3 ss
      val SOME n = IntInf.fromString (Substring.string ns)
      val nt = natural n
    in mk_comb(Int_tm, nt) end
    else if Substring.isPrefix "bytes" ss then let
      val ns = Substring.triml 5 ss
      val bt = parse_optnum_ss ns
    in mk_comb(Bytes_tm, bt) end
    (* TODO: Fixed, Ufixed *)
    else let val s = Substring.string ss
    in   if s = "bool" then Bool_tm
    else if s = "address" then Address_tm
    else if s = "string" then String_tm
    else raise Fail ("parse_abi_type_ss: " ^ s) end

  val parse_abi_type = parse_abi_type_ss o Substring.full

(* Mergesort, without a dependency on a host-specific utility library. *)
fun sort precedes xs = let
  fun split ([], left, right) = (List.rev left, List.rev right)
    | split ([x], left, right) = (List.rev (x::left), List.rev right)
    | split (x::y::rest, left, right) = split (rest, x::left, y::right)
  fun merge ([], ys) = ys
    | merge (xs, []) = xs
    | merge (xs as x::xr, ys as y::yr) =
        if precedes y x then y :: merge (xs,yr) else x :: merge (xr,ys)
  fun go [] = []
    | go [x] = [x]
    | go xs = let val (left,right) = split (xs,[],[])
              in merge (go left, go right) end
in go xs end

fun check cd pred err d =
  andThen cd (fn x => if pred x then d else fail err)

fun check_field lab req =
  check (field lab string) (equal req) (lab ^ " not " ^ req)

fun check_trace_type req = check_field "trace_type" req

val numOfLargeInt = natural

fun achoose err ls = orElse(choose ls, fail err)

val numtm = JSONDecode.map numOfLargeInt intInf
val stringtm = JSONDecode.map fromMLstring string
val booltm = JSONDecode.map mk_bool bool
val negbooltm = JSONDecode.map (mk_bool o not) bool

val address : term decoder = JSONDecode.map address_from_hex string
val bytes : term decoder = JSONDecode.map flat_bytes_from_hex string

val Call_tm = constant{Thy="vyperTestRunner",Name="Call"}

local
  fun descending ([] : IntInf.int list) = true
    | descending [x] = true
    | descending (x::y::ls) = (x-1 = y) andalso descending (y::ls)

  fun ensure_not_empty s = if String.size s = 0 then "0" else s

  fun descending_key (k1 : IntInf.int, _) (k2, _) = k2 < k1
in
val blockHashes : term decoder =
  JSONDecode.map (fn ls => let
    fun f (k,v) = (Option.valOf (IntInf.fromString k),
                   decode (JSONDecode.map (bytes32_from_hex o ensure_not_empty) string) v)
    val ls = List.map f ls
    val ls = sort descending_key ls
    val true = descending (List.map #1 ls)
  in mk_list(List.map #2 ls, bytes32_ty) end) $ rawObject
val blobHashes : term decoder =
  JSONDecode.map (fn ls => mk_list(ls, bytes32_ty)) $
    array (JSONDecode.map (bytes32_from_hex o ensure_not_empty) string)
end

val call : term decoder =
  check_trace_type "call" $
  JSONDecode.map (fn ((a,c,v,t),(p,g,s,(h,bh)),(m,bn,bf,e)) =>
              mk_record (call_trace_ty, [
                ("sender", s),
                ("target", t),
                ("callData", c),
                ("value", v),
                ("timeStamp", m),
                ("blockNumber", bn),
                ("blockHashes", h),
                ("blobHashes", bh),
                ("blobBaseFee", bf),
                ("gasLimit", g),
                ("gasPrice", p),
                ("chainId", natural 1),
                ("static", a),
                ("expectedOutput", e)]))
          (tuple3 (
            field "call_args" $
              tuple4 (field "is_modifying" negbooltm,
                      field "calldata" bytes,
                      field "value" numtm,
                      field "to" address),
            field "env" $
              tuple4 (field "tx" $ field "gas_price" numtm,
                      field "tx" $ field "gas" numtm,
                      field "tx" $ field "origin" address,
                      tuple2 (field "block" $ field "block_hashes" blockHashes,
                              field "tx" $ field "blob_hashes" blobHashes)),
            tuple4 (
              field "env" $ field "block" $ field "timestamp" numtm,
              field "env" $ field "block" $ field "number" numtm,
              field "env" $ field "block" $ field "blob_basefee" numtm,
              field "output" (JSONDecode.map (from_term_option bytes_ty) $
                              nullable bytes))))

fun theoptstring NONE = "" | theoptstring (SOME s) = s

val abiBaseType : term decoder =
  JSONDecode.map parse_abi_type string

fun tuple_brackets s =
  if Substring.isSuffix "]" s then let
    val (ps, ns) = Substring.splitr (not o equal #"[") s
    val bt = parse_optnum_ss ns
    val s = Substring.trimr 1 ps
    val a = mk_comb(Array_tm, bt)
  in
    curry mk_comb a o tuple_brackets s
  end else if Substring.isEmpty s
  then I else raise Fail "not brackets"

fun d_abiType () : term decoder = achoose "abiType" [
  check (field "type" string)
        (String.isPrefix "tuple")
        "not tuple" $
    JSONDecode.map (fn (t, ls) =>
      (tuple_brackets $
       Substring.extract
         (t, String.size "tuple", NONE)) $
      mk_comb(Tuple_tm, mk_list (ls, abi_type_ty))) $
    tuple2 (field "type" string,
            field "components" $ array $ delay d_abiType),
  field "type" abiBaseType
]
val abiType = delay d_abiType

val abiArg : term decoder =
  JSONDecode.map mk_pair $
  tuple2 (field "name" stringtm, abiType)

val abiMutability : term decoder =
  andThen string (fn s =>
    if s = "nonpayable" then succeed Nonpayable_tm else
    if s = "view" then succeed View_tm else
    if s = "payable" then succeed Payable_tm else
    if s = "pure" then succeed Pure_tm else
    fail ("abiMutability: " ^ s))

val Function_tm = constant{Thy="vyperTestRunner",Name="Function"}
val Event_tm = constant{Thy="vyperTestRunner",Name="Event"}
val Error_tm = constant{Thy="vyperTestRunner",Name="Error"}
val abi_arg_ty = mk_prod(string_ty, abi_type_ty)

fun mk_Function (n,is,os,m) =
  mk_comb(Function_tm,
             mk_record (abi_function_ty, [
               ("name", n),
               ("inputs", mk_list(is, abi_arg_ty)),
               ("outputs", mk_list(os, abi_arg_ty)),
               ("mutability", m)]))
fun mk_Error (name, inputs) =
  list_mk_comb(Error_tm, [name, mk_list(inputs, abi_arg_ty)])

(* Only the pinned JSON-ABI exporter emits function entries without
   stateMutability. Normalize those entries before the canonical decoder;
   entries already carrying stateMutability follow the existing path. *)
fun normalize_abi_entry (kvs as (_, _) :: _) = let
  fun lookup key = Option.map #2 (List.find (fn (k, _) => k = key) kvs)
  val original = JSON.OBJECT kvs
  fun invalid msg = raise JSONError (Fail ("legacy ABI: " ^ msg), original)
in
  case (lookup "stateMutability", lookup "constant", lookup "payable") of
    (SOME _, _, _) => original
  | (NONE, NONE, NONE) => original
  | (NONE, SOME (JSON.BOOL constant), SOME (JSON.BOOL payable)) =>
      (case lookup "type" of
         SOME (JSON.STRING "function") =>
           if constant andalso payable then invalid "constant and payable both true"
           else JSON.OBJECT
             (("stateMutability", JSON.STRING
                (if payable then "payable"
                 else if constant then "view" else "nonpayable")) :: kvs)
       | _ => invalid "constant/payable only supported on functions")
  | _ => invalid "constant and payable must both be booleans"
end
  | normalize_abi_entry [] = JSON.OBJECT []

val canonicalAbiEntry : term decoder = achoose "abiEntry" [
    check_field "type" "function" $
    JSONDecode.map mk_Function $
      tuple4 (field "name" stringtm,
              field "inputs" (array abiArg),
              field "outputs" (array abiArg),
              field "stateMutability" abiMutability),
    check_field "type" "constructor" $
    JSONDecode.map mk_Function $
      tuple4 (succeed $ fromMLstring "__init__",
              field "inputs" (array abiArg),
              field "outputs" (array abiArg),
              field "stateMutability" abiMutability),
    check_field "type" "fallback" $
    JSONDecode.map mk_Function $
      tuple4 (succeed $ fromMLstring "__default__",
              succeed $ [],
              succeed $ [],
              field "stateMutability" abiMutability),
    check_field "type" "event" $
    JSONDecode.map (fn s => mk_comb(Event_tm, s)) $
    field "name" stringtm,
    check_field "type" "error" $
    JSONDecode.map mk_Error $
      tuple2 (field "name" stringtm,
              field "inputs" (array abiArg))
  ]

val abiEntry : term decoder =
  JSONDecode.map (decode canonicalAbiEntry o normalize_abi_entry) rawObject

val Deployment_tm = constant{Thy="vyperTestRunner",Name="Deployment"}

val RawDeployment_tm = constant{Thy="vyperTestRunner",Name="RawDeployment"}

val SetBalance_tm = constant{Thy="vyperTestRunner",Name="SetBalance"}
val ClearTransientStorage_tm =
  constant{Thy="vyperTestRunner",Name="ClearTransientStorage"}


val raw_deployment : term decoder =
  check_trace_type "deployment" $
  check (field "deployment_type" string)
        (fn s => s = "raw_bytecode" orelse s = "ir")
        "deployment_type not raw" $
  JSONDecode.map (fn (((i,d,(s,m,a,g),(gl,bn,bf,v)),(h,bh)),(e,bc,n)) =>
    mk_record (raw_deployment_trace_ty, [
      ("deployer", s),
      ("deployerNonce", from_term_option num_ty n),
      ("expectedAddress", a),
      ("expectedSuccess", e),
      ("value", v),
      ("timeStamp", m),
      ("blockNumber", bn),
      ("blockHashes", h),
      ("blobHashes", bh),
      ("blobBaseFee", bf),
      ("gasLimit", gl),
      ("gasPrice", g),
      ("chainId", natural 1),
      ("initcode", i),
      ("callData", d),
      ("expectedRuntimeBytecode", bc)
    ])) $
  tuple2 (
    tuple2 (
      tuple4 (field "initcode" bytes,
              field "calldata" $
                JSONDecode.map (flat_bytes_from_hex o theoptstring)
                  (nullable string),
              tuple4 (field "env" $ field "tx" $ field "origin" address,
                      field "env" $ field "block" $ field "timestamp" numtm,
                      field "deployed_address" address,
                      field "env" $ field "tx" $ field "gas_price" numtm),
              tuple4 (field "env" $ field "tx" $ field "gas" numtm,
                      field "env" $ field "block" $ field "number" numtm,
                      field "env" $ field "block" $ field "blob_basefee" numtm,
                      field "value" numtm)),
      tuple2 (field "env" $ field "block" $ field "block_hashes" blockHashes,
              field "env" $ field "tx" $ field "blob_hashes" blobHashes)),
    tuple3 (field "deployment_succeeded" booltm,
            (* Raw exports sometimes report "" even when initcode deposits
               nonempty code; only nonempty exports are bytecode assertions. *)
            field "runtime_bytecode"
              (JSONDecode.map (fn bc =>
                case bc of
                  SOME "" => mk_none bytes_ty
                | SOME hex => from_term_option bytes_ty
                                (SOME (flat_bytes_from_hex hex))
                | NONE => mk_none bytes_ty) $
               nullable string),
            (* Absent or null in exports that predate it. *)
            fieldD "deployer_nonce" (nullable numtm) NONE))

fun source_codes_json j =
  let
    fun gather (JSON.OBJECT kvs) =
          let
            val here =
              case List.find (fn (k, _) => k = "source_code") kvs of
                SOME (_, JSON.STRING s) => [s]
              | _ => []
            val nested = List.concat (List.map (fn (_, v) => gather v) kvs)
          in
            here @ nested
          end
      | gather (JSON.ARRAY xs) = List.concat (List.map gather xs)
      | gather _ = []
  in
    gather j
  end

(* Sources reading msg.gas get GAS readings from an EVM run of each call. *)
fun reads_gas_source_json j =
  List.exists (fn src => String.isSubstring "msg.gas" src orelse
                         String.isSubstring "msg.mana" src)
    (source_codes_json j)

val deployment : term decoder =
  check_trace_type "deployment" $
  JSONDecode.map (fn (((((((srcs_exps_imap,(i,h,bh),(s,m,a,g),(d,bn,bf,v)),e),bc),sl),bp),rg),ic) =>
             (* translate_annotated_ast returns (sources, exports, import_map) *)
             let val (srcs, exps_import_map) = dest_pair srcs_exps_imap
                 val (exps, import_map) = dest_pair exps_import_map in
             mk_record (deployment_trace_ty, [
               ("sourceAst", srcs),
               ("sourceExports", exps),
               ("importMap", import_map),
               ("contractAbi", mk_list(i, abi_entry_ty)),
               ("deployedAddress", a),
               ("deployer", s),
               ("deploymentSuccess", e),
               ("value", v),
               ("timeStamp", m),
               ("blockNumber", bn),
               ("blockHashes", h),
               ("blobHashes", bh),
               ("blobBaseFee", bf),
               ("gasPrice", g),
               ("chainId", natural 1),
               ("initcode", ic),
               ("callData", d),
               ("runtimeBytecode", bc),
               ("storageLayout", sl),
               ("isBlueprint", bp),
               ("readsGas", rg)
             ]) end)
          (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 (tuple4 (toplevels_via_jsonast,
                           tuple3 (
                             field "contract_abi" (array abiEntry),
                             field "env" $ field "block" $
                               field "block_hashes" blockHashes,
                             field "env" $ field "tx" $
                               field "blob_hashes" blobHashes),
                           tuple4 (field "env" $ field "tx" $ field "origin" address,
                                   field "env" $ field "block" $ field "timestamp" numtm,
                                   field "deployed_address" address,
                                   field "env" $ field "tx" $ field "gas_price" numtm),
                           tuple4 (field "calldata" $
                                   JSONDecode.map (flat_bytes_from_hex o theoptstring)
                                     (nullable string),
                                   field "env" $ field "block" $ field "number" numtm,
                                   field "env" $ field "block" $ field "blob_basefee" numtm,
                                   field "value" numtm)),
                   field "deployment_succeeded" booltm),
                  field "runtime_bytecode" bytes),
                 field "storage_layout" AST.storage_layout),
                JSONDecode.map (fn s => mk_bool (s = "blueprint"))
                  (field "deployment_type" string)),
               JSONDecode.map (fn kvs => mk_bool (reads_gas_source_json (JSON.OBJECT kvs)))
                 rawObject),
              JSONDecode.map (flat_bytes_from_hex o theoptstring)
                (orElse (field "initcode" (nullable string), succeed NONE))))

(* ===== Complete-state checkpoints ===== *)
(* Checkpoint evidence is strict even though legacy trace hex readers accept
   truncated words/odd byte strings. Validate before either backend sees it. *)
fun checkpoint_type name =
  named_type {Thy="vyperStateCheckpoint", Tyop=name}
val checkpoint_account_ty = checkpoint_type "checkpoint_account"
val state_checkpoint_ty = checkpoint_type "state_checkpoint"
val slot_pair_ty = mk_type ("prod", [num_ty,num_ty])
val transient_entry_ty = mk_type ("prod", [word_ty 160,slot_pair_ty])
val log_entry_ty = mk_type ("prod", [word_ty 160,
  mk_type ("prod", [mk_type ("list", [bytes32_ty]),bytes_ty])])

val checkpoint_address_text =
  andThen string (fn s =>
    if String.size s = 42 andalso String.isPrefix "0x" s andalso
       List.all Char.isHexDigit (String.explode (String.extract (s,2,NONE)))
    then succeed (String.map Char.toLower s)
    else fail "checkpoint address must contain exactly 20 hex bytes")
val checkpoint_address = JSONDecode.map address_from_hex checkpoint_address_text
val checkpoint_bytes =
  andThen string (fn s =>
    if String.size s mod 2 = 0 andalso List.all Char.isHexDigit (String.explode s)
    then succeed (bytes_from_hex s)
    else fail "checkpoint byte string must be even-length unprefixed hex")
val checkpoint_topic =
  andThen string (fn s =>
    if String.size s = 64 andalso List.all Char.isHexDigit (String.explode s)
    then succeed (bytes32_from_hex s)
    else fail "checkpoint topic must contain exactly 32 unprefixed hex bytes")
val checkpoint_natural =
  andThen intInf (fn n => if n >= 0 then succeed n
                         else fail "negative checkpoint number")
val checkpoint_word_limit = IntInf.pow (2,256)
val checkpoint_uint256 =
  andThen checkpoint_natural (fn n =>
    if n < checkpoint_word_limit then succeed n
    else fail "checkpoint word exceeds 256 bits")
val checkpoint_num = JSONDecode.map natural checkpoint_natural
val checkpoint_word_num = JSONDecode.map natural checkpoint_uint256

(* Validate uniqueness before zero normalization, including duplicate empty
   accounts and zero-valued slots. Retain input order for stable diagnostics. *)
fun checkpoint_unique_array less d =
  andThen (array d) (fn entries => let
    fun increasing [] = true
      | increasing [_] = true
      | increasing ((k,_)::(rest as (next,_)::_)) =
          less k next andalso increasing rest
    val sorted = sort (fn (a,_) => fn (b,_) => less a b) entries
  in
    if increasing sorted then succeed (List.map #2 entries)
    else fail "duplicate checkpoint key"
  end)
fun checkpoint_num_less (a:IntInf.int) b = a < b
fun checkpoint_address_less (a:string) b = a < b
fun checkpoint_transient_less (a,k) (b,j) =
  checkpoint_address_less a b orelse (a = b andalso checkpoint_num_less k j)

fun checkpoint_unique_members fields =
  let
    fun unique [] = true
      | unique [_] = true
      | unique (name::(rest as next::_)) =
          name <> next andalso unique rest
    val names = sort (fn (a:string) => fn b => a < b)
      (List.map (fn (name,_) => name) fields)
  in unique names end
fun checkpoint_object d =
  check rawObject checkpoint_unique_members "duplicate checkpoint member" d

(* Inspect all discriminators before dispatch: a second trace_type must not
   hide checkpoint evidence behind a legacy trace's first trace_type. *)
fun checkpoint_trace_members fields =
  not (List.exists
    (fn ("trace_type",JSON.STRING "state_checkpoint") => true | _ => false)
    fields) orelse checkpoint_unique_members fields

val checkpoint_slot =
  checkpoint_object $
  JSONDecode.map (fn (k,v) => (k,mk_pair (natural k,v))) $
    tuple2 (field "slot" checkpoint_uint256, field "value" checkpoint_word_num)
val checkpoint_account =
  checkpoint_object $
  JSONDecode.map (fn ((a,b,n,c),s) =>
    (a,mk_record (checkpoint_account_ty,
      [("cpAddress",address_from_hex a),("cpBalance",b),("cpNonce",n),
       ("cpCode",c),("cpStorage",mk_list (s,slot_pair_ty))]))) $
  tuple2 (tuple4 (field "address" checkpoint_address_text,
                  field "balance" checkpoint_word_num,
                  field "nonce" checkpoint_num, field "code" checkpoint_bytes),
          field "storage" (checkpoint_unique_array checkpoint_num_less checkpoint_slot))
val checkpoint_transient =
  checkpoint_object $
  JSONDecode.map (fn (a,(s,v)) =>
    ((a,s),mk_pair (address_from_hex a,mk_pair (natural s,v)))) $
    tuple2 (field "address" checkpoint_address_text,
            tuple2 (field "slot" checkpoint_uint256,field "value" checkpoint_word_num))
val checkpoint_log : term decoder =
  checkpoint_object $
  JSONDecode.map (fn (a,(ts,d)) =>
    mk_pair (a,mk_pair (mk_list (ts,bytes32_ty),d))) $
    tuple2 (field "address" checkpoint_address,
      tuple2 (field "topics" (array checkpoint_topic),
              field "data" checkpoint_bytes))
val state_checkpoint : term decoder =
  check (field "boundary" string)
    (fn s => s = "deployment" orelse s = "call") "invalid checkpoint boundary" $
  JSONDecode.map (fn ((b,i),(accounts,transient,logs)) =>
    mk_record (state_checkpoint_ty,
      [("cpBoundary",b),("cpIndex",i),
       ("cpAccounts",mk_list (accounts,checkpoint_account_ty)),
       ("cpTransient",mk_list (transient,transient_entry_ty)),
       ("cpLogs",mk_list (logs,log_entry_ty))])) $
    tuple2 (tuple2 (field "boundary" stringtm,field "call_index" checkpoint_num),
      tuple3 (field "accounts"
                (checkpoint_unique_array checkpoint_address_less checkpoint_account),
              field "transient_storage"
                (checkpoint_unique_array checkpoint_transient_less checkpoint_transient),
              field "logs" (array checkpoint_log)))

val trace : term decoder =
  check rawObject checkpoint_trace_members "duplicate checkpoint member" $
  andThen (field "trace_type" string) (fn kind =>
    case kind of
      "call" => JSONDecode.map (curry mk_comb Call_tm) call
    | "deployment" =>
        andThen (field "deployment_type" string) (fn deployment_kind =>
          if deployment_kind = "raw_bytecode" orelse deployment_kind = "ir"
          then JSONDecode.map (curry mk_comb RawDeployment_tm) raw_deployment
          else JSONDecode.map (curry mk_comb Deployment_tm) deployment)
    | "clear_transient_storage" => succeed ClearTransientStorage_tm
    | "state_checkpoint" =>
        JSONDecode.map (curry mk_comb (runner_const "StateCheckpoint"))
          state_checkpoint
    | "set_balance" =>
        JSONDecode.map (fn (a,b) => list_mk_comb(SetBalance_tm, [a,b])) $
          tuple2 (field "address" address, field "value" numtm)
    | _ => fail ("unknown trace type: " ^ kind))

(* ===== Fixture / dependency support ===== *)
(* Fixtures are shared setup items (item_type = "fixture") that tests depend
   on via their "deps" field. We resolve deps by prepending fixture traces
   to the test's own traces, so each test runs from a clean state with
   the fixture setup applied first. All current deps are same-file. *)

val indexed_traces =
  JSONDecode.map (fn jsons =>
    let
      fun go _ [] = []
        | go i (json::rest) =
            (decode trace json
             handle e => raise Fail ("trace " ^ Int.toString i ^
               ": " ^ exnMessage e)) :: go (i + 1) rest
    in go 0 jsons end)
    (array (JSONDecode.map JSON.OBJECT rawObject))

val fixture_decoder =
  check_field "item_type" "fixture" $
  field "traces" (array trace)

(* Decoder for test items with deps: reads both "deps" and "traces" fields. *)
val test_with_deps_decoder =
  check_field "item_type" "test" $
  tuple2 (field "deps" (array string),
          field "traces" indexed_traces)

(* Extract fixture name from a dep string.
   Dep format: "tests/export/functional/.../test_file.json/fixture_name"
   We take the part after the last '/' as the fixture name. *)
fun fixture_name_of_dep dep =
  case String.fields (fn c => c = #"/") dep of
    [] => ""
  | parts => List.last parts


(* Inputs retain each consumer's lookup precedence and raw fixture metadata.
   Dependencies are already flattened: preserve their order and repetitions,
   without traversing fixture deps or applying HOL source/coverage policy. *)
fun resolve_fixtures fixtures deps =
  List.map (fn dep =>
    case List.find
      (fn (name, _, _) => name = fixture_name_of_dep dep) fixtures of
      SOME fixture => fixture
    | NONE => raise Fail ("unresolved fixture dependency: " ^ dep)) deps
(* Fixture dependencies are already flattened by the exporter. Resolve only
   their final path component, preserving the exported dependency order. *)
fun decode_cases (JSON.ARRAY values) =
      [("case", decode indexed_traces (JSON.ARRAY values))]
  | decode_cases (original as JSON.OBJECT items) = let
      fun item_kind (_, json) = decode (field "item_type" string) json
      val () = List.app (fn item =>
        case item_kind item of
          "test" => ()
        | "fixture" => ()
        | kind => raise JSONError
            (Fail ("unknown item type: " ^ kind), #2 item)) items
      val fixtures = List.mapPartial (fn (name,json) =>
        if item_kind (name,json) = "fixture"
        then SOME (name, json, decode fixture_decoder json)
        else NONE) items
      fun decode_test (name,json) =
        if item_kind (name,json) = "fixture" then NONE
        else let
          val (deps,traces) = decode test_with_deps_decoder json
          val resolved = resolve_fixtures fixtures deps
            handle e as Fail _ => raise JSONError (e, original)
          val setup = List.concat
            (List.map (fn (_, _, fixture_traces) => fixture_traces) resolved)
        in SOME (name, setup @ traces) end
    in List.mapPartial decode_test items end
  | decode_cases json = raise JSONError
      (Fail "expected exported test object or trace array", json)

end
