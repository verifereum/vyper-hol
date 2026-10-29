(* JSON import terms retain just the structure inspected by the shared decoder.
   Only encode crosses into the emitted semantics' CV representation. *)
structure JsonImportCV = struct
  open RunTestML
  datatype hol_type = Named of string | Applied of string * hol_type list
                    | WordType of int
  datatype term = Constant of string | Apply of term * term
                | Natural of IntInf.int | Integer of IntInf.int
                | StringValue of string | BoolValue of bool
                | WordValue of int * IntInf.int
                | ListValue of term list * hol_type
                | PairValue of term * term
                | NoneValue of hol_type | SomeValue of term
                | RecordValue of hol_type * (string * term) list
                | Encoded of cv

  fun constant {Thy,Name} = Constant (Thy ^ "." ^ Name)
  fun named_type {Thy,Tyop} = Named (Thy ^ "." ^ Tyop)
  val bool_ty = Named "bool.bool"
  val string_ty = Named "string.string"
  val int_ty = Named "integer.int"
  val num_ty = Named "num.num"
  fun mk_type (name,args) = Applied (name,args)
  fun mk_prod (a,b) = Applied ("prod",[a,b])
  fun mk_option ty = Applied ("option",[ty])
  fun word_ty bits = WordType bits
  fun word_literal (bits,n) = WordValue (bits,IntInf.mod (n,IntInf.pow (2,bits)))
  fun natural n = if n < 0 then raise Fail "negative natural number" else Natural n
  val integer = Integer
  val fromMLstring = StringValue
  val mk_bool = BoolValue
  val mk_comb = Apply
  fun list_mk_comb (head,args) = List.foldl (fn (a,f) => Apply (f,a)) head args
  val mk_pair = PairValue
  val mk_list = ListValue
  val mk_none = NoneValue
  val mk_some = SomeValue

  fun strip_comb tm = let
    fun go (Apply (f,a)) args = go f (a::args)
      | go head args = (head,args)
  in case tm of
       ListValue ([],_) => (constant {Thy="list",Name="NIL"},[])
     | ListValue (x::xs,ty) =>
         (constant {Thy="list",Name="CONS"},[x,ListValue (xs,ty)])
     | PairValue (a,b) => (constant {Thy="pair",Name=","},[a,b])
     | SomeValue x => (constant {Thy="option",Name="SOME"},[x])
     | NoneValue _ => (constant {Thy="option",Name="NONE"},[])
     | _ => go tm []
  end
  fun aconv a b = a = b
  fun is_string_or_natural (StringValue _) = true
    | is_string_or_natural (Natural _) = true
    | is_string_or_natural _ = false
  fun dest_list (ListValue pair) = pair
    | dest_list _ = raise Fail "expected imported list"
  val mk_record = RecordValue

  fun key_of (Named name) = name
    | key_of (Applied (name,[])) = "jsonAST." ^ name
    | key_of _ = raise Fail "expected named record type"
  fun encode tm =
    case tm of
      Encoded cv => cv
    | Natural n => Num n
    | Integer n => if n < 0 then Pair (Num (~n),Num 0) else Num n
    | StringValue s => let
        fun chars i tail =
          if i < 0 then tail
          else chars (i-1) (Pair (Num (IntInf.fromInt (Char.ord (String.sub (s,i)))),tail))
      in chars (String.size s - 1) (Num 0) end
    | BoolValue b => Num (if b then 1 else 0)
    | WordValue (_,n) => Num n
    | ListValue (xs,_) => List.foldr (fn (x,tail) => Pair (encode x,tail)) (Num 0) xs
    | PairValue (a,b) => Pair (encode a,encode b)
    | NoneValue _ => Num 0
    | SomeValue x => Pair (Num 1,encode x)
    | RecordValue (ty,fields) => let
        val name = key_of ty
      in case List.find (fn (key,_,_) => key = name) JsonConstructors.records of
           NONE => raise Fail ("unknown record: " ^ name)
         | SOME (_,labels,build) => let
             fun field name =
               case List.find (fn (key,_) => key = name) fields of
                 SOME (_,value) => encode value
               | NONE => raise Fail ("missing record field: " ^ name)
             val () = if length fields = length labels andalso
                 List.all (fn (key,_) => List.exists (fn label => label=key) labels) fields
               then () else raise Fail ("unexpected fields for " ^ name)
           in build (map field labels) end
      end
    | _ => let val (head,args) = strip_comb tm in
        case head of
          Constant name =>
            (case List.find (fn (key,_) => key=name) JsonConstructors.nodes of
               SOME (_,build) => build (map encode args)
             | NONE => raise Fail ("unknown constructor: " ^ name))
        | _ => raise Fail "expected imported constructor"
      end

  fun dest_pair (PairValue pair) = pair
    | dest_pair (Encoded (Pair (a,b))) = (Encoded a,Encoded b)
    | dest_pair _ = raise Fail "expected imported pair"
  fun is_some (SomeValue _) = true
    | is_some (Encoded (Pair (Num tag,_))) = tag=1
    | is_some _ = false
  fun dest_some (SomeValue x) = x
    | dest_some (Encoded (Pair (Num tag,x))) =
        if tag=1 then Encoded x else raise Fail "expected SOME"
    | dest_some _ = raise Fail "expected SOME"

  fun without_prefix s =
    if String.isPrefix "0x" s then String.extract (s,2,NONE) else s
  fun digit c =
    if c >= #"0" andalso c <= #"9" then Char.ord c - Char.ord #"0"
    else if c >= #"a" andalso c <= #"f" then 10 + Char.ord c - Char.ord #"a"
    else if c >= #"A" andalso c <= #"F" then 10 + Char.ord c - Char.ord #"A"
    else raise Fail "invalid hexadecimal digit"
  (* Match keccak$hex_to_rev_bytes, including UNHEX's total fallback. *)
  fun byte_digit c = if Char.isHexDigit c then digit c else 0
  (* Match Arbnum.fromHexString's scanner and full-consumption check; byte
     strings below deliberately retain keccak's separate permissive rules. *)
  fun hex_number text =
    case IntInf.scan StringCvt.HEX Substring.getc (Substring.full text) of
      SOME (n,rest) =>
        if Substring.isEmpty rest then n
        else raise Fail "invalid hexadecimal word"
    | NONE => raise Fail "invalid hexadecimal word"
  fun address_from_hex s = word_literal (160,hex_number s)
  fun bytes32_from_hex s = word_literal (256,hex_number s)
  fun bytes_from_hex text = let
    val s = without_prefix text
    val size = String.size s
    val tail = if size mod 2 = 0 then [] else
      [word_literal (8,IntInf.fromInt (byte_digit (String.sub (s,size-1))))]
    fun bytes i result =
      if i < 0 then result
      else bytes (i-2)
        (word_literal (8,IntInf.fromInt
          (16*byte_digit (String.sub (s,i)) +
           byte_digit (String.sub (s,i+1)))) :: result)
  in mk_list (bytes (size - size mod 2 - 2) tail,word_ty 8) end
  (* Native values are already concrete byte lists; no HOL cache flattening
     is needed to match the trace importer's byte value. *)
  val flat_bytes_from_hex = bytes_from_hex
end
