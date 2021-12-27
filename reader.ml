(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;
 
 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
 
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
 
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Boolean - Done *)
 let nt_boolt = word_ci "#t";;
 let nt_boolf = word_ci "#f";;
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Chars - Done (check the hexa...) *)
 let digs = range '0' '9';;
 let char_prefix = word "#\\";;
 let visible_simple_char = const (fun ch -> ch >' ');;
 let hex_char s = disj (range_ci 'a' 'f') (digs) s;; 
 
 (* let tmp_hexa_decimal = 
   let nt1 = pack (plus(hex_char)) (fun x ->  int_of_string("0x"^list_to_string x)) in  
   let nt2 = pack nt1 (fun x -> char_of_int x) in nt2;; *)
 (* let hexa_decimal = caten (char 'x') (tmp_hexa_decimal);; *)
 
 let hexadecimal_char str = 
   let nt1 = char_ci 'x' in
   let nt2 = plus hex_char in
   let nt2 = caten nt1 nt2 in
   let nt3 = pack nt2 (fun( prex, hexL)-> char_of_int(int_of_string("0x"^list_to_string(hexL))) ) in
   nt3 str;;
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Numbers *)
 
 
 let natural  = pack (plus(digs)) (fun x -> int_of_string(list_to_string x));;
 let dot = char '.';;
 let mantissa_point = 
   let nt1 = (caten dot (plus(digs))) in
   let nt2 = pack nt1 (fun(d,c) -> d::c) in 
   let nt3 = pack nt2  (fun x -> list_to_string x) in
   let nt4 = pack nt3 (fun y -> float_of_string y) in
   nt4;;
   
 let sign = maybe(disj (const(fun ch -> ch = '+'))  (const(fun ch -> ch = '-')));;
 
 let integer = pack (caten sign natural) (fun s ->
   match s with
   |(Some a, num) -> if(a = '+') then +num else -num
   |((None, num)) -> num
   );;
 let exponent_token = disj (disj (word_ci "e") (word "*10^")) (word "*10**") ;;
 let exponent = pack (caten exponent_token integer) (fun(e,n)-> 10.0** float_of_int n);;
 let fraction str =
   let nt1 = caten (caten integer (not_followed_by (char '/') (char '0'))) natural in
   let nt2 = pack nt1 (fun((nom,_),den) ->  let res = gcd (abs nom) den in
   ScmRational(nom/res , den/res)) in nt2 str;;
 
 let integer_part = pack natural (fun x -> float_of_int x);;
 let point_mantissa = pack (plus(digs)) (fun x -> float_of_string("0."^list_to_string (x)));;
 
 let float_a = pack (caten (caten (caten integer_part dot) (maybe point_mantissa)) (maybe exponent) ) (fun(((prt,dot),mant),exp) -> match mant,exp with 
 | None,None ->  prt
 | None,Some expo -> (prt) *. expo
 | Some man ,None -> (prt) +. (man)
 | Some man, Some expo -> ((prt) +. (man)) *.expo 
 );;
 let float_b = pack (caten mantissa_point (maybe exponent)) (fun(n,exp)-> match exp with 
 |None -> n
 |Some expo -> n *. expo);;
 let float_c =  pack (caten integer_part exponent) (fun(n,e) -> (n) *. e);;
 let flot = disj_list[float_a; float_b; float_c];;
 let floats = pack (caten sign flot) (fun s ->
   match s with
   |(Some a, num) -> if(a = '+') then num else -.num
   |((None, num)) -> num
   );;
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Symbols *)
 let symbol_parser s =
 let specialchar = disj_list [(const (fun ch -> ch='!'||ch='$'||ch='^'||ch='*'||ch='-'||ch='_'||ch='+'||ch='='||ch='<'||ch='>'||ch='?'||ch='/'||ch=':'))] in
 let symbol_char = disj (disj specialchar digs) (range_ci 'a' 'z') in symbol_char s;;
 
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Strings *)
 let string_metachar = caten (char ('\\')) (const (fun ch -> ch='f'||ch='n'||ch='\\'||ch='t'||ch='r'||ch='"'||ch='~'));; (* Check the double ~~ thingy *)
 let replace_metachar s = 
   match s with
     | ('\\','f') -> '\012'
     | ('\\','n') -> '\n'
     | ('\\','t') -> '\t'
     | ('\\','r') -> '\r'
     | ('\\','\\') -> '\\'
     | ('\\', '\"') -> '\"'
     | ('\\', '~') -> '~'
     | (s, r) -> raise X_no_match;;
 let string_the_metachar = pack string_metachar replace_metachar;;
 let string_literalchar =  (const (fun ch -> ch!='\"' && ch!= '\\' && ch!='~'));;
 
 let tmp_string_hexachar = 
   let nt1 = pack (plus(hex_char)) (fun x ->  int_of_string("0x"^list_to_string x)) in  
   let nt2 = pack nt1 (fun x -> char_of_int x) in nt2;;
 let x_hexachar = pack (word "\\x") (fun x -> list_to_string x);;
 
 let string_hexchar =  
   let nt1 = pack (caten x_hexachar tmp_string_hexachar) (fun(a,b) -> b) in nt1;;
 
 let string_char = disj_list [ string_literalchar; string_hexchar ;string_the_metachar];;
 
 
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Lists *)
 let lparen = ( char '(');;
 let rparen = ( char ')');;
 let semicolon = ( char ';');;
 
 (* let proper_list = pack (caten (caten lparen (star(nt_sexpr))) rparen) (fun ((l, e), r) -> match e with 
 | [] -> ScmNil
 | _ -> List.fold_right (fun a b -> ScmPair(a,b)) e ScmNil) ;;
 
 let improper_list str = 
   let nt1 = caten (lparen)  (caten (plus nt_sexpr) (caten (dot) (caten nt_sexpr (rparen)))) in 
   pack nt1 (fun (l ,(starexp ,(dot,(exp, r))))-> match starexp with
   _ -> List.fold_right(fun a b -> ScmPair(a,b)) starexp exp)
   str;; *)
   
   (* pack (caten (caten (caten ((caten lparen (plus(nt_sexpr))) char '.')) nt_sexpr) rparen) (fun ((((l,e1),d),e2),r) -> 
   (* e1::e2 *)
   List.fold_right(fun a b -> ScmPair(a,b)) e1 e2 (* Not sure as well *)
   );; *)
 
 
   
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
 (* Comments *)
 
 
 
 (* Original *)
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str
 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
 and nt_line_comment str =
  (* raise X_not_yet_implemented *)
   let nt1 = caten semicolon nt_end_of_line_or_file in
   let nt2 = unitify (pack nt1 (fun ((e,s)) -> ' ')) in 
   nt2 str
 
   (* Not implemented yet *)
 and nt_paired_comment str = 
 let nt1 = char '{' in
   let nt2 = disj_list[unitify nt_char; unitify nt_string; unitify nt_comment] in
   let nt2' = disj nt2 (unitify (one_of "{}")) in
   let nt3 = diff nt_any nt2' in
   let nt3 = unitify nt3 in
   let nt3 = disj nt3 nt2 in
   let nt3 = star nt3 in
   let nt4 = char '}' in
   let nt1 = unitify (caten nt1 (caten nt3 nt4)) in
   nt1 str;
 
 
 (* raise X_not_yet_implemented *)
 
 
 and nt_sexpr_comment str =
  (* raise X_not_yet_implemented *)
 let nt1 = word "#;" in
     let nt2 = caten nt1 nt_sexpr in
     let nt3 = unitify(pack nt2 (fun _ -> '_' )) in nt3 str
 
 and nt_comment str =
   disj_list
     [nt_line_comment;
      nt_paired_comment;
      nt_sexpr_comment] str
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str
 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1
 
 and nt_int str =  integer str
 and nt_frac str =  fraction str
 and nt_integer_part str = integer_part str
 and nt_mantissa str = point_mantissa str
 and nt_exponent str = exponent str
 and nt_float str = pack floats (fun x -> ScmReal x) str
 
 and nt_number str =
   let nt1 = nt_float in 
   let nt2 = nt_frac in 
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in 
   let nt1 = disj nt1 (disj nt2 nt3) in 
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
 
 and nt_boolean str = disj (pack nt_boolt (fun _-> ScmBoolean(true))) 
   (pack nt_boolf (fun _-> ScmBoolean(false))) str
   
 and nt_char_simple str = visible_simple_char
 and make_named_char char_name ch str= pack (word_ci char_name) (fun s -> match s with |char_name ->ch) str
 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str
 
   (* make sure this is the hex char they want !!!!!!!!!!! *)
 and nt_char_hex str = hex_char str
 and nt_char str =
 let nt1 = caten char_prefix (disj_list [nt_char_named; visible_simple_char; hexadecimal_char] ) in 
 let nt2 = pack nt1 (fun(a,b) -> ScmChar(b)) in nt2 str
 
 (* pack (caten char_prefix (disj_list [nt_char_named; visible_simple_char; hexadecimal_char] )) (fun(a,b) -> ScmChar(b))  *)
 and nt_symbol_char str = symbol_parser str
 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str
 
 and nt_string str = 
 let nt1 = caten (char '"') (caten (star string_char) (char '"')) in
 let nt2 = pack nt1 (fun((l,(s,r)))-> ScmString (list_to_string s)) in
 nt2 str
 
 and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str
 
 
 (* make sure these 2 work, why??????????????????????*)
 and proper_list str = 
 let nt1 = caten (caten lparen (star(nt_sexpr))) rparen in 
 let nt2 = pack nt1 (fun ((l, e), r) -> match e with 
 | [] -> ScmNil
 | _ -> List.fold_right (fun a b -> ScmPair(a,b)) e ScmNil) in nt2 str
 
 and improper_list str = 
   let nt1 = caten (lparen)  (caten (plus nt_sexpr) (caten (dot) (caten nt_sexpr (rparen)))) in 
   pack nt1 (fun (l ,(starexp ,(dot,(exp, r))))-> match starexp with
   _ -> List.fold_right(fun a b -> ScmPair(a,b)) starexp exp)
   str
 
 (* ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////// *)
   (* Quotes *)
   and quote_parser str = 
     (* why char ''' doesn't work idk? *)
   let nt1 =  word "'" in
   let nt2 = pack (caten  nt1 nt_sexpr) (fun (e,s) -> ScmPair(ScmSymbol "quote" , ScmPair(s, ScmNil))) in nt2 str
   
   and quasiquote_parser str=
   let nt1  = (char '`') in
   let nt2 = pack  (caten  nt1 nt_sexpr) (fun (e,s) -> ScmPair(ScmSymbol("quasiquote") , ScmPair(s, ScmNil))) in nt2 str
   
   and unquote_parser str = 
   let nt1 = (char ',') in
   let nt2 = pack  (caten  nt1 nt_sexpr) (fun (e,s) -> ScmPair(ScmSymbol("unquote") , ScmPair(s, ScmNil))) in nt2 str
   
   and unqspliced_parser  str= 
   let nt1 = char ',' in
   let nt2 = caten nt1 (char '@') in
   let nt3 = pack (caten nt2  nt_sexpr) (fun (e,s) -> ScmPair(ScmSymbol("unquote-splicing") , ScmPair(s,ScmNil))) in 
     nt3 str
 
 and nt_list str = disj improper_list proper_list str
 and nt_quoted_forms str =  disj_list[(quote_parser);(quasiquote_parser);(unquote_parser);(unqspliced_parser)] str
 
 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string;nt_vector ;nt_list;nt_quoted_forms;] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;
 