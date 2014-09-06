open Scanner.Tokens
open Risc

exception ParseError of string

let string_of_position (l,c) = "line "^(string_of_int l)^", column "^(string_of_int c)

let accept_token scanner t =
  let t' = scanner#currentToken in
    if compare_token t t' = 0 then (scanner#nextToken; t')
    else raise (ParseError("expected token: "^(string_of_token t)^"\tfound:"^(string_of_token t')^" at "^(string_of_position scanner#getPosition)))

let parse_int scanner =
  let INT(n) = accept_token scanner (INT(Int32.zero)) in
    Int32.to_int n

let parse_register scanner =
  match scanner#currentToken with
      REG(n) -> 
	scanner#nextToken;
	R(n)
    | _ ->
	let n = parse_int scanner in
	  if 0 <= n && n <= 31 then R(n)
	  else raise (ParseError("invalid register R"^(string_of_int n)))

let parse_relative scanner code =
  match scanner#currentToken with
      MINUS ->
	scanner#nextToken;
	let n = parse_int scanner in
	  Relative(freeze (-n))
    | IDENT(s) ->
	scanner#nextToken;
	let pc = (code#getLabel "pc") () in
	let label = code#getLabel s in
	  Relative(fun () -> (label ()) - pc)
    | _ ->
	let n = parse_int scanner in
	  Relative(freeze n)

let parse_absolute scanner code =
  match scanner#currentToken with
      MINUS ->
	scanner#nextToken;
	let n = parse_int scanner in
	  Absolute(freeze (-n))
    | IDENT(s) ->
	scanner#nextToken;
	let label = code#getLabel s in
	  Absolute(label)
    | _ ->
	let n = parse_int scanner in
	  Absolute(freeze n)

(* 
   E = T {(+|-) T}
   T = F0 {* F0}
   F0 = [-] F
   F = ( E ) | INT | IDENT
*)

let binop_freeze op e1 e2 () = op (e1 ()) (e2 ())

let unop_freeze op e () = op (e ())

let binop_of_token = function
  | PLUS -> binop_freeze Int32.add
  | MINUS -> binop_freeze Int32.sub
  | MULT -> binop_freeze Int32.mul
  | BAND -> binop_freeze Int32.logand
  | BOR -> binop_freeze Int32.logor
  | BSHL -> binop_freeze (fun x n -> Int32.shift_left x (Int32.to_int n))
  | BSHR -> binop_freeze (fun x n -> Int32.shift_right_logical x (Int32.to_int n))
  | BASHR -> binop_freeze (fun x n -> Int32.shift_right x (Int32.to_int n))

let unop_of_token = function
  | MINUS -> unop_freeze Int32.neg
  | BNOT -> unop_freeze Int32.lognot

let gen_string str =
  let n = String.length str in
  let getChar i = 
    if i < n then Int32.of_int (Char.code str.[i])
    else 0l
  in
  let rec aux i accu =
    if i < n then
      let v = ref 0l in
	for j = 0 to 3 do
	  let c = getChar (i+j) in
	    v := Int32.shift_left (!v) 8;
	    v := Int32.logor (!v) c
	done;
	aux (i+4) (Data(fun () -> !v)::accu)
    else List.rev accu
  in aux 0 []

let rec parse_expression scanner code = 
  let rec aux expr =
    match scanner#currentToken with
	PLUS | MINUS | BOR ->
	  let op = binop_of_token scanner#currentToken in
	    scanner#nextToken;
	    let term = parse_term scanner code in
	      aux (op expr term)
      | _ -> expr
  in aux (parse_term scanner code)
and parse_term scanner code =
  let rec aux term =
    match scanner#currentToken with
	MULT | BAND ->
	  let op = binop_of_token scanner#currentToken in
	    scanner#nextToken;
	    let factor = parse_factor0 scanner code in
	      aux (op term factor)
      | _ -> term
  in aux (parse_factor0 scanner code)
and parse_factor0 scanner code = 
  let factor = parse_factor1 scanner code in
    match scanner#currentToken with
	BSHL | BSHR | BASHR ->
	  let op = binop_of_token scanner#currentToken in
	    scanner#nextToken;
	    let INT(n) = accept_token scanner (INT(0l)) in
	      op factor (freeze n)
      | _ -> factor
and parse_factor1 scanner code =
  match scanner#currentToken with
      MINUS | BNOT -> 
	let op = unop_of_token scanner#currentToken in
	  scanner#nextToken;
	  let factor = parse_factor scanner code in
	    op factor
    | _ -> parse_factor scanner code
and parse_factor scanner code =
  match scanner#currentToken with
      INT(n) ->
	scanner#nextToken;
	(freeze n)
    | IDENT(s) ->
	scanner#nextToken;
	let label = code#getLabel s in
	  (fun () -> Int32.of_int (4*label ()))
    | _ ->
	ignore (accept_token scanner LPAREN);
	let e = parse_expression scanner code in
	  ignore (accept_token scanner RPAREN);
	  e

let parse_int_expression scanner code =
  let e = parse_expression scanner code in
    (fun () -> (Int32.to_int (e ())))

let parse_a_riiu_r scanner code = AR(parse_register scanner)
let parse_a_riiu_i scanner code = AI(Signed(parse_int_expression scanner code))
let parse_a_riiu_iu scanner code = AIU(Unsigned(parse_int_expression scanner code))

let parse_b_ri_r scanner code = BR(parse_register scanner)
let parse_b_ri_i scanner code = BI(Signed(parse_int_expression scanner code))

let arith_op_of_token = function
    | ADD -> Add,parse_a_riiu_r
    | SUB -> Sub,parse_a_riiu_r
    | MUL -> Mul,parse_a_riiu_r
    | DIV -> Div,parse_a_riiu_r
    | CMP -> Cmp,parse_a_riiu_r
    | MOD -> Mod,parse_a_riiu_r
    | ADDI -> Add,parse_a_riiu_i
    | SUBI -> Sub,parse_a_riiu_i
    | MULI -> Mul,parse_a_riiu_i
    | DIVI -> Div,parse_a_riiu_i
    | CMPI -> Cmp,parse_a_riiu_i
    | MODI -> Mod,parse_a_riiu_i
    | ADDIU -> Add,parse_a_riiu_iu
    | SUBIU -> Sub,parse_a_riiu_iu
    | MULIU -> Mul,parse_a_riiu_iu
    | DIVIU -> Div,parse_a_riiu_iu
    | CMPIU -> Cmp,parse_a_riiu_iu
    | MODIU -> Mod,parse_a_riiu_iu

let log_op_of_token = function
    | AND -> And,parse_a_riiu_r
    | OR -> Or,parse_a_riiu_r
    | XOR -> Xor,parse_a_riiu_r
    | BIC -> Bic,parse_a_riiu_r
    | ANDI -> And,parse_a_riiu_i
    | ORI -> Or,parse_a_riiu_i
    | XORI -> Xor,parse_a_riiu_i
    | BICI -> Bic,parse_a_riiu_i
    | ANDIU -> And,parse_a_riiu_iu
    | ORIU -> Or,parse_a_riiu_iu
    | XORIU -> Xor,parse_a_riiu_iu
    | BICIU -> Bic,parse_a_riiu_iu

let sh_op_of_token = function
  | LSH -> Lsh,parse_b_ri_r
  | ASH -> Ash,parse_b_ri_r
  | LSHI -> Lsh,parse_b_ri_i
  | ASHI -> Ash,parse_b_ri_i

let mem_op_of_token = function
    LDW -> Ldw
  | STW -> Stw
  | LDB -> Ldb
  | STB -> Stb
  | PSH -> Psh
  | POP -> Pop

let test_op_of_token = function
    BEQ -> Beq
  | BNE -> Bne
  | BGT -> Bgt
  | BLE -> Ble
  | BGE -> Bge
  | BLT -> Blt 

let chk_op_of_token = function
  | CHK -> (fun a c -> Chk(a,c)),parse_a_riiu_r
  | CHKI -> (fun a c -> Chk(a,c)),parse_a_riiu_i
  | CHKIU -> (fun a c -> Chk(a,c)),parse_a_riiu_iu

let parse_instruction scanner code =
  match scanner#currentToken with
    | ADD | ADDI | ADDIU
    | SUB | SUBI | SUBIU
    | MUL | MULI | MULIU
    | DIV | DIVI | DIVIU
    | CMP | CMPI | CMPIU
    | MOD | MODI | MODIU ->
	let (op,third) = arith_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = parse_register scanner in
	  let rb = parse_register scanner in
	  let rc = third scanner code in
	    [IArith(op,ra,rb,rc)]
    | AND | ANDI | ANDIU
    | OR | ORI | ORIU
    | XOR | XORI | XORIU
    | BIC | BICI | BICIU ->
	let (op,third) = log_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = parse_register scanner in
	  let rb = parse_register scanner in
	  let rc = third scanner code in
	    [ILog(op,ra,rb,rc)]
    | LSH | LSHI
    | ASH | ASHI ->
	let (op,third) = sh_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = parse_register scanner in
	  let rb = parse_register scanner in
	  let rc = third scanner code in
	    [ISh(op,ra,rb,rc)]
    | LDW
    | LDB
    | STW
    | STB
    | POP
    | PSH ->
	let op = mem_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = parse_register scanner in
	  let rb = parse_register scanner in
	  let rc = Signed(parse_int_expression scanner code) in
	    [IMem(op,ra,rb,rc)]
    | BEQ
    | BNE
    | BLT
    | BGE
    | BGT
    | BLE ->
	let op = test_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = parse_register scanner in
	  let rc = parse_relative scanner code in
	    [ITest(op,ra,rc)]
    | CHK | CHKI | CHKIU ->
	let chk,second = chk_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = parse_register scanner in
	  let rc = second scanner code in
	    [chk ra rc]
    | BSR ->
	scanner#nextToken;
	let rc = parse_relative scanner code in
	  [Bsr(rc)]
    | JSR ->
	scanner#nextToken;
	let rc = parse_absolute scanner code in
	  [Jsr(rc)]
    | RET ->
	scanner#nextToken;
	let ra = parse_register scanner in
	  [Ret(ra)]
    | BREAK ->
	scanner#nextToken;
	[Break]
    | SYSCALL ->
	scanner#nextToken;
	let ra = parse_register scanner in
	let rb = parse_register scanner in
	let n = parse_int scanner in
	  (match syscall_of_int n with
	       Some(syscall) -> [Syscall(ra,rb,syscall)]
	     | None -> raise (ParseError("unknown syscall: "^(string_of_int n))))
    | DATA ->
	scanner#nextToken;
	let e = parse_expression scanner code in
	  [Data(e)]
    | ASCIIZ ->
	scanner#nextToken;
	let STRING(s) = accept_token scanner (STRING("")) in
	  gen_string (s^"\000")
    | ASCIIL ->
	scanner#nextToken;
	let STRING(s) = accept_token scanner (STRING("")) in
	  gen_string ((String.make 1 (Char.chr (String.length s)))^s)
    | _ -> raise (ParseError("expected token: "^"a mnemonic"^"\tfound:"^(string_of_token scanner#currentToken)^" at "^(string_of_position scanner#getPosition)))

let parse_program scanner = 
  let rec aux code = 
    match scanner#currentToken with
	EOF -> code
      | IDENT(s) ->
	  scanner#nextToken;
	  ignore (accept_token scanner COLON);
	  code#setLabel s;
	  aux code
      | _ -> 
	  List.iter code#emit (parse_instruction scanner code);
	  aux code
  in aux (new code_generator)
