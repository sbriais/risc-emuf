open Scanner.Tokens
open Risc

exception ParseError of string

let string_of_position (l,c) = "line "^(string_of_int l)^", column "^(string_of_int c)

let accept_token scanner t =
  let t' = scanner#currentToken in
    if compare_token t t' = 0 then (scanner#nextToken; t')
    else raise (ParseError("expected token: "^(string_of_token t)^"\tfound:"^(string_of_token t')^" at "^(string_of_position scanner#getPosition)))

let analyze_int scanner =
  let INT(n) = accept_token scanner (INT(Int32.zero)) in
    Int32.to_int n

let analyze_register scanner =
  match scanner#currentToken with
      REG(n) -> 
	scanner#nextToken;
	R(n)
    | _ ->
	let n = analyze_int scanner in
	  if 0 <= n && n <= 31 then R(n)
	  else raise (ParseError("invalid register R"^(string_of_int n)))

let analyze_relative scanner code =
  match scanner#currentToken with
      MINUS ->
	scanner#nextToken;
	let n = analyze_int scanner in
	  Relative(freeze (-n))
    | IDENT(s) ->
	scanner#nextToken;
	let pc = (code#getLabel "pc") () in
	let label = code#getLabel s in
	  Relative(fun () -> (label ()) - pc)
    | _ ->
	let n = analyze_int scanner in
	  Relative(freeze n)

let analyze_absolute scanner code =
  match scanner#currentToken with
      MINUS ->
	scanner#nextToken;
	let n = analyze_int scanner in
	  Absolute(freeze (-n))
    | IDENT(s) ->
	scanner#nextToken;
	let label = code#getLabel s in
	  Absolute(label)
    | _ ->
	let n = analyze_int scanner in
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

let unop_of_token = function
  | MINUS -> unop_freeze Int32.neg

let rec analyze_expression scanner code = 
  let rec aux expr =
    match scanner#currentToken with
	PLUS | MINUS ->
	  let op = binop_of_token scanner#currentToken in
	    scanner#nextToken;
	    let term = analyze_term scanner code in
	      aux (op expr term)
      | _ -> expr
  in aux (analyze_term scanner code)
and analyze_term scanner code =
  let rec aux term =
    match scanner#currentToken with
	MULT ->
	  let op = binop_of_token scanner#currentToken in
	    scanner#nextToken;
	    let factor = analyze_factor0 scanner code in
	      aux (op term factor)
      | _ -> term
  in aux (analyze_factor0 scanner code)
and analyze_factor0 scanner code =
  match scanner#currentToken with
      MINUS -> 
	let op = unop_of_token scanner#currentToken in
	  scanner#nextToken;
	  let factor = analyze_factor scanner code in
	    op factor
    | _ -> analyze_factor scanner code
and analyze_factor scanner code =
  match scanner#currentToken with
      INT(n) ->
	scanner#nextToken;
	(freeze n)
    | IDENT(s) ->
	scanner#nextToken;
	let label = code#getLabel s in
	  (fun () -> Int32.of_int (label ()))
    | _ ->
	ignore (accept_token scanner LPAREN);
	let e = analyze_expression scanner code in
	  ignore (accept_token scanner RPAREN);
	  e

let analyze_int_expression scanner code =
  let e = analyze_expression scanner code in
    (fun () -> (Int32.to_int (e ())))

let analyze_a_riiu_r scanner code = AR(analyze_register scanner)
let analyze_a_riiu_i scanner code = AI(Signed(analyze_int_expression scanner code))
let analyze_a_riiu_iu scanner code = AIU(Unsigned(analyze_int_expression scanner code))

let analyze_b_ri_r scanner code = BR(analyze_register scanner)
let analyze_b_ri_i scanner code = BI(Signed(analyze_int_expression scanner code))

let arith_op_of_token = function
    | ADD -> Add,analyze_a_riiu_r
    | SUB -> Sub,analyze_a_riiu_r
    | MUL -> Mul,analyze_a_riiu_r
    | DIV -> Div,analyze_a_riiu_r
    | CMP -> Cmp,analyze_a_riiu_r
    | MOD -> Mod,analyze_a_riiu_r
    | ADDI -> Add,analyze_a_riiu_i
    | SUBI -> Sub,analyze_a_riiu_i
    | MULI -> Mul,analyze_a_riiu_i
    | DIVI -> Div,analyze_a_riiu_i
    | CMPI -> Cmp,analyze_a_riiu_i
    | MODI -> Mod,analyze_a_riiu_i
    | ADDIU -> Add,analyze_a_riiu_iu
    | SUBIU -> Sub,analyze_a_riiu_iu
    | MULIU -> Mul,analyze_a_riiu_iu
    | DIVIU -> Div,analyze_a_riiu_iu
    | CMPIU -> Cmp,analyze_a_riiu_iu
    | MODIU -> Mod,analyze_a_riiu_iu

let log_op_of_token = function
    | AND -> And,analyze_a_riiu_r
    | OR -> Or,analyze_a_riiu_r
    | XOR -> Xor,analyze_a_riiu_r
    | BIC -> Bic,analyze_a_riiu_r
    | ANDI -> And,analyze_a_riiu_i
    | ORI -> Or,analyze_a_riiu_i
    | XORI -> Xor,analyze_a_riiu_i
    | BICI -> Bic,analyze_a_riiu_i
    | ANDIU -> And,analyze_a_riiu_iu
    | ORIU -> Or,analyze_a_riiu_iu
    | XORIU -> Xor,analyze_a_riiu_iu
    | BICIU -> Bic,analyze_a_riiu_iu

let sh_op_of_token = function
  | LSH -> Lsh,analyze_b_ri_r
  | ASH -> Ash,analyze_b_ri_r
  | LSHI -> Lsh,analyze_b_ri_i
  | ASHI -> Ash,analyze_b_ri_i

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
  | CHK -> (fun a c -> Chk(a,c)),analyze_a_riiu_r
  | CHKI -> (fun a c -> Chk(a,c)),analyze_a_riiu_i
  | CHKIU -> (fun a c -> Chk(a,c)),analyze_a_riiu_iu

let analyze_instruction scanner code =
  match scanner#currentToken with
    | ADD | ADDI | ADDIU
    | SUB | SUBI | SUBIU
    | MUL | MULI | MULIU
    | DIV | DIVI | DIVIU
    | CMP | CMPI | CMPIU
    | MOD | MODI | MODIU ->
	let (op,third) = arith_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = analyze_register scanner in
	  let rb = analyze_register scanner in
	  let rc = third scanner code in
	    IArith(op,ra,rb,rc)
    | AND | ANDI | ANDIU
    | OR | ORI | ORIU
    | XOR | XORI | XORIU
    | BIC | BICI | BICIU ->
	let (op,third) = log_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = analyze_register scanner in
	  let rb = analyze_register scanner in
	  let rc = third scanner code in
	    ILog(op,ra,rb,rc)
    | LSH | LSHI
    | ASH | ASHI ->
	let (op,third) = sh_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = analyze_register scanner in
	  let rb = analyze_register scanner in
	  let rc = third scanner code in
	    ISh(op,ra,rb,rc)
    | LDW
    | LDB
    | STW
    | STB
    | POP
    | PSH ->
	let op = mem_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = analyze_register scanner in
	  let rb = analyze_register scanner in
	  let rc = Signed(analyze_int_expression scanner code) in
	    IMem(op,ra,rb,rc)
    | BEQ
    | BNE
    | BLT
    | BGE
    | BGT
    | BLE ->
	let op = test_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = analyze_register scanner in
	  let rc = analyze_relative scanner code in
	    ITest(op,ra,rc)
    | CHK | CHKI | CHKIU ->
	let chk,second = chk_op_of_token scanner#currentToken in
	  scanner#nextToken;
	  let ra = analyze_register scanner in
	  let rc = second scanner code in
	    chk ra rc
    | BSR ->
	scanner#nextToken;
	let rc = analyze_relative scanner code in
	  Bsr(rc)
    | JSR ->
	scanner#nextToken;
	let rc = analyze_absolute scanner code in
	  Jsr(rc)
    | RET ->
	scanner#nextToken;
	let ra = analyze_register scanner in
	  Ret(ra)
    | BREAK ->
	scanner#nextToken;
	Break
    | SYSCALL ->
	scanner#nextToken;
	let ra = analyze_register scanner in
	let rb = analyze_register scanner in
	let n = analyze_int scanner in
	  (match syscall_of_int n with
	       Some(syscall) -> Syscall(ra,rb,syscall)
	     | None -> raise (ParseError("unknown syscall: "^(string_of_int n))))
    | DATA ->
	scanner#nextToken;
	let e = analyze_expression scanner code in
	  Data(e)
    | _ -> raise (ParseError("expected token: "^"a mnemonic"^"\tfound:"^(string_of_token scanner#currentToken)^" at "^(string_of_position scanner#getPosition)))

let analyze_program scanner = 
  let rec aux code = 
    match scanner#currentToken with
	EOF -> code
      | IDENT(s) ->
	  scanner#nextToken;
	  ignore (accept_token scanner COLON);
	  code#setLabel s;
	  aux code
      | _ -> 
	  code#emit (analyze_instruction scanner code);
	  aux code
  in aux (new code_generator)
