module Tokens =
  struct
    type token = 
	(* tokens de controle *)
      | BAD of char | EOF
	    (* tokens classiques *)
      | INT of Int32.t
      | IDENT of string
      | STRING of string
      | PLUS
      | MINUS
      | MULT
      | LPAREN
      | RPAREN
      | COLON
	  (* token pour mots cl�s *)
      | ADD | ADDI | ADDIU
      | SUB | SUBI | SUBIU
      | MUL | MULI | MULIU
      | DIV | DIVI | DIVIU
      | CMP | CMPI | CMPIU
      | MOD | MODI | MODIU
      | AND | ANDI | ANDIU
      | OR | ORI | ORIU
      | XOR | XORI | XORIU
      | BIC | BICI | BICIU
      | LSH | LSHI
      | ASH | ASHI
      | LDW
      | LDB
      | STW
      | STB
      | POP
      | PSH
      | BEQ
      | BNE
      | BLT
      | BGE
      | BGT
      | BLE
      | CHK | CHKI | CHKIU
      | BSR
      | JSR
      | RET
      | BREAK
      | SYSCALL
      | DATA
      | REG of int
	  
    let compare_token t t' =
      match (t,t') with
	| BAD(_),BAD(_) -> 0
	| INT(_),INT(_) -> 0
	| IDENT(_),IDENT(_) -> 0
	| STRING(_),STRING(_) -> 0
	| _,_ -> Pervasives.compare t t'
	    
    let keywords = 
      let keywords = Hashtbl.create 10 in
      let kwds = ["ADD",ADD;"ADDI",ADDI;"ADDIU",ADDIU;
		  "SUB",SUB;"SUBI",SUBI;"SUBIU",SUBIU;
		  "MUL",MUL;"MULI",MULI;"MULIU",MULIU;
		  "DIV",DIV;"DIVI",DIVI;"DIVIU",DIVIU;
		  "CMP",CMP;"CMPI",CMPI;"CMPIU",CMPIU;
		  "MOD",MOD;"MODI",MODI;"MODIU",MODIU;
		  "AND",AND;"ANDI",ANDI;"ANDIU",ANDIU;
		  "OR",OR;"ORI",ORI;"ORIU",ORIU;
		  "XOR",XOR;"XORI",XORI;"XORIU",XORIU;
		  "BIC",BIC;"BICI",BICI;"BICIU",BICIU;
		  "LSH",LSH;"LSHI",LSHI;
		  "ASH",LSH;"ASHI",LSHI;
		  "LDW",LDW;
		  "LDB",LDB;
		  "STW",STW;
		  "STB",STB;
		  "POP",POP;
		  "PSH",PSH;
		  "BEQ",BEQ;
		  "BNE",BNE;
		  "BLT",BLT;
		  "BGE",BGE;
		  "BGT",BGT;
		  "BLE",BLE;
		  "CHK",CHK;"CHKI",CHKI;"CHKIU",CHKIU;
		  "BSR",BSR;
		  "JSR",JSR;
		  "RET",RET;
		  "BREAK",BREAK;
		  "SYSCALL",SYSCALL;
		  "DATA",DATA;
		  "DW",DATA;
		 ] in
      let regs = 
	let l = ref [] in
	  for i = 31 downto 0 do
	    l := (("R"^(string_of_int i)),REG(i)):: !l
	  done;
	  !l
      in
      let kwds = kwds @ regs in
      let kwds = kwds @ (List.map (fun (s,t) -> (String.lowercase s,t)) kwds) in
      let _ = List.iter (fun (s,t) -> Hashtbl.add keywords s t) kwds
      in keywords
	   
    let string_of_token = function
      | BAD(c) -> "<bad:"^(String.make 1 c)^">"
      | EOF -> "<eof>"
      | IDENT(s) -> "IDENT"
      | STRING(s) -> "STRING"
      | INT(n) -> "INT"
      | PLUS -> "+"
      | MINUS -> "-"
      | MULT -> "*"
      | LPAREN -> "("
      | RPAREN -> ")"
      | COLON -> ":"
      | t ->
	  begin
	    match (Hashtbl.fold  (fun s t' str -> if t = t' then Some(s) else str) keywords None) with
	      | Some(s) -> s
	      | None -> "<?>"
	  end
  end
  
open Tokens

class charReader = fun input_char ->
object(self)
  val mutable cchar = Some(' ')
  val mutable ochar = Some(' ')
  val mutable line = 1
  val mutable column = 0
  method private readChar =
    try
      Some(input_char ())
    with
	End_of_file -> None
  method nextChar =
    begin
      match cchar with
	  None -> ()
	| Some('\n') -> 
	    column <- 0;
	    line <- line + 1
	| _ -> 
	    column <- column + 1
    end;
    cchar <- self#readChar;
    ochar <-
    if ochar= Some('\r') && cchar = Some('\n') 
    then self#readChar 
    else cchar;
    cchar <- if ochar = Some('\r') then Some('\n') else ochar
  method currentChar = cchar
  method getPosition = line,column
  initializer
    self#nextChar
end

let charReader_of_string s =
  let i = ref 0 and n = String.length s in
  let input_char () = 
    if !i < n then 
      let c = s.[!i] in incr i; c
    else raise End_of_file
  in
    new charReader input_char

let charReader_of_in_channel c =
  new charReader (function () -> Pervasives.input_char c)

exception UnclosedComment of (int * int)

class scanner = 
  let isChar c = function
      None -> false
    | Some(c') -> c == c'
  in 
  let ( ||| ) f f' c = (f c) || (f' c) 
  and ( === ) c c' = isChar c' c
  and isNot f c = not (f c)
  in
  let isEof = function None -> true | _ -> false in
  let isDigit = function
      None -> false
    | Some(c) -> (match c with '0'..'9' -> true | _ -> false)
  and isLetter = function
      None -> false
    | Some(c) -> (match c with 'a'..'z' | 'A'..'Z' -> true | _ -> false)
  and isWhitespace = (isChar ' ') ||| (isChar '\t') ||| (isChar '\012') ||| (isChar '\n')
  in
    fun (chars:charReader) ->
      let acceptToken t = chars#nextChar;t
      in
      let string_such_that p =
	let buf = Buffer.create 10 in
	  while(p chars#currentChar) do
	    let Some(c) = chars#currentChar in
	      chars#nextChar;
	      Buffer.add_char buf c
	  done;
	  Buffer.contents buf
      in
object(self)
  val mutable token = EOF
  val mutable start = (0,0)
  method private readToken =
    if isWhitespace chars#currentChar then 
      begin
	chars#nextChar; 
	self#readToken
      end
    else
      begin
	start <- chars#getPosition;
	match chars#currentChar with
	    None -> EOF
	  | Some('/') ->
	      begin
		chars#nextChar;
		match chars#currentChar with
		    Some('/') ->
		      while chars#currentChar <> Some('\n') && chars#currentChar <> None do
			chars#nextChar
		      done;
		      self#readToken
		  | Some('*') ->
		      let level = ref 1 in
			while !level > 0 do
			  chars#nextChar;
			  match chars#currentChar with
			      None -> raise (UnclosedComment(start))
			    | Some('/') ->
				chars#nextChar;
				if chars#currentChar = Some('*') then incr level
			    | Some('*') ->
				chars#nextChar;
				if chars#currentChar = Some('/') then decr level
			    | _ -> ()
			done;
			chars#nextChar;
			self#readToken
		  | _ -> BAD('/')
	      end
	  | Some('-') -> acceptToken MINUS
	  | Some('+') -> acceptToken PLUS
	  | Some('*') -> acceptToken MULT
	  | Some('(') -> acceptToken LPAREN
	  | Some(')') -> acceptToken RPAREN
	  | Some(':') -> acceptToken COLON
	  | Some('"') -> 
	      chars#nextChar;
              let isPrematureEnd = isEof ||| (isChar '\n') in
              let string = string_such_that (isNot ((isChar '"') ||| isPrematureEnd)) in
                if isPrematureEnd chars#currentChar then
                  failwith "unterminated string"
                else
                  begin
                    chars#nextChar;
                    STRING(string)
                  end
	  | c when isLetter(c) ->
	      let string = string_such_that (isLetter ||| isDigit ||| (isChar '_')) in
		begin
		  try
		    Hashtbl.find keywords string 
		  with Not_found -> IDENT(string)
		end
	  | c when c === '0' -> acceptToken (INT(Int32.zero))
	  | c when isDigit(c) ->
	      let string = string_such_that isDigit in
		begin
		  try
		    INT(Int32.of_string string)
		  with Failure(_) -> INT(Int32.zero)
		end
	  | Some(c) -> acceptToken (BAD(c))
      end
  method currentToken = token
  method nextToken = token <- self#readToken
  method getPosition = start
  initializer 
    self#nextToken
end

class scannerLLk = fun (chars:charReader) ->
object(self)
  val scanner = new scanner chars
  val mutable start = (0,0)
  val mutable token = EOF
  val mutable tokens = []
  method nextToken = 
    match tokens with
	[] -> 
	  scanner#nextToken;
	  token <- scanner#currentToken;
	  start <- scanner#getPosition
      | (st,tok)::tl ->
	  start <- st;
	  token <- tok;
	  tokens <- tl
  method peekAhead i =
    assert (i >= 0);
    let accu = ref [] in
      for j = List.length tokens to i do
	scanner#nextToken;
	accu := (scanner#getPosition,scanner#currentToken)::(!accu);
      done;
      tokens <- tokens @ (List.rev (!accu));
      snd (List.nth tokens i)
  method getPosition = start
  method currentToken = token
  initializer
    start <- scanner#getPosition;
    token <- scanner#currentToken
end

